import base64
import json
import os
import re
import subprocess
import sys
import threading
import time
import traceback
import tkinter as tk
from pathlib import Path
from tkinter import filedialog, messagebox, ttk


def _boot_log_crash(err_text):
    """启动/导入崩溃时把堆栈写到程序旁的 crash.log，便于诊断。"""
    try:
        base = Path(sys.executable).parent if getattr(sys, "frozen", False) else Path(__file__).parent
        (base / "crash.log").write_text(err_text, encoding="utf-8")
    except Exception:
        pass


try:
    import imageio_ffmpeg
    import numpy as np
except Exception:
    _boot_log_crash(traceback.format_exc())
    raise

def _res_base():
    """PyInstaller 打包后资源在 _MEIPASS 临时目录；源码运行时在脚本目录。"""
    return Path(getattr(sys, "_MEIPASS", Path(__file__).parent))


DEFAULT_CODEBOOK = _res_base() / "codebook.json"

# 视频：字符 -> 帧颜色（RGB）
COLOR_MAP = {
    "0": (0, 0, 0),       # 黑
    "1": (255, 255, 255), # 白
    " ": (128, 128, 128), # 灰（分隔符）
}
YELLOW = (255, 255, 0)

# 音轨：帧颜色 -> 正弦波频率（黑=高频，灰=中频，白=低频，黄/tab 分隔=无声）
FREQ_MAP = {
    "0": 3000.0,  # 黑 -> 高频
    " ": 1000.0,  # 灰 -> 中频
    "1": 300.0,   # 白 -> 低频
}
SAMPLE_RATE = 44100
AUDIO_CHUNK_FRAMES = 1024  # 音频分块写入的帧数（约34秒/块@30fps），内存占用恒定

YELLOW_FRAMES = 3  # 头声明与正文之间的黄色分隔帧数

# v2 正文格式：每帧按 BxB 像素块打包，块黑=0 / 白=1 / 灰=码元分隔，
# 每帧承载 (w/B)*(h/B) 个码元，密度比 v1（整帧=1比特）高数百倍
BLOCK = 2
BODY_BATCH = 256  # 正文帧批量构建写入的批大小
BIT_TABLE = str.maketrans("01 ", "\x00\x01\x02")  # token 比特流 -> 码元字节
CELL_LUT = np.array([(0, 0, 0), (255, 255, 255), (128, 128, 128)], dtype=np.uint8)

# 水印：底部黑条内 3x5 点阵白字（帧过小时自动省略，头声明退回 V2）
WATERMARK = "sgz541122ouo"
WM_FONT = {  # 3x5 像素点阵，每行 3 位（bit2=左列），1=点亮
    "s": (7, 4, 7, 1, 7), "g": (7, 5, 7, 1, 6), "z": (7, 1, 2, 4, 7),
    "5": (7, 4, 7, 1, 7), "4": (5, 5, 7, 1, 1), "1": (2, 6, 2, 2, 7),
    "2": (7, 1, 7, 4, 7), "o": (7, 5, 5, 5, 7), "u": (5, 5, 5, 5, 7),
}
WM_ROWS = 3  # 底部水印条占用的 cell 行数（6 像素高）


def _wm_ok(w, h):
    """帧足够大才启用水印（容纳 48x6 点阵且不干扰整帧颜色分类）。"""
    return w >= 64 and h >= 32


def _wm_text_pts(w, h):
    """水印白色文字像素坐标（底部左侧，1px 边距）。"""
    ys, xs = [], []
    x, y0 = 1, h - 6
    for ch in WATERMARK:
        for ry, rowbits in enumerate(WM_FONT[ch]):
            for rx in range(3):
                if rowbits >> (2 - rx) & 1:
                    ys.append(y0 + ry)
                    xs.append(x + rx)
        x += 4
    return np.array(ys), np.array(xs)


def _stamp_wm(frame, wm_pts):
    """在整帧纯色帧上画水印：先黑影(+1,+1)再白字，浅色帧上也可见。"""
    ty, tx = wm_pts
    frame[ty + 1, tx + 1] = 0
    frame[ty, tx] = 255


class App:
    def __init__(self, root):
        self.root = root
        self.root.title("FileVideoCoder")
        self.root.geometry("1180x560")

        # ============ 左栏：编码成视频 ============
        left = tk.LabelFrame(root, text="编码：文件 → 视频", padx=8, pady=6)
        left.grid(row=0, column=0, sticky="nw", padx=10, pady=8)

        tk.Label(left, text="输入文件:").grid(row=0, column=0, sticky="w", pady=4)
        self.input_var = tk.StringVar()
        tk.Entry(left, textvariable=self.input_var, width=46).grid(row=0, column=1, padx=4)
        tk.Button(left, text="浏览...", command=lambda: self._pick(
            self.input_var, save=False, filetypes=[("所有文件", "*.*")])
        ).grid(row=0, column=2)

        tk.Label(left, text="视频输出:").grid(row=1, column=0, sticky="w", pady=4)
        self.video_var = tk.StringVar()
        tk.Entry(left, textvariable=self.video_var, width=46).grid(row=1, column=1, padx=4)
        tk.Button(left, text="另存为...", command=lambda: self._pick(
            self.video_var, save=True, defaultextension=".mkv",
            filetypes=[("MKV", "*.mkv"), ("MP4", "*.mp4"), ("All", "*.*")])
        ).grid(row=1, column=2)

        tk.Label(left, text="编码表:").grid(row=2, column=0, sticky="w", pady=4)
        self.cb_enc_var = tk.StringVar(value=str(DEFAULT_CODEBOOK))
        tk.Entry(left, textvariable=self.cb_enc_var, width=46).grid(row=2, column=1, padx=4)
        tk.Button(left, text="浏览...", command=lambda: self._pick(
            self.cb_enc_var, save=False, filetypes=[("JSON", "*.json"), ("All", "*.*")])
        ).grid(row=2, column=2)

        tk.Label(left, text="视频参数:").grid(row=3, column=0, sticky="w", pady=4)
        param = tk.Frame(left)
        param.grid(row=3, column=1, sticky="w")
        self.size_var = tk.StringVar(value="80x80")
        self.fps_var = tk.StringVar(value="60")
        tk.Label(param, text="尺寸:").pack(side="left")
        tk.Entry(param, textvariable=self.size_var, width=10).pack(side="left", padx=4)
        tk.Label(param, text="帧率:").pack(side="left")
        tk.Entry(param, textvariable=self.fps_var, width=5).pack(side="left", padx=4)

        self.btn_encode = tk.Button(left, text="开始（编码 → 视频）", command=self.start_encode,
                                    bg="#4CAF50", fg="white", width=30)
        self.btn_encode.grid(row=4, column=0, columnspan=3, pady=10)

        # ============ 右栏：解码成文件 ============
        right = tk.LabelFrame(root, text="解码：视频 → 文件", padx=8, pady=6)
        right.grid(row=0, column=1, sticky="nw", padx=10, pady=8)

        tk.Label(right, text="视频输入:").grid(row=0, column=0, sticky="w", pady=4)
        self.vid_in_var = tk.StringVar()
        tk.Entry(right, textvariable=self.vid_in_var, width=46).grid(row=0, column=1, padx=4)
        tk.Button(right, text="浏览...", command=lambda: self._pick(
            self.vid_in_var, save=False,
            filetypes=[("Video", "*.mkv *.mp4"), ("All", "*.*")])
        ).grid(row=0, column=2)

        tk.Label(right, text="文件输出:").grid(row=1, column=0, sticky="w", pady=4)
        self.text_out_var = tk.StringVar()
        tk.Entry(right, textvariable=self.text_out_var, width=46).grid(row=1, column=1, padx=4)
        tk.Button(right, text="另存为...", command=lambda: self._pick(
            self.text_out_var, save=True, defaultextension="",
            filetypes=[("All", "*.*")])
        ).grid(row=1, column=2)

        tk.Label(right, text="编码表:").grid(row=2, column=0, sticky="w", pady=4)
        self.cb_dec_var = tk.StringVar(value=str(DEFAULT_CODEBOOK))
        tk.Entry(right, textvariable=self.cb_dec_var, width=46).grid(row=2, column=1, padx=4)
        tk.Button(right, text="浏览...", command=lambda: self._pick(
            self.cb_dec_var, save=False, filetypes=[("JSON", "*.json"), ("All", "*.*")])
        ).grid(row=2, column=2)

        tk.Label(right, text="说明:").grid(row=3, column=0, sticky="nw", pady=4)
        tk.Label(right, text="黄帧前=头声明(Base64编码的文件名)，黄帧后=内容；\n"
                             "正文按像素块打包(黑=0/白=1/灰=分隔)；\n"
                             "解码后全部 Base64 还原为原始文件。",
                 fg="gray", justify="left").grid(row=3, column=1, columnspan=2, sticky="w")

        self.btn_decode = tk.Button(right, text="开始解码", command=self.start_decode,
                                    bg="#2196F3", fg="white", width=30)
        self.btn_decode.grid(row=4, column=0, columnspan=3, pady=10)

        # ============ 底部：进度 + 状态 ============
        bottom = tk.Frame(root)
        bottom.grid(row=1, column=0, columnspan=2, sticky="ew", padx=10, pady=8)
        self.progress = ttk.Progressbar(bottom, mode="determinate", length=900)
        self.progress.pack(side="left", padx=4)
        self.status_var = tk.StringVar(value="就绪")
        tk.Label(bottom, textvariable=self.status_var, fg="gray").pack(side="left", padx=8)

    # ---------- UI 辅助 ----------
    def _pick(self, var, save, filetypes=None, defaultextension=".txt"):
        if filetypes is None:
            filetypes = [("Text files", "*.txt"), ("All files", "*.*")]
        if save:
            path = filedialog.asksaveasfilename(defaultextension=defaultextension,
                                                filetypes=filetypes)
        else:
            path = filedialog.askopenfilename(filetypes=filetypes)
        if path:
            var.set(path)

    def _reset_progress(self, msg):
        self.progress.config(mode="determinate")
        self.progress["value"] = 0
        self.status_var.set(msg)

    def _fail(self, msg):
        self.progress.config(mode="determinate")
        self.progress.stop()
        self.progress["value"] = 0
        self.status_var.set(msg)
        self.btn_encode.config(state="normal")
        self.btn_decode.config(state="normal")
        messagebox.showerror("错误", msg)

    def _fail_after(self, msg):
        """主线程弹错误。msg 必须在调用处立即求值——except 的 e 会随块结束解绑，
        不能写进 lambda 里延迟引用。"""
        self.root.after(0, lambda: self._fail(msg))

    def _done(self, msg):
        self.progress.config(mode="determinate")
        self.progress["value"] = 100
        self.status_var.set(msg)
        self.btn_encode.config(state="normal")
        self.btn_decode.config(state="normal")
        messagebox.showinfo("完成", msg)

    def _set_buttons(self, state):
        self.btn_encode.config(state=state)
        self.btn_decode.config(state=state)

    # ---------- 编码入口 ----------
    def start_encode(self):
        inp = self.input_var.get().strip()
        vid_out = self.video_var.get().strip()
        cb = self.cb_enc_var.get().strip()
        if not inp or not vid_out:
            messagebox.showwarning("提示", "请选择输入文件和视频输出")
            return
        if not cb or not Path(cb).exists():
            messagebox.showwarning("提示", "编码表不存在")
            return
        try:
            w, h = (int(x) for x in self.size_var.get().lower().split("x"))
            fps = int(self.fps_var.get())
            if w < BLOCK or h < BLOCK or fps <= 0 or w % BLOCK or h % BLOCK:
                raise ValueError
        except Exception:
            messagebox.showwarning("提示", "尺寸需为 2 的倍数（如 80x80），帧率为正整数")
            return
        self._set_buttons("disabled")
        self.root.after(0, lambda: self._reset_progress("处理中..."))
        threading.Thread(target=self._do_encode, args=(inp, vid_out, cb, (w, h), fps),
                         daemon=True).start()

    # ---------- 解码入口 ----------
    def start_decode(self):
        vid_in = self.vid_in_var.get().strip()
        text_out = self.text_out_var.get().strip()
        cb = self.cb_dec_var.get().strip()
        if not vid_in or not text_out:
            messagebox.showwarning("提示", "请选择视频输入和文件输出")
            return
        if not cb or not Path(cb).exists():
            messagebox.showwarning("提示", "编码表不存在")
            return
        self._set_buttons("disabled")
        self.root.after(0, lambda: self._reset_progress("解码中..."))
        threading.Thread(target=self._do_decode, args=(vid_in, text_out, cb), daemon=True).start()

    # ---------- 核心处理 ----------
    def _encode_text(self, text, codebook):
        """全文逐字符编码；未收录字符自动分配新码并加入编码表（写回文件由调用方负责）。

        token 以空格分隔，解码按空格切分，不依赖固定位宽。
        编码统一 15 位定长（可容纳 32768 个字符），仅当超过才自动升位。
        """
        all_tokens, encoded, added = [], 0, []
        total = len(text)
        last_ui = 0.0
        for i, ch in enumerate(text):
            now = time.monotonic()
            if now - last_ui >= 0.2 or i == total - 1:  # 按时间节流，避免UI回调堆积
                last_ui = now
                v = (i + 1) * 100 / max(total, 1)
                self.root.after(0, lambda v=v: self.progress.configure(value=v))
                self.root.after(0, lambda cur=i + 1, tot=total:
                                self.status_var.set(f"编码中... {cur}/{tot} 字符"))
            if ch == "\r":
                continue  # \r\n 读取时已统一为 \n，回车符跳过
            if ch not in codebook:
                code = len(codebook)
                # 统一 7 位定长（Base64 仅需 65 个码，7 位可容 128）；超出才自动升位
                width = max(7, code.bit_length())
                codebook[ch] = format(code, f"0{width}b")
                added.append(ch)
            all_tokens.append(codebook[ch])
            encoded += 1
        return " ".join(all_tokens), encoded, added

    def _make_video(self, lang_tokens, body_tokens, out_path, size, fps):
        """结构：头声明帧（V3:/V2: 开头的整帧比特） → 3黄帧 → 正文块帧。

        正文为 v2 块格式：每帧切成 BxB 像素块，块黑=0/白=1/灰=码元分隔。
        启用水印时（V3:）底部 WM_ROWS 行 cell 为黑底白字水印条，不承载数据。
        音轨与帧一一对应（正文统一中频，黄帧无声）。
        两遍处理：第一遍纯视频编码 -> 临时 mp4；第二遍视频流复制并合成 PCM 音轨。
        """
        w, h = size
        gw, gh = w // BLOCK, h // BLOCK
        wm = _wm_text_pts(w, h) if _wm_ok(w, h) else None
        rows = gh - WM_ROWS if wm is not None else gh
        cpf = gw * rows  # 每帧数据码元数
        ff = imageio_ffmpeg.get_ffmpeg_exe()

        # 头声明与黄帧为整帧纯色，预生成字节缓存避免逐帧转换
        solid = {ch: np.full((h, w, 3), rgb, dtype=np.uint8)
                 for ch, rgb in COLOR_MAP.items()}
        yellow = np.full((h, w, 3), YELLOW, dtype=np.uint8)
        if wm is not None:
            for arr in (*solid.values(), yellow):
                _stamp_wm(arr, wm)
        header_frames = [solid[ch].tobytes() for ch in lang_tokens if ch in solid]
        header_freqs = [FREQ_MAP.get(ch, 0.0) for ch in lang_tokens if ch in solid]
        yellow_b = yellow.tobytes()

        # 正文 token 比特流 -> 码元数组（0黑/1白/2灰分隔），末尾补灰对齐整帧
        n_body = 0
        cells = np.empty(0, dtype=np.uint8)
        body_bits = body_tokens.translate(BIT_TABLE).encode("ascii")
        if body_bits:
            cells = np.frombuffer(body_bits, dtype=np.uint8)
            pad = (-len(cells)) % cpf
            if pad:
                cells = np.concatenate([cells, np.full(pad, 2, dtype=np.uint8)])
            n_body = len(cells) // cpf

        total = len(header_frames) + YELLOW_FRAMES + n_body
        freq_list = header_freqs + [0.0] * YELLOW_FRAMES + [1000.0] * n_body

        # 音轨：raw PCM（无头、无 4GiB 限制），分块流式写盘，内存恒定；
        # 相位连续避免爆音；频率 0 = 真静音
        pcm_path = Path(out_path).with_suffix(".tmp.pcm")
        tmp_video = Path(out_path).with_suffix(".tmp.mp4")
        has_audio = bool(freq_list)
        if has_audio:
            spf = max(1, round(SAMPLE_RATE / fps))  # 每帧采样数
            phase = 0.0
            with open(pcm_path, "wb") as af:
                for i in range(0, len(freq_list), AUDIO_CHUNK_FRAMES):
                    block = np.asarray(freq_list[i:i + AUDIO_CHUNK_FRAMES],
                                       dtype=np.float64)
                    dphi = np.repeat(2 * np.pi * block / SAMPLE_RATE, spf)
                    samples = np.where(dphi > 0, np.sin(phase + np.cumsum(dphi)), 0.0)
                    phase += float(dphi.sum())
                    af.write((0.35 * samples * 32767).astype(np.int16).tobytes())

        target = str(tmp_video) if has_audio else str(out_path)
        cmd = [ff, "-y",
               "-f", "rawvideo", "-pix_fmt", "rgb24",
               "-s", f"{w}x{h}", "-r", str(fps), "-i", "-",
               "-an", "-c:v", "libx264", "-preset", "veryfast", "-crf", "18",
               "-pix_fmt", "yuv420p", target]
        try:
            proc = subprocess.Popen(cmd, stdin=subprocess.PIPE,
                                    stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            count = 0
            last_ui = 0.0

            def _ui():
                nonlocal count, last_ui
                now = time.monotonic()
                if now - last_ui < 0.5:  # 按时间节流，避免UI回调堆积
                    return
                last_ui = now
                v = count * 50 / max(total, 1)
                self.root.after(0, lambda v=v: self.progress.configure(value=v))
                self.root.after(0, lambda c=count:
                                self.status_var.set(f"生成视频... {c}/{total}"))

            try:
                # 头声明帧 + 3 黄分隔帧
                for fb in header_frames:
                    proc.stdin.write(fb)
                count += len(header_frames)
                proc.stdin.write(yellow_b * YELLOW_FRAMES)
                count += YELLOW_FRAMES
                # 正文块帧：批量向量化构建后写入
                for i in range(0, n_body, BODY_BATCH):
                    batch = cells[i * cpf:(i + BODY_BATCH) * cpf].reshape(-1, rows, gw)
                    if wm is not None:  # 数据行 + 底部黑条（水印区不承载数据）
                        grid = np.zeros((len(batch), gh, gw), np.uint8)
                        grid[:, :rows] = batch
                        batch = grid
                    fr = CELL_LUT[batch].repeat(BLOCK, axis=1).repeat(BLOCK, axis=2)
                    if wm is not None:
                        ty, tx = wm
                        fr[:, ty, tx] = 255  # 白色水印文字
                    proc.stdin.write(fr.tobytes())
                    count += len(fr)
                    _ui()
                proc.stdin.close()
            except BrokenPipeError:
                pass
            rc = proc.wait()
            if rc != 0:
                raise RuntimeError(f"ffmpeg 退出码 {rc}")

            if has_audio:
                # 第二遍：视频流复制 + PCM 音轨（PCM 无编码器 priming，
                # 不依赖 edit list，所有播放器音画同步；音频时长=帧数/fps 天然对齐）
                # 解析 ffmpeg 的 time= 进度，进度条占 50~100%
                self.root.after(0, lambda: self.status_var.set("合成音轨... 0%"))
                cmd2 = [ff, "-y", "-i", str(tmp_video),
                        "-f", "s16le", "-ar", str(SAMPLE_RATE), "-ac", "1",
                        "-i", str(pcm_path),
                        "-map", "0:v", "-map", "1:a",
                        "-c:v", "copy", "-c:a", "pcm_s16le",
                        str(out_path)]
                proc2 = subprocess.Popen(cmd2, stdout=subprocess.DEVNULL,
                                         stderr=subprocess.PIPE)
                dur = total / fps if fps else 0
                tpat = re.compile(rb"time=(\d+):(\d+):(\d+\.\d+)")
                buf = b""
                cnt = 0
                last_pct = 50.0
                while True:
                    chunk = proc2.stderr.read(256)
                    if not chunk:
                        break
                    buf += chunk
                    while b"\r" in buf or b"\n" in buf:
                        sep = b"\r" if b"\r" in buf else b"\n"
                        line, buf = buf.split(sep, 1)
                        m = tpat.search(line)
                        if not m or dur <= 0:
                            continue
                        cnt += 1
                        if cnt % 8:  # 节流，避免UI回调堆积
                            continue
                        secs = (int(m.group(1)) * 3600
                                + int(m.group(2)) * 60 + float(m.group(3)))
                        last_pct = 50 + min(secs / dur, 1.0) * 50
                        self.root.after(0, lambda v=last_pct:
                                        self.progress.configure(value=v))
                        self.root.after(0, lambda p=int(last_pct):
                                        self.status_var.set(f"合成音轨... {p}%"))
                proc2.stderr.close()
                rc2 = proc2.wait()
                # 兜底：瞬间完成或未读到进度时，补满
                self.root.after(0, lambda: self.progress.configure(value=100))
                if rc2 != 0:
                    raise RuntimeError(f"ffmpeg 退出码 {rc2}")
            return count
        finally:
            tmp_video.unlink(missing_ok=True)
            pcm_path.unlink(missing_ok=True)

    # ---------- 解码核心 ----------
    def _video_size(self, path):
        ff = imageio_ffmpeg.get_ffmpeg_exe()
        proc = subprocess.Popen([ff, "-i", str(path)],
                                stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
        _, err = proc.communicate()
        info = err.decode("utf-8", "ignore")
        m = re.search(r"(\d{2,5})x(\d{2,5})", info)
        if m:
            return int(m.group(1)), int(m.group(2))
        return 1280, 720

    def _decode_video(self, vid_path, codebook):
        """读全部帧。黄色前=头声明（Base64编码的文件名），黄色后=内容。

        所有内容均按 BxB 像素块解码（块黑=0/白=1/灰=码元分隔）。
        水印通过 _wm_ok(w,h) 判断，与编码端一致。
        返回 (头声明, 正文, 是否遇黄, 读帧数)。"""
        w, h = self._video_size(vid_path)
        gw, gh = max(1, w // BLOCK), max(1, h // BLOCK)
        wm = _wm_ok(w, h)  # 与编码端一致：帧够大则底部有水印条
        ff = imageio_ffmpeg.get_ffmpeg_exe()
        cmd = [ff, "-i", str(vid_path),
               "-vf", f"scale={gw}:{gh}:flags=area",
               "-f", "rawvideo", "-pix_fmt", "rgb24", "-"]
        proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                                bufsize=8 * 1024 * 1024)
        frame_size = gw * gh * 3
        rev = {v: k for k, v in codebook.items()}

        def _dec(chars):
            return "".join(rev.get(tok, "?") for tok in "".join(chars).split(" "))

        header_chars = []
        v2_cells = []
        hit_yellow = False
        in_sep = False
        read = 0
        pending = b""
        last_ui = 0.0
        char_lut = ("0", "1", " ", "", "")

        def _cells_of(arr):
            """缩放后帧 (m,gh,gw,3) -> 每像素分类为码元。wm 时跳过底部水印行。"""
            cells = np.full(arr.shape[:3], 3, dtype=np.uint8)
            cells[(arr < 50).all(-1)] = 0
            cells[(arr > 200).all(-1)] = 1
            cells[((arr >= 83) & (arr <= 173)).all(-1)] = 2
            if wm:
                cells = cells[:, :gh - WM_ROWS, :]
            v2_cells.append(cells.reshape(-1).tobytes())

        def _whole_lab(arr):
            """整帧均值 -> 标签（缩放后帧均值=原始帧均值，纯色帧不受影响）。"""
            mean = arr.mean(axis=(1, 2))
            lab = np.full(len(arr), -1, np.int8)
            lab[(mean < 50).all(1)] = 0
            lab[(mean > 200).all(1)] = 1
            lab[(np.abs(mean - 128) < 45).all(1)] = 2
            lab[(mean[:, 0] > 200) & (mean[:, 1] > 200)
                & (mean[:, 2] < 100)] = 3
            return lab

        try:
            while True:
                # 大块读取减少系统调用；单次请求上限 8MB 兼顾超大分辨率
                chunk = proc.stdout.read(max(1, 8 * 1024 * 1024 // frame_size)
                                         * frame_size)
                if not chunk:
                    break
                data = pending + chunk
                nf = len(data) // frame_size
                if nf == 0:
                    continue
                read += nf
                arr = np.frombuffer(data, dtype=np.uint8,
                                    count=nf * frame_size).reshape(nf, gh, gw, 3)
                pending = data[nf * frame_size:]

                if not hit_yellow:
                    # 头声明阶段：整帧分类，找首个黄帧
                    lab = _whole_lab(arr)
                    yl = np.flatnonzero(lab == 3)
                    if len(yl):
                        first = int(yl[0])
                        header_chars.extend(char_lut[v] for v in lab[:first] if v >= 0)
                        hit_yellow = True
                        # 跳过首个黄帧后连续的黄分隔帧
                        start = first + 1
                        while start < nf and lab[start] == 3:
                            start += 1
                        if start < nf:
                            _cells_of(arr[start:])
                        else:
                            in_sep = True
                    else:
                        header_chars.extend(char_lut[v] for v in lab if v >= 0)
                elif in_sep:
                    # 跨块继续跳过黄分隔帧
                    lab = _whole_lab(arr)
                    start = 0
                    while start < nf and lab[start] == 3:
                        start += 1
                    if start < nf:
                        in_sep = False
                        _cells_of(arr[start:])
                else:
                    # 正文：块解码
                    _cells_of(arr)

                now = time.monotonic()
                if now - last_ui >= 0.5:
                    last_ui = now
                    self.root.after(0, lambda n=read:
                                    self.status_var.set(f"解码中... 已读 {n} 帧"))
        finally:
            proc.stdout.close()
            proc.wait()

        if hit_yellow:
            header = _dec(header_chars).strip()
            all_cells = np.frombuffer(b"".join(v2_cells), dtype=np.uint8)
            widths = set(len(v) for v in codebook.values())
            if len(widths) == 1 and all_cells.size > 0:
                tw = widths.pop()
                stride = tw + 1
                n = all_cells.size // stride
                blocks = all_cells[:n * stride].reshape(n, stride)
                bits = blocks[:, :tw].astype(np.int64)
                bad = (blocks[:, :tw] >= 2).any(axis=1)
                powers = (1 << np.arange(tw - 1, -1, -1)).astype(np.int64)
                indices = bits @ powers
                max_idx = int(indices[~bad].max()) + 1 if (~bad).any() else 1
                lut = np.full(max_idx, "?", dtype="U1")
                for ch, code in codebook.items():
                    idx = int(code, 2)
                    if idx < max_idx:
                        lut[idx] = ch
                safe = np.clip(indices, 0, max_idx - 1)
                chars = np.where(bad | (indices >= max_idx), "?", lut[safe])
                good = ~bad & (indices < max_idx)
                last_good = int(np.flatnonzero(good)[-1]) if good.any() else -1
                chars = chars[:last_good + 1] if last_good >= 0 else chars[:0]
                body = "".join(chars.tolist())
            else:
                stream = all_cells.translate(
                    bytes.maketrans(b"\x00\x01\x02\x03", b"01 ?")
                ).decode("ascii", "ignore")
                body = "".join(rev.get(tok, "?") for tok in stream.split(" ") if tok)
        else:
            header = ""
            body = _dec(header_chars)
        return header, body, hit_yellow, read

    # ---------- 编码线程任务 ----------
    def _do_encode(self, inp, vid_out, cb, size, fps):
        # 强制 mkv 容器：mkv 原生支持 PCM（有声音）且用负时间戳不依赖 edit list（音画同步）
        vid_out = str(Path(vid_out).with_suffix(".mkv"))
        # 所有文件统一 Base64 编码（码表仅需 65 个 Base64 字符）
        try:
            data = Path(inp).read_bytes()
        except Exception as e:
            self._fail_after(f"读取文件失败: {e}")
            return
        text = base64.b64encode(data).decode("ascii")
        # 头声明 = Base64(原文件名)，解码端据此还原文件名
        filename_b64 = base64.b64encode(Path(inp).name.encode("utf-8")).decode("ascii")
        try:
            codebook = json.loads(Path(cb).read_text(encoding="utf-8"))
        except Exception as e:
            self._fail_after(f"读取编码表失败: {e}")
            return
        self.root.after(0, lambda: self._reset_progress("编码中..."))
        lang_tokens, _, added = self._encode_text(filename_b64, codebook)
        body_tokens, encoded, body_added = self._encode_text(text, codebook)
        added += body_added

        if added:
            try:
                Path(cb).write_text(json.dumps(codebook, ensure_ascii=True, indent=2),
                                    encoding="utf-8")
            except Exception as e:
                self._fail_after(f"写回编码表失败: {e}")
                return

        # 写 log
        log_path = Path(vid_out).with_suffix(".log")
        try:
            Path(log_path).write_text(f"{filename_b64}\n{body_tokens}", encoding="utf-8")
        except Exception as e:
            self._fail_after(f"写入log失败: {e}")
            return

        # 生成视频：头声明帧 → 3黄帧 → 正文帧
        self.root.after(0, lambda: self._reset_progress("生成视频..."))
        try:
            vcount = self._make_video(lang_tokens, body_tokens, vid_out, size, fps)
        except Exception as e:
            self._fail_after(f"生成视频失败: {e}")
            return

        msg = (f"完成\n文件: {Path(inp).name}（{len(data)} 字节 → Base64 {len(text)} 字符）\n"
               f"视频: {vid_out}（{vcount} 帧, {vcount / fps:.2f} 秒, "
               f"{size[0]}x{size[1]}, {fps}fps）\nlog: {log_path}")
        if _wm_ok(*size):
            msg += f"\n含水印: {WATERMARK}"
        self.root.after(0, lambda: self._done(msg))

    # ---------- 解码线程任务 ----------
    def _do_decode(self, vid_in, text_out, cb):
        try:
            codebook = json.loads(Path(cb).read_text(encoding="utf-8"))
        except Exception as e:
            self._fail_after(f"读取编码表失败: {e}")
            return
        self.root.after(0, lambda: self._reset_progress("解码中..."))
        try:
            header, body, hit_yellow, read = self._decode_video(vid_in, codebook)
        except Exception as e:
            self._fail_after(f"解码失败: {e}")
            return

        # 头声明 = Base64(原文件名)
        try:
            orig_name = base64.b64decode(header).decode("utf-8") if header else "output"
        except Exception:
            orig_name = "output"

        # 正文 = Base64 编码的原始文件内容
        try:
            out_data = base64.b64decode(body, validate=True)
        except Exception as e:
            self._fail_after(f"还原文件失败（视频可能损坏）: {e}")
            return
        try:
            Path(text_out).write_bytes(out_data)
        except Exception as e:
            self._fail_after(f"写入文件失败: {e}")
            return
        msg = (f"解码完成\n文件: {text_out}\n读帧: {read}\n"
               f"原始文件: {orig_name}（{len(out_data)} 字节）")
        self.root.after(0, lambda: self._done(msg))


if __name__ == "__main__":
    try:
        root = tk.Tk()
        App(root)
        root.mainloop()
    except Exception:
        _boot_log_crash(traceback.format_exc())
        raise
