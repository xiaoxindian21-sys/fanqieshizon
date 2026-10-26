#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
番茄钟 —— 桌面番茄工作法计时器（圆形界面）

功能：
  - 核心番茄钟：工作 / 短休息 / 长休息 自动循环，圆形进度环随倒计时消减
  - 双击时间区域可自由调整当前倒计时（支持 "25:00" 或纯分钟数 "10"）
  - 任务清单：添加今日任务、勾选完成、记录每个任务完成的番茄数
  - 统计报表：今日 / 本周 / 总计番茄数，以及最近 14 天的历史
  - 自定义时长 + 提示音：可自定义各阶段时长，以及开始/结束提示音（内置可爱音效或自定义 .mp3/.wav 文件）

运行：python pomodoro.py
依赖：仅使用 Python 标准库（tkinter、json、winsound）
"""

import json
import os
import threading
import time
import tkinter as tk
from tkinter import ttk, messagebox, filedialog, colorchooser
from datetime import date, timedelta

# Windows 下用 winsound 播放提示音；其它平台退化为系统铃声
try:
    import winsound
except ImportError:  # pragma: no cover
    winsound = None

APP_DIR = os.path.dirname(os.path.abspath(__file__))
DATA_FILE = os.path.join(APP_DIR, "pomodoro_data.json")

# 阶段定义
PHASE_WORK = "work"
PHASE_SHORT = "short_break"
PHASE_LONG = "long_break"

PHASE_INFO = {
    PHASE_WORK: {"label": "工作", "color": "#e74c3c"},
    PHASE_SHORT: {"label": "短休息", "color": "#2ecc71"},
    PHASE_LONG: {"label": "长休息", "color": "#3498db"},
}

# 提示音相关
CUSTOM_FILE = "选择音频文件…"  # 下拉框中的“选文件”占位项
NONE_SOUND = "无提示音"

# 内置可爱音效（winsound.Beep 音符序列：(频率 Hz, 时长 ms)）
SOUND_PRESETS = {
    "叮咚": [(880, 120), (1109, 180)],
    "清脆铃": [(1319, 100), (1568, 100), (2093, 180)],
    "欢快上梯": [(784, 90), (988, 90), (1175, 90), (1568, 180)],
    "温柔结束": [(988, 130), (1175, 130), (1319, 260)],
    "可爱星星": [(1568, 80), (1760, 80), (2093, 140), (1760, 80), (2093, 220)],
    "咕咕鸟": [(659, 120), (784, 120), (659, 120), (784, 200)],
}

DEFAULT_SETTINGS = {
    "work_min": 25,
    "short_min": 5,
    "long_min": 15,
    "long_break_every": 4,     # 每完成几个番茄后进入长休息
    "auto_start_next": False,  # 阶段结束后是否自动开始下一阶段
    "start_sound": "叮咚",      # 开始提示音（预设名 / .mp3/.wav 路径 / ""）
    "end_sound": "温柔结束",     # 结束提示音
    "float_color": "#2c3e50",   # 悬浮窗字体颜色
    "float_font_size": 40,      # 悬浮窗字号
    "float_x": None,            # 悬浮窗上次位置（屏幕坐标）
    "float_y": None,
    "float_alpha": 1.0,         # 悬浮窗不透明度 0.0~1.0
    "float_topmost": True,      # 悬浮窗是否置顶
}


# --------------------------------------------------------------------------
# 数据读写
# --------------------------------------------------------------------------

def load_data():
    """读取数据文件；不存在或损坏时返回默认结构。"""
    if os.path.exists(DATA_FILE):
        try:
            with open(DATA_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
            data.setdefault("settings", dict(DEFAULT_SETTINGS))
            data.setdefault("tasks", [])
            data.setdefault("stats", {})
            for k, v in DEFAULT_SETTINGS.items():
                data["settings"].setdefault(k, v)
            return data
        except (json.JSONDecodeError, OSError):
            try:
                os.replace(DATA_FILE, DATA_FILE + ".bak")
            except OSError:
                pass
    return {"settings": dict(DEFAULT_SETTINGS), "tasks": [], "stats": {}}


def save_data(data):
    """把数据写回文件。"""
    try:
        with open(DATA_FILE, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
    except OSError as e:
        messagebox.showerror("保存失败", f"无法写入数据文件：\n{e}")


def today_str():
    return date.today().isoformat()


# --------------------------------------------------------------------------
# 主应用
# --------------------------------------------------------------------------

class PomodoroApp:
    CANVAS_SIZE = 280  # 圆形进度环画布的边长（像素）

    def __init__(self, root: tk.Tk):
        self.root = root
        self.data = load_data()
        self.settings = self.data["settings"]

        # 计时状态
        self.phase = PHASE_WORK
        self.remaining = self.phase_seconds(PHASE_WORK)
        self.running = False
        self.cycle_count = 0        # 当前循环内已完成的工作番茄数（0..long_break_every）
        self.after_id = None
        self.active_task_id = None  # 当前选中的任务 id

        # 时间编辑状态
        self._editing = False
        self._was_running = False
        self.edit_entry = None
        self.edit_win = None

        # 悬浮窗口状态
        self.float_win = None
        self.float_color = self.settings.get("float_color", "#2c3e50")
        self.float_font_size = int(self.settings.get("float_font_size", 40))
        self.float_alpha = float(self.settings.get("float_alpha", 1.0))
        self.float_topmost = bool(self.settings.get("float_topmost", True))
        self._topmost_var = tk.BooleanVar(value=self.float_topmost)
        self._alpha_var = tk.IntVar(value=int(round(self.float_alpha * 100)))
        self._drag_start = (0, 0)
        self._drag_pos = (0, 0)
        self._dragged = False

        self._build_ui()
        self._refresh_all()

        # 空格键：开始 / 暂停
        root.bind("<space>", lambda e: self.toggle())
        root.protocol("WM_DELETE_WINDOW", self._on_close)

    # ---------------- 配置 ----------------

    def phase_seconds(self, phase):
        if phase == PHASE_WORK:
            return int(self.settings["work_min"]) * 60
        if phase == PHASE_SHORT:
            return int(self.settings["short_min"]) * 60
        return int(self.settings["long_min"]) * 60

    def phase_label(self, phase):
        return PHASE_INFO[phase]["label"]

    # ---------------- 界面 ----------------

    def _build_ui(self):
        self.root.title("番茄钟")
        self.root.geometry("400x680")
        self.root.minsize(380, 600)
        self.root.configure(bg="#f7f7f7")

        style = ttk.Style(self.root)
        if "clam" in style.theme_names():
            style.theme_use("clam")
        style.configure("TNotebook", background="#f7f7f7", borderwidth=0)

        # 圆形进度环画布
        self.canvas = tk.Canvas(
            self.root, width=self.CANVAS_SIZE, height=self.CANVAS_SIZE,
            bg="#f7f7f7", highlightthickness=0, cursor="hand2")
        self.canvas.pack(pady=(24, 8))
        self.canvas.bind("<Double-Button-1>", self._on_double_click)

        # 控制按钮
        btn_frame = tk.Frame(self.root, bg="#f7f7f7")
        btn_frame.pack(pady=12)
        self.start_btn = tk.Button(
            btn_frame, text="开始", width=8, font=("Microsoft YaHei", 12, "bold"),
            bg="#2ecc71", fg="#ffffff", activebackground="#27ae60",
            activeforeground="#ffffff", relief="flat", cursor="hand2",
            command=self.toggle)
        self.start_btn.pack(side="left", padx=6)
        for text, cmd in (("重置", self.reset), ("跳过", self.skip)):
            tk.Button(
                btn_frame, text=text, width=8, font=("Microsoft YaHei", 12),
                relief="flat", cursor="hand2", command=cmd,
                bg="#ecf0f1", activebackground="#dfe4e6").pack(side="left", padx=6)
        tk.Button(
            btn_frame, text="缩小", width=8, font=("Microsoft YaHei", 12),
            relief="flat", cursor="hand2", command=self.minimize_to_float,
            bg="#ecf0f1", activebackground="#dfe4e6").pack(side="left", padx=6)

        # 底部选项卡：任务 / 统计 / 设置
        self.notebook = ttk.Notebook(self.root)
        self.notebook.pack(fill="both", expand=True, padx=14, pady=(4, 14))

        self._build_task_tab()
        self._build_stats_tab()
        self._build_settings_tab()

    def _build_task_tab(self):
        tab = ttk.Frame(self.notebook)
        self.notebook.add(tab, text="任务")

        entry_frame = tk.Frame(tab)
        entry_frame.pack(fill="x", padx=8, pady=8)
        self.task_entry = tk.Entry(entry_frame, font=("Microsoft YaHei", 11))
        self.task_entry.pack(side="left", fill="x", expand=True, ipady=3)
        self.task_entry.bind("<Return>", lambda e: self.add_task())
        tk.Button(entry_frame, text="＋ 添加", font=("Microsoft YaHei", 10),
                  command=self.add_task, cursor="hand2").pack(side="left", padx=(6, 0))

        list_frame = tk.Frame(tab)
        list_frame.pack(fill="both", expand=True, padx=8)
        scroll = tk.Scrollbar(list_frame)
        scroll.pack(side="right", fill="y")
        self.task_list = tk.Listbox(
            list_frame, font=("Microsoft YaHei", 11), selectmode="single",
            activestyle="none", yscrollcommand=scroll.set)
        self.task_list.pack(fill="both", expand=True)
        scroll.config(command=self.task_list.yview)
        self.task_list.bind("<<ListboxSelect>>", self._on_task_select)

        op_frame = tk.Frame(tab)
        op_frame.pack(fill="x", padx=8, pady=8)
        tk.Button(op_frame, text="完成", command=self.complete_task,
                  cursor="hand2").pack(side="left", padx=4)
        tk.Button(op_frame, text="删除", command=self.delete_task,
                  cursor="hand2").pack(side="left", padx=4)
        self.active_task_lbl = tk.Label(
            op_frame, text="当前任务：无", font=("Microsoft YaHei", 9), fg="#7f8c8d")
        self.active_task_lbl.pack(side="right")

    def _build_stats_tab(self):
        tab = ttk.Frame(self.notebook)
        self.notebook.add(tab, text="统计")

        card = tk.Frame(tab, bg="#ecf0f1")
        card.pack(fill="x", padx=8, pady=8)
        self.today_var = tk.StringVar()
        self.week_var = tk.StringVar()
        self.total_var = tk.StringVar()
        for text, var in (("今日", self.today_var), ("本周", self.week_var),
                          ("总计", self.total_var)):
            box = tk.Frame(card, bg="#ecf0f1")
            box.pack(side="left", expand=True, pady=10)
            tk.Label(box, text=text, font=("Microsoft YaHei", 10),
                     fg="#7f8c8d", bg="#ecf0f1").pack()
            tk.Label(box, textvariable=var, font=("Microsoft YaHei", 22, "bold"),
                     fg="#2c3e50", bg="#ecf0f1").pack()

        tk.Label(tab, text="最近 14 天", font=("Microsoft YaHei", 10, "bold"),
                 anchor="w").pack(fill="x", padx=10, pady=(4, 2))
        tree_frame = tk.Frame(tab)
        tree_frame.pack(fill="both", expand=True, padx=8)
        tscroll = tk.Scrollbar(tree_frame)
        tscroll.pack(side="right", fill="y")
        self.history_tree = ttk.Treeview(
            tree_frame, columns=("date", "count"), show="headings",
            yscrollcommand=tscroll.set, height=10)
        self.history_tree.heading("date", text="日期")
        self.history_tree.heading("count", text="番茄数")
        self.history_tree.column("date", width=140, anchor="center")
        self.history_tree.column("count", width=100, anchor="center")
        self.history_tree.pack(fill="both", expand=True)
        tscroll.config(command=self.history_tree.yview)

    def _build_settings_tab(self):
        tab = ttk.Frame(self.notebook)
        self.notebook.add(tab, text="设置")

        # 可滚动容器，避免设置项过多时被底部截断
        canvas = tk.Canvas(tab, highlightthickness=0, bg="#f7f7f7")
        scrollbar = ttk.Scrollbar(tab, orient="vertical", command=canvas.yview)
        inner = tk.Frame(canvas, bg="#f7f7f7")
        inner.bind("<Configure>",
                   lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
        win = canvas.create_window((0, 0), window=inner, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)
        canvas.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")
        canvas.bind("<Configure>", lambda e: canvas.itemconfig(win, width=e.width))
        canvas.bind("<MouseWheel>", self._on_mousewheel)
        self._settings_canvas = canvas

        # 时长设置
        rows = [
            ("工作时长（分钟）", "work_min", 1, 120),
            ("短休息时长（分钟）", "short_min", 1, 60),
            ("长休息时长（分钟）", "long_min", 1, 120),
            ("几个番茄后长休息", "long_break_every", 1, 12),
        ]
        self.setting_vars = {}
        frame = tk.Frame(inner, bg="#f7f7f7")
        frame.pack(fill="x", padx=20, pady=(16, 4))
        for i, (label, key, lo, hi) in enumerate(rows):
            tk.Label(frame, text=label, font=("Microsoft YaHei", 11),
                     anchor="w", bg="#f7f7f7").grid(row=i, column=0, sticky="w", pady=8)
            var = tk.IntVar(value=int(self.settings[key]))
            tk.Spinbox(frame, from_=lo, to=hi, textvariable=var, width=6,
                       font=("Microsoft YaHei", 11)).grid(row=i, column=1, pady=8)
            self.setting_vars[key] = var

        self.auto_var = tk.BooleanVar(value=bool(self.settings["auto_start_next"]))
        tk.Checkbutton(
            inner, text="阶段结束后自动开始下一阶段", variable=self.auto_var,
            font=("Microsoft YaHei", 10), bg="#f7f7f7").pack(anchor="w", padx=20, pady=6)

        # 提示音设置
        tk.Label(inner, text="提示音", font=("Microsoft YaHei", 11, "bold"),
                 anchor="w", bg="#f7f7f7").pack(fill="x", padx=20, pady=(12, 4))
        self.sound_combos = {}
        for which, label in (("start", "开始提示音"), ("end", "结束提示音")):
            row = tk.Frame(inner, bg="#f7f7f7")
            row.pack(fill="x", padx=20, pady=4)
            tk.Label(row, text=label, width=11, anchor="w",
                     font=("Microsoft YaHei", 10), bg="#f7f7f7").pack(side="left")
            combo = ttk.Combobox(row, state="readonly", width=22,
                                 font=("Microsoft YaHei", 10))
            combo["values"] = self._sound_choices(which)
            combo.set(self._sound_display(which))
            combo.pack(side="left", padx=6)
            combo.bind("<<ComboboxSelected>>", self._make_sound_handler(which))
            self.sound_combos[which] = combo
            tk.Button(row, text="试听", font=("Microsoft YaHei", 9),
                      command=lambda w=which: self._preview_sound(w),
                      cursor="hand2").pack(side="left")

        tk.Button(inner, text="保存设置", font=("Microsoft YaHei", 11),
                  bg="#3498db", fg="#ffffff", relief="flat", cursor="hand2",
                  command=self.save_settings).pack(pady=16)

        # 让设置区内的所有控件都响应鼠标滚轮
        self._bind_mousewheel(inner)

    def _bind_mousewheel(self, widget):
        widget.bind("<MouseWheel>", self._on_mousewheel)
        for child in widget.winfo_children():
            self._bind_mousewheel(child)

    def _on_mousewheel(self, event):
        self._settings_canvas.yview_scroll(int(-event.delta / 120), "units")

    # ---------------- 圆形进度环渲染 ----------------

    def _fmt_time(self):
        m, s = divmod(max(0, self.remaining), 60)
        return f"{m:02d}:{s:02d}"

    def _render_timer(self):
        """重绘圆形进度环、中心时间、阶段文字与循环圆点。"""
        c = self.canvas
        c.delete("all")
        cx = cy = self.CANVAS_SIZE / 2
        r = self.CANVAS_SIZE / 2 - 26

        # 背景圆环
        c.create_oval(cx - r, cy - r, cx + r, cy + r,
                      outline="#eceff1", width=14)

        # 进度弧（按剩余时间比例，顺时针消减）
        total = self.phase_seconds(self.phase)
        frac = max(0.0, min(1.0, self.remaining / total))
        color = PHASE_INFO[self.phase]["color"]
        if frac > 0:
            c.create_arc(cx - r, cy - r, cx + r, cy + r,
                         start=90, extent=-360 * frac,
                         style=tk.ARC, outline=color, width=14)

        # 阶段文字
        c.create_text(cx, cy - 40, text=self.phase_label(self.phase),
                      font=("Microsoft YaHei", 13, "bold"), fill=color)
        # 中心时间
        c.create_text(cx, cy + 2, text=self._fmt_time(),
                      font=("Consolas", 44, "bold"), fill="#2c3e50")
        # 循环进度圆点
        n = int(self.settings["long_break_every"])
        c.create_text(cx, cy + 44, text="●" * self.cycle_count + "○" * (n - self.cycle_count),
                      font=("Segoe UI Symbol", 11), fill="#95a5a6")

        # 悬浮窗同步刷新
        if self.float_win is not None:
            self._update_float()

    # ---------------- 双击编辑时间 ----------------

    def _on_double_click(self, event):
        self._begin_edit_time()

    def _begin_edit_time(self):
        if self._editing:
            return
        self._editing = True
        self._was_running = self.running
        if self.running:
            self._pause()

        cx = cy = self.CANVAS_SIZE / 2
        self.edit_var = tk.StringVar(value=self._fmt_time())
        self.edit_entry = tk.Entry(
            self.canvas, textvariable=self.edit_var, font=("Consolas", 26, "bold"),
            justify="center", width=8, relief="flat", bd=0, bg="#ffffff",
            fg="#2c3e50")
        self.edit_entry.bind("<Return>", lambda e: self._commit_edit())
        self.edit_entry.bind("<FocusOut>", lambda e: self._commit_edit())
        self.edit_entry.bind("<Escape>", lambda e: self._cancel_edit())
        self.edit_win = self.canvas.create_window(cx, cy, window=self.edit_entry)
        self.edit_entry.focus_set()
        self.edit_entry.select_range(0, "end")

    def _parse_time(self, s):
        """把输入解析为秒数。支持 "MM:SS" 或纯分钟数，非法则抛 ValueError。"""
        s = s.strip()
        if not s:
            raise ValueError
        if ":" in s:
            parts = s.split(":")
            if len(parts) != 2:
                raise ValueError
            m, sec = int(parts[0]), int(parts[1])
            if not (0 <= sec < 60) or m < 0:
                raise ValueError
            seconds = m * 60 + sec
        else:
            seconds = int(s) * 60
        if seconds <= 0:
            raise ValueError
        return seconds

    def _commit_edit(self):
        if not self._editing:
            return
        self._editing = False
        try:
            self.remaining = self._parse_time(self.edit_var.get())
        except ValueError:
            self._end_edit()
            self._show_toast("时间格式无效，请输入 MM:SS 或分钟数")
            return
        self._end_edit()

    def _cancel_edit(self):
        if not self._editing:
            return
        self._editing = False
        self._end_edit()

    def _end_edit(self):
        if self.edit_win is not None:
            self.canvas.delete(self.edit_win)
            self.edit_win = None
        if self.edit_entry is not None:
            self.edit_entry.destroy()
            self.edit_entry = None
        self._render_timer()
        if self._was_running:
            self._start()

    # ---------------- 计时逻辑 ----------------

    def toggle(self):
        if self.running:
            self._pause()
        else:
            self._start(play_sound=True)

    def _start(self, play_sound=False):
        if play_sound:
            self._play_sound("start")
        self.running = True
        self.start_btn.config(text="暂停", bg="#e67e22", activebackground="#d35400")
        self._schedule_tick()

    def _pause(self):
        self.running = False
        if self.after_id is not None:
            self.root.after_cancel(self.after_id)
            self.after_id = None
        self.start_btn.config(text="继续", bg="#2ecc71", activebackground="#27ae60")

    def reset(self):
        self._pause()
        self.remaining = self.phase_seconds(self.phase)
        self.start_btn.config(text="开始")
        self._render_timer()

    def skip(self):
        self._pause()
        self._advance_phase(count=False)
        self.start_btn.config(text="开始")
        self._render_timer()

    def _schedule_tick(self):
        self.after_id = self.root.after(1000, self._tick)

    def _tick(self):
        if not self.running:
            return
        self.remaining -= 1
        if self.remaining <= 0:
            self._finish_phase()
        else:
            self._render_timer()
            self._schedule_tick()

    def _finish_phase(self):
        """当前阶段结束：结算番茄 / 切换阶段 / 提醒。"""
        self._pause()
        self._advance_phase(count=(self.phase == PHASE_WORK))
        self._render_timer()
        self._notify_phase_start()
        if self.settings.get("auto_start_next"):
            self._start()

    def _advance_phase(self, count):
        """切换到下一阶段。count=True 表示本次工作番茄计入统计。"""
        if self.phase == PHASE_WORK:
            if count:
                self._record_pomodoro()
            if self.cycle_count >= int(self.settings["long_break_every"]):
                self.phase = PHASE_LONG
                self.cycle_count = 0
            else:
                self.phase = PHASE_SHORT
        else:  # 休息结束 -> 工作
            self.phase = PHASE_WORK
        self.remaining = self.phase_seconds(self.phase)

    def _record_pomodoro(self):
        self.cycle_count += 1
        key = today_str()
        self.data["stats"][key] = self.data["stats"].get(key, 0) + 1
        task = self._find_task(self.active_task_id)
        if task is not None:
            task["pomodoros"] += 1
        save_data(self.data)
        self._refresh_stats()
        self._refresh_task_list()

    # ---------------- 提醒 ----------------

    def _notify_phase_start(self):
        self._play_sound("end")
        if self.phase == PHASE_WORK:
            text = "休息结束，开始工作吧！💪"
        elif self.phase == PHASE_LONG:
            text = "辛苦了！来一次长休息吧 ☕"
        else:
            text = "一个番茄完成，休息一下吧 ☕"
        self._show_toast(text)

    def _play_sound(self, which):
        """播放某类提示音（start / end），按保存的设置。"""
        self._play_config(self.settings.get(which + "_sound", ""))

    def _play_config(self, cfg):
        """按配置播放：预设名 -> 旋律；文件路径 -> wav；否则静音。"""
        if not cfg or cfg in (NONE_SOUND, CUSTOM_FILE):
            return
        if cfg in SOUND_PRESETS:
            self._play_melody(SOUND_PRESETS[cfg])
        elif os.path.exists(cfg):
            self._play_file(cfg)

    def _play_melody(self, notes):
        """用系统蜂鸣播放音符序列，放后台线程避免卡界面。"""
        if winsound is None:
            self.root.bell()
            return

        def run():
            try:
                for freq, dur in notes:
                    winsound.Beep(freq, dur)
            except RuntimeError:
                pass

        threading.Thread(target=run, daemon=True).start()

    def _play_file(self, path):
        """播放音频文件（支持 .mp3 / .wav 等），优先用 MCI，回退 winsound。"""
        if not os.path.exists(path):
            return
        abspath = os.path.abspath(path)
        if os.name == "nt":
            try:
                import ctypes
                winmm = ctypes.windll.winmm
                winmm.mciSendStringW("close pomodoro", None, 0, 0)
                ext = os.path.splitext(abspath)[1].lower()
                type_map = {".mp3": "mpegvideo", ".wav": "waveaudio"}
                cmd = f'open "{abspath}" alias pomodoro'
                if ext in type_map:
                    cmd += f" type {type_map[ext]}"
                if winmm.mciSendStringW(cmd, None, 0, 0) == 0:
                    winmm.mciSendStringW("play pomodoro", None, 0, 0)
                    return
            except (OSError, AttributeError):
                pass
        # 回退：winsound 播放 wav
        if winsound is not None:
            try:
                winsound.PlaySound(abspath, winsound.SND_FILENAME | winsound.SND_ASYNC)
                return
            except RuntimeError:
                pass
        self.root.bell()

    # ---------------- 提示音设置界面辅助 ----------------

    def _sound_choices(self, which):
        vals = list(SOUND_PRESETS.keys()) + [CUSTOM_FILE, NONE_SOUND]
        cfg = self.settings.get(which + "_sound", "")
        if cfg and cfg not in SOUND_PRESETS:
            vals.insert(0, cfg)  # 自定义文件路径，加入下拉以便显示
        return vals

    def _sound_display(self, which):
        cfg = self.settings.get(which + "_sound", "")
        return NONE_SOUND if cfg == "" else cfg

    def _make_sound_handler(self, which):
        def handler(event):
            combo = self.sound_combos[which]
            if combo.get() != CUSTOM_FILE:
                return
            path = filedialog.askopenfilename(
                title="选择提示音文件",
                filetypes=[("音频文件", "*.mp3 *.wav"),
                           ("MP3 音频", "*.mp3"),
                           ("WAV 音频", "*.wav"),
                           ("所有文件", "*.*")])
            if path:
                vals = list(combo.cget("values"))
                if path not in vals:
                    vals.insert(0, path)
                    combo.config(values=vals)
                combo.set(path)
            else:
                combo.set(self._sound_display(which))
        return handler

    def _preview_sound(self, which):
        self._play_config(self.sound_combos[which].get())

    def _show_toast(self, text):
        """弹出一个置顶提醒窗口，3 秒后自动关闭。"""
        toast = tk.Toplevel(self.root)
        toast.overrideredirect(True)
        toast.attributes("-topmost", True)
        toast.configure(bg="#2c3e50")
        tk.Label(toast, text=text, font=("Microsoft YaHei", 13, "bold"),
                 bg="#2c3e50", fg="#ffffff", padx=24, pady=16).pack()
        toast.update_idletasks()
        w, h = toast.winfo_width(), toast.winfo_height()
        x = (toast.winfo_screenwidth() - w) // 2
        y = (toast.winfo_screenheight() - h) // 2
        toast.geometry(f"+{x}+{y}")
        toast.deiconify()
        toast.lift()
        toast.after(3000, toast.destroy)
        if self.root.state() != "withdrawn":
            self.root.lift()

    # ---------------- 悬浮窗口 ----------------

    def minimize_to_float(self):
        """隐藏主窗口，显示桌面悬浮计时窗（进程保持运行）。"""
        self.root.withdraw()
        if self.float_win is None:
            self._build_float()
        else:
            self.float_win.deiconify()
        self._update_float()

    def _build_float(self):
        win = tk.Toplevel(self.root)
        win.overrideredirect(True)
        win.attributes("-topmost", self.float_topmost)
        win.attributes("-alpha", self.float_alpha)
        self.float_win = win

        self.float_border = tk.Frame(win, bg=PHASE_INFO[self.phase]["color"])
        self.float_border.pack()
        self.float_label = tk.Label(
            self.float_border, text=self._fmt_time(),
            font=("Consolas", self.float_font_size, "bold"),
            fg=self.float_color, bg="#ffffff", padx=8, pady=4)
        self.float_label.pack(padx=2, pady=2)

        # 事件：右键拖拽移动、滚轮缩放、双击恢复主界面
        for w in (win, self.float_border, self.float_label):
            w.bind("<Button-3>", self._on_float_press)
            w.bind("<B3-Motion>", self._on_float_drag)
            w.bind("<ButtonRelease-3>", self._on_float_release)
            w.bind("<MouseWheel>", self._on_float_wheel)
            w.bind("<Double-Button-1>", lambda e: self.restore_main())

        self._apply_float_font(place=True)

    def _apply_float_font(self, place=False):
        """按当前字号重设悬浮窗大小（place=True 时按记忆位置或右上角摆放）。"""
        if self.float_win is None:
            return
        self.float_label.config(font=("Consolas", self.float_font_size, "bold"))
        self.float_label.update_idletasks()
        w = self.float_label.winfo_reqwidth() + 4   # 左右各 2px 边框
        h = self.float_label.winfo_reqheight() + 4  # 上下各 2px 边框
        if place:
            sw = self.float_win.winfo_screenwidth()
            sh = self.float_win.winfo_screenheight()
            sx = self.settings.get("float_x")
            sy = self.settings.get("float_y")
            if sx is not None and sy is not None:
                # 使用记忆位置，并夹在屏幕范围内
                x = max(0, min(int(sx), sw - w))
                y = max(0, min(int(sy), sh - h))
            else:
                x = sw - w - 24
                y = 24
            self.float_win.geometry(f"{w}x{h}+{x}+{y}")
        else:
            x, y = self.float_win.winfo_x(), self.float_win.winfo_y()
            self.float_win.geometry(f"{w}x{h}+{x}+{y}")

    def _update_float(self):
        if self.float_win is None:
            return
        self.float_label.config(text=self._fmt_time())
        self.float_border.config(bg=PHASE_INFO[self.phase]["color"])

    def restore_main(self):
        """从悬浮窗恢复主界面。"""
        self.root.deiconify()
        self.root.lift()
        self.root.focus_force()
        if self.float_win is not None:
            self.float_win.destroy()
            self.float_win = None

    def quit_app(self):
        """真正退出程序。"""
        self._on_close()

    # 拖拽 / 缩放 / 颜色

    def _on_float_press(self, event):
        self._drag_start = (event.x_root, event.y_root)
        self._drag_pos = (self.float_win.winfo_x(), self.float_win.winfo_y())
        self._dragged = False

    def _on_float_drag(self, event):
        dx = event.x_root - self._drag_start[0]
        dy = event.y_root - self._drag_start[1]
        if abs(dx) > 3 or abs(dy) > 3:
            self._dragged = True
        self.float_win.geometry(
            f"+{self._drag_pos[0] + dx}+{self._drag_pos[1] + dy}")

    def _on_float_release(self, event):
        if not self._dragged:
            self._show_float_menu(event)
        self._save_float_pos()
        save_data(self.data)

    def _on_float_wheel(self, event):
        step = 2 if event.delta > 0 else -2
        self._float_zoom(step)

    def _float_zoom(self, step):
        self.float_font_size = max(12, min(96, self.float_font_size + step))
        self.settings["float_font_size"] = self.float_font_size
        save_data(self.data)
        self._apply_float_font()

    def _show_float_menu(self, event):
        menu = tk.Menu(self.float_win, tearoff=0)
        menu.add_command(label="更改颜色…", command=self._change_float_color)
        menu.add_command(label="放大", command=lambda: self._float_zoom(2))
        menu.add_command(label="缩小", command=lambda: self._float_zoom(-2))
        # 透明度子菜单
        alpha_menu = tk.Menu(menu, tearoff=0)
        for pct in (100, 85, 70, 55, 40):
            alpha_menu.add_radiobutton(
                label=f"{pct}%", variable=self._alpha_var, value=pct,
                command=lambda v=pct: self._set_float_alpha(v / 100))
        menu.add_cascade(label="透明度", menu=alpha_menu)
        menu.add_checkbutton(label="置顶显示", variable=self._topmost_var,
                             command=self._apply_topmost)
        menu.add_separator()
        menu.add_command(label="恢复主界面", command=self.restore_main)
        menu.add_command(label="退出", command=self.quit_app)
        menu.tk_popup(event.x_root, event.y_root)
        menu.grab_release()

    def _change_float_color(self):
        _, color = colorchooser.askcolor(color=self.float_color, title="选择字体颜色")
        if color:
            self.float_color = color
            self.settings["float_color"] = color
            save_data(self.data)
            self.float_label.config(fg=color)

    def _save_float_pos(self):
        if self.float_win is not None:
            self.settings["float_x"] = self.float_win.winfo_x()
            self.settings["float_y"] = self.float_win.winfo_y()

    def _set_float_alpha(self, val):
        self.float_alpha = val
        self.settings["float_alpha"] = val
        save_data(self.data)
        if self.float_win is not None:
            self.float_win.attributes("-alpha", val)

    def _apply_topmost(self):
        self.float_topmost = bool(self._topmost_var.get())
        self.settings["float_topmost"] = self.float_topmost
        save_data(self.data)
        if self.float_win is not None:
            self.float_win.attributes("-topmost", self.float_topmost)

    # ---------------- 任务 ----------------

    def _find_task(self, task_id):
        for t in self.data["tasks"]:
            if t["id"] == task_id:
                return t
        return None

    def add_task(self):
        name = self.task_entry.get().strip()
        if not name:
            return
        task = {
            "id": time.time_ns(),
            "name": name,
            "pomodoros": 0,
            "done": False,
            "created": today_str(),
        }
        self.data["tasks"].append(task)
        save_data(self.data)
        self.task_entry.delete(0, "end")
        self.active_task_id = task["id"]
        self._refresh_task_list()
        self._update_active_task_label()

    def complete_task(self):
        task = self._find_task(self.active_task_id)
        if task is None:
            return
        task["done"] = not task["done"]
        save_data(self.data)
        self._refresh_task_list()

    def delete_task(self):
        task = self._find_task(self.active_task_id)
        if task is None:
            return
        self.data["tasks"] = [t for t in self.data["tasks"] if t["id"] != task["id"]]
        if self.active_task_id == task["id"]:
            self.active_task_id = None
        save_data(self.data)
        self._refresh_task_list()
        self._update_active_task_label()

    def _on_task_select(self, event):
        sel = self.task_list.curselection()
        if not sel:
            return
        idx = sel[0]
        if 0 <= idx < len(self.data["tasks"]):
            self.active_task_id = self.data["tasks"][idx]["id"]
            self._update_active_task_label()

    def _update_active_task_label(self):
        task = self._find_task(self.active_task_id)
        name = task["name"] if task else "无"
        self.active_task_lbl.config(text=f"当前任务：{name}")

    def _refresh_task_list(self):
        self.task_list.delete(0, "end")
        for i, t in enumerate(self.data["tasks"]):
            mark = "✓ " if t["done"] else "   "
            self.task_list.insert("end", f"{mark}{t['name']}  （🍅 × {t['pomodoros']}）")
            if t["id"] == self.active_task_id:
                self.task_list.selection_set(i)

    # ---------------- 统计 ----------------

    def _refresh_stats(self):
        stats = self.data["stats"]
        today = today_str()
        today_count = stats.get(today, 0)
        week_ago = (date.today() - timedelta(days=6)).isoformat()
        week_count = sum(v for k, v in stats.items() if k >= week_ago)
        total = sum(stats.values())

        self.today_var.set(str(today_count))
        self.week_var.set(str(week_count))
        self.total_var.set(str(total))

        self.history_tree.delete(*self.history_tree.get_children())
        for i in range(13, -1, -1):
            d = (date.today() - timedelta(days=i)).isoformat()
            cnt = stats.get(d, 0)
            display = "今天" if i == 0 else d[5:]  # 显示 MM-DD
            self.history_tree.insert("", "end", values=(display, cnt))

    # ---------------- 设置 ----------------

    def save_settings(self):
        for key, var in self.setting_vars.items():
            self.settings[key] = int(var.get())
        self.settings["auto_start_next"] = bool(self.auto_var.get())
        for which in ("start", "end"):
            val = self.sound_combos[which].get()
            if val in (NONE_SOUND, CUSTOM_FILE):
                val = ""
            self.settings[which + "_sound"] = val
        save_data(self.data)
        if not self.running:
            self.remaining = self.phase_seconds(self.phase)
            self._render_timer()
        messagebox.showinfo("已保存", "设置已保存。")

    # ---------------- 其它 ----------------

    def _refresh_all(self):
        self._render_timer()
        self._refresh_task_list()
        self._update_active_task_label()
        self._refresh_stats()

    def _on_close(self):
        self._save_float_pos()
        save_data(self.data)
        self.root.destroy()


def main():
    root = tk.Tk()
    PomodoroApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()
