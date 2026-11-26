# -*- coding: utf-8 -*-
"""
Snowfall 2 — зимний оверлей для Windows 10/11 и macOS 12+.

Снег падает и копится на верхних краях окон и панели задач, сугробы едут
вместе с окнами, а когда окно закрывают — снег осыпается вниз. Из снега можно
катать шары и лепить снеговиков, есть варежка, лопата, снегоуборщики,
гирлянды и настройки снега для каждого окна (иконка в системном трее).

Запуск:   Windows: pip install PySide6 -> py Snowfall.py
          macOS:   pip3 install PySide6 pyobjc-framework-Quartz pyobjc-framework-Cocoa -> python3 Snowfall.py
"""
import sys
import os
import math
import random
import time
import json
import ctypes
import struct
import atexit
import base64
import re
import xml.etree.ElementTree as ET
from ctypes import wintypes

IS_WIN = sys.platform == "win32"
IS_MAC = sys.platform == "darwin"

from PySide6.QtCore import Qt, QTimer, QPointF, QRectF, QRect, QSize, Signal
from PySide6.QtGui import (QPainter, QColor, QPen, QBrush, QPainterPath, QPolygonF,
                           QRegion, QIcon, QPixmap, QImage, QCursor, QAction,
                           QActionGroup, QLinearGradient, QRadialGradient, QFont)
from PySide6.QtWidgets import (QApplication, QWidget, QSystemTrayIcon, QMenu, QFileDialog,
                               QVBoxLayout, QHBoxLayout, QGridLayout, QLabel, QPushButton,
                               QToolButton, QButtonGroup, QStackedWidget, QSlider, QFrame,
                               QScrollArea, QSizePolicy)

# ----------------------------------------------------------------- настройки
BIN = 3                  # ширина столбика сугроба, px
SNOW_MASS = 2.0          # сколько снега приносит одна снежинка (больше = быстрее растут сугробы)
CAP_WIN = 26             # макс. высота сугроба на окне
CAP_TB = 38              # макс. высота сугроба на панели задач
MAXSLOPE = 2.5           # крутизна склона сугроба
AUTO_PLOW_MEAN = 9.0     # средняя высота на панели задач, после которой выезжает снегоуборщик
BALL_MAX = 27.0          # максимальный радиус снежного шара
BULB_COLORS = [QColor(255, 226, 170), QColor(255, 184, 96), QColor(168, 208, 255),
               QColor(255, 168, 188), QColor(170, 232, 200)]

INTENSITY = {            # количество снежинок, скорость падения
    "Лёгкий снег": (120, 1.6),
    "Ровный снег": (260, 2.2),
    "Метель": (560, 3.2),
}
FPS_PRESETS = {"Экономный (24 кадра/с)": 24, "Обычный (40 кадров/с)": 40, "Плавный (60 кадров/с)": 60}
GARLAND_MODES = {"Выключены": "off", "Горят ровно": "static", "Мигают": "blink",
                 "Бегущая волна": "wave", "Мерцают": "twinkle"}
PLOW_FRONT = {"tractor": 84, "snowmobile": 72, "penguin": 35, "custom": 56}

DEFAULTS = {"intensity": "Ровный снег", "wind_base": 0.0, "gusts": False, "auto_plow": True,
            "vehicle": "tractor", "custom_path": "", "garland": "off", "fps": 40,
            "pause_fs": True, "rules": {}, "cat": True, "cat_break": True,
            "cat_color": "ginger", "cat_energy": 1,
            "snow_on_panel": False, "flakes_over_windows": True,
            "garland_style": "fairy", "snowman_outfit": "classic", "tree_preset": "gold"}
if IS_MAC:
    SETTINGS_PATH = os.path.join(os.path.expanduser("~"), "Library", "Application Support", "Snowfall", "settings.json")
else:
    SETTINGS_PATH = os.path.join(os.environ.get("APPDATA", os.path.expanduser("~")),
                                 "Snowfall", "settings.json")


def load_settings():
    cfg = json.loads(json.dumps(DEFAULTS))
    try:
        with open(SETTINGS_PATH, "r", encoding="utf-8") as f:
            data = json.load(f)
        for k in DEFAULTS:
            if k in data:
                cfg[k] = data[k]
    except Exception:
        pass
    if cfg.get("garland_style") not in ("fairy", "globe", "star", "icicle"):
        cfg["garland_style"] = "fairy"
    if cfg.get("tree_preset") not in ("lights", "gold", "red", "silver", "snow", "candy", "blue", "pink", "bells", "glow", "", None):
        cfg["tree_preset"] = "gold"
    return cfg


def save_settings(cfg):
    try:
        os.makedirs(os.path.dirname(SETTINGS_PATH), exist_ok=True)
        with open(SETTINGS_PATH, "w", encoding="utf-8") as f:
            json.dump(cfg, f, ensure_ascii=False, indent=1)
    except Exception:
        pass


# ------------------------------------------------------- чистая логика (без Qt)
def subtract(intervals, a, b):
    """Вычесть отрезок [a, b) из списка отрезков."""
    out = []
    for (l, r) in intervals:
        if b <= l or a >= r:
            out.append((l, r))
            continue
        if a > l:
            out.append((l, a))
        if b < r:
            out.append((b, r))
    return out


def in_vis(vis, x):
    for (l, r) in vis:
        if l <= x < r:
            return True
    return False


def relax(h, i):
    """Осыпание: снег не лежит слишком крутой горкой (волна осыпания от точки падения)."""
    n = len(h)
    stack = [i]
    guard = 120
    while stack and guard > 0:
        guard -= 1
        j = stack.pop()
        for nb in (j - 1, j + 1):
            nh = h[nb] if 0 <= nb < n else 0.0
            diff = h[j] - nh
            if diff > MAXSLOPE:
                d = (diff - MAXSLOPE) * 0.5
                h[j] -= d
                if 0 <= nb < n:
                    h[nb] += d
                    stack.append(nb)


def add_mass(h, c, mass, cap):
    """Добавить снег в столбик c (и соседние), с осыпанием."""
    n = len(h)
    w = 1 if mass <= 3.0 else min(10, int(math.sqrt(mass)) + 1)
    weights = [w + 1 - abs(k) for k in range(-w, w + 1)]
    tot = float(sum(weights))
    for k, wt in zip(range(-w, w + 1), weights):
        j = c + k
        if 0 <= j < n:
            h[j] = min(h[j] + mass * wt / tot, cap)
    relax(h, c)


# ------------------------------------------------------------------ Win32
SKIP_CLASSES = {
    "Progman", "WorkerW", "Shell_TrayWnd", "Shell_SecondaryTrayWnd",
    "Windows.UI.Core.CoreWindow", "ApplicationFrameInputSinkWindow",
    "XamlExplorerHostIslandWindow", "TopLevelWindowForOverflowXamlIsland",
}

if IS_WIN:
    user32 = ctypes.windll.user32
    dwmapi = ctypes.windll.dwmapi
    kernel32 = ctypes.windll.kernel32
    EnumProc = ctypes.WINFUNCTYPE(wintypes.BOOL, wintypes.HWND, wintypes.LPARAM)
    user32.IsWindowVisible.argtypes = [wintypes.HWND]
    user32.IsIconic.argtypes = [wintypes.HWND]
    user32.GetWindowLongW.argtypes = [wintypes.HWND, ctypes.c_int]
    user32.GetWindowLongW.restype = ctypes.c_long
    user32.SetWindowLongW.argtypes = [wintypes.HWND, ctypes.c_int, ctypes.c_long]
    user32.GetClassNameW.argtypes = [wintypes.HWND, wintypes.LPWSTR, ctypes.c_int]
    user32.GetWindowTextLengthW.argtypes = [wintypes.HWND]
    user32.GetWindowTextW.argtypes = [wintypes.HWND, wintypes.LPWSTR, ctypes.c_int]
    user32.GetWindowRect.argtypes = [wintypes.HWND, ctypes.POINTER(wintypes.RECT)]
    user32.FindWindowW.argtypes = [wintypes.LPCWSTR, wintypes.LPCWSTR]
    user32.FindWindowW.restype = wintypes.HWND
    user32.GetForegroundWindow.restype = wintypes.HWND
    user32.EnumWindows.argtypes = [EnumProc, wintypes.LPARAM]
    user32.GetAsyncKeyState.argtypes = [ctypes.c_int]
    user32.GetAsyncKeyState.restype = ctypes.c_short
    user32.GetWindowThreadProcessId.argtypes = [wintypes.HWND, ctypes.POINTER(wintypes.DWORD)]
    user32.LoadImageW.argtypes = [wintypes.HINSTANCE, wintypes.LPCWSTR, wintypes.UINT,
                                  ctypes.c_int, ctypes.c_int, wintypes.UINT]
    user32.LoadImageW.restype = ctypes.c_void_p
    user32.SetSystemCursor.argtypes = [ctypes.c_void_p, wintypes.DWORD]
    user32.SystemParametersInfoW.argtypes = [wintypes.UINT, wintypes.UINT, ctypes.c_void_p, wintypes.UINT]
    kernel32.OpenProcess.argtypes = [wintypes.DWORD, wintypes.BOOL, wintypes.DWORD]
    kernel32.OpenProcess.restype = ctypes.c_void_p
    kernel32.QueryFullProcessImageNameW.argtypes = [ctypes.c_void_p, wintypes.DWORD, wintypes.LPWSTR,
                                                    ctypes.POINTER(wintypes.DWORD)]
    kernel32.CloseHandle.argtypes = [ctypes.c_void_p]
    dwmapi.DwmGetWindowAttribute.argtypes = [wintypes.HWND, wintypes.DWORD, ctypes.c_void_p, wintypes.DWORD]

    def win_rect(hwnd):
        r = wintypes.RECT()
        if dwmapi.DwmGetWindowAttribute(hwnd, 9, ctypes.byref(r), ctypes.sizeof(r)) != 0:
            user32.GetWindowRect(hwnd, ctypes.byref(r))
        return r.left, r.top, r.right, r.bottom

    def list_windows(own):
        """Видимые окна сверху вниз по Z-порядку (физические пиксели)."""
        res = []

        def cb(hwnd, _lp):
            h = int(hwnd) if hwnd else 0
            if h in own or not h:
                return True
            if not user32.IsWindowVisible(hwnd) or user32.IsIconic(hwnd):
                return True
            cloaked = wintypes.DWORD(0)
            dwmapi.DwmGetWindowAttribute(hwnd, 14, ctypes.byref(cloaked), 4)
            if cloaked.value:
                return True
            ex = user32.GetWindowLongW(hwnd, -20) & 0xFFFFFFFF
            if (ex & 0x80) and not (ex & 0x40000):
                return True
            if ex & 0x08000000:
                return True
            buf = ctypes.create_unicode_buffer(256)
            user32.GetClassNameW(hwnd, buf, 256)
            if buf.value in SKIP_CLASSES:
                return True
            if user32.GetWindowTextLengthW(hwnd) == 0:
                return True
            res.append((h,) + win_rect(hwnd))
            return True

        user32.EnumWindows(EnumProc(cb), 0)
        return res

    def window_title(hwnd):
        buf = ctypes.create_unicode_buffer(256)
        user32.GetWindowTextW(hwnd, buf, 256)
        return buf.value

    def exe_of(hwnd):
        pid = wintypes.DWORD(0)
        user32.GetWindowThreadProcessId(hwnd, ctypes.byref(pid))
        hp = kernel32.OpenProcess(0x1000, False, pid.value)   # QUERY_LIMITED_INFORMATION
        if not hp:
            return ""
        buf = ctypes.create_unicode_buffer(520)
        n = wintypes.DWORD(520)
        ok = kernel32.QueryFullProcessImageNameW(hp, 0, buf, ctypes.byref(n))
        kernel32.CloseHandle(hp)
        return os.path.basename(buf.value).lower() if ok else ""

    def taskbar_top():
        tb = user32.FindWindowW("Shell_TrayWnd", None)
        if tb and user32.IsWindowVisible(tb):
            return win_rect(tb)[1]
        return None

    def set_overlay_style(hwnd, transparent):
        ex = user32.GetWindowLongW(hwnd, -20) & 0xFFFFFFFF
        ex |= 0x80000 | 0x80 | 0x08000000          # LAYERED | TOOLWINDOW | NOACTIVATE
        ex = (ex | 0x20) if transparent else (ex & ~0x20)  # 0x20 = TRANSPARENT (клики сквозь окно)
        user32.SetWindowLongW(hwnd, -20, ex & 0x7FFFFFFF)

    def native_id(handle):
        return handle

    def key_down(vk):
        return bool(user32.GetAsyncKeyState(vk) & 0x8000)

    def foreground_fullscreen(self_hwnd):
        hw = user32.GetForegroundWindow()
        if not hw or int(hw) == self_hwnd:
            return False
        buf = ctypes.create_unicode_buffer(256)
        user32.GetClassNameW(hw, buf, 256)
        if buf.value in SKIP_CLASSES:
            return False
        r = wintypes.RECT()
        user32.GetWindowRect(hw, ctypes.byref(r))
        sw, sh = user32.GetSystemMetrics(0), user32.GetSystemMetrics(1)
        return r.left <= 0 and r.top <= 0 and r.right >= sw and r.bottom >= sh

    def make_cursor_file(pm, hot, path):
        """Сохраняет QPixmap 32x32 как .cur (32-бит BGRA)."""
        img = pm.toImage().convertToFormat(QImage.Format.Format_ARGB32)
        w, h = img.width(), img.height()
        pix = bytearray()
        for y in range(h - 1, -1, -1):
            for x in range(w):
                px = img.pixel(x, y) & 0xFFFFFFFF
                pix += bytes((px & 255, (px >> 8) & 255, (px >> 16) & 255, (px >> 24) & 255))
        mask = bytes(((w + 31) // 32) * 4 * h)
        bih = struct.pack("<IiiHHIIiiII", 40, w, h * 2, 1, 32, 0, len(pix) + len(mask), 0, 0, 0, 0)
        data = bih + bytes(pix) + mask
        hdr = struct.pack("<HHH", 0, 2, 1) + struct.pack("<BBBBHHII", w, h, 0, 0, hot[0], hot[1], len(data), 22)
        with open(path, "wb") as f:
            f.write(hdr + data)

    def set_system_arrow(path):
        """Подменяет системную стрелку своим курсором (path=None — вернуть обычные курсоры)."""
        if path:
            hc = user32.LoadImageW(None, path, 2, 0, 0, 0x10)     # IMAGE_CURSOR, LR_LOADFROMFILE
            if hc:
                user32.SetSystemCursor(hc, 32512)                  # OCR_NORMAL
        else:
            user32.SystemParametersInfoW(0x57, 0, None, 0)         # SPI_SETCURSORS
elif IS_MAC:
    # ---------------------------------------------------------------- macOS (Quartz + AppKit через pyobjc)
    import objc
    from Quartz import (CGWindowListCopyWindowInfo, CGWindowListCreateDescriptionFromArray,
                        kCGWindowListOptionOnScreenOnly, kCGWindowListExcludeDesktopElements,
                        kCGNullWindowID, CGEventSourceKeyState)
    from AppKit import NSApplication, NSColor, NSWorkspace

    _MAC_INFO = {}                                   # id окна -> (программа, заголовок)
    _MAC_KEYS = {0x1B: 53}                           # Esc

    def _mac_dpr():
        try:
            return QApplication.primaryScreen().devicePixelRatio()
        except Exception:
            return 2.0

    def _bounds(d):
        b = d.get("kCGWindowBounds") or {}
        k = _mac_dpr()           # дальше код ждёт «физические» пиксели и сам делит на dpr
        x, y, w, h = b.get("X", 0), b.get("Y", 0), b.get("Width", 0), b.get("Height", 0)
        return int(x * k), int(y * k), int((x + w) * k), int((y + h) * k)

    def win_rect(hwnd):
        try:
            arr = CGWindowListCreateDescriptionFromArray([hwnd])
            if arr and len(arr):
                return _bounds(arr[0])
        except Exception:
            pass
        return (0, 0, 0, 0)

    def list_windows(own):
        """Обычные окна (слой 0) сверху вниз по Z-порядку. Окна оверлея лежат выше (слой 25) и не попадают в список."""
        res = []
        try:
            infos = CGWindowListCopyWindowInfo(kCGWindowListOptionOnScreenOnly | kCGWindowListExcludeDesktopElements,
                                               kCGNullWindowID) or []
        except Exception:
            return res
        for d in infos:
            try:
                if int(d.get("kCGWindowLayer", 1)) != 0:
                    continue
                if float(d.get("kCGWindowAlpha", 1.0)) < 0.05:
                    continue
                wid = int(d.get("kCGWindowNumber", 0))
                if not wid or wid in own:
                    continue
                r = _bounds(d)
                k = _mac_dpr()
                if (r[2] - r[0]) < 60 * k or (r[3] - r[1]) < 40 * k:
                    continue
                _MAC_INFO[wid] = (str(d.get("kCGWindowOwnerName") or "").lower(), str(d.get("kCGWindowName") or ""),
                                  int(d.get("kCGWindowOwnerPID", 0)))
                res.append((wid,) + r)
            except Exception:
                continue
        return res

    def window_title(hwnd):
        i = _MAC_INFO.get(hwnd)
        return i[1] if i else ""

    def exe_of(hwnd):
        i = _MAC_INFO.get(hwnd)
        return i[0] if i else ""

    def taskbar_top():
        """Верх Dock-а, если он снизу и не прячется (по разнице между screen и availableGeometry)."""
        try:
            sc = QApplication.primaryScreen()
            g, a = sc.geometry(), sc.availableGeometry()
            if a.y() + a.height() < g.y() + g.height() - 4:
                return int((a.y() + a.height()) * sc.devicePixelRatio())
        except Exception:
            pass
        return None

    def native_id(handle):
        """winId() Qt -> номер окна Quartz (тот же, что в списке окон)."""
        try:
            view = objc.objc_object(c_void_p=ctypes.c_void_p(handle))
            return int(view.window().windowNumber())
        except Exception:
            return handle

    def set_overlay_style(hwnd, transparent):
        try:
            view = objc.objc_object(c_void_p=ctypes.c_void_p(hwnd))
            w = view.window()
            if w is None:
                return
            w.setOpaque_(False)
            w.setBackgroundColor_(NSColor.clearColor())
            w.setHasShadow_(False)
            w.setLevel_(25)                                # NSStatusWindowLevel: выше обычных окон и Dock
            # на всех рабочих столах | не листается Mission Control | поверх полноэкранных | вне Cmd+Tab
            w.setCollectionBehavior_((1 << 0) | (1 << 4) | (1 << 6) | (1 << 8))
            w.setIgnoresMouseEvents_(bool(transparent))
        except Exception:
            pass

    def key_down(vk):
        code = _MAC_KEYS.get(vk)
        if code is None:
            return False
        try:
            return bool(CGEventSourceKeyState(0, code))
        except Exception:
            return False

    def foreground_fullscreen(self_hwnd):
        try:
            app = NSWorkspace.sharedWorkspace().frontmostApplication()
            pid = int(app.processIdentifier())
            if pid == os.getpid():
                return False
            sc = QApplication.primaryScreen().geometry()
            k = _mac_dpr()
            for (wid, l, t, r, b) in list_windows(set()):
                i = _MAC_INFO.get(wid)
                if i and i[2] == pid and l <= 0 and t <= 0 and r >= sc.width() * k - 2 and b >= sc.height() * k - 2:
                    return True
        except Exception:
            pass
        return False

    def make_cursor_file(pm, hot, path):
        pass

    def set_system_arrow(path):
        pass                                               # системный курсор на Mac не подменить; см. Overlay.set_mitten
else:                                   # заглушки, чтобы файл можно было импортировать на других системах
    def win_rect(hwnd): return (0, 0, 0, 0)
    def list_windows(own): return []
    def window_title(hwnd): return ""
    def exe_of(hwnd): return ""
    def taskbar_top(): return None
    def set_overlay_style(hwnd, transparent): pass
    def key_down(vk): return False
    def foreground_fullscreen(self_hwnd): return False
    def make_cursor_file(pm, hot, path): pass
    def set_system_arrow(path): pass
    def native_id(h): return h


# ===================================================================== ART
INK = QColor(46, 38, 64)


def mkpen(w=2.0, c=None, alpha=None):
    col = QColor(c if c is not None else INK)
    if alpha is not None:
        col.setAlpha(alpha)
    pen = QPen(col)
    pen.setWidthF(w)
    pen.setJoinStyle(Qt.PenJoinStyle.RoundJoin)
    pen.setCapStyle(Qt.PenCapStyle.RoundCap)
    return pen


def lin(x1, y1, x2, y2, *stops):
    g = QLinearGradient(x1, y1, x2, y2)
    for pos, col in stops:
        g.setColorAt(pos, col)
    return QBrush(g)


def rad(cx, cy, r, fx, fy, *stops):
    g = QRadialGradient(cx, cy, r, fx, fy)
    for pos, col in stops:
        g.setColorAt(pos, col)
    return QBrush(g)


def poly(*pts):
    return QPolygonF([QPointF(x, y) for x, y in pts])


def spline(pts, closed=True, k=1.0):
    """Гладкая кривая (Катмулл-Ром) через точки."""
    path = QPainterPath()
    n = len(pts)

    def P(i):
        return pts[i % n] if closed else pts[max(0, min(n - 1, i))]
    path.moveTo(pts[0][0], pts[0][1])
    for i in range(n if closed else n - 1):
        p0, p1, p2, p3 = P(i - 1), P(i), P(i + 1), P(i + 2)
        path.cubicTo(p1[0] + (p2[0] - p0[0]) * k / 6, p1[1] + (p2[1] - p0[1]) * k / 6,
                     p2[0] - (p3[0] - p1[0]) * k / 6, p2[1] - (p3[1] - p1[1]) * k / 6,
                     p2[0], p2[1])
    if closed:
        path.closeSubpath()
    return path


def shape(p, path_or_poly, fill, w=2.0, c=None):
    p.setPen(mkpen(w, c) if w else Qt.PenStyle.NoPen)
    p.setBrush(fill)
    if isinstance(path_or_poly, QPolygonF):
        p.drawPolygon(path_or_poly)
    else:
        p.drawPath(path_or_poly)


def circle(p, x, y, r, fill, w=1.6, c=None):
    p.setPen(mkpen(w, c) if w else Qt.PenStyle.NoPen)
    p.setBrush(fill)
    p.drawEllipse(QPointF(x, y), r, r)


def ellipse(p, x, y, rx, ry, fill, w=1.6, c=None):
    p.setPen(mkpen(w, c) if w else Qt.PenStyle.NoPen)
    p.setBrush(fill)
    p.drawEllipse(QPointF(x, y), rx, ry)


def rrect(p, x, y, w_, h_, r, fill, w=1.8, c=None):
    p.setPen(mkpen(w, c) if w else Qt.PenStyle.NoPen)
    p.setBrush(fill)
    p.drawRoundedRect(QRectF(x, y, w_, h_), r, r)


def line(p, x1, y1, x2, y2, w, col, alpha=None):
    p.setPen(mkpen(w, col, alpha))
    p.drawLine(QPointF(x1, y1), QPointF(x2, y2))


def make_pm(w, h, fn, S, ox, oy):
    pm = QPixmap(int(w * S), int(h * S))
    pm.fill(Qt.GlobalColor.transparent)
    pm.setDevicePixelRatio(S)
    p = QPainter(pm)
    p.setRenderHint(QPainter.RenderHint.Antialiasing)
    p.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform)
    p.translate(ox, oy)
    fn(p)
    p.end()
    return (pm, ox, oy)


RED1, RED2 = QColor(238, 92, 76), QColor(178, 34, 50)
YEL1, YEL2 = QColor(255, 214, 70), QColor(240, 150, 24)
STEEL1, STEEL2 = QColor(200, 208, 222), QColor(120, 128, 150)
GLASS = QColor(176, 222, 246)


def mitten_cursor_pm():
    """Варежка-курсор 32x32; острие (горячая точка) слева сверху."""
    pm = QPixmap(32, 32)
    pm.fill(Qt.GlobalColor.transparent)
    p = QPainter(pm)
    p.setRenderHint(QPainter.RenderHint.Antialiasing)
    p.translate(7, 5)
    p.rotate(-28)
    shape(p, spline([(2, 0), (9, 2), (12, 10), (13, 19), (5, 20), (-1, 19), (-2, 10), (-1, 3)], True, 0.9),
          lin(0, 0, 0, 20, (0, QColor(255, 96, 96)), (1, QColor(200, 38, 56))), 1.8)
    shape(p, spline([(12, 11), (17, 9), (18, 14), (13, 16)], True, 0.9), QColor(232, 60, 74), 1.6)
    rrect(p, -2.2, 18, 16, 6, 2, QColor(255, 250, 240), 1.6)
    for k in range(4):
        line(p, 1 + k * 3.6, 18.8, 1 + k * 3.6, 23, 0.9, INK, 90)
    line(p, 3, 3, 8, 3.4, 1.4, QColor(255, 255, 255), 170)
    p.end()
    return pm


# ---- снеговик: детали рисуются кодом (радиусы шаров задаёт игрок) ----
SNOW_W = QColor(252, 254, 255)
SNOW_B = QColor(196, 214, 238)


def draw_ball(p, cx, cy, r, alpha=1.0):
    p.setPen(mkpen(max(1.3, r * 0.09), QColor(86, 102, 150)))
    p.setBrush(rad(cx, cy, r, cx - r * .3, cy - r * .35, (0, SNOW_W), (0.6, QColor(236, 244, 255)), (1, SNOW_B)))
    p.drawEllipse(QPointF(cx, cy), r, r)
    p.setPen(Qt.PenStyle.NoPen)
    p.setBrush(QColor(255, 255, 255, 190))
    p.drawEllipse(QPointF(cx - r * .38, cy - r * .42), r * .22, r * .13)


def part_hat(p, s):
    """Цилиндр; (0,0) — центр основания полей."""
    rrect(p, -8.5 * s, -1.6 * s, 17 * s, 3.2 * s, 1.5 * s, lin(0, -2 * s, 0, 2 * s, (0, QColor(70, 70, 92)), (1, QColor(28, 28, 40))), 1.6)
    rrect(p, -5.2 * s, -13.5 * s, 10.4 * s, 12.4 * s, 1.6 * s, lin(-5 * s, 0, 5 * s, 0, (0, QColor(78, 78, 100)), (1, QColor(30, 30, 44))), 1.6)
    rrect(p, -5.3 * s, -4.6 * s, 10.6 * s, 2.8 * s, 0.8 * s, QColor(220, 50, 64), 1.2)
    line(p, -3.4 * s, -12 * s, -3.4 * s, -6 * s, 1.0, QColor(255, 255, 255), 90)


def part_nose(p, s):
    shape(p, poly((0, -1.4 * s), (-9 * s, 0.8 * s), (0, 1.9 * s)),
          lin(0, -1.5 * s, 0, 2 * s, (0, QColor(255, 170, 60)), (1, QColor(232, 102, 20))), 1.3)
    line(p, -2 * s, 0.1 * s, -6 * s, 0.7 * s, 0.9, QColor(150, 60, 10), 150)


def part_arm(p, s, side=1):
    """Ветка-рука, начало в (0,0), растёт вправо (side=1) или влево (side=-1)."""
    p.save()
    p.scale(side, 1)
    path = QPainterPath()
    path.moveTo(0, 0)
    path.quadTo(10 * s, -3 * s, 20 * s, -7 * s)
    p.setBrush(Qt.BrushStyle.NoBrush)
    p.setPen(mkpen(3.6 * max(.7, s * .8), QColor(40, 26, 24)))
    p.drawPath(path)
    p.setPen(mkpen(2.2 * max(.7, s * .8), QColor(138, 92, 52)))
    p.drawPath(path)
    for (x0, y0, x1, y1) in ((13 * s, -4.6 * s, 19 * s, -13 * s), (16 * s, -5.8 * s, 24 * s, -10 * s)):
        line(p, x0, y0, x1, y1, 2.8, QColor(40, 26, 24))
        line(p, x0, y0, x1, y1, 1.6, QColor(138, 92, 52))
    p.restore()


def part_scarf_wrap(p, r, s, col1=QColor(222, 54, 66)):
    """Намотка шарфа вокруг шеи; r — радиус головы, (0,0) — центр шеи."""
    w = r * 1.55
    shape(p, spline([(-w, -2.6 * s), (-w * .4, 1.8 * s), (w * .4, 1.8 * s), (w, -2.6 * s), (w * .9, 3.2 * s),
                     (w * .4, 5.8 * s), (-w * .4, 5.8 * s), (-w * .9, 3.2 * s)], True, 0.8),
          lin(0, -2 * s, 0, 6 * s, (0, QColor(240, 80, 92)), (1, QColor(176, 32, 52))), 1.7)
    for k in range(5):
        x = -w * .72 + k * w * .36
        line(p, x, 2.6 * s, x, 5.2 * s, 1.5, QColor(255, 255, 255), 215)


def part_scarf_tail(p, s, flutter=0.0):
    path = QPainterPath()
    path.moveTo(0, 0)
    path.cubicTo(5 * s + flutter, 6 * s, 3 * s + flutter * 1.6, 12 * s, 7 * s + flutter * 2, 18 * s)
    p.setBrush(Qt.BrushStyle.NoBrush)
    p.setPen(mkpen(7 * s * .7 + 1.2))
    p.drawPath(path)
    p.setPen(mkpen(5 * s * .7 + .6, QColor(222, 54, 66)))
    p.drawPath(path)
    p.setPen(mkpen(1.4, QColor(255, 255, 255), 215))
    p.drawLine(QPointF(4 * s + flutter, 6 * s), QPointF(8 * s + flutter, 6.6 * s))
    p.drawLine(QPointF(4 * s + flutter * 1.5, 11 * s), QPointF(8 * s + flutter * 1.5, 11.6 * s))


def part_coal(p, s):
    circle(p, 0, 0, 1.8 * s, rad(0, 0, 1.8 * s, -.5 * s, -.5 * s, (0, QColor(96, 96, 112)), (1, QColor(24, 24, 34))), 1.0)


def snowman_geometry(balls):
    """balls: радиусы снизу вверх (убывающие). Возвращает центры y (вверх отрицательные)."""
    cys = []
    cy = -balls[0]
    cys.append(cy)
    for i in range(1, len(balls)):
        cy -= (balls[i - 1] + balls[i]) * 0.82
        cys.append(cy)
    return cys


def snowman_extent(balls, done=True):
    cys = snowman_geometry(balls)
    top = cys[-1] - balls[-1]
    if done and len(balls) == 3:
        top -= balls[-1] * 1.75     # цилиндр
    return -top, max(balls)


def draw_snowman(p, balls, done, flutter=0.0, hide=()):
    """Рисует снеговика, основание (0,0). hide — набор не рисуемых деталей (для разлёта)."""
    cys = snowman_geometry(balls)
    for r, cy in zip(balls, cys):
        if 'ball' not in hide:
            draw_ball(p, 0, cy, r)
    if not (done and len(balls) == 3):
        return
    r1, r2, r3 = balls
    c1, c2, c3 = cys
    s = r3 / 9.0
    if 'buttons' not in hide:
        for k in range(3):
            p.save()
            p.translate(-r2 * .06, c2 - r2 * .45 + k * r2 * .45)
            part_coal(p, r2 / 9.0 * 1.2)
            p.restore()
    if 'arms' not in hide:
        p.save()
        p.translate(r2 * .86, c2 - r2 * .1)
        p.rotate(-22)
        part_arm(p, r2 / 11.0, 1)
        p.restore()
        p.save()
        p.translate(-r2 * .86, c2 - r2 * .05)
        p.rotate(26)
        part_arm(p, r2 / 11.0, -1)
        p.restore()
    if 'scarf' not in hide:
        p.save()
        p.translate(0, c3 + r3 * .84)
        part_scarf_wrap(p, r3, s)
        p.translate(r3 * .56, 2.4 * s)
        part_scarf_tail(p, s, flutter)
        p.restore()
    if 'face' not in hide:
        for ex in (-.34, .3):
            p.save()
            p.translate(r3 * ex, c3 - r3 * .3)
            part_coal(p, s * 1.0)
            p.restore()
        for k in range(5):
            a = math.radians(-60 + k * 30)
            p.save()
            p.translate(-r3 * .04 + r3 * .46 * math.sin(a) / .87, c3 + r3 * (0.50 - 0.26 * (1 - math.cos(a))))
            part_coal(p, s * .62)
            p.restore()
        p.save()
        p.translate(-r3 * .04, c3 + r3 * .04)
        p.rotate(6)
        part_nose(p, s * 1.15)
        p.restore()
    if 'hat' not in hide:
        p.save()
        p.translate(r3 * .04, c3 - r3 * .86)
        p.rotate(-6)
        part_hat(p, s * 1.0)
        p.restore()


# ===== минималистичный стиль: плоские формы, без контуров, сдержанная палитра =====
G0 = QColor(32, 36, 48)       # графит
G1 = QColor(56, 62, 78)
G2 = QColor(98, 106, 124)
ST = QColor(160, 170, 186)    # сталь
WH = QColor(243, 246, 250)    # белый
OR = QColor(232, 104, 58)     # акцент (тёплый оранжевый)
OR2 = QColor(190, 74, 40)
TL = QColor(44, 160, 166)     # бирюзовый акцент
TL2 = QColor(30, 118, 130)
GL = QColor(166, 200, 224)    # стекло


def al(col, a):
    c = QColor(col)
    c.setAlpha(int(a))
    return c


def fl(p, obj, col):
    p.setPen(Qt.PenStyle.NoPen)
    p.setBrush(col)
    if isinstance(obj, QPolygonF):
        p.drawPolygon(obj)
    else:
        p.drawPath(obj)


def fr(p, x, y, w, h, r, col):
    p.setPen(Qt.PenStyle.NoPen)
    p.setBrush(col)
    p.drawRoundedRect(QRectF(x, y, w, h), r, r)


def fc(p, x, y, r, col):
    p.setPen(Qt.PenStyle.NoPen)
    p.setBrush(col)
    p.drawEllipse(QPointF(x, y), r, r)


def fe(p, x, y, rx, ry, col):
    p.setPen(Qt.PenStyle.NoPen)
    p.setBrush(col)
    p.drawEllipse(QPointF(x, y), rx, ry)


def stroke(p, path, w, col):
    p.setBrush(Qt.BrushStyle.NoBrush)
    p.setPen(mkpen(w, col))
    p.drawPath(path)


def soft_shadow(p, cx, rx):
    p.setPen(Qt.PenStyle.NoPen)
    p.setBrush(rad(cx, 0.5, rx, cx, 0.5, (0, QColor(10, 16, 30, 70)), (1, QColor(10, 16, 30, 0))))
    p.drawEllipse(QPointF(cx, 0.5), rx, 3.2)


def plow_blade(p, x0, y0, sc=1.0):
    """Отвал: светлый, с тонкой акцентной кромкой. (x0, y0) — нижняя точка у земли."""
    p.save()
    p.translate(x0, y0)
    p.scale(sc, sc)
    body = spline([(3, -2), (-8, -6), (-12, -22), (-9, -36), (3, -32), (5, -16)], True, 0.7)
    fl(p, body, WH)
    fl(p, poly((3, -32), (5, -16), (3, -2), (1.4, -3), (3.2, -16), (1.8, -31)), al(ST, 150))
    fl(p, poly((-9.2, -36), (3, -32), (3.4, -28.6), (-10.4, -32.4)), OR)
    fl(p, poly((3, -2), (-8, -6), (-9, -9), (4.4, -5)), G1)
    p.restore()


TR_RED, TR_RED_D, TR_RED_L = QColor(204, 34, 54), QColor(150, 22, 40), QColor(228, 70, 84)
TR_BLK = QColor(26, 26, 30)
TR_GLASS, TR_GLASS_D = QColor(198, 226, 244), QColor(170, 205, 228)
TR_PIPE, TR_PIPE_L = QColor(52, 54, 62), QColor(118, 122, 134)


def arc_path(cx, cy, r, a0, a1, n=18):
    path = QPainterPath()
    for i in range(n + 1):
        a = math.radians(a0 + (a1 - a0) * i / n)
        x, y = cx + r * math.cos(a), cy + r * math.sin(a)
        if i == 0:
            path.moveTo(x, y)
        else:
            path.lineTo(x, y)
    return path


def tractor_body(p):
    """Трактор (смотрит влево): плоский стиль. Колёса — отдельные спрайты (22,-17,r17) и (-30,-11.5,r11.5)."""
    soft_shadow(p, -2, 58)
    fr(p, -41, -18, 64, 6, 2, TR_BLK)                      # шасси
    fr(p, -48, -22, 7, 12, 2.5, TR_BLK)                    # передний груз
    # капот
    fr(p, -44, -42, 47, 25, 6.5, TR_RED)
    p.setPen(mkpen(1.5, TR_RED_L))
    p.drawLine(QPointF(-38, -39.4), QPointF(-8, -39.8))
    for k in range(8):                                     # решётка
        fr(p, -35 + k * 3.5, -37, 1.9, 11, 0.9, TR_RED_D)
    fc(p, -45.2, -31.5, 4.4, QColor(168, 172, 184))        # фара
    fc(p, -46.4, -32.8, 1.5, WH)
    # выхлопная труба
    fr(p, -22, -61, 5, 22, 1.6, TR_PIPE)
    fr(p, -23.2, -63.6, 7.4, 4, 1.6, TR_PIPE_L)
    # кабина
    fr(p, 3, -66, 41, 45, 4, TR_BLK)
    fr(p, 6, -62, 22, 34, 2, TR_GLASS)
    fr(p, 31, -62, 10, 34, 2, TR_GLASS)
    fl(p, poly((8, -61), (15, -61), (9, -43), (8, -43)), al(WH, 100))
    fl(p, poly((33, -61), (37, -61), (33, -50)), al(WH, 90))
    fr(p, 0.5, -71.5, 47, 6, 1.6, TR_RED)                  # крыша
    p.setPen(mkpen(1.4, TR_RED_L))
    p.drawLine(QPointF(3, -69.6), QPointF(44, -69.6))
    fr(p, 21.5, -74.8, 5.4, 3.4, 1.2, TR_BLK)              # основание мигалки
    # крылья (тонкие дуги)
    stroke(p, arc_path(22, -17, 22.5, 196, 344), 4.0, TR_RED)
    stroke(p, arc_path(-30, -11.5, 16.5, 198, 342), 3.4, TR_RED)
    # подножка и задний фонарь
    fr(p, 30, -14.5, 13, 2.6, 1.0, QColor(150, 150, 156))
    fr(p, 32, -14, 2, 6, 0.8, QColor(150, 150, 156))
    fr(p, 45, -36, 2.6, 5.6, 1.0, QColor(236, 70, 70))


def tractor_loader(p):
    """Фронтальный ковш со стрелой (рисуется поверх кузова и колёс)."""
    p.setPen(mkpen(3.8, TR_PIPE))
    p.drawLine(QPointF(8, -31), QPointF(-58, -27))
    p.setPen(mkpen(1.3, TR_PIPE_L))
    p.drawLine(QPointF(6, -32.6), QPointF(-54, -28.8))
    p.setPen(mkpen(2.2, QColor(120, 124, 136)))            # гидроцилиндр
    p.drawLine(QPointF(-6, -22), QPointF(-46, -17))
    fc(p, 8, -31, 2.6, TR_BLK)
    bucket = poly((-56, -37), (-70, -41), (-79, -28), (-80, -9), (-73, -4.5), (-56, -8))
    fl(p, bucket, QColor(60, 62, 72))
    fl(p, poly((-56, -37), (-70, -41), (-79, -28), (-72, -27.4), (-62, -30), (-56, -29)), QColor(84, 88, 100))
    fl(p, poly((-80, -9), (-73, -4.5), (-70, -6.6), (-80, -12)), ST)
    p.setPen(mkpen(1.6, TR_RED))
    p.drawLine(QPointF(-57, -35), QPointF(-57, -10))
    fc(p, -58, -27, 2.4, TR_BLK)
    fc(p, -58, -27, 1.0, ST)


def wheel_sprite(p, r):
    """Колесо трактора: тёмная шина, ступица с болтами. Центр (0,0)."""
    fc(p, 0, 0, r, QColor(38, 38, 44))
    n = 22 if r > 13 else 16
    for k in range(n):
        p.save()
        p.rotate(k * 360.0 / n)
        fr(p, -r * 0.045, -r + 0.6, r * 0.09, r * 0.2, 0.4, QColor(62, 62, 70))
        p.restore()
    fc(p, 0, 0, r * 0.74, QColor(48, 48, 56))
    fc(p, 0, 0, r * 0.52, QColor(152, 136, 140))
    fc(p, 0, 0, r * 0.47, QColor(168, 152, 156))
    for k in range(8):
        a = math.radians(k * 45 + 22.5)
        fc(p, r * 0.34 * math.cos(a), r * 0.34 * math.sin(a), max(0.9, r * 0.065), QColor(104, 90, 96))
    fc(p, 0, 0, r * 0.15, QColor(118, 104, 108))


def snowmobile_body(p):
    soft_shadow(p, -8, 54)
    # трек
    fr(p, -6, -14, 50, 14, 7, G0)
    # лыжа и стойки
    p.setPen(mkpen(2.4, G1))
    p.drawLine(QPointF(-40, -4), QPointF(-33, -18))
    p.drawLine(QPointF(-26, -4), QPointF(-24, -18))
    ski = spline([(-62, -9), (-58, -3.5), (-48, -0.8), (-14, -0.8), (-14, -3.6), (-48, -4.4), (-57, -6.6)], True, 0.6)
    fl(p, ski, G1)
    # рычаг отвала
    p.setPen(mkpen(3.0, G1))
    p.drawLine(QPointF(-54, -17), QPointF(-67, -15))
    # корпус
    body = spline([(-57, -15), (-53, -27), (-39, -37), (-22, -39), (-6, -37), (10, -35), (27, -31), (39, -22),
                   (41, -12), (10, -11), (-30, -10)], True, 0.9)
    fl(p, body, WH)
    stripe = spline([(-52, -16), (-30, -22), (0, -22), (36, -17), (40, -12), (10, -11), (-30, -10)], True, 0.8)
    fl(p, stripe, TL)
    fl(p, spline([(-30, -10), (10, -11), (41, -12), (40, -14), (8, -13.4), (-28, -12.2)], True, 0.5), TL2)
    p.setPen(mkpen(1.6, ST, 130))
    p.drawLine(QPointF(-44, -33), QPointF(-22, -36.6))
    fr(p, -56.4, -24.6, 3, 7.4, 1.5, QColor(255, 238, 170))
    # сиденье, стекло, фонарь
    fl(p, spline([(0, -31), (2, -36), (24, -33), (31, -27), (26, -25.5), (2, -28)], True, 0.8), G0)
    fl(p, poly((-35, -36), (-25, -53), (-16, -53), (-19, -36)), al(GL, 205))
    fl(p, poly((-30, -41), (-26, -50), (-23.4, -50), (-27.6, -41)), al(WH, 120))
    fr(p, 39.2, -21, 2.8, 5.6, 1.2, QColor(238, 80, 80))
    p.setPen(mkpen(2.2, G1))
    p.drawLine(QPointF(-16, -38), QPointF(-9, -46))


def snowmobile_rider(p):
    fl(p, spline([(5, -33), (8, -51), (19, -59), (29, -49), (27, -33)], True, 0.9), G1)
    p.setPen(mkpen(5.4, G1))
    p.drawLine(QPointF(11, -50), QPointF(-9, -45))
    fc(p, -10, -45, 3.0, G0)
    fc(p, 13, -64, 8.6, WH)
    fl(p, spline([(4.8, -64), (5.4, -68.6), (10.4, -69), (11.2, -63), (9.2, -59.8), (5.8, -60.2)], True, 0.9), G0)
    fl(p, poly((16, -72), (22, -62), (20, -60), (14, -70)), al(ST, 90))
    p.setPen(mkpen(2.2, OR))
    p.drawLine(QPointF(7, -55.4), QPointF(19, -53.4))


def scarf_tail(p, t, wind=1.0):
    path = QPainterPath()
    x0, y0 = 20, -54.4
    path.moveTo(x0, y0)
    for k in range(1, 6):
        path.lineTo(x0 + 6 + 5 * k, y0 + 3 + 2.2 * math.sin(t * 9 - k * 1.2) * (0.5 + k * .35))
    stroke(p, path, 3.2, OR)


def penguin_body(p):
    soft_shadow(p, 2, 24)
    # задний ласт
    fl(p, spline([(11, -42), (20, -33), (20, -20), (14, -28)], True, 0.9), G0)
    # тело
    body = spline([(0, -71), (-11, -66), (-16.5, -52), (-18.5, -33), (-15, -14), (-6, -5), (8, -5), (16, -14),
                   (19, -33), (17, -52), (11, -66)], True, 1.0)
    fl(p, body, G1)
    # живот
    fl(p, spline([(-3, -45), (-10.5, -34), (-11, -20), (-5, -9), (5, -9), (11, -20), (11, -34), (4, -45)], True, 1.0), WH)
    # глаза и клюв
    for ex in (-8.4, 2.6):
        fc(p, ex, -53, 2.8, WH)
        fc(p, ex - 0.9, -53, 1.4, G0)
    fl(p, poly((-11, -48.5), (-20, -45.6), (-11, -42.4)), QColor(238, 150, 56))
    # шапка и шарф
    cap = QPainterPath()
    cap.moveTo(-14.6, -60)
    cap.cubicTo(-15, -80, 12.4, -80, 12.6, -60)
    cap.closeSubpath()
    fl(p, cap, OR)
    fr(p, -15.6, -62.6, 29.6, 6.4, 3.2, OR2)
    fl(p, spline([(-15, -41), (-5, -37.5), (8, -37.5), (17, -41), (17, -35), (8, -31.5), (-5, -31.5), (-15, -35)], True, 0.8), TL)
    fl(p, spline([(12, -36), (19, -33), (21, -19), (15.5, -19), (14, -30)], True, 0.9), TL2)
    # передний ласт
    fl(p, spline([(-5, -34), (-10, -28), (-9, -19), (-3, -25)], True, 0.9), G0)


def penguin_feet(p, t):
    for k, ox in enumerate((-6.5, 7.5)):
        lift = max(0.0, math.sin(t * 7 + k * math.pi)) * 2.4
        fl(p, spline([(ox - 7, -lift), (ox - 5, -4.5 - lift), (ox + 3, -4.5 - lift), (ox + 6.5, -lift), (ox + 3, 1), (ox - 5, 1)], True, 0.8),
           QColor(238, 150, 56))


def penguin_shovel(p, swing=0.0):
    p.save()
    p.translate(-6, -27)
    p.rotate(swing)
    p.setPen(mkpen(2.6, QColor(176, 130, 82)))
    p.drawLine(QPointF(0, 0), QPointF(-26, 22))
    fl(p, spline([(-25, 26), (-45, 26), (-48, 14), (-35, 8), (-22, 14)], True, 0.7), ST)
    fl(p, poly((-47, 14.5), (-35, 8.6), (-31.6, 10.4), (-45, 17)), al(WH, 130))
    p.restore()


def bulb_sprite(p, col, level):
    """Маленькая огоньковая лампочка. Точка крепления (16, 8), центр шарика (16, 13.6) (с учётом сдвига на 5)."""
    b = (0.0, 0.3, 0.55, 0.8, 1.0)[level]
    p.translate(0, 5)                 # запас сверху под свечение
    if level > 0:
        g = QColor(col)
        g.setAlpha(int(135 * b))
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(rad(16, 8.6, 13, 16, 8.6, (0, g), (1, QColor(col.red(), col.green(), col.blue(), 0))))
        p.drawEllipse(QPointF(16, 8.6), 13, 13)
    fr(p, 14.7, 1.6, 2.6, 3.4, 1.0, G0)
    dim = QColor(int(col.red() * .3 + 46), int(col.green() * .3 + 48), int(col.blue() * .3 + 56))
    lit = QColor(min(255, int(col.red() * .8 + 55)), min(255, int(col.green() * .8 + 55)), min(255, int(col.blue() * .8 + 55)))
    mid = QColor(int(dim.red() + (lit.red() - dim.red()) * b), int(dim.green() + (lit.green() - dim.green()) * b),
                 int(dim.blue() + (lit.blue() - dim.blue()) * b))
    fc(p, 16, 8.6, 3.5, mid)
    fc(p, 15.1, 7.6, 1.0, al(WH, 90 + 140 * b))


# ===== пиксель-арт (пингвин, котик) =====
class Pix:
    """Крошечный растр: рисуем эллипсами/многоугольниками/линиями, получаем настоящий пиксель-арт."""

    def __init__(self, w, h):
        self.w, self.h, self.p = w, h, {}

    def put(self, x, y, c):
        x, y = int(x), int(y)
        if 0 <= x < self.w and 0 <= y < self.h:
            self.p[(x, y)] = c

    def get(self, x, y):
        return self.p.get((int(x), int(y)))

    def rect(self, x0, y0, x1, y1, c):
        for y in range(int(y0), int(y1)):
            for x in range(int(x0), int(x1)):
                self.put(x, y, c)

    def ell(self, cx, cy, rx, ry, c):
        for y in range(int(cy - ry) - 1, int(cy + ry) + 2):
            for x in range(int(cx - rx) - 1, int(cx + rx) + 2):
                dx, dy = (x + .5 - cx) / rx, (y + .5 - cy) / ry
                if dx * dx + dy * dy <= 1.0:
                    self.put(x, y, c)

    def poly(self, pts, c):
        ys = [q[1] for q in pts]
        n = len(pts)
        for y in range(int(min(ys)), int(max(ys)) + 1):
            yy = y + .5
            xs = []
            for i in range(n):
                (x0, y0), (x1, y1) = pts[i], pts[(i + 1) % n]
                if (y0 <= yy < y1) or (y1 <= yy < y0):
                    xs.append(x0 + (yy - y0) * (x1 - x0) / (y1 - y0))
            xs.sort()
            for k in range(0, len(xs) - 1, 2):
                for x in range(int(math.floor(xs[k] + .5)), int(math.floor(xs[k + 1] + .5))):
                    self.put(x, y, c)

    def line(self, x0, y0, x1, y1, c, th=1):
        n = int(max(abs(x1 - x0), abs(y1 - y0))) * 2 + 1
        for i in range(n + 1):
            t = i / float(n)
            x, y = x0 + (x1 - x0) * t, y0 + (y1 - y0) * t
            for a in range(th):
                for b in range(th):
                    self.put(int(x) + a - (th - 1) // 2, int(y) + b - (th - 1) // 2, c)

    def mask(self):
        return set(self.p)

    def outline(self, c):
        m = self.mask()
        add = {}
        for (x, y) in m:
            for dx, dy in ((1, 0), (-1, 0), (0, 1), (0, -1)):
                q = (x + dx, y + dy)
                if q not in m and 0 <= q[0] < self.w and 0 <= q[1] < self.h:
                    add[q] = c
        self.p.update(add)

    def rim(self, base, light=None, dark=None):
        """Подсветка верхне-левого и затенение нижне-правого края областей цвета base."""
        pts = [k for k, v in self.p.items() if v == base]
        S = set(pts)
        for (x, y) in pts:
            if dark and ((x + 1, y) not in S or (x, y + 1) not in S):
                self.p[(x, y)] = dark
            elif light and ((x - 1, y) not in S or (x, y - 1) not in S):
                self.p[(x, y)] = light


def pix_to_qimage(pix):
    img = QImage(pix.w, pix.h, QImage.Format.Format_ARGB32)
    img.fill(Qt.GlobalColor.transparent)
    for (x, y), c in pix.p.items():
        img.setPixelColor(x, y, QColor(c[0], c[1], c[2], c[3] if len(c) > 3 else 255))
    return img


def pix_to_sprite(pix, anchor, dpr, ps=2):
    """-> (QPixmap, ax, ay): каждый пиксель арта = ps логических px (целое число физических)."""
    k = max(2, int(round(ps * dpr)))
    pm = QPixmap.fromImage(pix_to_qimage(pix)).scaled(
        pix.w * k, pix.h * k, Qt.AspectRatioMode.IgnoreAspectRatio, Qt.TransformationMode.FastTransformation)
    pm.setDevicePixelRatio(dpr)
    return (pm, anchor[0] * k / dpr, anchor[1] * k / dpr)


# ---------- пингвин (смотрит влево; ground y = 40) ----------
PG_BODY, PG_BODY_L, PG_BODY_D = (44, 46, 56), (66, 70, 82), (30, 32, 40)
PG_HEAD = (24, 24, 30)
PG_BELLY, PG_BELLY_D = (238, 228, 210), (190, 182, 170)
PG_FACE = (250, 248, 242)
PG_BEAK, PG_BEAK_D = (238, 130, 46), (196, 88, 30)
PG_FOOT = (240, 134, 48)
PG_FLIP = (54, 58, 70)
PG_WOOD, PG_WOOD_D = (182, 132, 80), (134, 92, 54)
PG_STEEL, PG_STEEL_L, PG_STEEL_D = (150, 164, 184), (206, 216, 230), (98, 108, 126)


def penguin_pix(phase=0):
    """Пингвин с лопатой. phase 0..3 — шаг (0/2 — шаг, 1/3 — «подпрыгивание»)."""
    W_, H_ = 48, 42
    pix = Pix(W_, H_)
    bob = (0, -1, 0, -1)[phase % 4]
    lift_l = 1 if phase % 4 == 1 else 0
    lift_r = 1 if phase % 4 == 3 else 0
    pix.ell(30, 40.4, 14, 1.5, (20, 28, 48, 70))                     # тень
    # лопата (под ластом)
    pix.line(20, 27 + bob, 9, 37 + bob, PG_WOOD, 1)
    pix.line(21, 27 + bob, 10, 37 + bob, PG_WOOD_D, 1)
    blade = [(2, 36 + bob), (12, 32 + bob), (15, 38 + bob), (5, 41 + bob)]
    pix.poly(blade, PG_STEEL)
    pix.line(2, 36 + bob, 12, 32 + bob, PG_STEEL_L, 1)
    pix.line(5, 40 + bob, 14, 37 + bob, PG_STEEL_D, 1)
    # задний ласт
    pix.poly([(39, 17 + bob), (45, 27 + bob), (44, 35 + bob), (38, 29 + bob)], PG_FLIP)
    # тело
    pix.ell(30, 26 + bob, 11.5, 13.5, PG_BODY)
    pix.rim(PG_BODY, PG_BODY_L, PG_BODY_D)
    # живот
    pix.ell(27.5, 28 + bob, 8.2, 11.4, PG_BELLY)
    pix.rim(PG_BELLY, None, PG_BELLY_D)
    # голова
    pix.ell(26, 10 + bob, 9, 8, PG_HEAD)
    pix.ell(24.2, 10.8 + bob, 5.3, 4.7, PG_FACE)
    pix.rim(PG_FACE, None, (222, 220, 214))
    # глаз
    pix.rect(22, 9 + bob, 24, 11 + bob, (20, 20, 24))
    pix.put(22, 9 + bob, (150, 150, 160))
    # клюв
    pix.poly([(17, 11 + bob), (10, 12.6 + bob), (17, 14.8 + bob)], PG_BEAK)
    pix.line(11, 13 + bob, 17, 14 + bob, PG_BEAK_D, 1)
    # передний ласт (держит лопату)
    pix.poly([(24, 19 + bob), (18, 26 + bob), (19, 33 + bob), (25, 29 + bob)], PG_FLIP)
    pix.line(24, 20 + bob, 19, 26 + bob, (78, 82, 96), 1)
    # лапы
    pix.ell(26, 39.4 - lift_l, 3.9, 1.6, PG_FOOT)
    pix.ell(36, 39.4 - lift_r, 3.9, 1.6, PG_FOOT)
    pix.line(23, 40 - lift_l, 29, 40 - lift_l, PG_BEAK_D, 1) if False else None
    return pix, (30, 40)


# ---------- котик (смотрит влево; ground y = 29) ----------
CAT_PALETTES = {
    "ginger": dict(name="Рыжий", swatch="#e8984a", F=(232, 152, 74), FD=(194, 104, 42), ST=(194, 104, 42),
                   FL=(250, 228, 194), OUT=(104, 56, 30), EAR=(240, 150, 150), NOSE=(228, 110, 124), EYE=(96, 188, 108)),
    "gray": dict(name="Серый", swatch="#96a0b0", F=(150, 158, 172), FD=(104, 112, 128), ST=(120, 128, 144),
                 FL=(226, 230, 238), OUT=(56, 62, 78), EAR=(236, 160, 170), NOSE=(226, 120, 134), EYE=(232, 192, 70)),
    "black": dict(name="Чёрный", swatch="#3c3e48", F=(62, 64, 74), FD=(38, 40, 48), ST=(48, 50, 60),
                  FL=(112, 116, 130), OUT=(12, 12, 18), EAR=(150, 110, 122), NOSE=(170, 104, 116), EYE=(240, 208, 70)),
    "white": dict(name="Белый", swatch="#f2f0ec", F=(246, 244, 240), FD=(214, 208, 204), ST=(226, 222, 218),
                  FL=(255, 255, 255), OUT=(150, 148, 156), EAR=(244, 176, 184), NOSE=(240, 150, 164), EYE=(110, 170, 232)),
    "siamese": dict(name="Сиамский", swatch="#d9c3a0", F=(240, 226, 204), FD=(112, 82, 66), ST=(226, 208, 184),
                    FL=(250, 242, 230), OUT=(96, 70, 58), EAR=(150, 112, 100), NOSE=(150, 100, 96), EYE=(110, 170, 232)),
    "tuxedo": dict(name="Чёрно-белый", swatch="#8d93a6", F=(48, 50, 60), FD=(30, 32, 40), ST=(40, 42, 52),
                   FL=(250, 250, 250), OUT=(12, 12, 18), EAR=(150, 110, 122), NOSE=(236, 150, 164), EYE=(96, 188, 108)),
}
CT_PUP = (24, 24, 32)


def _cat_head(pix, hx, hy, blink, look, pal):
    """Голова с ушами; (hx, hy) — центр. look=(dx,dy) в {-1,0,1}: куда смотрят зрачки."""
    F, FD, ST, FL, OUT = pal["F"], pal["FD"], pal["ST"], pal["FL"], pal["OUT"]
    pix.ell(hx, hy, 6.2, 5.2, F)
    pix.poly([(hx - 5.6, hy - 2.6), (hx - 4.6, hy - 8.2), (hx - 0.8, hy - 4.2)], F)
    pix.poly([(hx + 0.6, hy - 4.4), (hx + 3.8, hy - 8.4), (hx + 5.2, hy - 2.4)], F)
    pix.poly([(hx - 4.6, hy - 3.6), (hx - 4.0, hy - 6.6), (hx - 2.2, hy - 4.4)], pal["EAR"])
    pix.poly([(hx + 1.8, hy - 4.6), (hx + 3.4, hy - 6.8), (hx + 4.0, hy - 3.6)], pal["EAR"])
    pix.ell(hx - 3.6, hy + 1.8, 2.8, 2.0, FL)
    pix.put(hx - 6, hy + 0.4, pal["NOSE"])
    pix.put(hx - 5, hy + 0.4, pal["NOSE"])
    for k in range(3):
        pix.put(hx - 1 + k * 2, hy - 4, ST)
        pix.put(hx - 1 + k * 2, hy - 3, ST)
    for ex in (int(hx - 3), int(hx + 1.6)):
        ey = int(hy - 1.4)
        if blink:
            pix.rect(ex, ey + 1, ex + 2, ey + 2, OUT)
        else:
            pix.rect(ex, ey, ex + 2, ey + 2, pal["EYE"])
            pix.put(ex + (1 if look[0] > 0 else 0), ey + (1 if look[1] > 0 else 0), CT_PUP)


def cat_pix(pose="sit", phase=0, blink=False, look=(0, 0), color="ginger"):
    """pose: sit wash stretch loaf roll crouch swat walk run leap dig sleep climb. phase — кадр цикла."""
    pal = CAT_PALETTES.get(color, CAT_PALETTES["ginger"])
    F, FD, ST, FL, OUT = pal["F"], pal["FD"], pal["ST"], pal["FL"], pal["OUT"]
    pix = Pix(42, 30)
    pix.ell(21, 29.3, 12, 1.2, (20, 28, 48, 60))
    if pose in ("sit", "swat", "wash"):
        tail = (0, 1, 2, 1)[phase % 4]
        pix.line(28, 26, 33, 25 - (tail > 1), FD, 2)
        pix.line(33, 25 - (tail > 1), 34, 20 - tail, FD, 2)
        pix.line(34, 20 - tail, 32, 17 - tail, FD, 2)
        pix.put(32, 17 - tail, FL)
        pix.ell(23, 22, 7.5, 7, F)
        pix.ell(18, 17.5, 5.2, 9.5, F)
        pix.ell(16.2, 22, 2.6, 6, FL)
        for k in range(3):
            pix.line(24 + k * 2, 17 + k, 26 + k * 2, 19 + k, ST, 1)
        hy = 11 if pose == "wash" else 9.5
        _cat_head(pix, 13, hy, blink or pose == "wash", look, pal)
        if pose == "swat":
            pix.line(15, 17, 8, 13 - (phase % 2), F, 3)
            pix.ell(7, 12.5 - (phase % 2), 2.2, 2.0, FL)
            pix.rect(13, 19, 16, 28, F)
        elif pose == "wash":
            pix.line(15, 18, 10, 13 + (phase % 2), F, 2)
            pix.ell(9.5, 12.6 + (phase % 2), 1.9, 1.7, FL)
            pix.rect(12, 20, 16, 28, F)
            pix.rect(12, 26, 16, 29, FL)
        else:
            pix.rect(12, 19, 16, 28, F)
            pix.rect(12, 26, 16, 29, FL)
        pix.ell(24, 28.2, 4.5, 1.6, FL)
    elif pose in ("walk", "run", "leap", "dig"):
        sw = (-1, 0, 1, 0)[phase % 4] * (1.6 if pose == "run" else 1)
        low = 2 if pose == "run" else 0
        if pose in ("leap", "dig"):
            sw = 0
        by = 17 + low
        pix.line(30, by - 2, 34, by - 8, FD, 2)
        pix.line(34, by - 8, 33, by - 12, FD, 2)
        pix.put(33, by - 12, FL)
        stretch = 2 if pose in ("run", "leap") else 0
        for lx, s_ in ((11 - stretch, -sw), (27 + stretch, sw)):
            if pose == "leap":
                pix.line(lx, by + 2, lx + (-5 if lx < 18 else 5), by + 5, FD, 2)
            else:
                pix.line(lx, by + 2, lx + s_ * 3, 28, FD, 2)
        pix.ell(19, by, 10.5 + stretch * 0.6, 5.2 - low * 0.3, F)
        pix.ell(17, by + 2.4, 6.5, 2.4, FL)
        for k in range(4):
            pix.line(16 + k * 3, by - 5, 17 + k * 3, by - 2, ST, 1)
        for lx, s_ in ((14 - stretch, sw), (24 + stretch, -sw)):
            if pose == "leap":
                pix.line(lx, by + 3, lx + (-6 if lx < 18 else 6), by + 5, F, 2)
            elif pose == "dig" and lx < 18:
                pix.line(lx, by + 3, 4 + (phase % 2) * 4, 27 - (phase % 2) * 2, F, 2)      # передняя лапа копает снег
                pix.rect(2 + (phase % 2) * 4, 27 - (phase % 2) * 2, 6 + (phase % 2) * 4, 29, FL)
            else:
                pix.line(lx, by + 3, lx + s_ * 3, 28, F, 2)
                pix.rect(lx + s_ * 3 - 1, 28, lx + s_ * 3 + 3, 29, FL)
        _cat_head(pix, 8 - stretch, by - 3 + (1 if pose in ("run", "dig") else 0), blink, look, pal)
    elif pose == "stretch":      # потягивается: передняя часть внизу, попа кверху
        pix.line(30, 13, 34, 8, FD, 2)
        pix.put(34, 7, FL)
        pix.ell(26, 17, 6.5, 6, F)
        pix.ell(19, 21, 6, 4.2, F)
        pix.ell(13, 24, 5, 3.8, F)
        pix.ell(20, 22.5, 5, 2, FL)
        pix.rect(24, 21, 28, 29, F)
        pix.rect(24, 27, 29, 29, FL)
        pix.line(14, 26, 4, 28, F, 2)
        pix.ell(3.5, 28, 2.2, 1.2, FL)
        _cat_head(pix, 10.5, 22.5, True, (0, 0), pal)
    elif pose == "crouch":       # крадётся: прижался, попа виляет
        w = phase % 2
        pix.line(31, 23, 37, 24 + w, FD, 2)
        pix.ell(27, 20.5 - w, 5, 5, F)
        pix.ell(19, 22.5, 7, 4.2, F)
        pix.ell(18, 25, 6, 1.8, FL)
        pix.rect(25, 25, 29, 29, F)
        pix.rect(25, 27, 30, 29, FL)
        pix.rect(10, 26, 15, 29, F)
        pix.rect(9, 27, 13, 29, FL)
        _cat_head(pix, 9, 22.5, False, look, pal)
    elif pose == "roll":         # валяется на спине
        w = phase % 2
        pix.line(31, 26, 36, 22, FD, 2)
        pix.ell(19, 25, 12, 3.8, F)
        pix.ell(19, 22, 10.5, 3.6, FL)
        for lx, ly, tx_, ty_ in ((13, 22, 11 - w, 14), (17, 21, 16 + w, 13), (23, 21, 24 - w, 13), (27, 22, 29 + w, 15)):
            pix.line(lx, ly, tx_, ty_, F, 2)
            pix.put(tx_, ty_ - 1, FL)
        _cat_head(pix, 7, 24.5, True, (0, 0), pal)
    elif pose == "loaf":         # лежит «хлебушком»
        tail = (0, 1)[phase % 2]
        pix.line(30, 26, 34, 25 - tail, FD, 2)
        pix.ell(20, 23, 11.5, 6, F)
        pix.ell(20, 26, 9.5, 2.6, FL)
        for k in range(4):
            pix.line(18 + k * 3, 18, 19 + k * 3, 21, ST, 1)
        pix.ell(11, 27.4, 4, 1.8, FL)
        _cat_head(pix, 10, 18.5, blink, look, pal)
    elif pose == "climb":        # лезет по стене (стена слева)
        w = phase % 2
        pix.line(27, 25, 30, 29, FD, 2)
        pix.ell(23, 23.5, 5.5, 5, F)
        pix.ell(19, 18.5, 5, 8, F)
        pix.ell(16.5, 20, 2.4, 5.6, FL)
        pix.line(16, 15, 9, 10 + w * 2, F, 2)
        pix.line(18, 17, 10, 15 - w * 2, F, 2)
        pix.put(8, 10 + w * 2, FL)
        pix.put(9, 15 - w * 2, FL)
        pix.line(21, 26, 14, 24 + w, FD, 2)
        pix.line(24, 27, 17, 28 - w, F, 2)
        _cat_head(pix, 14, 9.5, False, (-1, -1), pal)
    else:                        # sleep: свернулся
        pix.ell(19, 23.5, 13, 5.6, F)
        pix.ell(19, 26, 11, 2.6, FL)
        for k in range(5):
            pix.line(14 + k * 3, 19, 15 + k * 3, 22, ST, 1)
        pix.line(30, 24, 35, 22, FD, 2)
        pix.line(35, 22, 34, 18, FD, 2)
        pix.put(34, 18, FL)
        _cat_head(pix, 8, 23.5, True, (0, 0), pal)
    pix.p = {(x + 3, y): c for (x, y), c in pix.p.items() if x + 3 < pix.w}
    pix.outline(OUT)
    return pix, (22, 29)


def heart_pix():
    pix = Pix(7, 6)
    rows = [".XX.XX.", "XXXXXXX", "XXXXXXX", ".XXXXX.", "..XXX..", "...X..."]
    for y, r in enumerate(rows):
        for x, ch in enumerate(r):
            if ch == "X":
                pix.put(x, y, (236, 84, 110))
    pix.put(1, 1, (255, 176, 190))
    return pix, (3, 6)


def zzz_pix():
    pix = Pix(5, 5)
    rows = ["XXXXX", "...X.", "..X..", ".X...", "XXXXX"]
    for y, r in enumerate(rows):
        for x, ch in enumerate(r):
            if ch == "X":
                pix.put(x, y, (170, 188, 226))
    return pix, (2, 5)


def emote_pix(kind):
    """Смайлы над котиком: '!' '?'."""
    if kind == "!":
        pix, rows, col = Pix(2, 7), ["XX", "XX", "XX", "XX", "..", "XX", "XX"], (255, 96, 84)
    else:
        pix, rows, col = Pix(5, 7), [".XXX.", "X...X", "....X", "...X.", "..X..", ".....", "..X.."], (120, 196, 255)
    for y, r in enumerate(rows):
        for x, ch in enumerate(r):
            if ch == "X":
                pix.put(x, y, col)
    pix.outline((20, 24, 40))
    return pix, (pix.w // 2, pix.h)


# ===== SVG-спрайты (пингвин и снегоход — ваши рисунки), свой лёгкий рендерер без QtSvg =====
PENGUIN_SVG = r"""<svg xmlns="http://www.w3.org/2000/svg" viewBox="96 84 280 352" width="560" height="704">
  <title>Пингвин с лопатой</title>
  <defs>
    <linearGradient id="pg-body" x1="0" y1="0" x2="1" y2="0">
      <stop offset="0" stop-color="#1B2C3F"/>
      <stop offset="1" stop-color="#2D4560"/>
    </linearGradient>
    <clipPath id="pg-clip">
      <path d="M215 128 C250 128 268 156 266 190 C264 215 285 250 288 300 C291 360 265 410 215 414 C165 418 130 385 128 330 C126 270 148 235 160 195 C164 155 185 128 215 128 Z"/>
    </clipPath>
  </defs>

  <!-- хвост -->
  <path d="M142 378 L108 412 L166 406 Z" fill="#16263A"/>
  <!-- дальняя лапа -->
  <path d="M168 416 Q172 404 192 406 Q216 408 218 418 Q196 424 168 416 Z" fill="#F29A1F"/>
  <!-- тело -->
  <path d="M215 128 C250 128 268 156 266 190 C264 215 285 250 288 300 C291 360 265 410 215 414 C165 418 130 385 128 330 C126 270 148 235 160 195 C164 155 185 128 215 128 Z" fill="url(#pg-body)"/>
  <!-- живот и щека -->
  <g clip-path="url(#pg-clip)">
    <path d="M262 190 C256 230 292 262 292 305 C292 358 266 404 214 412 C238 380 250 340 248 300 C246 262 252 224 262 190 Z" fill="#FFFFFF"/>
    <path d="M232 186 C246 178 262 180 270 190 L270 214 C254 218 238 210 232 186 Z" fill="#FFFFFF"/>
  </g>
  <!-- ближняя лапа -->
  <path d="M214 418 Q218 402 244 404 Q272 406 276 418 Q246 426 214 418 Z" fill="#FFAB2E"/>
  <path d="M234 410 V418 M246 408 V420 M258 410 V418" stroke="#E08A12" stroke-width="2" stroke-linecap="round"/>
  <!-- клюв -->
  <path d="M262 172 Q292 172 308 186 L262 190 Z" fill="#FFB02E"/>
  <path d="M262 190 L304 188 Q288 202 262 200 Z" fill="#F08C14"/>
  <!-- глаз -->
  <circle cx="242" cy="176" r="8.5" fill="#FFFFFF"/>
  <circle cx="245" cy="177" r="5" fill="#16263A"/>
  <circle cx="246.8" cy="175" r="1.6" fill="#FFFFFF"/>
  <!-- румянец -->
  <circle cx="252" cy="194" r="6" fill="#FF9AA2" opacity="0.55"/>

  <!-- шапка -->
  <path d="M168 154 Q168 108 216 106 Q264 108 266 154 Z" fill="#E4572E"/>
  <path d="M170 140 Q216 128 264 140 V146 Q216 134 170 146 Z" fill="#FFFFFF" opacity="0.9"/>
  <rect x="164" y="150" width="106" height="16" rx="8" fill="#FFFFFF"/>
  <circle cx="216" cy="102" r="11" fill="#FFFFFF"/>

  <!-- шарф -->
  <path d="M160 214 Q214 240 270 212 L272 234 Q214 262 158 236 Z" fill="#E4572E"/>
  <path d="M174 226 Q214 244 258 224" fill="none" stroke="#FFFFFF" stroke-width="4" stroke-linecap="round" opacity="0.85"/>
  <path d="M164 228 Q128 232 112 262 L136 270 Q146 250 168 246 Z" fill="#E4572E"/>
  <path d="M122 252 L142 260" stroke="#FFFFFF" stroke-width="4" stroke-linecap="round" opacity="0.85"/>

  <!-- лопата -->
  <line x1="342" y1="232" x2="312" y2="400" stroke="#A9713A" stroke-width="9" stroke-linecap="round"/>
  <path d="M326 226 Q342 212 358 226" fill="none" stroke="#A9713A" stroke-width="8" stroke-linecap="round"/>
  <path d="M288 392 Q312 384 340 392 Q352 408 348 424 L286 424 Q278 406 288 392 Z" fill="#53AEE3"/>
  <path d="M294 398 Q312 392 332 398" fill="none" stroke="#9AD3F2" stroke-width="4" stroke-linecap="round"/>
  <path d="M292 394 Q300 376 318 380 Q336 376 342 394 Z" fill="#FFFFFF" stroke="#D5E7F4" stroke-width="2"/>

  <!-- крыло держит лопату -->
  <path d="M206 236 C246 230 292 258 322 290 C320 306 304 310 292 300 C268 280 236 270 204 264 Z" fill="#16263A"/>
  <path d="M224 246 C252 248 280 262 304 284" fill="none" stroke="#2D4560" stroke-width="3" stroke-linecap="round"/>
</svg>
"""

SNOWMOBILE_SVG = r"""<svg xmlns="http://www.w3.org/2000/svg" viewBox="436 264 420 172" width="840" height="344">
  <title>Снегоход с отвалом</title>
  <defs>
    <linearGradient id="sm-sled" x1="0" y1="0" x2="0" y2="1">
      <stop offset="0" stop-color="#FF8F55"/>
      <stop offset="1" stop-color="#E5502A"/>
    </linearGradient>
    <linearGradient id="sm-blade" x1="0" y1="0" x2="1" y2="0">
      <stop offset="0" stop-color="#FFD14D"/>
      <stop offset="1" stop-color="#F5AE1B"/>
    </linearGradient>
  </defs>

  <g transform="translate(-26 0)">
    <!-- гусеница -->
    <rect x="470" y="380" width="250" height="42" rx="21" fill="#1B2C3F"/>
    <rect x="478" y="387" width="234" height="28" rx="14" fill="none" stroke="#3B5470" stroke-width="2" stroke-dasharray="3 7"/>
    <circle cx="494" cy="401" r="11" fill="#6E87A0"/><circle cx="494" cy="401" r="4" fill="#1B2C3F"/>
    <circle cx="596" cy="401" r="8" fill="#6E87A0"/>
    <circle cx="696" cy="401" r="11" fill="#6E87A0"/><circle cx="696" cy="401" r="4" fill="#1B2C3F"/>

    <!-- корпус -->
    <path d="M478 380 C476 340 496 322 524 320 L618 320 C646 304 690 318 720 342 C744 352 750 366 744 382 Z" fill="url(#sm-sled)"/>
    <path d="M486 366 Q610 352 744 364 L744 376 Q610 366 484 378 Z" fill="#FFFFFF" opacity="0.92"/>
    <path d="M640 326 Q676 322 704 340" fill="none" stroke="#FFB48A" stroke-width="4" stroke-linecap="round"/>
    <!-- сиденье -->
    <path d="M498 320 Q504 294 530 294 H600 Q614 294 616 320 Z" fill="#1B2C3F"/>
    <!-- руль -->
    <line x1="648" y1="318" x2="644" y2="294" stroke="#1B2C3F" stroke-width="6" stroke-linecap="round"/>
    <line x1="630" y1="292" x2="660" y2="292" stroke="#1B2C3F" stroke-width="7" stroke-linecap="round"/>
    <!-- стекло -->
    <path d="M656 316 Q664 282 690 274 Q694 298 698 330 Z" fill="#CDEAFA" opacity="0.9"/>
    <path d="M674 288 Q680 296 682 312" fill="none" stroke="#FFFFFF" stroke-width="3" stroke-linecap="round"/>
    <!-- фара -->
    <circle cx="738" cy="356" r="17" fill="#FFE08A" opacity="0.3"/>
    <circle cx="738" cy="356" r="8" fill="#FFE27A"/>
    <!-- лыжа -->
    <path d="M702 426 H788 Q808 426 812 406" fill="none" stroke="#1B2C3F" stroke-width="7" stroke-linecap="round"/>
    <line x1="724" y1="382" x2="744" y2="424" stroke="#1B2C3F" stroke-width="6" stroke-linecap="round"/>
    <!-- кронштейн и отвал -->
    <line x1="750" y1="384" x2="818" y2="384" stroke="#1B2C3F" stroke-width="7" stroke-linecap="round"/>
    <path d="M812 336 Q852 340 856 372 V420 Q832 428 812 414 Z" fill="url(#sm-blade)"/>
    <path d="M824 346 Q844 352 846 372" fill="none" stroke="#FFE69A" stroke-width="4" stroke-linecap="round"/>
    <!-- брызги снега -->
    <g fill="#FFFFFF" stroke="#BCD7EA" stroke-width="1.5">
      <circle cx="866" cy="400" r="7"/><circle cx="878" cy="382" r="4.5"/><circle cx="858" cy="388" r="3.5"/>
    </g>
  </g>
</svg>
"""


def _svg_color(s, default=None):
    if not s or s == "none":
        return default
    if s.startswith("#"):
        s = s[1:]
        if len(s) == 3:
            s = "".join(ch * 2 for ch in s)
        return QColor(int(s[0:2], 16), int(s[2:4], 16), int(s[4:6], 16))
    return default


def svg_path(d):
    """Разбор атрибута d (M L H V C Q Z, прописные и строчные) -> QPainterPath."""
    toks = re.findall(r"[A-Za-z]|-?\d*\.\d+|-?\d+", d)
    path = QPainterPath()
    i, n, cmd = 0, len(toks), None
    x = y = sx = sy = 0.0

    def num():
        nonlocal i
        v = float(toks[i])
        i += 1
        return v
    guard = 0
    while i < n and guard < 100000:
        guard += 1
        if toks[i].isalpha():
            cmd = toks[i]
            i += 1
        if cmd in ("M", "m"):
            nx, ny = num(), num()
            if cmd == "m":
                nx, ny = nx + x, ny + y
            x, y, sx, sy = nx, ny, nx, ny
            path.moveTo(x, y)
            cmd = "L" if cmd == "M" else "l"
        elif cmd in ("L", "l"):
            nx, ny = num(), num()
            if cmd == "l":
                nx, ny = nx + x, ny + y
            x, y = nx, ny
            path.lineTo(x, y)
        elif cmd in ("H", "h"):
            nx = num()
            x = nx + x if cmd == "h" else nx
            path.lineTo(x, y)
        elif cmd in ("V", "v"):
            ny = num()
            y = ny + y if cmd == "v" else ny
            path.lineTo(x, y)
        elif cmd in ("C", "c"):
            v = [num() for _ in range(6)]
            if cmd == "c":
                v = [v[0] + x, v[1] + y, v[2] + x, v[3] + y, v[4] + x, v[5] + y]
            path.cubicTo(*v)
            x, y = v[4], v[5]
        elif cmd in ("Q", "q"):
            v = [num() for _ in range(4)]
            if cmd == "q":
                v = [v[0] + x, v[1] + y, v[2] + x, v[3] + y]
            path.quadTo(*v)
            x, y = v[2], v[3]
        elif cmd in ("Z", "z"):
            path.closeSubpath()
            x, y = sx, sy
            cmd = None
        else:
            i += 1
    return path


class SvgDoc:
    """Минимальный SVG: path/circle/rect/line, linearGradient, clipPath, g(transform=translate, clip-path)."""

    def __init__(self, text):
        root = ET.fromstring(text)
        self.vb = [float(v) for v in root.get("viewBox").replace(",", " ").split()]
        self.grads, self.clips, self.ops = {}, {}, []
        strip = lambda t: t.split("}")[-1]
        for el in root.iter():
            tag = strip(el.tag)
            if tag == "linearGradient":
                stops = []
                for st in el:
                    stops.append((float(st.get("offset", "0")), _svg_color(st.get("stop-color"), QColor(0, 0, 0)),
                                  float(st.get("stop-opacity", "1"))))
                self.grads[el.get("id")] = (float(el.get("x1", "0")), float(el.get("y1", "0")),
                                            float(el.get("x2", "1")), float(el.get("y2", "0")), stops)
            elif tag == "clipPath":
                for ch in el:
                    if strip(ch.tag) == "path":
                        self.clips[el.get("id")] = svg_path(ch.get("d"))
        self._walk(root, 0.0, 0.0, None, strip, {})

    def _walk(self, node, dx, dy, clip, strip, inh):
        for el in node:
            tag = strip(el.tag)
            if tag in ("defs", "title", "linearGradient", "clipPath", "stop"):
                continue
            if tag == "g":
                ndx, ndy = dx, dy
                tr = el.get("transform", "")
                m = re.match(r"translate\(\s*(-?[\d.]+)[ ,]+(-?[\d.]+)\s*\)", tr)
                if m:
                    ndx, ndy = dx + float(m.group(1)), dy + float(m.group(2))
                cp = el.get("clip-path")
                nclip = clip
                if cp:
                    m2 = re.match(r"url\(#([^)]+)\)", cp)
                    nclip = m2.group(1) if m2 else clip
                ninh = dict(inh)
                for k in ("fill", "stroke", "stroke-width", "stroke-linecap", "stroke-dasharray"):
                    if el.get(k) is not None:
                        ninh[k] = el.get(k)
                self._walk(el, ndx, ndy, nclip, strip, ninh)
                continue
            path = QPainterPath()
            if tag == "path":
                path = svg_path(el.get("d"))
            elif tag == "circle":
                cx, cy, r = float(el.get("cx")), float(el.get("cy")), float(el.get("r"))
                path.addEllipse(QPointF(cx, cy), r, r)
            elif tag == "rect":
                x, y = float(el.get("x", "0")), float(el.get("y", "0"))
                w, h = float(el.get("width")), float(el.get("height"))
                rx = float(el.get("rx", el.get("ry", "0")))
                ry = float(el.get("ry", el.get("rx", "0")))
                path.addRoundedRect(QRectF(x, y, w, h), rx, ry)
            elif tag == "line":
                path.moveTo(float(el.get("x1")), float(el.get("y1")))
                path.lineTo(float(el.get("x2")), float(el.get("y2")))
            else:
                continue
            fill = el.get("fill", inh.get("fill", "#000000" if tag != "line" else "none"))
            self.ops.append({"path": path, "fill": fill, "stroke": el.get("stroke", inh.get("stroke")),
                             "sw": float(el.get("stroke-width", inh.get("stroke-width", "1"))),
                             "cap": el.get("stroke-linecap", inh.get("stroke-linecap")),
                             "op": float(el.get("opacity", "1")),
                             "dash": el.get("stroke-dasharray", inh.get("stroke-dasharray")),
                             "clip": clip, "tr": (dx, dy), "d": el.get("d", "")})

    def find(self, prefix):
        """Индексы элементов, у которых d начинается с prefix (для анимации частей)."""
        return [i for i, o in enumerate(self.ops) if o["d"].startswith(prefix)]

    def draw(self, p, tweaks=None, dash=0.0):
        tweaks = tweaks or {}
        for idx, o in enumerate(self.ops):
            p.save()
            p.translate(o["tr"][0], o["tr"][1])
            tw = tweaks.get(idx)
            if tw:
                p.translate(tw[0], tw[1])
            if o["clip"] and o["clip"] in self.clips:
                p.setClipPath(self.clips[o["clip"]])
            p.setOpacity(o["op"])
            path = o["path"]
            fill = o["fill"]
            brush = Qt.BrushStyle.NoBrush
            if fill and fill.startswith("url("):
                gid = re.match(r"url\(#([^)]+)\)", fill).group(1)
                g = self.grads.get(gid)
                if g:
                    bb = path.boundingRect()
                    grad = QLinearGradient(bb.x() + g[0] * bb.width(), bb.y() + g[1] * bb.height(),
                                           bb.x() + g[2] * bb.width(), bb.y() + g[3] * bb.height())
                    for off, col, a in g[4]:
                        c = QColor(col)
                        c.setAlphaF(a)
                        grad.setColorAt(off, c)
                    brush = QBrush(grad)
            else:
                col = _svg_color(fill)
                if col is not None:
                    brush = col
            sc = _svg_color(o["stroke"])
            if sc is not None:
                pen = QPen(sc)
                pen.setWidthF(o["sw"])
                if o["cap"] == "round":
                    pen.setCapStyle(Qt.PenCapStyle.RoundCap)
                else:
                    pen.setCapStyle(Qt.PenCapStyle.FlatCap)
                pen.setJoinStyle(Qt.PenJoinStyle.MiterJoin)
                if o["dash"]:
                    parts = [float(v) / max(o["sw"], 0.1) for v in re.split(r"[ ,]+", o["dash"].strip())]
                    pen.setDashPattern(parts)
                    pen.setDashOffset(dash / max(o["sw"], 0.1))
                p.setPen(pen)
            else:
                p.setPen(Qt.PenStyle.NoPen)
            p.setBrush(brush)
            p.drawPath(path)
            p.restore()


def svg_sprite(doc, scale, ground, anchor_x, dpr, mirror=True, tweaks=None, dash=0.0, pad=6):
    """SVG -> спрайт. ground — y земли в координатах SVG, anchor_x — x точки привязки.
    mirror=True: рисунок смотрит вправо, поэтому зеркалим, чтобы «по умолчанию» он смотрел влево."""
    vx, vy, vw, vh = doc.vb
    S = max(2, int(math.ceil(dpr)))
    wl = vw * scale + 2 * pad
    hl = (ground - vy) * scale + pad
    pm = QPixmap(int(math.ceil(wl * S)), int(math.ceil(hl * S)))
    pm.fill(Qt.GlobalColor.transparent)
    pm.setDevicePixelRatio(S)
    p = QPainter(pm)
    p.setRenderHint(QPainter.RenderHint.Antialiasing)
    p.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform)
    ax = (anchor_x - vx) * scale + pad
    if mirror:
        p.translate(wl, 0)
        p.scale(-1, 1)
        ax = wl - ax
    p.translate(pad, 0)
    p.scale(scale, scale)
    p.translate(-vx, -vy)
    doc.draw(p, tweaks, dash)
    p.end()
    return (pm, ax, (ground - vy) * scale)


def build_svg_vehicles(dpr):
    """Кадры пингвина (3) и снегохода (6) из ваших SVG."""
    pg, sm = SvgDoc(PENGUIN_SVG), SvgDoc(SNOWMOBILE_SVG)
    far = pg.find("M168 416")            # дальняя лапа
    near = pg.find("M214 418") + pg.find("M234 410")   # ближняя лапа и «пальцы»
    ps = 0.19
    penguin = [svg_sprite(pg, ps, 426, 215, dpr),
               svg_sprite(pg, ps, 426, 215, dpr, tweaks={i: (0, -12) for i in far}),
               svg_sprite(pg, ps, 426, 215, dpr, tweaks={i: (0, -12) for i in near})]
    sled = [svg_sprite(sm, 0.31, 430, 626, dpr, dash=k * 1.7) for k in range(6)]
    return penguin, sled



# ================================================================ гирлянды: стили лампочек
_LV = (0.0, 0.3, 0.55, 0.8, 1.0)


def _mixc(a, b, t):
    return QColor(int(a.red() + (b.red() - a.red()) * t), int(a.green() + (b.green() - a.green()) * t),
                  int(a.blue() + (b.blue() - a.blue()) * t))


def _bulb_tones(col, b):
    dim = QColor(int(col.red() * .3 + 46), int(col.green() * .3 + 48), int(col.blue() * .3 + 56))
    lit = QColor(min(255, int(col.red() * .8 + 55)), min(255, int(col.green() * .8 + 55)), min(255, int(col.blue() * .8 + 55)))
    return dim, lit, _mixc(dim, lit, b)


def _glow(p, cx, cy, r, col, b, a=135, ry=None):
    if b <= 0:
        return
    g = QColor(col)
    g.setAlpha(int(a * b))
    p.setPen(Qt.PenStyle.NoPen)
    p.setBrush(rad(cx, cy, r, cx, cy, (0, g), (1, QColor(col.red(), col.green(), col.blue(), 0))))
    p.drawEllipse(QPointF(cx, cy), r, ry or r)


def bulb_globe(p, col, level, var=0):
    """Круглые матовые шарики."""
    b = _LV[level]
    dim, lit, mid = _bulb_tones(col, b)
    _glow(p, 16, 15, 14, col, b, 140)
    fr(p, 13, 0.5, 6, 5, 1.2, QColor(58, 98, 68))
    fc(p, 16, 14.6, 6.8, rad(16, 14.6, 7.2, 14, 12.2, (0, _mixc(mid, WH, 0.35 * b)), (1, mid)))
    fc(p, 13.7, 12.3, 1.8, al(WH, 80 + 130 * b))


def _star_poly(cx, cy, R, r, n=5, rot=-90.0):
    pts = []
    for i in range(n * 2):
        a = math.radians(rot + i * 180.0 / n)
        rr = R if i % 2 == 0 else r
        pts.append((cx + rr * math.cos(a), cy + rr * math.sin(a)))
    return poly(*pts)


def bulb_star(p, col, level, var=0):
    """Звёздочки."""
    b = _LV[level]
    dim, lit, mid = _bulb_tones(col, b)
    _glow(p, 18, 17, 15, col, b, 150)
    fr(p, 16, 0.5, 4, 4.6, 1, QColor(92, 80, 50))
    fl(p, _star_poly(18, 17, 8.8, 3.9), mid)
    fl(p, _star_poly(18, 17, 4.6, 2.0), al(WH, 60 + 150 * b))


def bulb_icicle(p, col, level, var=0):
    """Сосульки разной длины."""
    b = _LV[level]
    dim, lit, mid = _bulb_tones(col, b)
    L = (12, 20, 28)[var % 3]
    _glow(p, 16, 5 + L / 2.0, 10, col, b, 120, ry=L / 2.0 + 7)
    fr(p, 13.5, 0.5, 5, 4, 1, QColor(150, 160, 178))
    drop = spline([(13, 4.5), (19, 4.5), (18.2, 5 + L * 0.55), (16, 5 + L), (13.8, 5 + L * 0.55)], True, 0.8)
    fl(p, drop, lin(0, 5, 0, 5 + L, (0, _mixc(mid, WH, 0.3 * b)), (1, mid)))
    p.setPen(mkpen(1.1, WH, 90 + 140 * b))
    p.drawLine(QPointF(14.7, 7), QPointF(14.9, 4 + L * 0.6))


GARLAND_STYLES = {
    "fairy": dict(name="Огоньки", gap=20, wire=(1.1, (30, 34, 44, 200)), size=(32, 40), attach=(16, 8),
                  pal=[(255, 226, 170), (255, 184, 96), (168, 208, 255), (255, 168, 188), (170, 232, 200)],
                  draw=lambda p, c, l, v=0: bulb_sprite(p, c, l)),
    "globe": dict(name="Шарики", gap=24, wire=(1.6, (30, 70, 56, 225)), size=(32, 40), attach=(16, 3),
                  pal=[(255, 110, 110), (255, 200, 90), (120, 210, 140), (110, 170, 255), (200, 140, 255)], draw=bulb_globe),
    "star": dict(name="Звёздочки", gap=30, wire=(1.2, (130, 108, 56, 225)), size=(36, 44), attach=(18, 3),
                 pal=[(255, 215, 90), (255, 250, 240), (255, 170, 200), (140, 210, 255), (190, 255, 200)], draw=bulb_star),
    "icicle": dict(name="Сосульки", gap=15, wire=(1.6, (196, 210, 228, 235)), size=(32, 48), attach=(16, 3),
                   pal=[(235, 246, 255), (170, 214, 255), (200, 240, 250), (214, 200, 255), (255, 230, 240)], draw=bulb_icicle),
}
GARLAND_ORDER = ["fairy", "globe", "star", "icicle"]


# ================================================================ наряды снеговика
OUTFITS = {
    "classic": dict(name="Классика", hat="top", hat_c=(30, 30, 40), band=(220, 50, 64),
                    scarf=((222, 54, 66), (255, 255, 255)), glasses=None, buttons=(26, 26, 34)),
    "winter": dict(name="Зимний", hat="beanie", hat_c=(46, 164, 168), scarf=((46, 164, 168), (255, 255, 255)),
                   glasses=None, buttons=(30, 60, 70)),
    "santa": dict(name="Дед Мороз", hat="santa", hat_c=(214, 40, 52), scarf=((250, 250, 250), (214, 40, 52)),
                  glasses=None, buttons=(214, 40, 52)),
    "cool": dict(name="Модник", hat="cap", hat_c=(60, 110, 220), scarf=((250, 200, 60), (250, 250, 250)),
                 glasses=(28, 28, 38), buttons=(60, 110, 220)),
    "royal": dict(name="Король", hat="crown", hat_c=(250, 200, 60), scarf=((124, 62, 172), (250, 224, 130)),
                  glasses=None, buttons=(250, 200, 60)),
    "ski": dict(name="Лыжник", hat="earmuffs", hat_c=(230, 60, 80), scarf=((230, 60, 80), (250, 250, 250)),
                glasses=(80, 170, 240), buttons=(230, 60, 80)),
    "party": dict(name="Праздничный", hat="party", hat_c=(250, 120, 170), scarf=((250, 120, 170), (255, 232, 110)),
                  glasses=None, buttons=(255, 200, 70)),
    "plain": dict(name="Без наряда", hat="none", hat_c=(0, 0, 0), scarf=None, glasses=None, buttons=(26, 26, 34)),
}
OUTFIT_ORDER = ["classic", "winter", "santa", "cool", "royal", "ski", "party", "plain"]


def _qc(t, a=255):
    return QColor(t[0], t[1], t[2], a)


def part_hat(p, s, o=None):
    """Шляпа по наряду. (0,0) — центр основания на макушке, растёт вверх."""
    o = o or OUTFITS["classic"]
    kind, c = o["hat"], _qc(o["hat_c"])
    cl = QColor(min(255, c.red() + 40), min(255, c.green() + 40), min(255, c.blue() + 40))
    if kind == "top":
        rrect(p, -8.5 * s, -1.6 * s, 17 * s, 3.2 * s, 1.5 * s, lin(0, -2 * s, 0, 2 * s, (0, cl), (1, c)), 1.6)
        rrect(p, -5.2 * s, -13.5 * s, 10.4 * s, 12.4 * s, 1.6 * s, lin(-5 * s, 0, 5 * s, 0, (0, cl), (1, c)), 1.6)
        rrect(p, -5.3 * s, -4.6 * s, 10.6 * s, 2.8 * s, 0.8 * s, _qc(o.get("band", (220, 50, 64))), 1.2)
        line(p, -3.4 * s, -12 * s, -3.4 * s, -6 * s, 1.0, QColor(255, 255, 255), 90)
    elif kind == "beanie":
        dome = QPainterPath()
        dome.moveTo(-7.8 * s, 0)
        dome.cubicTo(-8.4 * s, -11.5 * s, 8.4 * s, -11.5 * s, 7.8 * s, 0)
        dome.closeSubpath()
        shape(p, dome, lin(0, -9 * s, 0, 0, (0, cl), (1, c)), 1.6)
        for k in (-3.4, 0.0, 3.4):
            line(p, k * s, -9 * s, k * s * 1.05, -3.6 * s, 1.0, QColor(255, 255, 255), 110)
        rrect(p, -8.6 * s, -3.6 * s, 17.2 * s, 4.0 * s, 1.8 * s, _mixc(c, WH, 0.35), 1.6)
        circle(p, 0, -11.4 * s, 2.9 * s, rad(0, -11.4 * s, 3 * s, -0.8 * s, -12.2 * s, (0, SNOW_W), (1, SNOW_B)), 1.4)
    elif kind == "santa":
        cone = QPainterPath()
        cone.moveTo(-7.8 * s, 0)
        cone.cubicTo(-7 * s, -9 * s, 0, -13 * s, 8.5 * s, -9 * s)
        cone.cubicTo(6.8 * s, -5 * s, 7.4 * s, -2 * s, 7.8 * s, 0)
        cone.closeSubpath()
        shape(p, cone, lin(0, -12 * s, 0, 0, (0, cl), (1, c)), 1.6)
        circle(p, 8.8 * s, -8.6 * s, 2.7 * s, rad(8.8 * s, -8.6 * s, 3 * s, 8 * s, -9.4 * s, (0, SNOW_W), (1, SNOW_B)), 1.4)
        rrect(p, -8.8 * s, -3.2 * s, 17.6 * s, 4.2 * s, 2.0 * s, rad(0, 0, 10 * s, -2 * s, -3 * s, (0, SNOW_W), (1, SNOW_B)), 1.6)
    elif kind == "cap":
        dome = QPainterPath()
        dome.moveTo(-7.6 * s, 0)
        dome.cubicTo(-8 * s, -9.4 * s, 8 * s, -9.4 * s, 7.6 * s, 0)
        dome.closeSubpath()
        shape(p, dome, lin(0, -8 * s, 0, 0, (0, cl), (1, c)), 1.6)
        shape(p, spline([(-6 * s, -0.6 * s), (-13.6 * s, 1.4 * s), (-13 * s, 3 * s), (-5 * s, 1.6 * s)], True, 0.7), c, 1.5)
        circle(p, 0, -8.4 * s, 1.1 * s, cl, 1.0)
    elif kind == "crown":
        pts = [(-7.4, 0), (-8.2, -8.2), (-4.2, -4.2), (0, -10.4), (4.2, -4.2), (8.2, -8.2), (7.4, 0)]
        shape(p, poly(*[(x * s, y * s) for x, y in pts]), lin(0, -10 * s, 0, 0, (0, QColor(255, 230, 120)), (1, c)), 1.6)
        for (x, y, col) in ((0, -2.6, (220, 50, 64)), (-4.2, -2.6, (60, 130, 240)), (4.2, -2.6, (60, 190, 110))):
            circle(p, x * s, y * s, 1.1 * s, _qc(col), 0.8)
    elif kind == "party":
        cone = poly((-5.6 * s, 0), (5.6 * s, 0), (0.6 * s, -15 * s))
        shape(p, cone, lin(0, -15 * s, 0, 0, (0, cl), (1, c)), 1.6)
        for k in range(3):
            circle(p, (-2.2 + k * 2.2) * s, (-3.6 - k * 3.2) * s, 0.9 * s, _qc((255, 235, 110)), 0)
        circle(p, 0.6 * s, -15.4 * s, 2.0 * s, _qc((255, 235, 110)), 1.2)


def part_scarf_wrap(p, r, s, cols=None):
    cols = cols or ((222, 54, 66), (255, 255, 255))
    w = r * 1.55
    c1, c2 = _qc(cols[0]), _qc(cols[1])
    shape(p, spline([(-w, -2.6 * s), (-w * .4, 1.8 * s), (w * .4, 1.8 * s), (w, -2.6 * s), (w * .9, 3.2 * s),
                     (w * .4, 5.8 * s), (-w * .4, 5.8 * s), (-w * .9, 3.2 * s)], True, 0.8),
          lin(0, -2 * s, 0, 6 * s, (0, _mixc(c1, WH, 0.15)), (1, _mixc(c1, QColor(0, 0, 0), 0.18))), 1.7)
    for k in range(5):
        x = -w * .72 + k * w * .36
        line(p, x, 2.6 * s, x, 5.2 * s, 1.5, c2, 225)


def part_scarf_tail(p, s, flutter=0.0, cols=None):
    cols = cols or ((222, 54, 66), (255, 255, 255))
    path = QPainterPath()
    path.moveTo(0, 0)
    path.cubicTo(5 * s + flutter, 6 * s, 3 * s + flutter * 1.6, 12 * s, 7 * s + flutter * 2, 18 * s)
    p.setBrush(Qt.BrushStyle.NoBrush)
    p.setPen(mkpen(7 * s * .7 + 1.2))
    p.drawPath(path)
    p.setPen(mkpen(5 * s * .7 + .6, _qc(cols[0])))
    p.drawPath(path)
    p.setPen(mkpen(1.4, _qc(cols[1]), 225))
    p.drawLine(QPointF(4 * s + flutter, 6 * s), QPointF(8 * s + flutter, 6.6 * s))
    p.drawLine(QPointF(4 * s + flutter * 1.5, 11 * s), QPointF(8 * s + flutter * 1.5, 11.6 * s))


def part_glasses(p, r, col):
    """Очки поверх глаз (центр головы в (0,0))."""
    c = _qc(col)
    y = -r * 0.3
    for ex in (-.34, .3):
        p.setPen(mkpen(1.3))
        p.setBrush(lin(0, y - r * .25, 0, y + r * .25, (0, _mixc(c, WH, 0.25)), (1, c)))
        p.drawEllipse(QPointF(r * ex, y), r * .28, r * .24)
    line(p, -r * .06, y, r * .02, y, 1.4, INK)
    line(p, -r * .62, y, -r * .86, y - r * .05, 1.3, INK)
    line(p, r * .58, y, r * .84, y - r * .05, 1.3, INK)


def part_earmuffs(p, r, col):
    c = _qc(col)
    path = QPainterPath()
    for i in range(0, 21):
        a = math.radians(200 + 140 * i / 20.0)
        x, y = r * 1.0 * math.cos(a), r * 1.02 * math.sin(a)
        if i == 0:
            path.moveTo(x, y)
        else:
            path.lineTo(x, y)
    stroke(p, path, 2.6, INK)
    stroke(p, path, 1.4, c)
    for sx in (-1, 1):
        circle(p, sx * r * 0.98, -r * 0.1, r * 0.3, rad(sx * r, -r * .15, r * .35, sx * r * .9, -r * .22, (0, _mixc(c, WH, .35)), (1, c)), 1.4)


def part_nose(p, s):
    shape(p, poly((0, -1.4 * s), (-9 * s, 0.8 * s), (0, 1.9 * s)),
          lin(0, -1.5 * s, 0, 2 * s, (0, QColor(255, 170, 60)), (1, QColor(232, 102, 20))), 1.3)
    line(p, -2 * s, 0.1 * s, -6 * s, 0.7 * s, 0.9, QColor(150, 60, 10), 150)


def draw_snowman(p, balls, done, flutter=0.0, hide=(), outfit="classic"):
    """Снеговик с нарядом, основание (0,0). hide — не рисуемые детали (для разлёта)."""
    o = OUTFITS.get(outfit, OUTFITS["classic"])
    cys = snowman_geometry(balls)
    for r, cy in zip(balls, cys):
        if 'ball' not in hide:
            draw_ball(p, 0, cy, r)
    if not (done and len(balls) == 3):
        return
    r1, r2, r3 = balls
    c1, c2, c3 = cys
    s = r3 / 9.0
    if 'buttons' not in hide:
        for k in range(3):
            p.save()
            p.translate(-r2 * .06, c2 - r2 * .45 + k * r2 * .45)
            circle(p, 0, 0, 1.8 * (r2 / 9.0 * 1.2), rad(0, 0, 3, -.8, -.8, (0, _mixc(_qc(o["buttons"]), WH, .35)), (1, _qc(o["buttons"]))), 1.0)
            p.restore()
    if 'arms' not in hide:
        p.save()
        p.translate(r2 * .86, c2 - r2 * .1)
        p.rotate(-22)
        part_arm(p, r2 / 11.0, 1)
        p.restore()
        p.save()
        p.translate(-r2 * .86, c2 - r2 * .05)
        p.rotate(26)
        part_arm(p, r2 / 11.0, -1)
        p.restore()
    if o["scarf"] and 'scarf' not in hide:
        p.save()
        p.translate(0, c3 + r3 * .84)
        part_scarf_wrap(p, r3, s, o["scarf"])
        p.translate(r3 * .56, 2.4 * s)
        part_scarf_tail(p, s, flutter, o["scarf"])
        p.restore()
    if 'face' not in hide:
        for ex in (-.34, .3):
            p.save()
            p.translate(r3 * ex, c3 - r3 * .3)
            part_coal(p, s * 1.0)
            p.restore()
        for k in range(5):
            a = math.radians(-60 + k * 30)
            p.save()
            p.translate(-r3 * .04 + r3 * .46 * math.sin(a) / .87, c3 + r3 * (0.50 - 0.26 * (1 - math.cos(a))))
            part_coal(p, s * .62)
            p.restore()
        p.save()
        p.translate(-r3 * .04, c3 + r3 * .04)
        p.rotate(6)
        part_nose(p, s * 1.15)
        p.restore()
        if o["glasses"]:
            p.save()
            p.translate(0, c3)
            part_glasses(p, r3, o["glasses"])
            p.restore()
    if o["hat"] == "earmuffs" and 'hat' not in hide:
        p.save()
        p.translate(0, c3)
        part_earmuffs(p, r3, o["hat_c"])
        p.restore()
    elif o["hat"] not in ("none", "earmuffs") and 'hat' not in hide:
        p.save()
        p.translate(r3 * .04, c3 - r3 * .86)
        p.rotate(-6)
        part_hat(p, s * 1.0, o)
        p.restore()


def snowman_extent(balls, done=True, outfit="classic"):
    cys = snowman_geometry(balls)
    top = cys[-1] - balls[-1]
    if done and len(balls) == 3:
        top -= balls[-1] * (0.35 if OUTFITS.get(outfit, OUTFITS["classic"])["hat"] in ("none", "earmuffs") else 1.75)
    return -top, max(balls)


# ================================================================ ёлка
TREE_TIERS = [(-12, 50, -66), (-46, 41, -106), (-82, 31, -140)]    # (низ, полуширина, вершина)
TREE_H = 150.0
TREE_W = 54.0
ORN_COLORS = {"red": (224, 48, 60), "gold": (244, 190, 50), "blue": (64, 120, 230), "silver": (204, 212, 226),
              "green": (60, 170, 100), "purple": (150, 90, 210), "pink": (240, 130, 180), "white": (250, 252, 255)}
ORN_PALETTE = [("ball", "red"), ("ball", "gold"), ("ball", "blue"), ("ball", "silver"), ("ball", "green"),
               ("ball", "purple"), ("ball", "pink"), ("star", "gold"), ("star", "silver"), ("candy", "red"),
               ("bow", "red"), ("bow", "gold"), ("bell", "gold"), ("snowflake", "white"), ("heart", "red")]
TOPPERS = ["star", "snowflake", "bow", "heart", "none"]
TOPPER_NAMES = {"star": "Звезда", "snowflake": "Снежинка", "bow": "Бант", "heart": "Сердце", "none": "Без верхушки"}
LIGHT_MODES = ["off", "warm", "cold", "multi", "white"]
LIGHT_NAMES = {"off": "Огни выкл", "warm": "Тёплые огни", "cold": "Холодные огни", "multi": "Разноцветные огни", "white": "Белые огни"}
LIGHT_COLS = {"warm": [(255, 214, 140)], "cold": [(170, 214, 255)], "white": [(255, 250, 240)],
              "multi": [(255, 90, 90), (255, 200, 70), (90, 220, 120), (100, 160, 255), (230, 120, 230)]}
TINSELS = [None, "gold", "silver", "red"]
TINSEL_COLS = {"gold": (244, 196, 70), "silver": (214, 222, 236), "red": (226, 70, 84)}
TINSEL_NAMES = {None: "Без мишуры", "gold": "Золотая мишура", "silver": "Серебряная мишура", "red": "Красная мишура"}

TREE_PRESETS = {
    "lights": dict(name="Только огни", pal=[], n=0, topper="none", lights=("warm", "static"), tinsel=None),
    "gold": dict(name="Золото", pal=[("ball", "gold", 1)], n=6, topper="star", lights=("off", "static"), tinsel=None),
    "red": dict(name="Красные шары", pal=[("ball", "red", 1)], n=7, topper="none", lights=("off", "static"), tinsel=None),
    "silver": dict(name="Серебро", pal=[("ball", "silver", 1)], n=7, topper="star", lights=("off", "static"), tinsel=None),
    "snow": dict(name="Снежинки", pal=[("snowflake", "white", 1)], n=5, topper="snowflake", lights=("cold", "twinkle"), tinsel=None),
    "candy": dict(name="Леденцы", pal=[("candy", "red", 1)], n=6, topper="bow", lights=("off", "static"), tinsel=None),
    "blue": dict(name="Синяя", pal=[("ball", "blue", 1)], n=7, topper="none", lights=("cold", "static"), tinsel=None),
    "pink": dict(name="Сердечки", pal=[("heart", "red", 1)], n=5, topper="heart", lights=("off", "static"), tinsel=None),
    "bells": dict(name="Колокольчики", pal=[("bell", "gold", 1)], n=5, topper="bow", lights=("off", "static"), tinsel=None),
    "glow": dict(name="Тёплое свечение", pal=[], n=0, topper="star", lights=("warm", "twinkle"), tinsel=None),
}
PRESET_ORDER = ["lights", "gold", "red", "silver", "snow", "candy", "blue", "pink", "bells", "glow"]


def tree_hw(yl):
    """Полуширина ёлки на высоте yl над землёй (в пикселях, масштаб 1)."""
    best = 0.0
    for (yb, hw, ya) in TREE_TIERS:
        bot, top = -yb, -ya
        if bot - 4 <= yl <= top:
            best = max(best, hw * (top - yl) / float(top - bot))
    return best


def tree_inside(lx, ly):
    """Попадает ли точка (локальные координаты, y вверх отрицательный) на ёлку."""
    yl = -ly
    return 16 <= yl <= 134 and abs(lx) <= tree_hw(yl) - 4


class TreeData:
    """Состояние украшений ёлки (без привязки к месту)."""

    def __init__(self):
        self.orn = []                       # [тип, цвет, x, y]
        self.topper, self.tinsel = "star", None
        self.light_mode, self.light_anim = "off", "static"
        self.preset = None

    def apply_preset(self, key, seed=None):
        pr = TREE_PRESETS[key]
        rnd = random.Random(seed if seed is not None else random.random())
        self.preset, self.topper, self.tinsel = key, pr["topper"], pr["tinsel"]
        self.light_mode, self.light_anim = pr["lights"]
        self.orn = []
        if pr["pal"]:
            t, c, _w = pr["pal"][0]
            slots = [(100, -0.5), (76, 0.55), (52, -0.7), (52, 0.7), (100, 0.5), (76, -0.55),
                     (28, 0.0), (122, 0.0), (28, -0.8), (28, 0.8)]
            for (yl, fr_) in slots[:pr["n"]]:
                hw = max(tree_hw(yl) - 8, 0)
                self.orn.append([t, c, fr_ * hw, -yl])


def tree_light_points():
    pts = []
    for (yb, hw, ya) in TREE_TIERS:
        h = yb - ya
        for frac, sag in ((0.16, 6.0), (0.5, 5.0)):
            y0 = yb - h * frac
            for k in range(6):
                u = (k + 0.5) / 6.0
                yy = y0 + math.sin(u * math.pi) * sag - 4
                w = tree_hw(-yy) - 5
                pts.append((-w + 2 * w * u, yy))
    return pts


TREE_LIGHTS = tree_light_points()


def tree_body(p):
    """Хвойная часть: три яруса со снежными шапками и стволом."""
    soft_shadow(p, 0, 34)
    fr(p, -6, -14, 12, 14, 2, QColor(112, 78, 54))
    fr(p, -6, -14, 4.5, 14, 2, QColor(138, 98, 66))
    GM, GD, GL = QColor(52, 142, 92), QColor(34, 104, 70), QColor(86, 178, 122)
    for (yb, hw, ya) in TREE_TIERS:
        path = QPainterPath()
        path.moveTo(0, ya)
        path.lineTo(hw * 0.97, yb - 4)
        n = 4
        for i in range(n):
            x0 = hw * 0.97 - i * (2 * hw * 0.97 / n)
            x1 = x0 - 2 * hw * 0.97 / n
            path.quadTo((x0 + x1) / 2, yb + 6, x1, yb - 4)
        path.closeSubpath()
        fl(p, path, lin(-hw, 0, hw, 0, (0, GL), (0.5, GM), (1, GD)))
        # ветки-складки
        p.setPen(mkpen(1.1, GD, 150))
        for k in (-0.42, 0.0, 0.42):
            p.drawLine(QPointF(k * hw * 0.35, ya + (yb - ya) * 0.35), QPointF(k * hw * 0.9, yb - 7))
        # снежная кайма по нижнему краю
        snow = QPainterPath()
        snow.moveTo(hw * 0.97, yb - 4)
        for i in range(n):
            x0 = hw * 0.97 - i * (2 * hw * 0.97 / n)
            x1 = x0 - 2 * hw * 0.97 / n
            snow.quadTo((x0 + x1) / 2, yb + 6, x1, yb - 4)
        for i in range(n):
            x0 = -hw * 0.97 + i * (2 * hw * 0.97 / n)
            x1 = x0 + 2 * hw * 0.97 / n
            snow.quadTo((x0 + x1) / 2, yb + 1.6, x1, yb - 4)
        snow.closeSubpath()
        fl(p, snow, al(WH, 235))
    fl(p, poly((0, -141), (4.4, -122), (-4.4, -122)), al(WH, 235))


def tree_topper(p, kind):
    """Верхушка; (0,0) — вершина ёлки."""
    if kind == "star":
        fl(p, _star_poly(0, -8, 11.5, 5.0), lin(0, -20, 0, 4, (0, QColor(255, 240, 150)), (1, QColor(246, 184, 40))))
        fl(p, _star_poly(0, -8, 5.2, 2.4), al(WH, 170))
    elif kind == "snowflake":
        p.setPen(mkpen(2.0, QColor(214, 238, 255)))
        for k in range(3):
            a = math.radians(60 * k + 90)
            p.drawLine(QPointF(-10 * math.cos(a), -8 - 10 * math.sin(a)), QPointF(10 * math.cos(a), -8 + 10 * math.sin(a)))
        fc(p, 0, -8, 2.4, WH)
    elif kind == "bow":
        fl(p, spline([(0, -6), (-10, -13), (-12, -4), (-1, -4)], True, 0.8), QColor(226, 54, 70))
        fl(p, spline([(0, -6), (10, -13), (12, -4), (1, -4)], True, 0.8), QColor(226, 54, 70))
        fc(p, 0, -5.4, 2.8, QColor(176, 30, 50))
    elif kind == "heart":
        path = QPainterPath()
        path.moveTo(0, -3)
        path.cubicTo(-12, -12, -7, -22, 0, -15)
        path.cubicTo(7, -22, 12, -12, 0, -3)
        fl(p, path, QColor(230, 60, 90))
        fe(p, -3.4, -14, 2.2, 1.4, al(WH, 150))


def orn_sprite(p, kind, color):
    """Украшение; центр (0,0)."""
    c = _qc(ORN_COLORS.get(color, (224, 48, 60)))
    if kind == "ball":
        fr(p, -2, -9.4, 4, 3, 0.8, QColor(226, 196, 110))
        fc(p, 0, -1, 6.6, rad(0, -1, 7, -2.4, -3.4, (0, _mixc(c, WH, 0.55)), (0.55, c), (1, _mixc(c, QColor(0, 0, 0), 0.3))))
        fe(p, -2.6, -3.6, 1.7, 1.1, al(WH, 190))
    elif kind == "star":
        fl(p, _star_poly(0, 0, 7.4, 3.3), lin(0, -8, 0, 8, (0, _mixc(c, WH, 0.5)), (1, c)))
    elif kind == "candy":
        path = QPainterPath()
        path.moveTo(3, 9)
        path.lineTo(3, -4)
        path.cubicTo(3, -10, -4, -10, -4, -4)
        p.setBrush(Qt.BrushStyle.NoBrush)
        p.setPen(mkpen(3.6, QColor(250, 250, 252)))
        p.drawPath(path)
        pen = mkpen(3.6, QColor(224, 48, 60))
        pen.setDashPattern([0.9, 1.1])
        p.setPen(pen)
        p.drawPath(path)
    elif kind == "bow":
        fl(p, spline([(0, 0), (-8, -6), (-9, 3), (-1, 1.4)], True, 0.8), c)
        fl(p, spline([(0, 0), (8, -6), (9, 3), (1, 1.4)], True, 0.8), c)
        fc(p, 0, 0.4, 2.2, _mixc(c, QColor(0, 0, 0), 0.3))
        fl(p, poly((-1.4, 2), (-4.4, 9), (-0.4, 7)), _mixc(c, QColor(0, 0, 0), 0.15))
        fl(p, poly((1.4, 2), (4.4, 9), (0.4, 7)), _mixc(c, QColor(0, 0, 0), 0.15))
    elif kind == "bell":
        path = QPainterPath()
        path.moveTo(-6, 5)
        path.cubicTo(-6, -8, 6, -8, 6, 5)
        path.closeSubpath()
        fl(p, path, lin(-6, 0, 6, 0, (0, QColor(255, 226, 120)), (1, QColor(226, 164, 40))))
        fc(p, 0, 6.4, 1.7, QColor(176, 120, 30))
        fr(p, -7, 3.6, 14, 2.2, 1, QColor(236, 184, 60))
    elif kind == "snowflake":
        p.setPen(mkpen(1.5, QColor(240, 250, 255)))
        for k in range(3):
            a = math.radians(60 * k + 90)
            p.drawLine(QPointF(-7 * math.cos(a), -7 * math.sin(a)), QPointF(7 * math.cos(a), 7 * math.sin(a)))
        fc(p, 0, 0, 1.6, WH)
    elif kind == "heart":
        path = QPainterPath()
        path.moveTo(0, 6)
        path.cubicTo(-10, -1, -6, -9, 0, -3.6)
        path.cubicTo(6, -9, 10, -1, 0, 6)
        fl(p, path, c)
        fe(p, -2.6, -3, 1.6, 1.0, al(WH, 160))


def tree_light(p, col, level):
    """Огонёк на ёлке; центр (0,0)."""
    b = _LV[level]
    dim, lit, mid = _bulb_tones(col, b)
    _glow(p, 0, 0, 8.5, col, b, 160)
    fc(p, 0, 0, 2.5, mid)
    fc(p, -0.7, -0.8, 0.8, al(WH, 90 + 140 * b))


def light_level(anim, i, t):
    if anim == "static":
        return 4
    if anim == "blink":
        return 4 if (int(t * 1.6) + i) % 2 == 0 else 1
    if anim == "wave":
        return max(1, min(4, int(1.5 + 3.0 * (0.5 + 0.5 * math.sin(t * 4 - i * 0.7)))))
    return 1 + (((i * 2654435761) + int(t * 4) * 40503) >> 5) % 4


class TreeSprites:
    """Заранее отрисованные детали ёлки."""

    def __init__(self, S):
        self.S = S
        self.body = make_pm(150, 170, tree_body, S, 75, 160)
        self.topper = {k: make_pm(44, 44, lambda p, k=k: tree_topper(p, k), S, 22, 34) for k in TOPPERS if k != "none"}
        self.orn, self.light = {}, {}

    def orn_sp(self, kind, color):
        k = (kind, color)
        if k not in self.orn:
            self.orn[k] = make_pm(26, 28, lambda p: orn_sprite(p, kind, color), self.S, 13, 14)
        return self.orn[k]

    def light_sp(self, rgb, lv):
        k = (rgb, lv)
        if k not in self.light:
            self.light[k] = make_pm(24, 24, lambda p: tree_light(p, QColor(rgb[0], rgb[1], rgb[2]), lv), self.S, 12, 12)
        return self.light[k]


def draw_tree(p, td, t, ts, blit):
    """Рисует ёлку, основание (0,0). td — TreeData, ts — TreeSprites."""
    blit(p, ts.body, 0, 0)
    if td.tinsel:
        col = _qc(TINSEL_COLS[td.tinsel])
        for (yb, hw, ya) in TREE_TIERS:
            y0 = yb - (yb - ya) * 0.3
            w = tree_hw(-y0) - 3
            path = QPainterPath()
            path.moveTo(-w, y0 - 2)
            path.quadTo(0, y0 + 13, w, y0 - 2)
            stroke(p, path, 3.2, col)
            p.setPen(Qt.PenStyle.NoPen)
            p.setBrush(al(WH, 170))
            for k in range(7):
                u = (k + 0.5) / 7.0
                x = -w + 2 * w * u
                y = (y0 - 2) * (1 - u) ** 2 + 2 * (y0 + 13) * u * (1 - u) + (y0 - 2) * u * u
                p.drawEllipse(QPointF(x, y - 0.6), 0.9, 0.9)
    for o in td.orn:
        blit(p, ts.orn_sp(o[0], o[1]), o[2], o[3])
    if td.light_mode != "off":
        cols = LIGHT_COLS[td.light_mode]
        for i, (x, y) in enumerate(TREE_LIGHTS):
            blit(p, ts.light_sp(cols[i % len(cols)], light_level(td.light_anim, i, t)), x, y)
    if td.topper != "none":
        blit(p, ts.topper[td.topper], 0, -139)


# =================================================================== объекты
class Sprites:
    """Заранее отрисованные спрайты (быстро рисуются каждый кадр)."""

    def __init__(self, S, dpr):
        mk = lambda w, h, fn, ox, oy: make_pm(w, h, fn, S, ox, oy)
        self.blade = mk(40, 50, lambda p: plow_blade(p, 0, 0), 30, 46)
        self.blade_s = mk(40, 50, lambda p: plow_blade(p, 0, 0, 0.9), 30, 46)
        self.tractor = mk(160, 100, tractor_body, 100, 90)
        self.loader = mk(160, 100, tractor_loader, 100, 90)
        self.wheel_big = mk(48, 48, lambda p: wheel_sprite(p, 17), 24, 24)
        self.wheel_small = mk(36, 36, lambda p: wheel_sprite(p, 11.5), 18, 18)
        self.sled = mk(140, 90, snowmobile_body, 92, 84)
        self.rider = mk(60, 90, snowmobile_rider, 14, 84)
        self.peng = [pix_to_sprite(*penguin_pix(i), dpr) for i in range(4)]
        self.heart = pix_to_sprite(*heart_pix(), dpr)
        self.zzz = pix_to_sprite(*zzz_pix(), dpr)
        self.emotes = {k: pix_to_sprite(*emote_pix(k), dpr) for k in ("!", "?")}
        try:                                      # ваши SVG: пингвин (3 кадра) и снегоход (6 кадров)
            self.peng_svg, self.sled_svg = build_svg_vehicles(dpr)
        except Exception:
            self.peng_svg = self.sled_svg = None
        self.bulbs = {}
        for ci, col in enumerate(BULB_COLORS):
            for lv in range(5):
                pm = make_pm(32, 40, lambda p, c=col, l=lv: bulb_sprite(p, c, l), S, 0, 0)
                self.bulbs[(ci, lv)] = (pm[0], 16, 8)
        self.mitten = mitten_cursor_pm()
        self.tree = TreeSprites(S)


def blit(p, spr, x, y):
    pm, ox, oy = spr
    p.drawPixmap(QPointF(x - ox, y - oy), pm)


class Heap:
    __slots__ = ("h", "ver", "poly", "pver", "pt")

    def __init__(self, n):
        self.h = [0.0] * n
        self.ver = 0
        self.poly = None
        self.pver = -1
        self.pt = 0.0


class Surface:
    __slots__ = ("key", "l", "r", "top", "bottom", "cap", "vis", "hp", "h", "above", "clip", "exe")

    def __init__(self, key, l, r, top, bottom, cap, vis, hp, above, clip, exe):
        self.key, self.l, self.r, self.top, self.bottom = key, l, r, top, bottom
        self.cap, self.vis, self.hp, self.h, self.above = cap, vis, hp, hp.h, above
        self.clip, self.exe = clip, exe


class Figure:
    """Снежный шар(ы) / снеговик. Стоит на поверхности (key, rx) или падает (fall)."""
    _n = 0

    def __init__(self, balls, done=False, key=None, rx=0.0, fall=None):
        Figure._n += 1
        self.id = Figure._n
        self.balls = sorted(balls, reverse=True)
        self.done = bool(done and len(self.balls) == 3)
        self.key, self.rx, self.fall = key, rx, fall
        self.wob, self.wv = 0.0, 0.0
        self.pos = None          # (x, y основания) на экране
        self.vis = True
        self.clicks = []
        self.kind = "snowman"    # snowman | tree
        self.outfit = "classic"

    def kick(self, a):
        self.wv += a

    def step(self, dt):
        self.wob += self.wv * dt
        self.wv += (-self.wob * 0.16 - self.wv * 0.10) * dt


class Tree(Figure):
    """Ёлка: стоит на поверхности, как снеговик; украшения лежат в td (TreeData)."""

    def __init__(self, key=None, rx=0.0):
        super().__init__([], True, key, rx)
        self.kind = "tree"
        self.td = TreeData()


class Cat:
    """Котик: гуляет по поверхностям, прыгает, играет с курсором, иногда ломает снеговиков."""

    def __init__(self):
        self.key, self.rx, self.fall, self.jump = None, 0.0, None, None
        self.pos, self.vis, self.dir = None, True, -1      # dir -1 = смотрит влево (как спрайт)
        self.state, self.t, self.dur = "sit", 0.0, 60.0
        self.tx, self.step, self.blink = 0.0, 0.0, 0.0
        self.victim, self.next_break, self.pet_t = None, 0.0, 0.0
        self.hearts = []
        self.emote = None            # [символ, оставшиеся кадры]
        self.climb, self.climb_plan = None, None
        self.cflake = None           # снежинка, которую хочет поймать
        self.px0, self.pdest = 0.0, None


class HitWin(QWidget):
    """Крошечное почти невидимое окно-«кнопка» над котиком/снеговиком (ловит клики)."""

    def __init__(self, cb, kind):
        super().__init__()
        self.cb, self.kind, self.last = cb, kind, None
        self.setWindowFlags(Qt.WindowType.FramelessWindowHint | Qt.WindowType.WindowStaysOnTopHint
                            | Qt.WindowType.Tool | Qt.WindowType.WindowDoesNotAcceptFocus)
        self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground)
        self.setAttribute(Qt.WidgetAttribute.WA_ShowWithoutActivating)
        if IS_MAC:
            self.setAttribute(Qt.WidgetAttribute.WA_MacAlwaysShowToolWindow)
        self.setCursor(Qt.CursorShape.PointingHandCursor)

    def paintEvent(self, _ev):
        p = QPainter(self)
        p.fillRect(self.rect(), QColor(0, 0, 0, 3))      # почти невидимо, но «ловит» мышь
        p.end()

    def mousePressEvent(self, e):
        if e.button() == Qt.MouseButton.LeftButton:
            self.cb(self.kind, "L")
        elif e.button() == Qt.MouseButton.RightButton:
            self.cb(self.kind, "R")

    def mouseDoubleClickEvent(self, e):
        self.mousePressEvent(e)


# ==================================================================== оверлей
class Overlay(QWidget):
    def __init__(self, cfg):
        super().__init__()
        self.cfg = cfg
        self.setWindowFlags(Qt.WindowType.FramelessWindowHint
                            | Qt.WindowType.WindowStaysOnTopHint
                            | Qt.WindowType.Tool
                            | Qt.WindowType.WindowDoesNotAcceptFocus)
        self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground)
        self.setAttribute(Qt.WidgetAttribute.WA_ShowWithoutActivating)
        if IS_MAC:
            self.setAttribute(Qt.WidgetAttribute.WA_MacAlwaysShowToolWindow)
        scr = QApplication.primaryScreen()
        g = scr.geometry()
        self.dpr = scr.devicePixelRatio()
        self.W, self.H = g.width(), g.height() - 1
        self.origin = (g.x(), g.y())
        self.setGeometry(g.x(), g.y(), self.W, self.H)

        self.sps = max(2, int(math.ceil(self.dpr)))
        self.sp = Sprites(self.sps, self.dpr)
        self.flakes = []                 # [x,y,vx,vy,r,ph,mass,kind]  kind 1 = кусок снега (падает быстро)
        self.snow = {}                   # key -> Heap
        self.gm = {}                     # key -> (l, top) последняя геометрия окна
        self.missing = {}
        self.surfaces, self.smap = [], {}
        self.wins, self.wins_all = [], []
        self.raw, self.alive = [], set()
        self.temp_rules = {}
        self.spawn_acc, self.gx, self.prefill, self.dt_s = 0.0, random.random(), None, 1.0
        self.panel_hwnd = 0
        self.boost_until = 0.0
        self.interval = 0
        self.exe_cache = {}
        self.clip_cache = {}
        self.garl = {}
        self.flake_clip = None
        self.tb_top = self.H
        self.figures, self.debris = [], []
        self.cat, self.cat_cache, self.cur_speed = None, {}, 0.0
        self.hits = {}
        self.bulb_cache = {}
        self.sel = ("orn", "ball", "red")        # выбранное украшение в режиме «Наряжать»
        self.dec_tree = None
        self.pal_hover = None
        self.notice = ("", 0.0)
        self.ghost_td = None
        self.plow, self.plow_cooldown = None, 0.0
        self.mode = None                 # None / 'sculpt' / 'place'
        self.drag = None
        self.capture = False
        self.cur_shape = None
        self.cur = (0, 0)
        self.esc_prev = False
        self.mitten_on = False
        self.wind_cur = 0.0
        self.density = 1.0
        self.cost = 0.0
        self.paint_ms = 0.0
        self.paused = False
        self.enabled = True
        self.custom_pix = None
        self.t0 = self.last = time.time()
        self.last_refresh = 0.0
        self.last_adapt = 0.0
        self.mitten_path = os.path.join(os.environ.get("TEMP", "."), "snowfall_mitten.cur")
        if cfg.get("custom_path"):
            self.load_custom(cfg["custom_path"])

        self.show()
        self._nid = int(self.winId())
        self.hwnd = native_id(self._nid)
        set_overlay_style(self._nid, True)
        self.timer = QTimer(self)
        self.timer.setTimerType(Qt.TimerType.PreciseTimer)
        self.timer.timeout.connect(self.tick)
        self.timer.start(int(1000 / cfg["fps"]))
        self.watch = QTimer(self)
        self.watch.timeout.connect(self.check_fullscreen)
        self.watch.start(600)
        atexit.register(self.cleanup)

    # ---------------------------------------------------------- служебное
    def cleanup(self):
        if self.mitten_on:
            set_system_arrow(None)
            self.mitten_on = False

    def set_fps(self, fps):
        self.cfg["fps"] = fps
        self.timer.setInterval(int(1000 / fps))
        save_settings(self.cfg)

    def load_custom(self, path):
        pm = QPixmap(path)
        if not pm.isNull():
            self.custom_pix = pm.scaledToHeight(48, Qt.TransformationMode.SmoothTransformation)
            self.cfg["vehicle"] = "custom"
            self.cfg["custom_path"] = path

    def set_mitten(self, on):
        if on == self.mitten_on:
            return
        self.mitten_on = on
        if IS_MAC:
            # системный курсор на Mac не заменить, поэтому варежка видна, когда указатель над окнами Snowfall
            if on:
                self.setCursor(QCursor(self.sp.mitten, 6, 4))
            else:
                self.unsetCursor()
            return
        if on:
            try:
                make_cursor_file(self.sp.mitten, (6, 4), self.mitten_path)
                set_system_arrow(self.mitten_path)
            except Exception:
                pass
        else:
            set_system_arrow(None)

    def remembered(self, exe):
        return exe not in self.temp_rules

    def set_rule(self, exe, key, val):
        mem = self.remembered(exe)
        store = self.cfg["rules"] if mem else self.temp_rules
        r = store.setdefault(exe, {})
        if val:
            r.pop(key, None)
        else:
            r[key] = False
        if not r and mem:
            store.pop(exe, None)
        if mem:
            save_settings(self.cfg)
        self.last_refresh = 0.0

    def set_remember(self, exe, on):
        """Запомнить настройки программы (сохраняются на диск) или применять только до закрытия."""
        if on:
            r = self.temp_rules.pop(exe, None)
            if r:
                self.cfg["rules"][exe] = r
        else:
            self.temp_rules[exe] = self.cfg["rules"].pop(exe, {})
        save_settings(self.cfg)
        self.last_refresh = 0.0

    def forget_rules(self, exe):
        self.cfg["rules"].pop(exe, None)
        self.temp_rules.pop(exe, None)
        save_settings(self.cfg)
        self.last_refresh = 0.0

    def rule(self, exe, key):
        r = self.cfg["rules"].get(exe)
        if r is None:
            r = self.temp_rules.get(exe, {})
        return r.get(key, True)

    def set_capture(self, on):
        if on != self.capture:
            self.capture = on
            set_overlay_style(self._nid, not on)

    def set_mode(self, m):
        if self.drag:
            self.end_drag()
        if m == "decorate":
            trees = [f for f in self.figures if f.kind == "tree"]
            if self.dec_tree not in trees:
                self.dec_tree = trees[-1] if trees else None
            if self.dec_tree is None:
                self.notice = ("Сначала поставьте ёлку (кнопка «Поставить ёлку»)", time.time() + 4.0)
                m = None
        if m == "place_tree":
            self.ghost_td = TreeData()
            key = self.cfg.get("tree_preset", "gold")
            if key in TREE_PRESETS:
                self.ghost_td.apply_preset(key, seed=1)
        self.mode = m
        if m is None:
            self.cur_shape = None

    def check_fullscreen(self):
        want = self.cfg.get("pause_fs", True) and foreground_fullscreen(self.hwnd)
        if want and not self.paused:
            self.paused = True
            self.timer.stop()
            for hw in self.hits.values():
                hw.hide()
            self.hide()
        elif not want and self.paused:
            self.paused = False
            self.show()
            set_overlay_style(self._nid, not self.capture)
            self.last = time.time()
            self.timer.start(int(1000 / self.cfg["fps"]))

    # ---------------------------------------------------------- окна и поверхности
    def enum_windows(self):
        """Тяжёлый перебор окон (раз в ~0.2 с): список окон, их программы, панель задач."""
        self.raw = list_windows({self.hwnd})
        alive, allw = set(), []
        for item in self.raw:
            hwnd = item[0]
            alive.add(hwnd)
            exe = self.exe_cache.get(hwnd)
            if exe is None:
                exe = exe_of(hwnd)
                if not exe:                                   # защищённые процессы: правило по заголовку окна
                    exe = "окно: " + window_title(hwnd)[:40]
                self.exe_cache[hwnd] = exe
            allw.append((hwnd, exe))
        for k in list(self.exe_cache):
            if k not in alive:
                del self.exe_cache[k]
        self.wins_all, self.alive = allw, alive
        tt = taskbar_top()
        tb_top = self.H
        if tt is not None:
            tb_top = tt / self.dpr - self.origin[1]
            if tb_top < self.H * 0.6:
                tb_top = self.H
        self.tb_top = tb_top

    def reread_rects(self):
        """Лёгкое обновление каждый кадр: перечитать позиции уже известных окон."""
        changed = False
        new = []
        for item in self.raw:
            r = win_rect(item[0])
            if r != tuple(item[1:]):
                changed = True
            new.append((item[0],) + r)
        self.raw = new
        return changed

    def build_surfaces(self):
        d = self.dpr
        ox, oy = self.origin
        alive = self.alive
        wins = []
        for (hwnd, l, t, r, b) in self.raw:
            exe = self.exe_cache.get(hwnd, "")
            l, t, r, b = l / d - ox, t / d - oy, r / d - ox, b / d - oy
            if r - l < 120 or b - t < 40:
                continue
            if r - l >= self.W - 2 and b - t >= self.H - 2:
                continue
            wins.append((hwnd, l, t, r, b, exe))
        self.wins = wins
        tb_top = self.tb_top

        garland_on = self.cfg["garland"] != "off"
        surfs, seen, protected = [], set(), []
        over = self.cfg.get("flakes_over_windows", True)
        for i, (hwnd, l, t, r, b, exe) in enumerate(wins):
            is_panel = hwnd == self.panel_hwnd and not self.cfg.get("snow_on_panel", False)
            if is_panel or not over or not self.rule(exe, "flakes"):
                protected.append((l, t, r, b))
            if is_panel:
                continue                                      # на панели управления снега и гирлянд нет
            if t < 30:
                continue
            if not self.rule(exe, "drift"):
                continue
            above = [(w[1], w[2], w[3], w[4]) for w in wins[:i]]
            vis = [(l, r)]
            for (l2, t2, r2, b2) in above:
                if t2 <= t < b2:
                    vis = subtract(vis, l2, r2)
            n = max(2, int((r - l) / BIN) + 1)
            hp = self.snow.get(hwnd)
            if hp is None:
                hp = self.snow[hwnd] = Heap(n)
            elif len(hp.h) != n:
                hp.h[:] = (hp.h + [0.0] * n)[:n]
                hp.ver += 1
            seen.add(hwnd)
            self.gm[hwnd] = (l, t)
            clip = None
            if above:
                sig = tuple((int(a), int(b_), int(c), int(d_)) for a, b_, c, d_ in above)
                cc = self.clip_cache.get(hwnd)
                if cc and cc[0] == sig:
                    clip = cc[1]
                else:
                    clip = QRegion(0, 0, self.W, self.H)
                    for (l2, t2, r2, b2) in above:
                        clip = clip.subtracted(QRegion(QRect(int(l2), int(t2), int(r2 - l2), int(b2 - t2))))
                    self.clip_cache[hwnd] = (sig, clip)
            surfs.append(Surface(hwnd, l, r, t, b, CAP_WIN, vis, hp, above, clip, exe))
            # гирлянда
            if garland_on and self.rule(exe, "garland"):
                gsig = (int(r - l), int(min(b, self.H) - t), self.cfg.get("garland_style", "fairy"))
                g = self.garl.get(hwnd)
                if g is None or g["sig"] != gsig:
                    self.garl[hwnd] = self.build_garland(r - l, min(b, self.H) - t, gsig)
            else:
                self.garl.pop(hwnd, None)

        n = int(self.W / BIN) + 1
        hp = self.snow.get("tb")
        if hp is None:
            hp = self.snow["tb"] = Heap(n)
        vis = [(0, self.W)]
        for w in wins:
            if w[2] <= tb_top < w[4]:
                vis = subtract(vis, w[1], w[3])
        surfs.append(Surface("tb", 0, self.W, tb_top, self.H, CAP_TB, vis, hp, [], None, ""))
        seen.add("tb")

        # окно закрыли / свернули / отключили сугроб — снег осыпается вниз
        for k in list(self.snow):
            if k in seen:
                self.missing.pop(k, None)
                continue
            c = self.missing.get(k, 0) + 1
            self.missing[k] = c
            gone_rule = k in alive and k not in seen
            if c >= 2 or gone_rule:
                self.release_heap(k)
                del self.snow[k]
                self.missing.pop(k, None)
        for k in list(self.garl):
            if k not in seen:
                del self.garl[k]
        for k in list(self.clip_cache):
            if k not in seen:
                del self.clip_cache[k]
        self.surfaces = surfs
        self.smap = {s.key: s for s in surfs}
        if protected:
            reg = QRegion(0, 0, self.W, self.H)
            for (l, t, r, b) in protected:
                reg = reg.subtracted(QRegion(QRect(int(l), int(t), int(r - l), int(b - t))))
            self.flake_clip = reg
        else:
            self.flake_clip = None

    def build_garland(self, w, hgt, sig):
        spec = GARLAND_STYLES[self.cfg.get("garland_style", "fairy")]
        gap = spec["gap"]
        n = max(1, int(round(w / 80.0)))
        span = w / n
        sag = min(14.0, span * 0.12)
        path = QPainterPath()
        bulbs, hooks = [], []
        idx = 0
        for i in range(n):
            x0, x1 = i * span, (i + 1) * span
            path.moveTo(x0, 0)
            path.quadTo((x0 + x1) / 2, 2 * sag, x1, 0)
            nb = max(2, int(span / gap))
            for k in range(nb):
                u = (k + 0.5) / nb
                bulbs.append((x0 + span * u, 4 * sag * u * (1 - u), idx))
                idx += 1
            hooks.append(x0)
        hooks.append(w)
        for sx, out in ((0.0, -5.0), (w, 5.0)):
            path.moveTo(sx, 0)
            path.lineTo(sx, hgt)
            yy = 16.0
            while yy < hgt - 8:
                path.moveTo(sx, yy)
                path.lineTo(sx + out, yy + 2)
                bulbs.append((sx + out, yy + 2, idx))
                idx += 1
                yy += gap * 1.3
        return {"sig": sig, "path": path, "bulbs": bulbs, "hooks": hooks}

    def bulb_sprite_for(self, style, i, lv):
        spec = GARLAND_STYLES[style]
        ci = i % 5
        var = (i // 5) % 3
        key = (style, ci, lv, var if style == "icicle" else 0)
        sp = self.bulb_cache.get(key)
        if sp is None:
            w, h = spec["size"]
            col = QColor(*spec["pal"][ci])
            pm = make_pm(w, h, lambda p, c=col, l=lv, v=var: spec["draw"](p, c, l, v), self.sps, 0, 0)
            sp = self.bulb_cache[key] = (pm[0], spec["attach"][0], spec["attach"][1])
        return sp

    def release_heap(self, key):
        """Сугроб потерял опору (окно закрыто) — кусками падает вниз."""
        hp, gm = self.snow.get(key), self.gm.pop(key, None)
        if not hp or not gm:
            return
        l, top = gm
        h = hp.h
        n = len(h)
        g = max(1, (n + 119) // 120)
        for i in range(0, n, g):
            m = sum(h[i:i + g])
            if m < 0.6:
                continue
            x = l + (i + g / 2.0) * BIN
            self.flakes.append([x, top - h[min(i, n - 1)] * 0.5, random.uniform(-0.7, 0.7),
                                random.uniform(-0.6, 0.2), min(5.5, 1.6 + math.sqrt(m) * 0.35),
                                0.0, m, 1])

    def tb_surface(self):
        return self.smap.get("tb")

    # ---------------------------------------------------------- главный шаг
    def tick(self):
        t_start = time.perf_counter()
        now = time.time()
        dt = min((now - self.last) * 30.0, 3.0)
        self.last = now
        self.dt_s = self.dt_s * 0.7 + dt * 0.3          # сглаживаем неровный темп кадров
        dt = self.dt_s
        moved = False
        if now - self.last_refresh > 0.2:
            self.last_refresh = now
            self.enum_windows()
            self.build_surfaces()
        elif self.raw and self.reread_rects():
            self.build_surfaces()           # окно двигают: сугроб следует за ним в этом же кадре
            moved = True
            self.boost_until = now + 0.5
        t = now - self.t0
        gust = 4.0 if self.cfg["intensity"] == "Метель" else 2.5
        self.wind_cur = self.cfg["wind_base"]
        if self.cfg["gusts"] or self.cfg["intensity"] == "Метель":
            self.wind_cur += math.sin(t * 0.35) * math.sin(t * 0.13 + 1) * gust
        self.spawn(dt)
        self.step_flakes(dt)
        self.poll_input(now, dt)
        if self.mitten_on:
            self.mitten(dt)
        self.step_plow(dt, now)
        self.update_figures(dt)
        self.update_cat(dt, now)
        self.update_hits()
        self.update_debris(dt)
        want = 16 if now < self.boost_until else int(1000 / self.cfg["fps"])
        if want != self.interval:
            self.interval = want
            self.timer.setInterval(want)
        if moved:
            self.repaint()                   # рисуем сразу, не ждём очереди событий
        else:
            self.update()
        # адаптивная нагрузка: если компьютер не тянет, снега становится меньше
        self.cost = self.cost * 0.9 + ((time.perf_counter() - t_start) * 1000 + self.paint_ms) * 0.1
        if now - self.last_adapt > 1.5:
            self.last_adapt = now
            budget = 1000.0 / self.cfg["fps"] * 0.5
            if self.cost > budget * 1.3:
                self.density = max(0.35, self.density * 0.88)
            elif self.cost < budget * 0.6:
                self.density = min(1.0, self.density * 1.06)

    def new_flake(self, y):
        """Новая снежинка: x равномерно «расплёскивается» (золотое сечение), чтобы снег шёл ровно, без сгустков."""
        fall = INTENSITY[self.cfg["intensity"]][1]
        self.gx = (self.gx + 0.6180339887) % 1.0
        r = random.uniform(0.6, 1.6)
        return [-100 + self.gx * (self.W + 200) + random.uniform(-5, 5), y, self.wind_cur,
                fall * (0.55 + r * 0.25), r, random.uniform(0, 6.28), SNOW_MASS, 0]

    def spawn(self, dt):
        """Снег идёт с постоянной скоростью и НИКОГДА не останавливается, что бы ни происходило на экране."""
        if not self.enabled:
            return
        target, fall = INTENSITY[self.cfg["intensity"]]
        target = target * self.density
        if self.prefill != self.cfg["intensity"]:          # старт или смена силы снега: сразу равномерно заполняем экран
            self.prefill = self.cfg["intensity"]
            live = [f for f in self.flakes if not f[7]]
            need = int(target) - len(live)
            for _ in range(max(0, need)):
                self.flakes.append(self.new_flake(random.uniform(-20, self.H)))
            if need < 0:
                random.shuffle(live)
                dead = set(id(f) for f in live[:-need])
                self.flakes = [f for f in self.flakes if id(f) not in dead]
        lifetime = (self.H + 40) / (fall * 0.825 * 30.0)    # секунд, пока снежинка пролетает экран сверху вниз
        self.spawn_acc += target / lifetime * dt / 30.0     # снежинок в секунду — всегда одно и то же
        n = int(self.spawn_acc)
        self.spawn_acc -= n
        if len(self.flakes) < target * 3 + 600:
            for _ in range(n):
                self.flakes.append(self.new_flake(-random.uniform(2, 14)))

    def step_flakes(self, dt):
        wind = self.wind_cur
        fall = INTENSITY[self.cfg["intensity"]][1]
        sway = {"Лёгкий снег": 0.22, "Ровный снег": 0.6}.get(self.cfg["intensity"], 1.0)
        surfs = self.surfaces
        min_top = min((s.top - s.cap - 2 for s in surfs), default=self.H + 99)
        H, W = self.H, self.W
        sin = math.sin
        alive = []
        app = alive.append
        for f in self.flakes:
            x, y, vx, vy, r, ph, mass, kind = f
            if kind:
                vy = min(vy + 0.55 * dt, 13.0)
                vx *= 0.995
            else:
                ph += 0.08 * dt
                vx += (wind + sin(ph) * sway - vx) * 0.08 * dt
                vy += (fall * (0.55 + r * 0.25) - vy) * 0.08 * dt
            nx, ny = x + vx * dt, y + vy * dt
            if ny >= min_top and mass > 0:
                landed = False
                for s in surfs:
                    if ny < s.top - s.cap - 2 or y > s.top + 12:
                        continue
                    if nx < s.l or nx >= s.r or not in_vis(s.vis, nx):
                        continue
                    h = s.h
                    c = min(int((nx - s.l) / BIN), len(h) - 1)
                    if ny >= s.top - h[c]:
                        landed = True
                        if h[c] < s.cap:
                            add_mass(h, c, mass, s.cap)
                            s.hp.ver += 1
                        break
                if landed:
                    continue
            if ny > H + 20 or nx < -150 or nx > W + 150:
                continue
            f[0], f[1], f[2], f[3], f[5] = nx, ny, vx, vy, ph
            app(f)
        self.flakes = alive

    def puff(self, x, y, n=8, spread=3.0):
        for _ in range(n):
            self.flakes.append([x, y, random.uniform(-spread, spread), -random.uniform(0.5, 3.5),
                                random.uniform(0.8, 1.6), random.uniform(0, 6.28), 0.0, 0])

    def mitten(self, dt):
        cx, cy = self.cur
        R = 28
        for s in self.surfaces:
            if not (s.top - s.cap - 20 <= cy <= s.top + 14):
                continue
            if not (s.l - R <= cx <= s.r + R):
                continue
            h = s.h
            c0 = max(0, int((cx - R - s.l) / BIN))
            c1 = min(len(h) - 1, int((cx + R - s.l) / BIN))
            got = 0.0
            for c in range(c0, c1 + 1):
                if h[c] > 0:
                    d = min(h[c], 3.0 * dt)
                    h[c] -= d
                    got += d
            if got > 0:
                s.hp.ver += 1
                if got > 2 and random.random() < 0.5:
                    self.puff(cx, cy, 1, 2.0)

    def clear_all(self):
        for hp in self.snow.values():
            for i in range(len(hp.h)):
                hp.h[i] = 0.0
            hp.ver += 1

    # ---------------------------------------------------------- снегоуборщик
    def start_plow(self):
        if self.plow:
            return
        d = random.choice((-1, 1))
        self.plow = {"x": self.W + 100 if d < 0 else -100, "dir": d, "dist": 0.0}

    def step_plow(self, dt, now):
        tb = self.tb_surface()
        if tb is None:
            return
        if (self.cfg["auto_plow"] and not self.plow and now > self.plow_cooldown
                and sum(tb.h) / len(tb.h) > AUTO_PLOW_MEAN):
            self.start_plow()
        pl = self.plow
        if not pl:
            return
        v = 5.2 * dt
        pl["x"] += pl["dir"] * v
        pl["dist"] += v
        front = pl["x"] + pl["dir"] * PLOW_FRONT.get(self.cfg["vehicle"], 60)
        a, b = min(pl["x"], front) - 6, max(pl["x"], front) + 6
        c0, c1 = max(0, int(a / BIN)), min(len(tb.h) - 1, int(b / BIN))
        cleared = 0.0
        for c in range(c0, c1 + 1):
            cleared += tb.h[c]
            tb.h[c] = 0.0
        if cleared > 0:
            tb.hp.ver += 1
            for _ in range(3):
                self.flakes.append([front, self.tb_top - 6, pl["dir"] * random.uniform(1.5, 4),
                                    -random.uniform(1, 4), random.uniform(0.8, 1.6),
                                    random.uniform(0, 6.28), 0.0, 0])
        for f in list(self.figures):
            if f.key == "tb" and f.pos and a <= f.pos[0] <= b:
                self.demolish(f, pl["dir"] * 3.0)
        if pl["x"] < -140 or pl["x"] > self.W + 140:
            self.plow = None
            self.plow_cooldown = now + 25

    # ---------------------------------------------------------- фигуры
    def col_of(self, s, x):
        return max(0, min(int((x - s.l) / BIN), len(s.h) - 1))

    def ground_at(self, key, x):
        s = self.smap.get(key) or self.smap.get("tb")
        if not s:
            return float(self.H)
        return s.top - s.h[self.col_of(s, x)]

    def tower_top(self, o):
        """Y верхушки неполной башни о."""
        cys = snowman_geometry(o.balls)
        return o.pos[1] + cys[-1] - o.balls[-1]

    def merge(self, tower, ball):
        tower.balls = sorted(tower.balls + ball.balls, reverse=True)
        if len(tower.balls) == 3:
            tower.done = True
            tower.outfit = self.cfg.get("snowman_outfit", "classic")
            tower.kick(14.0)
            if tower.pos:
                self.puff(tower.pos[0], tower.pos[1] - 40, 16, 3.5)
        else:
            tower.kick(7.0)
        if ball in self.figures:
            self.figures.remove(ball)

    def update_figures(self, dt):
        for f in list(self.figures):
            f.step(dt)
            if f.fall is None:
                s = self.smap.get(f.key)
                if s is None:
                    if f.key in self.snow or f.key == "tb":
                        f.vis = False
                    elif f.pos:
                        f.fall = [f.pos[0], f.pos[1], 0.0]
                        f.key = None
                    continue
                x = s.l + f.rx
                f.pos = (x, s.top - s.h[self.col_of(s, x)] + 2)
                f.vis = in_vis(s.vis, x) or s.key == "tb"
                continue
            x, y, vy = f.fall
            vy = min(vy + 0.6 * dt, 14.0)
            ny = y + vy * dt
            landed = False
            if len(f.balls) == 1 and not f.done:
                for o in self.figures:
                    if o is f or o.fall is not None or o.done or len(o.balls) >= 3 or not o.pos:
                        continue
                    top_y = self.tower_top(o)
                    if (abs(x - o.pos[0]) < max(o.balls[0], f.balls[0]) * 0.9
                            and ny >= top_y - 1 and y <= top_y + f.balls[0] * 2):
                        self.merge(o, f)
                        landed = True
                        break
                if landed:
                    continue
            for s in self.surfaces:
                if not (s.l <= x < s.r) or (s.key != "tb" and not in_vis(s.vis, x)):
                    continue
                ground = s.top - s.h[self.col_of(s, x)] + 2
                if y <= s.top + 12 and ny >= ground:
                    f.key, f.rx, f.fall = s.key, x - s.l, None
                    f.pos = (x, ground)
                    f.kick(9.0)
                    landed = True
                    break
            if landed:
                continue
            f.fall = [x, ny, vy]
            f.pos = (x, ny)
            if ny > self.H + 90:
                self.figures.remove(f)

    def drop_ball(self, r, x, y):
        """Игрок отпустил шар: ставим на башню или роняем на поверхность."""
        for o in self.figures:
            if o.fall is None and not o.done and len(o.balls) < 3 and o.pos:
                if abs(x - o.pos[0]) <= max(o.balls[0], r) and y < self.tower_top(o) + r * 1.2:
                    self.merge(o, Figure([r]))
                    return
        f = Figure([r])
        f.fall = [x, y + r, 0.0]
        f.pos = (x, y + r)
        self.figures.append(f)

    def snap(self, x, y):
        best = None
        for s in self.surfaces:
            if not (s.l <= x < s.r):
                continue
            if s.key != "tb" and not in_vis(s.vis, x):
                continue
            g = s.top - s.h[self.col_of(s, x)]
            if g >= y - 24 and (best is None or g < best[0]):
                best = (g, s)
        return best

    def place_snowman(self, x, y):
        b = self.snap(x, y)
        if not b:
            return False
        g, s = b
        f = Figure([17, 13, 10], True, s.key, x - s.l)
        f.outfit = self.cfg.get("snowman_outfit", "classic")
        f.pos = (x, g + 2)
        f.kick(11.0)
        self.figures.append(f)
        self.puff(x, g - 30, 10, 3.0)
        return True

    def new_tree(self, preset=None):
        t = Tree()
        key = preset if preset is not None else self.cfg.get("tree_preset", "gold")
        if key and key in TREE_PRESETS:
            t.td.apply_preset(key)
        return t

    def apply_tree_preset(self, key):
        """Готовый дизайн: для всех ёлок на экране и для новых."""
        self.cfg["tree_preset"] = key
        for f in self.figures:
            if f.kind == "tree":
                if key in TREE_PRESETS:
                    f.td.apply_preset(key)
                else:                                          # «без украшений»
                    f.td.orn, f.td.tinsel, f.td.light_mode, f.td.topper, f.td.preset = [], None, "off", "star", None
                f.kick(5.0)
        save_settings(self.cfg)

    def place_tree(self, x, y):
        b = self.snap(x, y)
        if not b:
            return False
        g, s = b
        t = self.new_tree()
        t.key, t.rx, t.pos = s.key, x - s.l, (x, g + 2)
        t.kick(6.0)
        self.figures.append(t)
        self.puff(x, g - 40, 12, 3.2)
        return True

    def fig_extent(self, f):
        """(высота, полуширина) фигуры для зоны клика."""
        if f.kind == "tree":
            return TREE_H, TREE_W
        return snowman_extent(f.balls, f.done, f.outfit)

    def fig_hit(self, f, x, y):
        if not f.pos or f.fall is not None or not f.vis:
            return False
        hgt, w = self.fig_extent(f)
        px, gy = f.pos
        return abs(x - px) <= w + 4 and gy - hgt - 4 <= y <= gy + 4

    def demolish(self, f, push=0.0):
        """Снеговик разваливается на части: слетают шарф и шляпа, шары рассыпаются в снег."""
        if f in self.figures:
            self.figures.remove(f)
        if not f.pos:
            return
        x, gy = f.pos
        key = f.key
        if f.kind == "tree":                                  # ёлка: украшения осыпаются
            for o in f.td.orn:
                self.debris.append(dict(kind="orn", x=x + o[2], y=gy + o[3], vx=random.uniform(-2.6, 2.6) + push,
                                        vy=-random.uniform(0.5, 4.5), ang=0.0, va=random.uniform(-5, 5), life=0.0,
                                        key=key, g=0.5, r=0.0, s=1.0, side=1, hits=0, orn=(o[0], o[1])))
            self.puff(x, gy - 60, 20, 4.0)
            return
        balls = f.balls
        cys = snowman_geometry(balls)

        def add(kind, px, py, **kw):
            d = dict(kind=kind, x=px, y=py, vx=random.uniform(-2.2, 2.2) + push, vy=-random.uniform(1.5, 6.5),
                     ang=random.uniform(-25, 25), va=random.uniform(-9, 9), life=0.0, key=key, g=0.55,
                     r=0.0, s=1.0, side=1, hits=0, outfit="classic")
            d.update(kw)
            self.debris.append(d)
        for r, cy in zip(balls, cys):
            add("ball", x, gy + cy, r=r, vy=-random.uniform(0.5, 4.0), va=random.uniform(-5, 5))
        if f.done:
            r1, r2, r3 = balls
            c1, c2, c3 = cys
            s = r3 / 9.0
            add("hat", x + r3 * .04, gy + c3 - r3 * .86, s=s, g=0.40, vy=-random.uniform(5, 8), outfit=f.outfit)
            add("scarf", x, gy + c3 + r3 * .84, s=s, r=r3, g=0.10, vy=-random.uniform(3, 5),
                vx=random.uniform(-3.2, 3.2) + push, va=random.uniform(-14, 14), outfit=f.outfit)
            add("nose", x - r3 * .04, gy + c3 + r3 * .04, s=s * 1.15, g=0.5)
            add("arm", x + r2 * .86, gy + c2 - r2 * .1, s=r2 / 11.0, side=1, vx=random.uniform(1, 4))
            add("arm", x - r2 * .86, gy + c2 - r2 * .05, s=r2 / 11.0, side=-1, vx=-random.uniform(1, 4))
            for ex in (-.34, .3):
                add("coal", x + r3 * ex, gy + c3 - r3 * .3, s=s)
            for k in range(3):
                add("coal", x - r2 * .06, gy + c2 - r2 * .45 + k * r2 * .45, s=r2 / 9.0 * 1.2)
        self.puff(x, gy - 20, 14, 4.0)

    def update_debris(self, dt):
        keep = []
        for d in self.debris:
            kind = d["kind"]
            d["vy"] = min(d["vy"] + d["g"] * dt, 2.4 if kind == "scarf" else 12.0)
            if kind == "scarf":
                d["vx"] *= 0.97
                d["vx"] += math.sin(d["life"] * 0.35) * 0.18 * dt
            d["x"] += d["vx"] * dt
            d["y"] += d["vy"] * dt
            d["ang"] += d["va"] * dt
            d["life"] += dt
            gy = self.ground_at(d["key"], d["x"])
            if d["y"] >= gy and d["vy"] > 0:
                if kind == "orn" and d["hits"] == 0:
                    self.puff(d["x"], gy - 3, 2, 1.6)
                if kind == "ball":
                    s = self.smap.get(d["key"]) or self.tb_surface()
                    if s:
                        m = math.pi * d["r"] ** 2 / BIN * 0.6
                        add_mass(s.h, self.col_of(s, d["x"]), m, s.cap)
                        s.hp.ver += 1
                    self.puff(d["x"], gy - 4, 6, 2.5)
                    continue
                d["y"] = gy
                d["vy"] *= -0.35
                d["vx"] *= 0.6
                d["va"] *= 0.5
                d["hits"] += 1
            if d["life"] < 120:
                keep.append(d)
        self.debris = keep

    # ---------------------------------------------------------- котик
    def cat_sprite(self, pose, phase, blink, look):
        color = self.cfg.get("cat_color", "ginger")
        key = (pose, phase, blink, look, color)
        sp = self.cat_cache.get(key)
        if sp is None:
            pix, anc = cat_pix(pose, phase, blink, look, color)
            sp = self.cat_cache[key] = pix_to_sprite(pix, anc, self.dpr)
        return sp

    def find_landing(self, x, y, ny):
        for s in self.surfaces:
            if not (s.l <= x < s.r) or (s.key != "tb" and not in_vis(s.vis, x)):
                continue
            ground = s.top - s.h[self.col_of(s, x)] + 2
            if y <= s.top + 12 and ny >= ground:
                return s, ground
        return None

    def walk_range(self, s, x):
        if s.key == "tb":
            return 70.0, self.W - 70.0
        iv = [(a, b) for (a, b) in s.vis if a <= x < b]
        if not iv:
            iv = sorted(s.vis, key=lambda ab: min(abs(x - ab[0]), abs(x - ab[1])))[:1]
        if not iv:
            return x, x
        a, b = iv[0]
        return a + 10, max(a + 10, b - 10)

    def cat_rect(self):
        """Прямоугольник кота на экране (x, y, w, h) или None."""
        c = self.cat
        if not c or not c.pos or not c.vis:
            return None
        x, gy = c.pos
        if c.state == "climb":
            return (x - 30, gy - 56, 60, 60)
        if c.fall is not None or c.jump or c.state in ("pounce", "catch"):
            return None
        return (x - 28, gy - 52, 56, 56)

    def cat_hit(self, x, y):
        r = self.cat_rect()
        return bool(r) and r[0] <= x <= r[0] + r[2] and r[1] <= y <= r[1] + r[3]

    def cat_emote(self, kind, frames=40.0):
        if self.cat:
            self.cat.emote = [kind, frames]

    def cat_pet(self):
        c = self.cat
        if not c or not c.pos:
            return
        c.pet_t = 100.0
        c.state, c.t, c.dur = "sit", 0.0, 110.0
        c.climb = c.jump = None
        for k in range(3):
            c.hearts.append([c.pos[0] + random.uniform(-16, 16), c.pos[1] - 52 - k * 11, 55.0 + k * 8])

    def call_cat(self):
        cx, cy = self.cur if self.cur != (0, 0) else (self.W / 2.0, 120.0)
        if self.cat is None:
            self.cat = Cat()
            self.cat.next_break = time.time() + 30
        c = self.cat
        c.fall, c.key, c.jump, c.climb = [cx, max(10.0, cy - 80), 0.0], None, None, None
        c.state, c.t, c.dur, c.victim = "sit", 0.0, 40.0, None

    def cat_move(self, c, s, x, speed, dt, lo, hi):
        target = max(lo, min(hi, c.tx + s.l))
        d = target - x
        if abs(d) <= speed * dt:
            c.rx = target - s.l
            return True
        c.dir = 1 if d > 0 else -1
        c.rx += c.dir * speed * dt
        c.step += speed * dt
        return False

    def cat_walk_target(self, x, lo, hi):
        """Куда пойти: подальше от стен/углов, к середине."""
        span = hi - lo
        m = min(90.0, span * 0.22)
        a, b = lo + m, hi - m
        if b <= a:
            return (lo + hi) / 2.0
        if x < lo + m * 1.4:
            t = random.uniform(x + 100, min(b, x + 480))
        elif x > hi - m * 1.4:
            t = random.uniform(max(a, x - 480), x - 100)
        else:
            t = x + random.uniform(-420, 420)
        t = max(a, min(b, t))
        if abs(t - x) < 50:
            t = random.uniform(a, b)
        return t

    def cat_plan_jump(self, c, s, x, gy, want_key=None):
        best = None
        for s2 in self.surfaces:
            if s2.key == s.key or (want_key is not None and s2.key != want_key):
                continue
            for (a, b) in ([(80, self.W - 80)] if s2.key == "tb" else s2.vis):
                if b - a < 60:
                    continue
                lx = max(a + 30, min(b - 30, x))
                if abs(lx - x) > 280:
                    continue
                g2 = s2.top - s2.h[self.col_of(s2, lx)] + 2
                dy = g2 - gy
                if dy < -260 or dy > 900:
                    continue
                score = abs(lx - x) + abs(dy) * 0.4 + random.uniform(0, 70)
                if best is None or score < best[0]:
                    best = (score, s2, lx, g2)
        if best is None:
            return False
        _, s2, lx, g2 = best
        up = max(0.0, gy - g2)
        c.jump = {"x0": x, "y0": gy, "key": s2.key, "rx": lx - s2.l, "t": 0.0,
                  "T": 16 + abs(lx - x) / 9.0 + abs(g2 - gy) / 24.0, "H": 30 + up * 0.8}
        if lx != x:
            c.dir = 1 if lx > x else -1
        c.state, c.t = "jump", 0.0
        return True

    def point_covered(self, s, x, y):
        for (l, t, r, b) in s.above:
            if l <= x < r and t <= y < b:
                return True
        return False

    def cat_home(self):
        """Окно, где был кот, скрыто — он тихо возвращается на панель задач и занимается делами там."""
        c = self.cat
        c.jump = c.climb = c.victim = None
        c.fall = None
        c.key, c.rx = "tb", random.uniform(self.W * 0.3, self.W * 0.7)
        c.state, c.t, c.dur = "sit", 0.0, 60.0

    def cat_plan_climb(self, c, s, x, gy, lo, hi):
        """К стенке окна: если окно висит выше пола — сначала подпрыгнуть до стенки, потом лезть по ней."""
        best = None
        for s2 in self.surfaces:
            if s2.key in (s.key, "tb") or s2.top > gy - 120 or not s2.vis:
                continue
            for side in (-1, 1):
                wall = s2.l if side < 0 else s2.r
                if not (30 < wall < self.W - 30):
                    continue
                y_att = min(gy, s2.bottom - 18)                # где кот цепляется за стенку
                if y_att < s2.top + 24:
                    continue                                   # стенка слишком короткая
                need = gy - y_att                              # на сколько нужно подпрыгнуть
                if need > 230:
                    continue
                if self.point_covered(s2, wall, y_att):
                    continue                                   # стенку закрывает другое окно
                x0 = wall + (-1 if side < 0 else 1) * (14 if need <= 0 else 50)
                if not (lo <= x0 <= hi):
                    continue
                score = abs(x0 - x) + need * 0.3 + random.uniform(0, 90)
                if best is None or score < best[0]:
                    best = (score, s2, side, x0, y_att, need)
        if best is None:
            return False
        _, s2, side, x0, y_att, need = best
        c.climb_plan = (s2.key, side, y_att - s2.top, need > 0)
        c.tx = x0 - s.l
        c.state, c.t = "walk_climb", 0.0
        return True

    def cat_plan_catch(self, c, x, gy):
        best = None
        for f in self.flakes:
            if f[7]:
                continue
            dx = abs(f[0] - x)
            if dx < 110 and gy - 125 < f[1] < gy - 35:
                d = dx + abs(f[1] - (gy - 70))
                if best is None or d < best[0]:
                    best = (d, f)
        if best is None:
            return False
        c.cflake = best[1]
        c.dir = 1 if best[1][0] > x else -1
        c.state, c.t, c.dur = "catch", 0.0, 24.0
        return True

    def cat_plan_attack(self, c, s, x, gy, now):
        cands = [f for f in self.figures if f.kind == "snowman" and f.fall is None and f.pos and f.vis]
        if not cands:
            return False
        f = min(cands, key=lambda q: (0 if q.key == c.key else 1, abs(q.pos[0] - x)))
        if f.key == c.key:
            c.victim = f
            c.state, c.t, c.pdest = "attack", 0.0, None
            self.cat_emote("!")
            return True
        if self.cat_plan_jump(c, s, x, gy, want_key=f.key):
            c.victim = f
            return True
        c.next_break = now + 12
        return False

    def cat_think(self, now):
        c = self.cat
        s = self.smap.get(c.key)
        if s is None or not c.pos:
            c.state, c.t, c.dur = "sit", 0.0, 40.0
            return
        x, gy = s.l + c.rx, c.pos[1]
        lo, hi = self.walk_range(s, x)
        c.t = 0.0
        if self.cfg.get("cat_break", True) and now >= c.next_break and self.figures:
            if self.cat_plan_attack(c, s, x, gy, now):
                return
        e = max(0, min(2, int(self.cfg.get("cat_energy", 1))))
        W = {  # sit, wash, loaf, sleep, stretch, walk, dig, catch, roll, hop, climb
            0: (14, 12, 12, 14, 6, 10, 4, 4, 2, 5, 3),
            1: (10, 9, 6, 8, 6, 18, 6, 7, 3, 10, 6),
            2: (5, 5, 3, 3, 5, 22, 8, 12, 5, 16, 10)}[e]
        names = ("sit", "wash", "loaf", "sleep", "stretch", "walk", "dig", "catch", "roll", "hop", "climb")
        heap = s.h[self.col_of(s, x)]
        weights = []
        for n, w in zip(names, W):
            if n == "walk" and hi - lo < 160:
                w = 0
            if n == "dig" and heap < 3:
                w = 0
            weights.append(w)
        pick = random.choices(names, weights)[0]
        ok = True
        if pick == "walk":
            c.tx = self.cat_walk_target(x, lo, hi) - s.l
            c.state = "walk"
        elif pick == "hop":
            ok = self.cat_plan_jump(c, s, x, gy)
        elif pick == "climb":
            ok = self.cat_plan_climb(c, s, x, gy, lo, hi)
        elif pick == "catch":
            ok = self.cat_plan_catch(c, x, gy)
        else:
            c.state = pick
            c.dur = {"sit": random.uniform(50, 140), "wash": random.uniform(80, 150), "loaf": random.uniform(160, 320),
                     "sleep": random.uniform(250, 450), "stretch": 60.0, "dig": random.uniform(90, 170),
                     "roll": random.uniform(80, 140)}[pick]
        if not ok:
            c.state, c.dur = "sit", random.uniform(40, 100)

    def cat_ai(self, c, s, x, gy, now, dt):
        lo, hi = self.walk_range(s, x)
        cx, cy = self.cur
        dxc, dyc = cx - x, cy - (gy - 16)
        dist = math.hypot(dxc, dyc)
        st = c.state
        if c.pet_t > 0:
            c.pet_t -= dt
        idle = ("sit", "wash", "loaf", "roll", "stretch", "dig", "walk", "sleep", "swat", "follow", "stalk")
        if st in idle and dist < 90 and self.cur_speed > 14 and c.pet_t <= 0:
            d = -1 if dxc > 0 else 1                       # курсор налетел — убегаем
            if (d < 0 and x - lo < 140) or (d > 0 and hi - x < 140):
                d = -d if abs(dxc) > 40 else d            # у стены — бежим вдоль, не в угол
            c.state, c.t = "run", 0.0
            c.tx = max(lo, min(hi, x + d * random.uniform(160, 300))) - s.l
            self.cat_emote("!")
            return
        if st in ("sit", "loaf", "wash", "roll", "stretch"):
            if c.t >= c.dur:
                self.cat_think(now)
            elif c.pet_t <= 0 and 90 < dist < 280 and abs(dyc) < 150 and self.cur_speed > 0.5:
                r = random.random()
                if r < 0.010 * dt:
                    c.state, c.t = "follow", 0.0
                    self.cat_emote("?")
                elif r < 0.016 * dt and self.cur_speed < 6:
                    c.state, c.t, c.dur = "stalk", 0.0, random.uniform(40, 70)
                    c.dir = 1 if dxc > 0 else -1
                    self.cat_emote("?", 30.0)
        elif st == "sleep":
            if c.t >= c.dur:
                c.state, c.t, c.dur = "stretch", 0.0, 60.0
            elif dist < 100:
                c.state, c.t, c.dur = "stretch", 0.0, 40.0
                self.cat_emote("?", 30.0)
        elif st == "dig":
            h = s.h
            col = self.col_of(s, x)
            if int(c.t) % 12 == 0 and int(c.t) != int(c.t - dt):
                for i in range(max(0, col - 5), min(len(h), col + 6)):
                    h[i] = max(0.0, h[i] - 1.2)
                s.hp.ver += 1
                self.puff(x + c.dir * 18, gy - 6, 3, 2.2)
            if c.t >= c.dur:
                c.state, c.t, c.dur = "sit", 0.0, 50.0
        elif st in ("walk", "run"):
            if self.cat_move(c, s, x, 1.3 if st == "walk" else 3.0, dt, lo, hi):
                c.state, c.t, c.dur = "sit", 0.0, random.uniform(40, 110)
        elif st == "walk_climb":
            if self.cat_move(c, s, x, 1.8, dt, lo, hi) and c.climb_plan:
                key, side, ty, need_jump = c.climb_plan
                s2 = self.smap.get(key)
                if s2 is None or not s2.vis:
                    c.state, c.t, c.dur = "sit", 0.0, 40.0
                elif need_jump:                                 # окно выше пола: прыжок до стенки
                    up = max(0.0, gy - (s2.top + ty))
                    c.jump = {"x0": x, "y0": gy, "key": key, "wall": side, "ty": ty, "t": 0.0,
                              "T": 18.0 + up / 14.0, "H": 24.0 + up * 0.3}
                    c.dir = 1 if side < 0 else -1
                    c.state, c.t = "jump", 0.0
                else:
                    c.climb = {"key": key, "side": side, "y": gy}
                    c.state, c.t = "climb", 0.0
        elif st == "follow":
            c.tx = max(lo, min(hi, cx)) - s.l
            if dist > 380 or abs(dyc) > 220:
                c.state, c.t, c.dur = "sit", 0.0, 60.0
            elif abs(dxc) < 46:
                c.state, c.t = "swat", 0.0
                c.dir = 1 if dxc > 0 else -1
            else:
                self.cat_move(c, s, x, 1.9, dt, lo, hi)
        elif st == "stalk":                                # крадётся и прыгает на курсор
            c.dir = 1 if dxc > 0 else -1
            if dist > 320 or abs(dyc) > 160:
                c.state, c.t, c.dur = "sit", 0.0, 50.0
            elif c.t >= c.dur:
                c.px0 = c.rx
                c.pdest = max(lo, min(hi, x + max(-170.0, min(170.0, dxc)))) - s.l
                c.state, c.t, c.victim = "pounce", 0.0, None
                self.cat_emote("!", 25.0)
        elif st == "swat":
            if dist > 140 or c.t > 160:
                c.state, c.t, c.dur = "sit", 0.0, 50.0
        elif st == "attack":
            v = c.victim
            if v is None or v not in self.figures or not v.pos or v.fall is not None or v.key != c.key:
                c.state, c.t, c.dur, c.victim = "sit", 0.0, 40.0, None
                return
            c.tx = v.pos[0] - s.l
            if abs(v.pos[0] - x) < 36:
                c.state, c.t, c.pdest = "pounce", 0.0, None
                c.dir = 1 if v.pos[0] > x else -1
            else:
                self.cat_move(c, s, x, 3.1, dt, lo, hi)
        elif st == "pounce":
            if c.pdest is not None:
                u = min(1.0, c.t / 16.0)
                c.rx = c.px0 + (c.pdest - c.px0) * u
                if c.t >= 16:
                    c.pdest = None
                    c.state, c.t, c.dur = "swat", 0.0, 60.0
            else:
                c.rx += c.dir * 1.6 * dt
                if c.t >= 14:
                    if c.victim in self.figures:
                        self.demolish(c.victim, c.dir * 4.0)
                    c.victim = None
                    c.state, c.t, c.dur = "sit", 0.0, 120.0
                    c.next_break = now + random.uniform(25, 55)
        elif st == "catch":
            f = c.cflake
            if c.t >= 12 and f is not None:
                try:
                    self.flakes.remove(f)
                    self.puff(x + c.dir * 10, gy - 40, 3, 2.0)
                except ValueError:
                    pass
                c.cflake = None
            if c.t >= c.dur:
                c.state, c.t, c.dur = "sit", 0.0, 40.0
        elif st == "jump":
            c.state, c.t, c.dur = "sit", 0.0, 40.0
        c.rx = max(2.0, min(s.r - s.l - 2.0, c.rx))

    def update_cat(self, dt, now):
        if not self.cfg.get("cat", True):
            self.cat = None
            return
        c = self.cat
        if c is None:
            tb = self.tb_surface()
            if tb is None:
                return
            c = self.cat = Cat()
            c.key, c.rx = "tb", random.uniform(self.W * 0.3, self.W * 0.7)
            c.next_break = now + random.uniform(20, 40)
            c.pos = (tb.l + c.rx, self.tb_top)
            self.cat_think(now)
        c.t += dt
        c.blink = (c.blink + dt) % 180
        if c.emote:
            c.emote[1] -= dt
            if c.emote[1] <= 0:
                c.emote = None
        for h in c.hearts:
            h[1] -= 0.6 * dt
            h[2] -= dt
        c.hearts = [h for h in c.hearts if h[2] > 0]
        if c.fall is not None:                               # падает (окно закрыли / позвали)
            x, y, vy = c.fall
            vy = min(vy + 0.6 * dt, 14.0)
            ny = y + vy * dt
            hit = self.find_landing(x, y, ny)
            if hit:
                s, ground = hit
                c.key, c.rx, c.fall = s.key, x - s.l, None
                c.pos = (x, ground)
                self.puff(x, ground - 4, 5, 2.5)
                self.cat_think(now)
            else:
                c.fall = [x, ny, vy]
                c.pos, c.vis = (x, ny), True
                if ny > self.H + 80:
                    c.fall, c.key, c.rx = None, "tb", random.uniform(self.W * 0.3, self.W * 0.7)
            return
        if c.jump:                                            # прыжок на другую поверхность / до стенки окна
            j = c.jump
            s1 = self.smap.get(j["key"])
            if s1 is None:
                x, y = c.pos if c.pos else (self.W / 2.0, 0.0)
                c.jump, c.fall, c.key = None, [x, y, 0.0], None
                return
            if s1.key != "tb" and not s1.vis:                  # цель скрыта другим окном — остаёмся внизу
                self.cat_home()
                return
            j["t"] += dt
            u = min(1.0, j["t"] / j["T"])
            wall = j.get("wall")
            if wall is not None:
                x1 = (s1.l if wall < 0 else s1.r) + (-12 if wall < 0 else 12)
                y1 = s1.top + j["ty"]
            else:
                x1 = s1.l + j["rx"]
                y1 = s1.top - s1.h[self.col_of(s1, x1)] + 2
            x = j["x0"] + (x1 - j["x0"]) * u
            y = j["y0"] + (y1 - j["y0"]) * u - 4 * j["H"] * u * (1 - u)
            c.pos = (x, y)
            c.vis = s1.key == "tb" or not self.point_covered(s1, x, y - 12)
            if u >= 1.0:
                if wall is not None:                           # долетел до стенки — теперь лезет
                    c.climb = {"key": j["key"], "side": wall, "y": y1}
                    c.jump, c.state, c.t = None, "climb", 0.0
                    c.dir = 1 if wall < 0 else -1
                    self.puff(x, y, 3, 1.5)
                else:
                    c.key, c.rx, c.jump = s1.key, x1 - s1.l, None
                    self.puff(x1, y1 - 4, 4, 2.0)
                    self.cat_think(now)
            return
        if c.state == "climb" and c.climb:                    # лезет вверх по боковой грани окна
            cl = c.climb
            s2 = self.smap.get(cl["key"])
            if s2 is None:
                x, y = c.pos if c.pos else (self.W / 2.0, 0.0)
                c.climb, c.fall, c.key = None, [x, y, 0.0], None
                return
            if not s2.vis:
                self.cat_home()
                return
            wall = s2.l if cl["side"] < 0 else s2.r
            x = wall + (-12 if cl["side"] < 0 else 12)
            cl["y"] -= 1.9 * dt
            c.step += 1.9 * dt
            c.dir = 1 if cl["side"] < 0 else -1
            c.pos = (x, cl["y"])
            c.vis = not self.point_covered(s2, x, cl["y"] - 12)
            if cl["y"] <= s2.top + 4:
                rx = 30 if cl["side"] < 0 else (s2.r - s2.l) - 30
                c.climb = None
                c.jump = {"x0": x, "y0": cl["y"], "key": s2.key, "rx": rx, "t": 0.0, "T": 14.0, "H": 16.0}
                c.state = "jump"
            return
        s = self.smap.get(c.key)
        if s is None:
            if c.key in self.snow or c.key == "tb":
                c.vis = False
            elif c.pos:
                c.fall, c.key = [c.pos[0], c.pos[1], 0.0], None
            return
        if s.key != "tb" and not s.vis:                       # окно полностью закрыто другим — кот уходит вниз
            self.cat_home()
            return
        x = s.l + c.rx
        gy = s.top - s.h[self.col_of(s, x)] + 2
        c.pos = (x, gy)
        c.vis = s.key == "tb" or in_vis(s.vis, x)
        self.cat_ai(c, s, x, gy, now, dt)

    def draw_cat(self, p, t):
        c = self.cat
        if not c or not c.pos or not c.vis:
            return
        x, gy = c.pos
        st = c.state
        if c.fall is not None or c.jump:
            pose, ph = "leap", 0
        elif st == "pounce":
            u = min(1.0, c.t / (16.0 if c.pdest is not None else 14.0))
            gy -= 22 * 4 * u * (1 - u)
            pose, ph = "leap", 0
        elif st == "catch":
            u = min(1.0, c.t / c.dur)
            amp = 40.0
            if c.cflake is not None:
                amp = max(30.0, min(60.0, gy - c.cflake[1]))
            gy -= amp * 4 * u * (1 - u)
            pose, ph = "leap", 0
        elif st == "climb":
            pose, ph = "climb", int(c.step * 0.12) % 2
        elif st in ("walk", "follow", "walk_climb"):
            pose, ph = "walk", int(c.step * 0.2) % 4
        elif st in ("run", "attack"):
            pose, ph = "run", int(c.step * 0.12) % 4
        elif st == "swat":
            pose, ph = "swat", int(c.t / 14) % 2
        elif st == "stalk":
            pose, ph = "crouch", int(c.t / 6) % 2
        elif st == "dig":
            pose, ph = "dig", int(c.t / 6) % 2
        elif st == "wash":
            pose, ph = "wash", int(c.t / 10) % 2
        elif st == "roll":
            pose, ph = "roll", int(c.t / 8) % 2
        elif st == "stretch":
            pose, ph = "stretch", 0
        elif st == "loaf":
            pose, ph = "loaf", 0
        elif st == "sleep":
            pose, ph = "sleep", 0
        else:
            pose, ph = "sit", int(c.t / 16) % 4
        cx, cy = self.cur
        dxs = (cx - x) if c.dir < 0 else (x - cx)
        look = (0 if abs(dxs) < 14 else (1 if dxs > 0 else -1),
                0 if abs(cy - (gy - 16)) < 16 else (1 if cy > gy - 16 else -1))
        if math.hypot(cx - x, cy - gy) > 420:
            look = (0, 0)
        sp = self.cat_sprite(pose, ph, c.pet_t > 0 or c.blink < 7, look)
        p.save()
        p.translate(round(x), round(gy))
        if c.dir > 0:
            p.scale(-1, 1)
        blit(p, sp, 0, 0)
        p.restore()
        for hx, hy, life in c.hearts:
            p.save()
            p.setOpacity(min(1.0, life / 20.0))
            blit(p, self.sp.heart, round(hx), round(hy))
            p.restore()
        if c.emote and st != "climb":
            p.save()
            p.setOpacity(min(1.0, c.emote[1] / 12.0))
            blit(p, self.sp.emotes[c.emote[0]], round(x - c.dir * 14), round(gy - 62 - (3 if int(t * 6) % 2 else 0)))
            p.restore()
        if st == "sleep" and c.fall is None and not c.jump:
            for k in range(3):
                ph2 = (t * 0.5 + k / 3.0) % 1.0
                p.save()
                p.setOpacity(1.0 - ph2)
                blit(p, self.sp.zzz, round(x + 14 + ph2 * 12), round(gy - 36 - ph2 * 26))
                p.restore()

    # ---------------------------------------------------------- «зоны клика» (маленькие окна)
    def update_hits(self):
        """Клик по котику/снеговику ловят крошечные окна над ними: большой оверлей остаётся
        полностью «прозрачным для мыши», поэтому окна под ним никогда не залипают."""
        ox, oy = self.origin
        want = {}
        if not self.mode and not self.drag and not self.paused:
            r = self.cat_rect()
            if r:
                want["cat"] = r
            for f in self.figures:
                if f.pos and f.vis and f.fall is None:
                    hgt, hw = self.fig_extent(f)
                    x, gy = f.pos
                    want[("f", f.id)] = (x - hw - 4, gy - hgt - 4, 2 * hw + 8, hgt + 8)
        for k in list(self.hits):
            if k not in want:
                hw = self.hits.pop(k)
                hw.hide()
                hw.deleteLater()
        for k, (x, y, w, h) in want.items():
            geo = (int(x + ox), int(y + oy), int(w), int(h))
            hw = self.hits.get(k)
            if hw is None:
                hw = self.hits[k] = HitWin(self.on_hit, k)
                hw.setGeometry(*geo)
                hw.last = geo
                hw.show()
                set_overlay_style(int(hw.winId()), False)
                continue
            if hw.last != geo:
                hw.setGeometry(*geo)
                hw.last = geo
            if not hw.isVisible():
                hw.show()

    def on_hit(self, kind, btn="L"):
        if kind == "cat":
            if btn == "L":
                self.cat_pet()
            return
        f = next((q for q in self.figures if q.id == kind[1]), None)
        if f is None:
            return
        if btn == "R":
            if f.kind == "tree":                           # ПКМ по ёлке — режим «Наряжать»
                self.dec_tree = f
                self.set_mode("decorate")
            else:                                          # ПКМ по снеговику — следующий наряд
                i = OUTFIT_ORDER.index(f.outfit) if f.outfit in OUTFIT_ORDER else 0
                f.outfit = OUTFIT_ORDER[(i + 1) % len(OUTFIT_ORDER)]
                f.kick(9.0)
                if f.pos:
                    self.puff(f.pos[0], f.pos[1] - 50, 6, 2.5)
            return
        now = time.time()
        f.clicks = [t for t in f.clicks if now - t < 0.9] + [now]
        f.kick(random.choice((-9.0, 9.0)))
        if len(f.clicks) >= 3:
            self.demolish(f)

    def release_mouse(self):
        """Аварийный выход: если что-то «залипло» — сбрасывает режимы и перехват мыши."""
        self.drag = None
        self.set_mode(None)
        self.set_capture(False)
        for k in list(self.hits):
            hw = self.hits.pop(k)
            hw.hide()
            hw.deleteLater()

    # ---------------------------------------------------------- ввод
    def find_heap(self, x, y):
        for s in self.surfaces:
            if not (s.l <= x < s.r) or (s.key != "tb" and not in_vis(s.vis, x)):
                continue
            c = self.col_of(s, x)
            g = s.top - s.h[c]
            if s.h[c] > 0.8 and g - 28 <= y <= s.top + 16:
                return s, c
        return None

    def poll_input(self, now, dt):
        p = QCursor.pos()
        cx, cy = p.x() - self.origin[0], p.y() - self.origin[1]
        prev, self.cur = self.cur, (cx, cy)
        self.cur_speed = self.cur_speed * 0.6 + math.hypot(cx - prev[0], cy - prev[1]) * 0.4
        esc = key_down(0x1B)
        if esc and not self.esc_prev and self.mode:
            self.set_mode(None)
        self.esc_prev = esc
        want = bool(self.mode or self.drag)
        self.set_capture(want)
        if want:
            if self.drag:
                shape = Qt.CursorShape.ClosedHandCursor
            elif self.mode == "sculpt":
                shape = Qt.CursorShape.OpenHandCursor
            else:
                shape = Qt.CursorShape.CrossCursor
            if self.mode == "decorate":
                self.pal_hover = self.palette_at(cx, cy)
                if self.pal_hover is not None:
                    shape = Qt.CursorShape.PointingHandCursor
            if shape != self.cur_shape:
                self.cur_shape = shape
                self.setCursor(shape)
        elif self.cur_shape is not None:
            self.cur_shape = None
            self.unsetCursor()
        if self.drag:
            self.update_drag(cx, cy, prev)

    def update_drag(self, cx, cy, prev):
        d = self.drag
        d["x"], d["y"] = cx, cy
        if not d["rolling"]:
            return
        dist = math.hypot(cx - prev[0], cy - prev[1])
        if dist < 0.4:
            return
        hit = self.find_heap(cx, cy + d["r"])
        if not hit:
            return
        s, c = hit
        R = d["r"]
        c0, c1 = max(0, c - int(R / BIN) - 1), min(len(s.h) - 1, c + int(R / BIN) + 1)
        took = 0.0
        for i in range(c0, c1 + 1):
            t = min(s.h[i], 0.25 * dist)
            s.h[i] -= t
            took += t
        s.hp.ver += 1
        d["area"] += took * BIN * 0.6
        d["r"] = min(BALL_MAX, math.sqrt(d["area"] / math.pi))

    # ---------------------------------------------------------- палитра украшений
    def palette_layout(self):
        """-> (прямоугольник панели, [(прямоугольник, элемент)])."""
        row1 = [("orn", t, c) for (t, c) in ORN_PALETTE]
        row2 = [("topper", k) for k in TOPPERS] + [("lights",), ("tinsel",), ("preset",), ("clear",), ("done",)]
        cell, gap = 40, 6
        def width(it):
            return 40 if it[0] in ("orn", "topper") else 66
        w1 = sum(width(i) + gap for i in row1) - gap
        w2 = sum(width(i) + gap for i in row2) - gap
        bw = max(w1, w2) + 28
        bh = cell * 2 + gap + 28
        bx = (self.W - bw) / 2.0
        by = min(self.tb_top - bh - 24, self.H - bh - 24)
        t = self.dec_tree
        if t is not None and t.pos:                           # панель не должна закрывать ёлку — тогда уезжает наверх
            tx, ty = t.pos
            if (tx + TREE_W + 20 > bx and tx - TREE_W - 20 < bx + bw) and (ty + 10 > by and ty - TREE_H - 10 < by + bh):
                by = 62.0
        items = []
        for ri, row in enumerate((row1, row2)):
            tw = sum(width(i) + gap for i in row) - gap
            x = bx + (bw - tw) / 2.0
            y = by + 14 + ri * (cell + gap)
            for it in row:
                items.append((QRectF(x, y, width(it), cell), it))
                x += width(it) + gap
        return QRectF(bx, by, bw, bh), items

    def palette_at(self, x, y):
        _, items = self.palette_layout()
        for r, it in items:
            if r.x() <= x <= r.x() + r.width() and r.y() <= y <= r.y() + r.height():
                return it
        return None

    def palette_click(self, it):
        t = self.dec_tree
        if it[0] == "orn":
            self.sel = it
        elif it[0] == "topper" and t:
            t.td.topper = it[1]
        elif it[0] == "lights" and t:
            i = LIGHT_MODES.index(t.td.light_mode) if t.td.light_mode in LIGHT_MODES else 0
            t.td.light_mode = LIGHT_MODES[(i + 1) % len(LIGHT_MODES)]
            if t.td.light_anim not in ("static", "blink", "wave", "twinkle"):
                t.td.light_anim = "static"
        elif it[0] == "tinsel" and t:
            i = TINSELS.index(t.td.tinsel) if t.td.tinsel in TINSELS else 0
            t.td.tinsel = TINSELS[(i + 1) % len(TINSELS)]
        elif it[0] == "preset" and t:
            i = PRESET_ORDER.index(t.td.preset) if t.td.preset in PRESET_ORDER else -1
            t.td.apply_preset(PRESET_ORDER[(i + 1) % len(PRESET_ORDER)])
        elif it[0] == "clear" and t:
            t.td.orn = []
        elif it[0] == "done":
            self.set_mode(None)

    def tree_local(self, f, x, y):
        return x - f.pos[0], y - f.pos[1]

    def decorate_click(self, cx, cy, btn):
        if btn == "R":
            t = self.dec_tree
            if t and t.pos:
                lx, ly = self.tree_local(t, cx, cy)
                best, bi = 12.0 ** 2, None
                for i, o in enumerate(t.td.orn):
                    d = (o[2] - lx) ** 2 + (o[3] - ly) ** 2
                    if d < best:
                        best, bi = d, i
                if bi is not None:
                    t.td.orn.pop(bi)
                    return
            self.set_mode(None)
            return
        it = self.palette_at(cx, cy)
        if it is not None:
            self.palette_click(it)
            return
        for f in self.figures:                              # клик по другой ёлке — переключаемся на неё
            if f.kind == "tree" and self.fig_hit(f, cx, cy):
                self.dec_tree = f
                break
        t = self.dec_tree
        if t and t.pos and self.sel and self.sel[0] == "orn":
            lx, ly = self.tree_local(t, cx, cy)
            if tree_inside(lx, ly):
                t.td.orn.append([self.sel[1], self.sel[2], lx, ly])
                t.kick(3.0)

    def mousePressEvent(self, e):
        cx, cy = e.position().x(), e.position().y()
        btn = e.button()
        if self.mode == "decorate":
            if btn == Qt.MouseButton.RightButton:
                self.decorate_click(cx, cy, "R")
            elif btn == Qt.MouseButton.LeftButton:
                self.decorate_click(cx, cy, "L")
            return
        if btn == Qt.MouseButton.RightButton:
            if self.mode:
                self.set_mode(None)
            return
        if btn != Qt.MouseButton.LeftButton:
            return
        if self.mode == "place":
            if self.place_snowman(cx, cy):
                self.set_mode(None)
            return
        if self.mode == "place_tree":
            if self.place_tree(cx, cy):
                self.set_mode(None)
            return
        if self.mode == "sculpt":
            for f in self.figures:           # поднять верхний шар неполной башни
                if f.done or f.fall is not None or not f.pos or not f.balls:
                    continue
                cys = snowman_geometry(f.balls)
                bx, by = f.pos[0], f.pos[1] + cys[-1]
                if math.hypot(cx - bx, cy - by) <= f.balls[-1] + 3:
                    r = f.balls.pop()
                    if not f.balls:
                        self.figures.remove(f)
                    self.drag = {"r": r, "area": math.pi * r * r, "rolling": False, "x": cx, "y": cy}
                    return
            hit = self.find_heap(cx, cy)
            if hit:
                self.drag = {"r": 6.0, "area": math.pi * 36, "rolling": True, "x": cx, "y": cy}
            return

    def mouseDoubleClickEvent(self, e):
        self.mousePressEvent(e)

    def mouseReleaseEvent(self, e):
        if e.button() == Qt.MouseButton.LeftButton and self.drag:
            self.end_drag()

    def end_drag(self):
        d, self.drag = self.drag, None
        if d:
            self.drop_ball(d["r"], d["x"], d["y"])

    # ---------------------------------------------------------- рисование
    def paintEvent(self, _ev):
        t0 = time.perf_counter()
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        t = time.time() - self.t0
        if self.mode:
            p.fillRect(QRectF(0, 0, self.W, self.H), QColor(0, 0, 0, 3))
        if self.cfg["garland"] != "off":
            self.draw_garlands(p, t)
        self.draw_snow(p)
        self.draw_figures(p, t)
        self.draw_cat(p, t)
        self.draw_debris(p)
        self.draw_plow(p, t)
        self.draw_flakes(p)
        self.draw_hint(p)
        p.end()
        self.paint_ms = self.paint_ms * 0.9 + (time.perf_counter() - t0) * 1000 * 0.1

    def draw_flakes(self, p):
        if self.flake_clip is not None:
            p.setClipRegion(self.flake_clip)
        small, mid, big, chunks = QPolygonF(), QPolygonF(), QPolygonF(), []
        for f in self.flakes:
            r = f[4]
            if f[7]:
                chunks.append(f)
            elif r < 0.95:
                small.append(QPointF(f[0], f[1]))
            elif r < 1.3:
                mid.append(QPointF(f[0], f[1]))
            else:
                big.append(QPointF(f[0], f[1]))
        for poly_, w in ((small, 2.2), (mid, 3.2), (big, 4.4)):
            pen = QPen(QColor(255, 255, 255, 225))
            pen.setWidthF(w)
            pen.setCapStyle(Qt.PenCapStyle.RoundCap)
            p.setPen(pen)
            p.drawPoints(poly_)
        if chunks:
            p.setPen(Qt.PenStyle.NoPen)
            p.setBrush(QColor(246, 250, 255, 235))
            for f in chunks:
                p.drawEllipse(QPointF(f[0], f[1]), f[4], f[4] * 0.85)
        if self.flake_clip is not None:
            p.setClipping(False)

    def draw_snow(self, p):
        now = time.time()
        p.setPen(QPen(QColor(190, 212, 240), 1.2))
        p.setBrush(QColor(242, 248, 255))
        for s in self.surfaces:
            hp = s.hp
            if hp.poly is None or (hp.pver != hp.ver and now - hp.pt > 0.08):
                h = hp.h
                pts = [QPointF(0, 1)]
                pts += [QPointF(i * BIN, -hv) for i, hv in enumerate(h)]
                pts.append(QPointF(s.r - s.l, 1))
                hp.poly = QPolygonF(pts)
                hp.pver, hp.pt = hp.ver, now
            if max(hp.h) < 0.35:
                continue
            if s.clip is not None:
                p.setClipRegion(s.clip)
            p.save()
            p.translate(s.l, s.top)
            p.drawPolygon(hp.poly)
            p.restore()
            if s.clip is not None:
                p.setClipping(False)

    def draw_garlands(self, p, t):
        mode = self.cfg["garland"]
        style = self.cfg.get("garland_style", "fairy")
        spec = GARLAND_STYLES[style]
        wire = mkpen(spec["wire"][0], QColor(*spec["wire"][1]))
        for s in self.surfaces:
            g = self.garl.get(s.key)
            if not g:
                continue
            if s.clip is not None:
                p.setClipRegion(s.clip)
            p.save()
            p.translate(s.l, s.top)
            p.setBrush(Qt.BrushStyle.NoBrush)
            p.setPen(wire)
            p.drawPath(g["path"])
            p.setPen(Qt.PenStyle.NoPen)
            p.setBrush(G2)
            for hx in g["hooks"]:
                p.drawEllipse(QPointF(hx, 0), 1.4, 1.4)
            for (x, y, i) in g["bulbs"]:
                if mode == "static":
                    lv = 4
                elif mode == "blink":
                    lv = 4 if (int(t * 1.6) + i) % 2 == 0 else 1
                elif mode == "wave":
                    lv = max(1, min(4, int(1.5 + 3.0 * (0.5 + 0.5 * math.sin(t * 4 - i * 0.7)))))
                else:
                    lv = 1 + (((i * 2654435761) + int(t * 4) * 40503) >> 5) % 4
                pm, ox, oy = self.bulb_sprite_for(style, i, lv)
                p.drawPixmap(QPointF(x - ox, y - oy), pm)
            p.restore()
            if s.clip is not None:
                p.setClipping(False)

    def draw_figures(self, p, t):
        for f in self.figures:
            if not f.pos or not f.vis:
                continue
            x, gy = f.pos
            if f.fall is None:
                hgt, hw = self.fig_extent(f)
                p.fillRect(QRectF(x - hw - 4, gy - hgt - 4, 2 * hw + 8, hgt + 8), QColor(0, 0, 0, 3))
            p.save()
            p.translate(round(x), round(gy))
            p.rotate(max(-25.0, min(25.0, f.wob)))
            if f.kind == "tree":
                draw_tree(p, f.td, t, self.sp.tree, blit)
            else:
                fl_ = math.sin(t * 3 + f.id) * 1.2 + self.wind_cur * 0.8
                draw_snowman(p, f.balls, f.done, fl_, (), f.outfit)
            p.restore()
        cx, cy = self.cur
        if self.mode == "place":
            b = self.snap(cx, cy)
            gx, gyy = (cx, b[0] + 2) if b else (cx, cy)
            p.save()
            p.setOpacity(0.55)
            p.translate(gx, gyy)
            draw_snowman(p, [17, 13, 10], True, 0.0, (), self.cfg.get("snowman_outfit", "classic"))
            p.restore()
        elif self.mode == "place_tree" and self.ghost_td is not None:
            b = self.snap(cx, cy)
            gx, gyy = (cx, b[0] + 2) if b else (cx, cy)
            p.save()
            p.setOpacity(0.6)
            p.translate(round(gx), round(gyy))
            draw_tree(p, self.ghost_td, t, self.sp.tree, blit)
            p.restore()
        elif self.mode == "decorate" and self.dec_tree is not None and self.dec_tree.pos:
            tx, ty = self.dec_tree.pos
            p.setBrush(Qt.BrushStyle.NoBrush)
            pen = QPen(QColor(120, 210, 255, 190))
            pen.setWidthF(1.6)
            pen.setStyle(Qt.PenStyle.DashLine)
            p.setPen(pen)
            p.drawRoundedRect(QRectF(tx - TREE_W - 8, ty - TREE_H - 10, 2 * TREE_W + 16, TREE_H + 14), 10, 10)
            if self.sel and self.sel[0] == "orn" and self.palette_at(cx, cy) is None and tree_inside(cx - tx, cy - ty):
                p.save()
                p.setOpacity(0.75)
                blit(p, self.sp.tree.orn_sp(self.sel[1], self.sel[2]), round(cx), round(cy))
                p.restore()
        if self.drag:
            d = self.drag
            p.save()
            p.translate(d["x"], d["y"])
            draw_ball(p, 0, 0, d["r"])
            p.restore()

    def draw_debris(self, p):
        for d in self.debris:
            fade = 1.0 if d["life"] < 80 else max(0.0, 1.0 - (d["life"] - 80) / 40.0)
            p.save()
            p.setOpacity(fade)
            p.translate(d["x"], d["y"])
            p.rotate(d["ang"])
            k, s = d["kind"], d["s"]
            if k == "ball":
                draw_ball(p, 0, 0, d["r"])
            elif k == "orn":
                blit(p, self.sp.tree.orn_sp(*d["orn"]), 0, 0)
            elif k == "hat":
                part_hat(p, s, OUTFITS.get(d.get("outfit"), OUTFITS["classic"]))
            elif k == "scarf":
                sc = OUTFITS.get(d.get("outfit"), OUTFITS["classic"])["scarf"] or OUTFITS["classic"]["scarf"]
                part_scarf_wrap(p, d["r"], s, sc)
                p.translate(d["r"] * .56, 2.4 * s)
                part_scarf_tail(p, s, math.sin(d["life"] * 0.5) * 3, sc)
            elif k == "nose":
                part_nose(p, s)
            elif k == "arm":
                part_arm(p, s, d["side"])
            else:
                part_coal(p, s)
            p.restore()

    def draw_plow(self, p, t):
        pl = self.plow
        if not pl:
            return
        sp, v = self.sp, self.cfg["vehicle"]
        d, dist = pl["dir"], pl["dist"]
        bob = math.sin(t * 14) * 0.9
        p.save()
        p.translate(round(pl["x"]), round(self.tb_top))
        if d > 0:
            p.scale(-1, 1)
        if v == "tractor":
            p.setPen(Qt.PenStyle.NoPen)                   # свет фары
            p.setBrush(lin(-47, 0, -125, 0, (0, QColor(255, 244, 160, 85)), (1, QColor(255, 244, 160, 0))))
            p.drawPolygon(poly((-47, -31), (-125, -54), (-125, -8)))
            p.save()
            p.translate(0, bob)
            blit(p, sp.tractor, 0, 0)
            p.restore()
            for (cx, cy, spr, r) in ((22, -17, sp.wheel_big, 17), (-30, -11.5, sp.wheel_small, 11.5)):
                p.save()
                p.translate(cx, cy)
                p.rotate(-dist / r * 57.3)
                blit(p, spr, 0, 0)
                p.restore()
            p.save()
            p.translate(0, bob)
            blit(p, sp.loader, 0, 0)
            for k in range(3):                            # дым из трубы
                ph = (t * 0.9 + k / 3.0) % 1.0
                p.setPen(Qt.PenStyle.NoPen)
                p.setBrush(QColor(236, 240, 248, int(170 * (1 - ph))))
                p.drawEllipse(QPointF(-19.5 + ph * 24, -66 - ph * 28), 2.5 + ph * 5, 2.5 + ph * 5)
            lv = 0.5 + 0.5 * math.sin(t * 8)              # небольшая мигалка
            p.setPen(Qt.PenStyle.NoPen)
            p.setBrush(rad(24, -77, 10, 24, -77, (0, QColor(255, 170, 40, int(150 * lv))), (1, QColor(255, 170, 40, 0))))
            p.drawEllipse(QPointF(24, -77), 10, 10)
            fe(p, 24, -76.2, 3.0, 2.6, QColor(255, int(150 + 80 * lv), 40))
            p.restore()
        elif v == "snowmobile":
            p.setPen(Qt.PenStyle.NoPen)
            p.setBrush(lin(-62, 0, -135, 0, (0, QColor(255, 244, 160, 80)), (1, QColor(255, 244, 160, 0))))
            p.drawPolygon(poly((-62, -17), (-135, -40), (-135, -3)))
            if sp.sled_svg:                                        # ваш SVG: гусеница «едет» (6 кадров)
                p.save()
                p.translate(0, bob * 0.6)
                blit(p, sp.sled_svg[int(dist * 0.45) % 6], 0, 0)
                p.restore()
            else:
                blit(p, sp.blade_s, -70, 0)
                p.save()
                p.translate(0, bob * 0.7)
                blit(p, sp.sled, 0, 0)
                blit(p, sp.rider, 0, 0)
                p.restore()
        elif v == "penguin":
            if sp.peng_svg:                                        # ваш SVG: переваливается с ноги на ногу
                ph = dist * 0.085
                sn = math.sin(ph)
                fr = 1 if sn > 0.4 else (2 if sn < -0.4 else 0)
                p.save()
                p.translate(0, -abs(sn) * 1.8)
                p.rotate(3.2 * sn)
                blit(p, sp.peng_svg[fr], 0, 0)
                p.restore()
            else:
                blit(p, sp.peng[int(dist * 0.05) % 4], 0, 0)
        elif v == "custom" and self.custom_pix:
            pm = self.custom_pix
            blit(p, sp.blade, -pm.width() / 2 - 2, 0)
            p.save()
            if d > 0:
                p.scale(-1, 1)
            p.translate(0, bob)
            p.drawPixmap(QPointF(-pm.width() / 2, -pm.height()), pm)
            p.restore()
        p.restore()

    def draw_hint(self, p):
        txt = ""
        if self.mode == "sculpt":
            txt = "Лепка: зажми ЛКМ на сугробе и води — шар растёт. Три шара = снеговик.  ПКМ / Esc — выход"
        elif self.mode == "place":
            txt = "Выбери место и нажми ЛКМ.  ПКМ / Esc — отмена"
        elif self.mode == "place_tree":
            txt = "Выбери место для ёлки и нажми ЛКМ.  ПКМ / Esc — отмена"
        elif self.mode == "decorate":
            txt = "Наряжаем ёлку: выбери украшение внизу и кликай по ёлке.  ПКМ по игрушке — снять,  Esc — готово"
        elif self.notice[0] and time.time() < self.notice[1]:
            txt = self.notice[0]
        if txt:
            p.setPen(Qt.PenStyle.NoPen)
            p.setBrush(QColor(20, 30, 60, 200))
            w = min(self.W - 40, 8.2 * len(txt) + 30)
            r = QRectF((self.W - w) / 2, 14, w, 34)
            p.drawRoundedRect(r, 10, 10)
            f = QFont()
            f.setPointSize(10)
            p.setFont(f)
            p.setPen(QColor(255, 255, 255))
            p.drawText(r, Qt.AlignmentFlag.AlignCenter, txt)
        if self.mode == "decorate":
            self.draw_palette(p)

    def draw_palette(self, p):
        bar, items = self.palette_layout()
        t = self.dec_tree
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(QColor(16, 24, 48, 235))
        p.drawRoundedRect(bar, 16, 16)
        f = QFont()
        f.setPointSize(8)
        p.setFont(f)
        names = {"lights": "Огни", "tinsel": "Мишура", "preset": "Дизайн", "clear": "Сбросить", "done": "Готово"}
        for r, it in items:
            sel = (it == self.sel) or (it[0] == "topper" and t is not None and t.td.topper == it[1])
            p.setBrush(QColor(60, 150, 220, 200) if sel else (QColor(54, 70, 110, 230) if it == self.pal_hover else QColor(32, 44, 80, 230)))
            p.setPen(QPen(QColor(120, 210, 255), 1.6) if sel else Qt.PenStyle.NoPen)
            p.drawRoundedRect(r, 9, 9)
            cx_, cy_ = r.x() + r.width() / 2.0, r.y() + r.height() / 2.0
            if it[0] == "orn":
                blit(p, self.sp.tree.orn_sp(it[1], it[2]), round(cx_), round(cy_))
            elif it[0] == "topper":
                if it[1] == "none":
                    p.setPen(QColor(200, 210, 235))
                    p.drawText(r, Qt.AlignmentFlag.AlignCenter, "нет")
                else:
                    p.save()
                    p.translate(round(cx_), round(cy_ + 14))
                    p.scale(0.62, 0.62)
                    blit(p, self.sp.tree.topper[it[1]], 0, 0)
                    p.restore()
            else:
                p.setPen(QColor(235, 242, 255))
                label = names[it[0]]
                if it[0] == "lights" and t is not None:
                    label = "Огни: " + {"off": "выкл", "warm": "тёпл.", "cold": "хол.", "multi": "цвет.", "white": "бел."}[t.td.light_mode]
                elif it[0] == "tinsel" and t is not None:
                    label = "Мишура: " + {None: "нет", "gold": "зол.", "silver": "сер.", "red": "красн."}[t.td.tinsel]
                p.drawText(r, Qt.AlignmentFlag.AlignCenter, label)
        if self.pal_hover is not None and self.pal_hover[0] == "orn":
            p.setPen(QColor(255, 255, 255))
            p.drawText(QRectF(bar.x(), bar.y() - 22, bar.width(), 18), Qt.AlignmentFlag.AlignCenter,
                       {"ball": "Шар", "star": "Звезда", "candy": "Леденец", "bow": "Бант", "bell": "Колокольчик",
                        "snowflake": "Снежинка", "heart": "Сердечко"}[self.pal_hover[1]])
ICON_PNG_B64 = (
    "iVBORw0KGgoAAAANSUhEUgAAACAAAAAgCAYAAABzenr0AAAFoElEQVR42q3Xe4ycZRUG8N98M7tlabfb7WXbbllqBXqjaGMRWqWN"
    "pSRU4g0vKGJSaqKGaMSIGCDBaGIDWioiig0xFiMGA/4DRrME0WpqouC1NandQmnZ7XbtjV5Y9tKd+fzjfLszO92ZWvVNNpl9553z"
    "PO+5PO85OedY+c4UCrgM1+FduAJzcWF27A0cwi5sx/Powkhxfa6u/dw5gPO4ErdiPS7KyNRbIziITmzDn1CsRSRXAxjacTs2YtZE"
    "P06RpiS1L3kkI/EQeqGaSK4G+NuxBdfU8lKKOY1cmGf/QPxfY6XYgTvwYjWJZALwtXgcq+uBT8nzyOU8s4KFkymldcO8OrO5tgor"
    "CFRsXIWtWFjLWimNv6Y8iybz5ibaGiMUdUjIbH4/wxjDTCoOtGNzPXB4bxtbFnPFlABNcXETn5vPqta6oYBFGUb7mHsyJgnuw5dr"
    "3TpFc4FfrGB1K139zGxkaoGDg8xv4qk+btkZxEZDVWNtxl0oJRWuv7UyxqOuzufYeBH3XsKkhF8eYagUcZ/eQCEX4KdG6DwaubFl"
    "MV+5lMaEYka+isyG0VAkWa1vQBuUsG4G9y/ibS20FvjC/DD4jml8az/feIXBUtnayRHu7mJbD8ub+VQHH2hjRgPvnsX3lnLdjLCd"
    "rbYMM1/I4rK+MmU/NJvPdPCJdp7si71CjpXTeOYw9+/jgoQ7F4S779vHo91xy1XTaErCc5sXccOsCFMx5VfHxnnheixKsC5TuDH3"
    "P97L88fCxbfPZ8mU+O7Klsj+gRE6s1AMpfzxBCNpkHpna5xdMoWPzQ0iT/UFwarVgWuTTNsLlXW54zU27OKHPYyUwgismMpNc2jM"
    "hzvTCtKNCTfN5eppZU8Ol/hBD5/fzc7TZ4lKAWsLWFZNrZDjsxdHCApJGWR6A48sZe10/nyqzOAtzWycx0fmhDKmGYGGhE/O40wp"
    "cmSCqlhWyF61s5SOcHHXyQD766nIgRtns2EeH5wdVQGbLosS7S/yk97w4PKp4bH5TXV1YW4u35kWqwRJisl5Zjdy/AwnRqIkG5PQ"
    "gE0LubplvKWdp/nqS1GKA8V4oFoKzGzg8DCnixPqeimpRW1qIRRuWkP5ps2Z/M5smFjwC7nyTZqSkOi2SeUcmvChyHemp9BcnQOP"
    "Xs7H20Pldr0eN1zZwprp4aHjw2G8lEZCNuTi5p1H2dPPihaWTg613PQyX395wmf7dCHrZMYRKKbsfYN/DdFxQcTxPVlH0DPIQwei"
    "7B5czIEBvvsqN8+NmN84u8K/6Bng1cGaDjiU4B9ntTQp2w7y9GGKFfu7X+fDf+OBfRwZjr3hNBLvfX8JlSym4y/y8yM8e7QmgV1J"
    "1sONVLJeM50n3sqnO0KnR40+dyxEpzqbcjn6htjaHSEbBS/kQlGfXM41reOkeLR1255kDWRPZTJ9dE5ke+8Q3zkQbi+lUV6jCXZV"
    "VgWzGkP/ifN/Px2fXzjJA69EBaxuDVWs4t2NXyfYkzWQYyX42EHu6Qq3bu2OKugZCi2YlHDXJeEd4sF5OBOngZEyyf4iX3spbNzT"
    "xY8OnuX+Z7FntB9YiafHXsS0LEbNBW7riJv89BB3LCg/zZVrb3/I95Fh7r2U3x4P0FFbOeOq4DDejz+cV0PSkjUkq1rpHojq6B0K"
    "zX9TEw/u54v/jJIs1e+Mvom7UcpV9GfteAJr6nWX186gfVKQ+fYSth+P5/iGWfysj9+fqJLVs9fvcDN6i+tz44aMXnwJP856hAm7"
    "4eeORg9wy7wyqR2vxT51ZwRZvt05OiOMNaUVffqLuC0bqyZcSS5QewbpHmR3f+hGkjsneFdm+4VKzP96MMnnWNAUj9WxM3VmvHMM"
    "Jv/TaFZKQ4TqgJ/faPZ/HE57sjo//+H0HOP5umy8WpY1MpOzY/3oy8bz32Tquvc/Gc//Dd5G/+CjOQDTAAAAAElFTkSuQmCC"
)


def make_icon():
    """Иконка приложения: вшита в код (PNG 32x32); если не загрузилась — рисуется снежинка."""
    pm = QPixmap()
    try:
        if pm.loadFromData(base64.b64decode("".join(ICON_PNG_B64))):
            ic = QIcon()
            for size in (16, 24, 32, 48, 64, 128):
                ic.addPixmap(pm.scaled(size, size, Qt.AspectRatioMode.KeepAspectRatio,
                                       Qt.TransformationMode.SmoothTransformation))
            return ic
    except Exception:
        pass
    pm = QPixmap(64, 64)
    pm.fill(Qt.GlobalColor.transparent)
    p = QPainter(pm)
    p.setRenderHint(QPainter.RenderHint.Antialiasing)
    p.setBrush(QColor(40, 90, 170))
    p.setPen(Qt.PenStyle.NoPen)
    p.drawEllipse(2, 2, 60, 60)
    p.setPen(mkpen(4, QColor(255, 255, 255)))
    for k in range(3):
        a = math.radians(60 * k)
        dx, dy = 22 * math.cos(a), 22 * math.sin(a)
        p.drawLine(QPointF(32 - dx, 32 - dy), QPointF(32 + dx, 32 + dy))
    p.end()
    return QIcon(pm)


# ======================================================================== панель управления
QSS = """
#root { background: #0e1525; }
#side { background: #0a101e; border-right: 1px solid #1a2440; }
#page { background: #0e1525; }
QWidget { color: #e6edfb; font-family: "Segoe UI", "Helvetica Neue", "Inter", sans-serif; font-size: 13px; }
QLabel { background: transparent; }
#logo { font-size: 21px; font-weight: 700; color: #ffffff; }
#tag { color: #7f90b8; font-size: 12px; }
#h1 { font-size: 24px; font-weight: 700; color: #ffffff; }
#h2 { font-size: 15px; font-weight: 600; color: #ffffff; }
#muted { color: #8b9bc0; }
#badge { color: #ffa8cc; font-size: 17px; font-family: "Segoe UI Emoji", "Apple Color Emoji", "Segoe UI", "Helvetica Neue", sans-serif;
         background: #2a2146; border-radius: 12px; padding: 3px 12px; }
#card { background: #162038; border: 1px solid #22305a; border-radius: 14px; }
#rowline { background: #22305a; max-height: 1px; min-height: 1px; border: none; }
QPushButton#nav { text-align: left; padding: 11px 16px; border-radius: 10px; border: none;
                  background: transparent; color: #a9b8da; font-size: 14px; }
QPushButton#nav:hover { background: #131c34; color: #ffffff; }
QPushButton#nav:checked { background: #1c2c52; color: #ffffff; font-weight: 600; }
QPushButton#seg { background: #1b2848; color: #b6c4e6; border: 1px solid #2a3b66; padding: 9px 16px; }
QPushButton#seg:hover { background: #21315a; }
QPushButton#seg:checked { background: #4cc3ff; color: #06121f; border-color: #4cc3ff; font-weight: 600; }
QPushButton#seg[pos="first"] { border-top-left-radius: 10px; border-bottom-left-radius: 10px; }
QPushButton#seg[pos="last"] { border-top-right-radius: 10px; border-bottom-right-radius: 10px; }
QPushButton#action { background: #1f2f55; border: 1px solid #30447a; border-radius: 10px; padding: 10px 18px; color: #e6edfb; }
QPushButton#action:hover { background: #29407a; border-color: #4cc3ff; }
QPushButton#primary { background: #4cc3ff; border: none; border-radius: 10px; padding: 10px 18px;
                      color: #06121f; font-weight: 600; }
QPushButton#primary:hover { background: #7bd3ff; }
QPushButton#danger { background: #3a1f2e; border: 1px solid #6a2f48; border-radius: 10px; padding: 10px 18px; color: #ffb4c6; }
QPushButton#danger:hover { background: #55273f; }
QToolButton#tile { background: #1b2848; border: 2px solid #2a3b66; border-radius: 14px; padding: 10px 8px; color: #cfd9f2; }
QToolButton#tile:hover { background: #21315a; }
QToolButton#tile:checked { border-color: #4cc3ff; background: #1d3560; color: #ffffff; }
QSlider::groove:horizontal { height: 6px; background: #2a3b66; border-radius: 3px; }
QSlider::sub-page:horizontal { background: #4cc3ff; border-radius: 3px; }
QSlider::handle:horizontal { background: #ffffff; width: 18px; height: 18px; margin: -6px 0; border-radius: 9px; }
QScrollArea { background: transparent; border: none; }
QScrollBar:vertical { background: transparent; width: 10px; margin: 2px; }
QScrollBar::handle:vertical { background: #2a3b66; border-radius: 5px; min-height: 30px; }
QScrollBar::add-line:vertical, QScrollBar::sub-line:vertical { height: 0; }
QToolTip { background: #1b2848; color: #e6edfb; border: 1px solid #30447a; padding: 4px 8px; }
"""
if IS_MAC:        # на Mac нет Segoe UI: сразу берём системный шрифт, без долгого поиска замены
    QSS = QSS.replace('"Segoe UI Emoji", "Apple Color Emoji", "Segoe UI", "Helvetica Neue"', '"Apple Color Emoji", "Helvetica Neue"')
    QSS = QSS.replace('"Segoe UI", "Helvetica Neue"', '"Helvetica Neue"')


class Switch(QWidget):
    """Красивый переключатель (вкл/выкл)."""
    toggled = Signal(bool)

    def __init__(self, checked=False):
        super().__init__()
        self._on = bool(checked)
        self.setFixedSize(46, 26)
        self.setCursor(Qt.CursorShape.PointingHandCursor)

    def isChecked(self):
        return self._on

    def setChecked(self, v):
        v = bool(v)
        if v != self._on:
            self._on = v
            self.update()

    def mousePressEvent(self, e):
        self._on = not self._on
        self.update()
        self.toggled.emit(self._on)

    def paintEvent(self, _ev):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(QColor("#4cc3ff") if self._on else QColor("#2b3a62"))
        p.drawRoundedRect(QRectF(0, 0, 46, 26), 13, 13)
        p.setBrush(QColor("#ffffff"))
        p.drawEllipse(QRectF(23 if self._on else 3, 3, 20, 20))
        p.end()


class Segmented(QWidget):
    """Сегментированный выбор: [Лёгкий | Ровный | Метель]."""
    changed = Signal(str)

    def __init__(self, options, current):
        super().__init__()
        lay = QHBoxLayout(self)
        lay.setContentsMargins(0, 0, 0, 0)
        lay.setSpacing(0)
        self.group = QButtonGroup(self)
        self.group.setExclusive(True)
        self.btns = {}
        for i, (label, val) in enumerate(options):
            b = QPushButton(label)
            b.setObjectName("seg")
            b.setCheckable(True)
            b.setCursor(Qt.CursorShape.PointingHandCursor)
            b.setProperty("pos", "first" if i == 0 else ("last" if i == len(options) - 1 else "mid"))
            b.setChecked(val == current)
            self.group.addButton(b)
            lay.addWidget(b)
            self.btns[val] = b
            b.clicked.connect(lambda _c=False, v=val: self.changed.emit(v))

    def set(self, val):
        if val in self.btns:
            self.btns[val].setChecked(True)


def nav_icon(kind):
    """Иконка вкладки, нарисованная кодом: обычная и «активная» (голубая)."""
    def paint(col):
        pm = QPixmap(48, 48)
        pm.fill(Qt.GlobalColor.transparent)
        pm.setDevicePixelRatio(2)
        p = QPainter(pm)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        p.setPen(mkpen(1.7, col))
        p.setBrush(Qt.BrushStyle.NoBrush)
        solid = QColor(col)
        if kind == "snow":
            for k in range(3):
                a = math.radians(60 * k + 90)
                dx, dy = 9 * math.cos(a), 9 * math.sin(a)
                p.drawLine(QPointF(12 - dx, 12 - dy), QPointF(12 + dx, 12 + dy))
                for s_ in (-1, 1):
                    for e in (1, -1):
                        bx, by = 12 + e * 6 * math.cos(a), 12 + e * 6 * math.sin(a)
                        b = a + s_ * math.radians(50) + (math.pi if e < 0 else 0)
                        p.drawLine(QPointF(bx, by), QPointF(bx + 2.6 * math.cos(b), by + 2.6 * math.sin(b)))
        elif kind == "tools":                                    # варежка
            p.drawRoundedRect(QRectF(7.5, 8.5, 9.5, 10), 4, 4)
            p.drawEllipse(QRectF(3.8, 11, 4.6, 6))
            p.drawRoundedRect(QRectF(7.5, 18.2, 9.5, 3.2), 1.2, 1.2)
        elif kind == "plow":                                     # трактор
            p.drawRoundedRect(QRectF(2.5, 11, 11, 5), 1.5, 1.5)
            p.drawRect(QRectF(10.5, 6.5, 7, 6.5))
            p.drawEllipse(QPointF(7, 18), 2.6, 2.6)
            p.drawEllipse(QPointF(17, 17.2), 3.4, 3.4)
            p.drawLine(QPointF(1.5, 9), QPointF(1.5, 17))
        elif kind == "cat":
            p.drawEllipse(QPointF(12, 13.2), 6.6, 6)
            p.drawLine(QPointF(5.9, 10.6), QPointF(6.8, 4.2))
            p.drawLine(QPointF(6.8, 4.2), QPointF(10.6, 7.4))
            p.drawLine(QPointF(18.1, 10.6), QPointF(17.2, 4.2))
            p.drawLine(QPointF(17.2, 4.2), QPointF(13.4, 7.4))
            p.setPen(Qt.PenStyle.NoPen)
            p.setBrush(solid)
            p.drawEllipse(QPointF(9.6, 12.6), 1.0, 1.2)
            p.drawEllipse(QPointF(14.4, 12.6), 1.0, 1.2)
        elif kind == "garland":
            path = QPainterPath()
            path.moveTo(2.5, 7)
            path.quadTo(12, 17, 21.5, 7)
            p.drawPath(path)
            p.setPen(Qt.PenStyle.NoPen)
            p.setBrush(solid)
            for x, y in ((6.6, 11.2), (12, 12.4), (17.4, 11.2)):
                p.drawEllipse(QPointF(x, y + 2), 2.0, 2.4)
        elif kind == "snowman":
            p.drawEllipse(QPointF(12, 16.4), 5.4, 5.4)
            p.drawEllipse(QPointF(12, 8.6), 3.7, 3.7)
            p.drawLine(QPointF(8.2, 5.4), QPointF(15.8, 5.4))
            p.drawLine(QPointF(9.6, 5.4), QPointF(9.6, 2.4))
            p.drawLine(QPointF(14.4, 5.4), QPointF(14.4, 2.4))
            p.drawLine(QPointF(9.6, 2.4), QPointF(14.4, 2.4))
        elif kind == "tree":
            path = QPainterPath()
            for i, (x, y) in enumerate(((12, 2.6), (17.4, 9), (14.6, 9), (19.6, 16), (13, 16), (13, 20.6),
                                        (11, 20.6), (11, 16), (4.4, 16), (9.4, 9), (6.6, 9))):
                if i == 0:
                    path.moveTo(x, y)
                else:
                    path.lineTo(x, y)
            path.closeSubpath()
            p.drawPath(path)
        elif kind == "windows":
            p.drawRoundedRect(QRectF(3.5, 5, 17, 14), 2.5, 2.5)
            p.drawLine(QPointF(3.5, 9.2), QPointF(20.5, 9.2))
            p.setPen(Qt.PenStyle.NoPen)
            p.setBrush(solid)
            p.drawEllipse(QPointF(6.4, 7.1), 0.8, 0.8)
        else:                                                    # шестерёнка
            p.drawEllipse(QPointF(12, 12), 4.2, 4.2)
            for k in range(8):
                a = math.radians(45 * k)
                p.drawLine(QPointF(12 + 6.2 * math.cos(a), 12 + 6.2 * math.sin(a)),
                           QPointF(12 + 8.6 * math.cos(a), 12 + 8.6 * math.sin(a)))
            p.drawEllipse(QPointF(12, 12), 7.0, 7.0) if False else None
        p.end()
        return pm
    ic = QIcon()
    ic.addPixmap(paint(QColor(169, 184, 218)), QIcon.Mode.Normal, QIcon.State.Off)
    ic.addPixmap(paint(QColor(255, 255, 255)), QIcon.Mode.Normal, QIcon.State.On)
    return ic


def vehicle_icon(sp, kind, S=2):
    """Картинка техники для плитки выбора."""
    w, h, ox, oy = 170, 100, 108, 92
    pm = QPixmap(int(w * S), int(h * S))
    pm.fill(Qt.GlobalColor.transparent)
    pm.setDevicePixelRatio(S)
    p = QPainter(pm)
    p.setRenderHint(QPainter.RenderHint.Antialiasing)
    p.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform)
    p.translate(ox, oy)
    if kind == "tractor":
        blit(p, sp.tractor, 0, 0)
        blit(p, sp.wheel_big, 22, -17)
        blit(p, sp.wheel_small, -30, -11.5)
        blit(p, sp.loader, 0, 0)
    elif kind == "snowmobile":
        if sp.sled_svg:
            blit(p, sp.sled_svg[0], 10, 0)
        else:
            blit(p, sp.blade_s, -70, 0)
            blit(p, sp.sled, 0, 0)
            blit(p, sp.rider, 0, 0)
    elif kind == "penguin":
        blit(p, sp.peng_svg[0] if sp.peng_svg else sp.peng[0], 0, 0)
    p.end()
    return pm


def _icon_pm(w, h, S=2):
    pm = QPixmap(int(w * S), int(h * S))
    pm.fill(Qt.GlobalColor.transparent)
    pm.setDevicePixelRatio(S)
    p = QPainter(pm)
    p.setRenderHint(QPainter.RenderHint.Antialiasing)
    p.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform)
    return pm, p


def outfit_icon(key):
    pm, p = _icon_pm(86, 104)
    p.translate(43, 98)
    p.scale(0.95, 0.95)
    draw_snowman(p, [17, 13, 10], True, 0.0, (), key)
    p.end()
    return pm


def preset_icon(ov, key):
    pm, p = _icon_pm(86, 104)
    p.translate(43, 98)
    p.scale(0.62, 0.62)
    td = TreeData()
    if key in TREE_PRESETS:
        td.apply_preset(key, seed=3)
    draw_tree(p, td, 0.7, ov.sp.tree, blit)
    p.end()
    return pm


def garland_icon(ov, style):
    pm, p = _icon_pm(190, 58)
    path = QPainterPath()
    path.moveTo(4, 8)
    path.quadTo(95, 30, 186, 8)
    spec = GARLAND_STYLES[style]
    stroke(p, path, spec["wire"][0], QColor(*spec["wire"][1]))
    for k in range(7):
        u = (k + 0.5) / 7.0
        x = 4 + 182 * u
        y = 8 + 4 * 11.0 * u * (1 - u) * 1.0
        sp = ov.bulb_sprite_for(style, k, 4)
        p.drawPixmap(QPointF(x - sp[1], y - sp[2]), sp[0])
    p.end()
    return pm


def _card(title=None, subtitle=None):
    f = QFrame()
    f.setObjectName("card")
    lay = QVBoxLayout(f)
    lay.setContentsMargins(20, 18, 20, 18)
    lay.setSpacing(12)
    if title:
        t = QLabel(title)
        t.setObjectName("h2")
        lay.addWidget(t)
    if subtitle:
        s = QLabel(subtitle)
        s.setObjectName("muted")
        s.setWordWrap(True)
        lay.addWidget(s)
    return f, lay


def _row(title, hint, widget):
    w = QWidget()
    h = QHBoxLayout(w)
    h.setContentsMargins(0, 0, 0, 0)
    h.setSpacing(14)
    col = QVBoxLayout()
    col.setSpacing(2)
    t = QLabel(title)
    col.addWidget(t)
    if hint:
        s = QLabel(hint)
        s.setObjectName("muted")
        s.setWordWrap(True)
        col.addWidget(s)
    h.addLayout(col, 1)
    h.addWidget(widget, 0, Qt.AlignmentFlag.AlignRight | Qt.AlignmentFlag.AlignVCenter)
    return w


def _btn(text, kind, cb):
    b = QPushButton(text)
    b.setObjectName(kind)
    b.setCursor(Qt.CursorShape.PointingHandCursor)
    b.clicked.connect(lambda _c=False: cb())
    return b


def _page_title(text, sub, badge=None):
    w = QWidget()
    v = QVBoxLayout(w)
    v.setContentsMargins(0, 0, 0, 4)
    v.setSpacing(2)
    row = QHBoxLayout()
    row.setSpacing(12)
    a = QLabel(text)
    a.setObjectName("h1")
    row.addWidget(a)
    if badge:
        bd = QLabel(badge)
        bd.setObjectName("badge")
        row.addWidget(bd)
    row.addStretch(1)
    v.addLayout(row)
    b = QLabel(sub)
    b.setObjectName("muted")
    v.addWidget(b)
    return w


class Panel(QWidget):
    def __init__(self, ov, tray):
        super().__init__()
        self.ov, self.cfg, self.tray = ov, ov.cfg, tray
        self.setObjectName("root")
        self.setWindowTitle(PANEL_TITLE)
        self.setWindowIcon(make_icon())
        self.resize(900, 640)
        self.setMinimumSize(800, 560)
        self.setStyleSheet(QSS)
        root = QHBoxLayout(self)
        root.setContentsMargins(0, 0, 0, 0)
        root.setSpacing(0)

        side = QFrame()
        side.setObjectName("side")
        side.setFixedWidth(220)
        sl = QVBoxLayout(side)
        sl.setContentsMargins(14, 22, 14, 16)
        sl.setSpacing(4)
        head = QHBoxLayout()
        head.setSpacing(10)
        logo_ic = QLabel()
        logo_ic.setPixmap(make_icon().pixmap(32, 32))
        logo = QLabel("Snowfall")
        logo.setObjectName("logo")
        head.addWidget(logo_ic)
        head.addWidget(logo, 1)
        sl.addLayout(head)
        tag = QLabel("зимнее настроение на рабочем столе")
        tag.setObjectName("tag")
        tag.setWordWrap(True)
        sl.addWidget(tag)
        sl.addSpacing(18)

        self.stack = QStackedWidget()
        self.navgroup = QButtonGroup(self)
        self.navgroup.setExclusive(True)
        pages = [("snow", "Снегопад", self.page_weather), ("tools", "Инструменты", self.page_tools),
                 ("plow", "Снегоуборщик", self.page_plow), ("cat", "Котик", self.page_cat),
                 ("snowman", "Снеговик", self.page_snowman), ("tree", "Ёлка", self.page_tree),
                 ("garland", "Гирлянды", self.page_garland), ("windows", "Окна", self.page_windows),
                 ("gear", "Система", self.page_system)]
        self.win_index = 7
        self.navbtns = []
        for i, (ic, name, builder) in enumerate(pages):
            b = QPushButton("  " + name)
            b.setIcon(nav_icon(ic))
            b.setIconSize(QSize(20, 20))
            b.setObjectName("nav")
            b.setCheckable(True)
            b.setCursor(Qt.CursorShape.PointingHandCursor)
            self.navgroup.addButton(b)
            sl.addWidget(b)
            self.navbtns.append(b)
            sc = QScrollArea()
            sc.setWidgetResizable(True)
            sc.setFrameShape(QFrame.Shape.NoFrame)
            sc.setWidget(builder())
            self.stack.addWidget(sc)
            b.clicked.connect(lambda _c=False, i=i: self.go(i))
        sl.addStretch(1)
        sl.addWidget(_btn("Скрыть в трей", "action", self.hide))
        sl.addWidget(_btn("Выход", "danger", self.tray.quit))
        root.addWidget(side)
        root.addWidget(self.stack, 1)
        self.go(0)

    def go(self, i):
        self.navbtns[i].setChecked(True)
        self.stack.setCurrentIndex(i)
        if i == self.win_index:
            self.fill_windows()

    def showEvent(self, e):
        self.ov.panel_hwnd = native_id(int(self.winId()))          # на панели управления снега нет
        self.ov.last_refresh = 0.0
        super().showEvent(e)

    def closeEvent(self, e):
        e.ignore()
        self.hide()

    def setc(self, key, val):
        self.cfg[key] = val
        save_settings(self.cfg)

    def _page(self, title, sub, badge=None):
        page = QWidget()
        page.setObjectName("page")
        lay = QVBoxLayout(page)
        lay.setContentsMargins(30, 26, 30, 26)
        lay.setSpacing(16)
        lay.addWidget(_page_title(title, sub, badge))
        return page, lay

    def _switch(self, key, extra=None):
        sw = Switch(self.cfg.get(key, False))

        def cb(v, key=key):
            self.setc(key, v)
            if extra:
                extra(v)
        sw.toggled.connect(cb)
        return sw

    # -------- страницы
    def page_weather(self):
        page, lay = self._page("Снегопад", "Какой снег идёт и куда его сносит ветер")
        c, cl = _card("Интенсивность")
        seg = Segmented([(n, n) for n in INTENSITY], self.cfg["intensity"])
        seg.changed.connect(lambda v: self.setc("intensity", v))
        cl.addWidget(seg)
        lay.addWidget(c)

        c, cl = _card("Ветер", "Двигайте ползунок: влево — ветер дует влево, вправо — вправо")
        self.wind_lbl = QLabel("")
        self.wind_lbl.setObjectName("muted")
        sl = QSlider(Qt.Orientation.Horizontal)
        sl.setRange(-50, 50)
        sl.setValue(int(round(self.cfg["wind_base"] / 4.5 * 50)))
        sl.valueChanged.connect(self.on_wind)
        sl.sliderReleased.connect(lambda: save_settings(self.cfg))
        self.on_wind(sl.value())
        cl.addWidget(sl)
        cl.addWidget(self.wind_lbl)
        cl.addWidget(_row("Порывы ветра", "Ветер то усиливается, то стихает", self._switch("gusts")))
        lay.addWidget(c)

        c, cl = _card("Снег")
        self.snow_sw = Switch(True)
        self.snow_sw.toggled.connect(self.on_snow_toggle)
        cl.addWidget(_row("Снег идёт", "Выключите, чтобы снег перестал падать", self.snow_sw))
        cl.addWidget(_btn("Убрать весь снег (лопата)", "action", self.ov.clear_all))
        lay.addWidget(c)
        lay.addStretch(1)
        return page

    def on_wind(self, v):
        self.cfg["wind_base"] = v / 50.0 * 4.5
        a = abs(v)
        word = "нет" if a < 4 else ("слабый" if a < 22 else ("сильный" if a < 40 else "штормовой"))
        arrow = "" if a < 4 else (" →" if v > 0 else " ←")
        self.wind_lbl.setText("Ветер: %s%s" % (word, arrow))

    def on_snow_toggle(self, v):
        self.ov.enabled = v
        if not v:
            self.ov.flakes.clear()

    def page_tools(self):
        page, lay = self._page("Инструменты", "Играйте со снегом")
        c, cl = _card("Убирать снег")
        mit = Switch(False)
        mit.toggled.connect(self.ov.set_mitten)
        cl.addWidget(_row("Варежка", "Курсор превращается в варежку и смахивает снег с окон и панели задач", mit))
        cl.addWidget(_btn("Лопата — убрать весь снег сразу", "action", self.ov.clear_all))
        lay.addWidget(c)

        c, cl = _card("Снеговики", "Окно панели скроется, чтобы не мешать. Выйти из режима: Esc или правая кнопка мыши")
        cl.addWidget(_btn("Слепить снеговика из снега", "primary", lambda: self.enter_mode("sculpt")))
        cl.addWidget(_btn("Поставить готового снеговика (выбрать место)", "action", lambda: self.enter_mode("place")))
        cl.addWidget(_btn("Убрать всех снеговиков", "danger", lambda: [self.ov.demolish(f) for f in list(self.ov.figures)]))
        tip = QLabel("Лепка: зажмите левую кнопку на сугробе и ведите — шар растёт. Три шара = снеговик. "
                     "Снеговика можно разрушить тройным кликом.")
        tip.setObjectName("muted")
        tip.setWordWrap(True)
        cl.addWidget(tip)
        lay.addWidget(c)
        lay.addStretch(1)
        return page

    def enter_mode(self, m):
        self.ov.set_mode(m)
        if self.ov.mode is not None:                       # режим включился — прячем панель, чтобы не мешала
            self.hide()

    def page_plow(self):
        page, lay = self._page("Снегоуборщик", "Выезжает, когда на панели задач накопится много снега")
        c, cl = _card("Техника")
        grid = QHBoxLayout()
        grid.setSpacing(12)
        self.tiles = {}
        grp = QButtonGroup(self)
        grp.setExclusive(True)
        items = [("tractor", "Трактор с ковшом"), ("snowmobile", "Снегоход"), ("penguin", "Пингвин с лопатой"),
                 ("custom", "Своя картинка")]
        for key, name in items:
            t = QToolButton()
            t.setObjectName("tile")
            t.setCheckable(True)
            t.setCursor(Qt.CursorShape.PointingHandCursor)
            t.setText(name)
            t.setToolButtonStyle(Qt.ToolButtonStyle.ToolButtonTextUnderIcon)
            t.setIconSize(QSize(120, 72))
            if key != "custom":
                t.setIcon(QIcon(vehicle_icon(self.ov.sp, key)))
            else:
                t.setIcon(QIcon(self.ov.custom_pix) if self.ov.custom_pix else QIcon())
            t.setMinimumHeight(118)
            t.setSizePolicy(QSizePolicy.Policy.Ignored, QSizePolicy.Policy.Fixed)
            t.setChecked(self.cfg["vehicle"] == key)
            grp.addButton(t)
            grid.addWidget(t, 1)
            self.tiles[key] = t
            t.clicked.connect(lambda _c=False, k=key: self.choose_vehicle(k))
        cl.addLayout(grid)
        lay.addWidget(c)

        c, cl = _card("Работа")
        cl.addWidget(_row("Выезжать автоматически", "Когда сугроб на панели задач станет большим", self._switch("auto_plow")))
        cl.addWidget(_btn("Вызвать снегоуборщик сейчас", "primary", self.ov.start_plow))
        lay.addWidget(c)
        lay.addStretch(1)
        return page

    def choose_vehicle(self, key):
        if key == "custom":
            path, _ = QFileDialog.getOpenFileName(self, "Картинка для снегоуборщика", "",
                                                  "Изображения (*.png *.jpg *.jpeg *.bmp *.gif)")
            if not path:
                self.tiles[self.cfg["vehicle"] if self.cfg["vehicle"] != "custom" else "tractor"].setChecked(True)
                return
            self.ov.load_custom(path)
            self.tiles["custom"].setIcon(QIcon(self.ov.custom_pix))
        else:
            self.cfg["vehicle"] = key
        save_settings(self.cfg)

    def page_cat(self):
        page, lay = self._page("Котик", "Гуляет по окнам, играет с курсором и иногда шалит", "(=ты 💗)")
        c, cl = _card("Поведение")
        cl.addWidget(_row("Показывать котика", "", self._switch("cat")))
        cl.addWidget(_row("Иногда ломает снеговиков", "Подбегает и прыгает на снеговика", self._switch("cat_break")))
        cl.addWidget(_row("Характер", "Как часто котик бегает и прыгает",
                          self._energy_seg()))
        row = QHBoxLayout()
        row.addWidget(_btn("Позвать котика к курсору", "primary", self.ov.call_cat))
        row.addStretch(1)
        cl.addLayout(row)
        tip = QLabel("Кликните по коту — погладите. Он следит за курсором, крадётся к нему и играет лапкой; "
                     "если резко махнуть курсором, убежит. Лазает по окнам, потягивается, умывается, ловит снежинки, "
                     "роет снег и спит.")
        tip.setObjectName("muted")
        tip.setWordWrap(True)
        cl.addWidget(tip)
        lay.addWidget(c)

        c, cl = _card("Окрас")
        row = QHBoxLayout()
        row.setSpacing(12)
        grp = QButtonGroup(self)
        grp.setExclusive(True)
        self.cat_sw = {}
        for key, pal in CAT_PALETTES.items():
            col = QVBoxLayout()
            b = QPushButton()
            b.setCheckable(True)
            b.setFixedSize(46, 46)
            b.setCursor(Qt.CursorShape.PointingHandCursor)
            b.setToolTip(pal["name"])
            b.setStyleSheet("QPushButton{background:%s;border-radius:23px;border:3px solid #22305a;}"
                            "QPushButton:hover{border-color:#6f86c0;}"
                            "QPushButton:checked{border:3px solid #4cc3ff;}" % pal["swatch"])
            b.setChecked(self.cfg["cat_color"] == key)
            grp.addButton(b)
            lbl = QLabel(pal["name"])
            lbl.setObjectName("muted")
            lbl.setAlignment(Qt.AlignmentFlag.AlignHCenter)
            col.addWidget(b, 0, Qt.AlignmentFlag.AlignHCenter)
            col.addWidget(lbl)
            row.addLayout(col)
            self.cat_sw[key] = b
            b.clicked.connect(lambda _c=False, k=key: self.setc("cat_color", k))
        row.addStretch(1)
        cl.addLayout(row)
        lay.addWidget(c)
        lay.addStretch(1)
        return page

    def _energy_seg(self):
        seg = Segmented([("Спокойный", "0"), ("Обычный", "1"), ("Непоседа", "2")], str(self.cfg["cat_energy"]))
        seg.changed.connect(lambda v: self.setc("cat_energy", int(v)))
        return seg

    def page_garland(self):
        page, lay = self._page("Гирлянды", "Огоньки по краям открытых окон")
        c, cl = _card("Вид лампочек")
        row = QHBoxLayout()
        row.setSpacing(10)
        grp = QButtonGroup(self)
        grp.setExclusive(True)
        self.g_tiles = {}
        for key in GARLAND_ORDER:
            t = QToolButton()
            t.setObjectName("tile")
            t.setCheckable(True)
            t.setCursor(Qt.CursorShape.PointingHandCursor)
            t.setText(GARLAND_STYLES[key]["name"])
            t.setToolButtonStyle(Qt.ToolButtonStyle.ToolButtonTextUnderIcon)
            t.setIconSize(QSize(120, 38))
            t.setIcon(QIcon(garland_icon(self.ov, key)))
            t.setMinimumHeight(84)
            t.setSizePolicy(QSizePolicy.Policy.Ignored, QSizePolicy.Policy.Fixed)
            t.setChecked(self.cfg.get("garland_style", "fairy") == key)
            grp.addButton(t)
            row.addWidget(t, 1)
            self.g_tiles[key] = t
            t.clicked.connect(lambda _c=False, k=key: self.set_garland_style(k))
        cl.addLayout(row)
        lay.addWidget(c)
        c, cl = _card("Режим")
        seg = Segmented([(n, v) for n, v in GARLAND_MODES.items()], self.cfg["garland"])
        seg.changed.connect(self.set_garland)
        cl.addWidget(seg)
        cl.addWidget(_btn("Для отдельных окон гирлянду можно выключить на странице «Окна»", "action",
                          lambda: self.go(self.win_index)))
        lay.addWidget(c)
        lay.addStretch(1)
        return page

    def set_garland_style(self, key):
        self.setc("garland_style", key)
        if self.cfg["garland"] == "off":                    # чтобы сразу было видно выбранный вид
            self.cfg["garland"] = "static"
        self.ov.last_refresh = 0.0

    def page_snowman(self):
        page, lay = self._page("Снеговик", "Выберите, как одет снеговик")
        c, cl = _card("Наряд", "Новые снеговики появятся в выбранном наряде. Правая кнопка мыши по снеговику — следующий наряд.")
        grid = QGridLayout()
        grid.setSpacing(10)
        grp = QButtonGroup(self)
        grp.setExclusive(True)
        self.o_tiles = {}
        for i, key in enumerate(OUTFIT_ORDER):
            t = QToolButton()
            t.setObjectName("tile")
            t.setCheckable(True)
            t.setCursor(Qt.CursorShape.PointingHandCursor)
            t.setText(OUTFITS[key]["name"])
            t.setToolButtonStyle(Qt.ToolButtonStyle.ToolButtonTextUnderIcon)
            t.setIconSize(QSize(66, 82))
            t.setIcon(QIcon(outfit_icon(key)))
            t.setMinimumHeight(128)
            t.setMinimumWidth(118)
            t.setSizePolicy(QSizePolicy.Policy.Ignored, QSizePolicy.Policy.Fixed)
            t.setChecked(self.cfg.get("snowman_outfit", "classic") == key)
            grp.addButton(t)
            grid.addWidget(t, i // 4, i % 4)
            self.o_tiles[key] = t
            t.clicked.connect(lambda _c=False, k=key: self.setc("snowman_outfit", k))
        for col in range(4):
            grid.setColumnStretch(col, 1)
            grid.setColumnMinimumWidth(col, 118)
        cl.addLayout(grid)
        lay.addWidget(c)
        c, cl = _card("Сейчас на экране")
        cl.addWidget(_btn("Одеть всех снеговиков в выбранный наряд", "primary", self.apply_outfit_all))
        cl.addWidget(_btn("Слепить снеговика из снега", "action", lambda: self.enter_mode("sculpt")))
        cl.addWidget(_btn("Поставить готового снеговика", "action", lambda: self.enter_mode("place")))
        lay.addWidget(c)
        lay.addStretch(1)
        return page

    def apply_outfit_all(self):
        key = self.cfg.get("snowman_outfit", "classic")
        for f in self.ov.figures:
            if f.kind == "snowman" and f.done:
                f.outfit = key
                f.kick(8.0)

    def page_tree(self):
        page, lay = self._page("Ёлка", "Поставьте ёлку и украсьте её — самим или готовым дизайном")
        c, cl = _card("Ёлка", "Окно панели скроется. Выйти из режима: Esc или правая кнопка мыши. "
                              "Правая кнопка по ёлке — режим «Наряжать», тройной клик — убрать.")
        cl.addWidget(_btn("Поставить ёлку (выбрать место)", "primary", lambda: self.enter_mode("place_tree")))
        cl.addWidget(_btn("Наряжать ёлку самому", "action", lambda: self.enter_mode("decorate")))
        cl.addWidget(_btn("Убрать все ёлки", "danger", self.remove_trees))
        lay.addWidget(c)
        c, cl = _card("Готовые дизайны", "Один клик — и ёлка нарядна. Дизайн применится ко всем ёлкам и к новым.")
        grid = QGridLayout()
        grid.setSpacing(10)
        grp = QButtonGroup(self)
        grp.setExclusive(True)
        self.t_tiles = {}
        keys = PRESET_ORDER + ["empty"]
        for i, key in enumerate(keys):
            t = QToolButton()
            t.setObjectName("tile")
            t.setCheckable(True)
            t.setCursor(Qt.CursorShape.PointingHandCursor)
            t.setText(TREE_PRESETS[key]["name"] if key in TREE_PRESETS else "Без украшений")
            t.setToolButtonStyle(Qt.ToolButtonStyle.ToolButtonTextUnderIcon)
            t.setIconSize(QSize(66, 82))
            t.setIcon(QIcon(preset_icon(self.ov, key)))
            t.setMinimumHeight(128)
            t.setMinimumWidth(118)
            t.setSizePolicy(QSizePolicy.Policy.Ignored, QSizePolicy.Policy.Fixed)
            t.setChecked(self.cfg.get("tree_preset", "gold") == key)
            grp.addButton(t)
            grid.addWidget(t, i // 4, i % 4)
            self.t_tiles[key] = t
            t.clicked.connect(lambda _c=False, k=key: self.ov.apply_tree_preset(k))
        for col in range(4):
            grid.setColumnStretch(col, 1)
            grid.setColumnMinimumWidth(col, 118)
        cl.addLayout(grid)
        lay.addWidget(c)
        c, cl = _card("Огни на ёлке")
        seg = Segmented([("Горят ровно", "static"), ("Мигают", "blink"), ("Бегущая волна", "wave"), ("Мерцают", "twinkle")], "wave")
        seg.changed.connect(self.set_tree_anim)
        cl.addWidget(seg)
        lay.addWidget(c)
        lay.addStretch(1)
        return page

    def set_tree_anim(self, v):
        for f in self.ov.figures:
            if f.kind == "tree":
                f.td.light_anim = v
                if f.td.light_mode == "off":
                    f.td.light_mode = "warm"

    def remove_trees(self):
        for f in list(self.ov.figures):
            if f.kind == "tree":
                self.ov.demolish(f)

    def set_garland(self, v):
        self.setc("garland", v)
        self.ov.last_refresh = 0.0

    def page_windows(self):
        page, lay = self._page("Окна", "Настройте снег для каждой программы отдельно — например, чтобы он не мешал в играх и видео")
        c, cl = _card("Общие настройки")
        refresh = lambda v: setattr(self.ov, "last_refresh", 0.0)
        cl.addWidget(_row("Снег падает поверх окон", "Выключите — снежинки будут идти только по рабочему столу, а над окнами не появятся",
                          self._switch("flakes_over_windows", refresh)))
        cl.addWidget(_row("Снег на панели управления", "По умолчанию выключен, чтобы не мешать настройкам",
                          self._switch("snow_on_panel", refresh)))
        lay.addWidget(c)
        t = QLabel("Отдельные программы")
        t.setObjectName("h2")
        lay.addWidget(t)
        self.win_holder = QVBoxLayout()
        self.win_holder.setSpacing(10)
        lay.addLayout(self.win_holder)
        lay.addWidget(_btn("Обновить список", "action", self.fill_windows))
        lay.addStretch(1)
        return page

    def fill_windows(self):
        h = self.win_holder
        while h.count():
            it = h.takeAt(0)
            w = it.widget()
            if w is not None:
                w.setParent(None)
                w.deleteLater()
        opened = {}
        for hwnd, exe in self.ov.wins_all:
            if exe and hwnd != self.ov.panel_hwnd and exe not in opened:
                opened[exe] = hwnd
        names = list(opened) + [e for e in self.cfg["rules"] if e not in opened]
        for exe in names:
            c, cl = _card()
            name = QLabel(exe)
            name.setObjectName("h2")
            cl.addWidget(name)
            if exe in opened:
                title = window_title(opened[exe])
                if title:
                    t = QLabel(title[:70])
                    t.setObjectName("muted")
                    cl.addWidget(t)
            else:
                t = QLabel("Сейчас не запущена — настройки сохранены")
                t.setObjectName("muted")
                cl.addWidget(t)
            rem = Switch(self.ov.remembered(exe))
            rem.toggled.connect(lambda v, exe=exe: self.ov.set_remember(exe, v))
            cl.addWidget(_row("Запомнить настройки", "Включено — настройки программы сохранятся и вернутся после перезапуска. "
                                                      "Выключено — действуют только пока программа открыта", rem))
            for key, label, hint in (("flakes", "Снег падает поверх окна", "Снежинки видны над этим окном"),
                                     ("drift", "Сугроб на верхнем крае", "Снег лежит на заголовке окна"),
                                     ("garland", "Гирлянда", "Огоньки по краю окна")):
                sw = Switch(self.ov.rule(exe, key))
                sw.toggled.connect(lambda v, exe=exe, key=key: self.ov.set_rule(exe, key, v))
                cl.addWidget(_row(label, hint, sw))
            if exe in self.cfg["rules"]:
                cl.addWidget(_btn("Забыть настройки этой программы", "danger",
                                  lambda exe=exe: (self.ov.forget_rules(exe), self.fill_windows())))
            h.addWidget(c)
        if not names:
            lbl = QLabel("Открытых окон не найдено")
            lbl.setObjectName("muted")
            h.addWidget(lbl)

    def page_system(self):
        page, lay = self._page("Система", "Производительность и аварийные кнопки")
        c, cl = _card("Плавность")
        seg = Segmented([(n, str(v)) for n, v in FPS_PRESETS.items()], str(self.cfg["fps"]))
        seg.changed.connect(lambda v: self.ov.set_fps(int(v)))
        cl.addWidget(seg)
        cl.addWidget(_row("Пауза в полноэкранных программах", "Игры и видео не тормозят из-за снега", self._switch("pause_fs")))
        lay.addWidget(c)
        c, cl = _card("Если что-то залипло", "Сбросит режимы лепки и перехват мыши")
        cl.addWidget(_btn("Освободить мышь", "action", self.ov.release_mouse))
        lay.addWidget(c)
        lay.addStretch(1)
        return page


class Tray:
    def __init__(self, app, ov):
        self.app, self.ov = app, ov
        self.tray = QSystemTrayIcon(make_icon(), app)
        self.tray.setToolTip("Snowfall")
        self.panel = Panel(ov, self)
        m = QMenu()
        self.menu = m
        m.addAction("Открыть панель управления").triggered.connect(self.show_panel)
        m.addSeparator()
        m.addAction("Убрать весь снег").triggered.connect(ov.clear_all)
        m.addAction("Позвать котика").triggered.connect(ov.call_cat)
        m.addAction("Освободить мышь").triggered.connect(ov.release_mouse)
        m.addSeparator()
        m.addAction("Выход").triggered.connect(self.quit)
        self.tray.setContextMenu(m)
        self.tray.activated.connect(self.on_activated)
        self.tray.show()
        self.panel.show()

    def show_panel(self):
        self.panel.show()
        self.panel.raise_()
        self.panel.activateWindow()
        if IS_MAC:
            try:
                NSApplication.sharedApplication().activateIgnoringOtherApps_(True)
            except Exception:
                pass

    def on_activated(self, reason):
        if reason == QSystemTrayIcon.ActivationReason.Trigger:
            if self.panel.isVisible():
                self.panel.hide()
            else:
                self.show_panel()

    def quit(self):
        self.ov.cleanup()
        self.app.quit()


PANEL_TITLE = "Snowfall — панель управления"
_MUTEX = []


def acquire_single_instance():
    """False, если Snowfall уже запущен."""
    try:
        k = ctypes.WinDLL("kernel32", use_last_error=True)
        k.CreateMutexW.argtypes = [ctypes.c_void_p, wintypes.BOOL, wintypes.LPCWSTR]
        k.CreateMutexW.restype = ctypes.c_void_p
        h = k.CreateMutexW(None, False, "Local\\Snowfall.Overlay.SingleInstance")
        err = ctypes.get_last_error()
        if not h:
            return True
        if err == 183:             # ERROR_ALREADY_EXISTS
            return False
        _MUTEX.append(h)
    except Exception:
        pass
    return True


def show_existing_panel():
    try:
        hw = user32.FindWindowW(None, PANEL_TITLE)
        if hw:
            user32.ShowWindow(hw, 9)
            user32.SetForegroundWindow(hw)
    except Exception:
        pass


MAC_SERVER_NAME = "Snowfall.Overlay.SingleInstance"


def mac_already_running():
    """macOS: если первый экземпляр уже слушает сокет — просим его показать панель и выходим."""
    from PySide6.QtNetwork import QLocalSocket
    sock = QLocalSocket()
    sock.connectToServer(MAC_SERVER_NAME)
    if sock.waitForConnected(400):
        sock.write(b"show")
        sock.flush()
        sock.waitForBytesWritten(400)
        sock.disconnectFromServer()
        return True
    return False


def mac_listen(tray):
    from PySide6.QtNetwork import QLocalServer
    from PySide6.QtCore import QObject
    srv = QLocalServer(tray.app)
    QLocalServer.removeServer(MAC_SERVER_NAME)
    srv.listen(MAC_SERVER_NAME)

    def on_conn():
        c = srv.nextPendingConnection()
        if c is not None:
            c.readyRead.connect(lambda: (c.readAll(), tray.show_panel()))
            c.disconnected.connect(c.deleteLater)
    srv.newConnection.connect(on_conn)
    return srv


def main():
    if not (IS_WIN or IS_MAC):
        sys.exit("Эта программа работает только в Windows и macOS.")
    if IS_WIN and not acquire_single_instance():
        show_existing_panel()
        sys.exit(0)
    try:
        ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID("Snowfall.Overlay.1")
    except Exception:
        pass
    import gc
    gc.collect()
    gc.freeze()                       # меньше пауз сборщика мусора -> плавнее снег
    gc.set_threshold(100000, 50, 50)
    app = QApplication(sys.argv)
    app.setQuitOnLastWindowClosed(False)
    app.setWindowIcon(make_icon())
    if IS_MAC:
        if mac_already_running():
            sys.exit(0)
        try:
            NSApplication.sharedApplication().setActivationPolicy_(1)   # без значка в Dock, только в строке меню
        except Exception:
            pass
    cfg = load_settings()
    set_system_arrow(None)           # на случай, если прошлый запуск закрылся с варежкой
    ov = Overlay(cfg)
    tray = Tray(app, ov)             # noqa: F841 (держим ссылку)
    srv = mac_listen(tray) if IS_MAC else None   # noqa: F841
    app.aboutToQuit.connect(ov.cleanup)
    sys.exit(app.exec())


if __name__ == "__main__":
    main()
