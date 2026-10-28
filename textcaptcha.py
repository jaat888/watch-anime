# -*- coding: utf-8 -*-
"""
textcaptcha.py - the "sarkari" captcha: a picture of distorted letters the visitor types in.

Free, no third party, no account: the picture is drawn here with Pillow.  The answer never leaves the
server (captcha.py keeps it for 2 minutes, one try, bound to the visitor's IP).

What makes the picture hard for a program but readable for a person:
  - every letter has its own size, rotation, colour and height, and they touch / overlap
  - the whole line is bent with a sine wave (so letters are no longer in a straight row)
  - wavy lines in the letters' own colours run THROUGH the text (a filter cannot just remove one colour)
  - speckle noise + a changing gradient background + a little blur
  - letters that look alike are never used (no 0 O 1 I L ...)

Honest limit: a picture alone is not bot-proof (modern OCR / AI can read many of these).  It is one layer
on top of the others the site already has: IP-bound pass token, hidden proof-of-work, minimum solve time,
one try per picture, burst and stream limits.
"""
import base64
import io
import math
import os
import secrets

try:
    from PIL import Image, ImageDraw, ImageFilter, ImageFont
    OK = True
except Exception:          # Pillow missing: captcha.py falls back to the ball game
    OK = False

ALPHABET = "ABCDEFGHJKMNPQRSTUVWXYZ23456789"      # no 0/O, 1/I/L: nothing that looks like something else
W, H = 260, 88
_R = secrets.SystemRandom()

_FONTS = [
    "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf",
    "/usr/share/fonts/dejavu/DejaVuSans-Bold.ttf",
    "/usr/share/fonts/truetype/liberation/LiberationSans-Bold.ttf",
    "/usr/share/fonts/TTF/DejaVuSans-Bold.ttf",
    "/Library/Fonts/Arial Bold.ttf",
]


def _font(size):
    for p in _FONTS:
        if os.path.exists(p):
            try:
                return ImageFont.truetype(p, size)
            except Exception:
                pass
    try:
        return ImageFont.load_default(size=size)     # Pillow >= 10.1 ships a scalable font: no font file needed
    except Exception:
        return ImageFont.load_default()


def new_text(n=6):
    return "".join(_R.choice(ALPHABET) for _ in range(n))


def norm(s):
    """What the visitor typed -> comparable form (case and spaces do not matter)."""
    return "".join(ch for ch in str(s or "").upper() if ch.isalnum())[:12]


def _dark():
    return (_R.randint(0, 95), _R.randint(0, 95), _R.randint(0, 110))


def _light():
    return (_R.randint(205, 250), _R.randint(205, 250), _R.randint(205, 250))


def _background(W=W, H=H):
    a, b = _light(), _light()
    img = Image.new("RGB", (W, H), a)
    d = ImageDraw.Draw(img)
    vertical = _R.random() < 0.5
    span = H if vertical else W
    for i in range(span):
        t = i / max(1, span - 1)
        c = tuple(int(a[k] + (b[k] - a[k]) * t) for k in range(3))
        d.line([(0, i), (W, i)] if vertical else [(i, 0), (i, H)], fill=c)
    for _ in range(260):                               # speckle
        x, y = _R.randint(0, W - 1), _R.randint(0, H - 1)
        c = _R.randint(120, 225)
        d.point((x, y), fill=(c, _R.randint(120, 225), _R.randint(120, 225)))
    return img


def _wavy_line(d, color, width, W=W, H=H):
    y0 = _R.randint(int(H * .25), int(H * .75))
    amp, fr, ph = _R.uniform(4, 11), _R.uniform(0.02, 0.05), _R.uniform(0, 6.28)
    sl = _R.uniform(-.08, .08)
    pts = [(x, y0 + amp * math.sin(x * fr + ph) + (x - W / 2) * sl) for x in range(-5, W + 6, 4)]
    d.line(pts, fill=color, width=width)


def _warp(img, bg, amps=(3.0, 5.5), W=W, H=H):
    amp, fr, ph = _R.uniform(*amps), _R.uniform(0.035, 0.065), _R.uniform(0, 6.28)
    step, mesh = 4, []
    for x0 in range(0, W, step):
        x1 = min(W, x0 + step)
        dy = amp * math.sin(x0 * fr + ph)
        mesh.append(((x0, 0, x1, H), (x0, dy, x0, H + dy, x1, H + dy, x1, dy)))
    return img.transform((W, H), Image.Transform.MESH, mesh, resample=Image.BICUBIC, fillcolor=bg)


def render(text, thin=False, calm=False):
    """text -> PNG bytes.  thin=True: only hairlines through the picture (a thick line must not look like a minus sign).
    calm=True (sums): small tilt and big operators, so a tilted + never looks like x."""
    bg = _background()
    layer = bg.copy()
    n = len(text)
    step = (W - 52) / (n - 1)          # centres of the letters run from 26 to W-26: nothing is cut at the edges
    for i, ch in enumerate(text):
        size = _R.randint(34, 44)
        if calm and ch in "+-":
            size = _R.randint(50, 56)
        f = _font(size)
        tile = Image.new("RGBA", (size + 24, size + 24), (0, 0, 0, 0))
        td = ImageDraw.Draw(tile)
        td.text((12, 8), ch, font=f, fill=_dark() + (255,))
        tile = tile.rotate(_R.uniform(-11, 11) if calm else _R.uniform(-30, 30), resample=Image.BICUBIC, expand=True)
        x = int(26 + i * step + _R.uniform(-2, 2) - tile.size[0] / 2)
        y = int((H - tile.size[1]) / 2 + _R.uniform(-4, 4) if calm else (H - tile.size[1]) / 2 + _R.uniform(-8, 8))
        layer.paste(tile, (x, y), tile)
    d = ImageDraw.Draw(layer)
    for _ in range(2 if thin else 3):                   # lines in the letters' own colours, through the text
        _wavy_line(d, _dark(), 1 if thin else 2)
    layer = _warp(layer, (235, 235, 235))
    d = ImageDraw.Draw(layer)
    for _ in range(0 if thin else 2):                   # and a few thin ones on top of the bend
        _wavy_line(d, _dark(), 1)
    for _ in range(60):
        d.point((_R.randint(0, W - 1), _R.randint(0, H - 1)), fill=_dark())
    layer = layer.filter(ImageFilter.GaussianBlur(0.55))
    buf = io.BytesIO()
    layer.save(buf, "PNG", optimize=True)
    return buf.getvalue()


def make(n=6):
    """-> (answer, data-URI of the picture)"""
    t = new_text(n)
    return t, "data:image/png;base64," + base64.b64encode(render(t)).decode()


def make_math():
    """Three small numbers with + and - in random order, e.g. 7+4-2 = ?   -> (answer as text, data-URI).
    The result is always 1..20, so the visitor never has to type a minus sign."""
    while True:
        a, b, c = (_R.randint(1, 9) for _ in range(3))
        o1, o2 = _R.choice("+-"), _R.choice("+-")
        r = a + (b if o1 == "+" else -b)
        r = r + (c if o2 == "+" else -c)
        if 1 <= r <= 20:
            break
    q = "%d%s%d%s%d=?" % (a, o1, b, o2, c)
    return str(r), "data:image/png;base64," + base64.b64encode(render(q, thin=True, calm=True)).decode()


SW, SH = 340, 120


def parse_nums(s):
    """What the visitor typed -> list of numbers (any separator: space, comma, dot...)."""
    import re
    return [int(x) for x in re.findall(r"\d{1,3}", str(s or ""))[:8]]


def make_sort():
    """3 or 4 different numbers (at most 2 digits each) scattered in the picture.  The instruction - small to big or
    big to small - is part of the PICTURE too, never in the page text, so a program must read it as well.
    -> (answer as "5,12,40,77" in the right order, data-URI)"""
    n = _R.choice((3, 4))
    nums = _R.sample(range(1, 100), n)
    desc = _R.random() < 0.5
    ans = sorted(nums, reverse=desc)
    bg = _background(SW, SH)
    layer = bg.copy()
    instr = "BIG TO SMALL" if desc else "SMALL TO BIG"
    f = _font(21)
    d0 = ImageDraw.Draw(layer)
    bb = d0.textbbox((0, 0), instr, font=f)
    d0.text(((SW - (bb[2] - bb[0])) // 2 - bb[0], 7), instr, font=f, fill=_dark())
    for i, num in enumerate(nums):
        size = _R.randint(36, 42)
        tile = Image.new("RGBA", (size * 2 + 30, size + 30), (0, 0, 0, 0))
        ImageDraw.Draw(tile).text((15, 10), str(num), font=_font(size), fill=_dark() + (255,))
        tile = tile.rotate(_R.uniform(-12, 12), resample=Image.BICUBIC, expand=True)
        cx = 52 + (SW - 104) * i / (n - 1) + _R.uniform(-2, 2)          # centres 50 px from the edges: nothing is cut off
        cy = 38 + (SH - 38) / 2 + (-7 if i % 2 else 7) + _R.uniform(-3, 3)      # neighbours sit a bit higher / lower: easy to tell apart
        layer.paste(tile, (int(cx - tile.size[0] / 2), int(cy - tile.size[1] / 2)), tile)
    d = ImageDraw.Draw(layer)
    for _ in range(2):
        _wavy_line(d, _dark(), 1, SW, SH)
    layer = _warp(layer, (235, 235, 235), (2.0, 3.5), SW, SH)
    d = ImageDraw.Draw(layer)
    for _ in range(70):
        d.point((_R.randint(0, SW - 1), _R.randint(0, SH - 1)), fill=_dark())
    layer = layer.filter(ImageFilter.GaussianBlur(0.5))
    buf = io.BytesIO()
    layer.save(buf, "PNG", optimize=True)
    return ",".join(str(x) for x in ans), "data:image/png;base64," + base64.b64encode(buf.getvalue()).decode()
