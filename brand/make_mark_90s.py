#!/usr/bin/env python3
"""Krell mark, 1990s CGI restyle: glossy balls + chrome tubes.
Same geometry as make_mark.py (K = 5 nodes + edges), shaded like an
SGI-era render: per-pixel sphere normals, Blinn specular, cylinder
gradient tubes, soft floor shadow."""
import numpy as np
from PIL import Image, ImageFilter

W = 1200
SS = 2  # supersample
R = W * SS

# geometry (1200-space, scaled below)
stem_x = 380
top = (stem_x, 290)
junction = (stem_x, 600)
bottom = (stem_x, 910)
upper_tip = (830, 250)
lower_tip = (850, 950)
NODES = [top, junction, bottom, upper_tip, lower_tip]
EDGES = [(top, bottom), (junction, upper_tip), (junction, lower_tip)]
NODE_R = 84
JUNCTION_R = 94
TUBE_R = 30

yy, xx = np.mgrid[0:R, 0:R].astype(np.float32) / SS

rgb = np.zeros((R, R, 3), np.float32)
alpha = np.zeros((R, R), np.float32)

# light direction (from upper-left-front), normalized
L = np.array([-0.45, -0.55, 0.70], np.float32)
L /= np.linalg.norm(L)
H = L + np.array([0, 0, 1], np.float32)
H /= np.linalg.norm(H)


def paint(mask, color):
    global rgb, alpha
    rgb[mask] = color[..., :3][mask]
    alpha[mask] = 1.0


def tube(a, b):
    ax, ay = a
    bx, by = b
    dx, dy = bx - ax, by - ay
    length2 = dx * dx + dy * dy
    t = ((xx - ax) * dx + (yy - ay) * dy) / length2
    t = np.clip(t, 0, 1)
    px, py = ax + t * dx, ay + t * dy
    dist = np.hypot(xx - px, yy - py)
    mask = dist <= TUBE_R
    # cylinder shading across the tube: s in [-1, 1]
    # perpendicular direction
    nx, ny = -dy / np.sqrt(length2), dx / np.sqrt(length2)
    s = ((xx - px) * nx + (yy - py) * ny) / TUBE_R
    nz = np.sqrt(np.clip(1 - s * s, 0, 1))
    # normal of cylinder surface
    nnx, nny = nx * s, ny * s
    diff = np.clip(nnx * L[0] + nny * L[1] + nz * L[2], 0, 1)
    spec = np.power(np.clip(nnx * H[0] + nny * H[1] + nz * H[2], 0, 1), 60) * 0.9
    base = np.array([0.62, 0.66, 0.72], np.float32)  # steel blue-grey
    shade = 0.25 + 0.75 * diff
    col = np.empty((R, R, 4), np.float32)
    col[..., 0] = base[0] * shade + spec
    col[..., 1] = base[1] * shade + spec
    col[..., 2] = base[2] * shade + spec
    col[..., 3] = 1.0
    paint(mask, col)


def ball(c, radius, base_color):
    cx, cy = c
    d2 = ((xx - cx) / radius) ** 2 + ((yy - cy) / radius) ** 2
    mask = d2 <= 1.0
    nx = (xx - cx) / radius
    ny = (yy - cy) / radius
    nz = np.sqrt(np.clip(1 - d2, 0, 1))
    diff = np.clip(nx * L[0] + ny * L[1] + nz * L[2], 0, 1)
    spec = np.power(np.clip(nx * H[0] + ny * H[1] + nz * H[2], 0, 1), 90) * 1.0
    rim = np.power(1 - nz, 3) * 0.25
    base = np.array(base_color, np.float32)
    shade = 0.18 + 0.85 * diff
    col = np.empty((R, R, 4), np.float32)
    col[..., 0] = base[0] * shade + spec + rim * 0.4
    col[..., 1] = base[1] * shade + spec + rim * 0.45
    col[..., 2] = base[2] * shade + spec + rim * 0.55
    col[..., 3] = 1.0
    paint(mask, col)


for a, b in EDGES:
    tube(a, b)
for n in NODES:
    if n == junction:
        ball(n, JUNCTION_R, (0.88, 0.03, 0.0))  # red root ball
    else:
        ball(n, NODE_R, (0.92, 0.91, 0.87))  # pearl balls

rgba = np.dstack([np.clip(rgb, 0, 1), alpha])
img = Image.fromarray((rgba * 255).astype(np.uint8), "RGBA")
img = img.resize((W, W), Image.LANCZOS)
img.save("krell-mark-90s-transparent.png")

# on black, with a soft drop shadow like a period render
bg = Image.new("RGBA", (W, W), (8, 8, 11, 255))
shadow = Image.new("RGBA", (W, W), (0, 0, 0, 0))
sh = img.split()[3].point(lambda a: int(a * 0.55))
shadow.putalpha(sh)
shadow = shadow.filter(ImageFilter.GaussianBlur(14))
black = Image.new("RGBA", (W, W), (0, 0, 0, 255))
shadow = Image.composite(black, shadow, shadow.split()[3])
bg.alpha_composite(shadow, (10, 16))
bg.alpha_composite(img, (0, 0))
bg.convert("RGB").save("krell-mark-90s.png")
print("done")
