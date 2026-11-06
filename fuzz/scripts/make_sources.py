#!/usr/bin/env python3
"""Writes small synthetic PAM (RGBA) / PPM (RGB) source images for corpus generation."""
import os, random, sys

out = sys.argv[1]
os.makedirs(out, exist_ok=True)
rnd = random.Random(1234)

def write_pam(path, w, h, px):  # px: list of (r,g,b,a)
    with open(path, "wb") as f:
        f.write(b"P7\nWIDTH %d\nHEIGHT %d\nDEPTH 4\nMAXVAL 255\nTUPLTYPE RGB_ALPHA\nENDHDR\n" % (w, h))
        f.write(bytes(c for p in px for c in p))

def write_ppm(path, w, h, px):
    with open(path, "wb") as f:
        f.write(b"P6\n%d %d\n255\n" % (w, h))
        f.write(bytes(c for p in px for c in p[:3]))

def pattern(name, w, h):
    px = []
    pal = [(rnd.randrange(256), rnd.randrange(256), rnd.randrange(256), rnd.choice([0, 128, 255])) for _ in range(256)]
    for y in range(h):
        for x in range(w):
            if name == "grad":
                p = (x * 255 // max(w - 1, 1), y * 255 // max(h - 1, 1), (x + y) * 127 // max(w + h - 2, 1), 255)
            elif name == "noise":
                p = (rnd.randrange(256), rnd.randrange(256), rnd.randrange(256), 255)
            elif name == "alphagrad":
                p = (200, (x * 7) & 255, 50, x * 255 // max(w - 1, 1))
            elif name == "alphanoise":
                p = (rnd.randrange(256), rnd.randrange(256), rnd.randrange(256), rnd.randrange(256))
            elif name == "binalpha":
                p = (x * 30 & 255, y * 30 & 255, 90, 255 if (x // 3 + y // 3) % 2 else 0)
            elif name == "transparent":
                p = (rnd.randrange(256), 0, 0, 0)
            elif name.startswith("pal"):
                n = int(name[3:])
                p = pal[(x * 3 + y * 5 + rnd.randrange(2)) % n]
            elif name == "checker":
                p = (255, 255, 255, 255) if (x + y) % 2 else (0, 0, 0, 255)
            elif name == "solid":
                p = (12, 200, 99, 255)
            else:
                raise ValueError(name)
            px.append(p)
    return px

sizes = [(1, 1), (2, 2), (1, 7), (7, 1), (3, 5), (8, 8), (13, 17), (16, 16), (31, 9), (33, 33), (64, 48), (100, 37), (128, 128)]
pats = ["grad", "noise", "alphagrad", "alphanoise", "binalpha", "transparent", "pal2", "pal4", "pal16", "pal200", "checker", "solid"]
for (w, h) in sizes:
    for pat in pats:
        if w * h > 4096 and pat in ("noise", "alphanoise"):
            continue
        px = pattern(pat, w, h)
        base = f"{out}/{pat}_{w}x{h}"
        if any(p[3] != 255 for p in px):
            write_pam(base + ".pam", w, h, px)
        else:
            write_ppm(base + ".ppm", w, h, px)
