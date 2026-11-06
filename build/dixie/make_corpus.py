#!/usr/bin/env python3
"""Generate build/dixie/corpus/{valid,corrupt} (deterministic, seeded).

  python3 -I make_corpus.py [--seed 1] [--only valid|corrupt]

valid/ext/      symlinks to lossy files ('VP8 ' chunk) of
                corpus-src/libwebp-test-data and image-webp/tests/images
valid/cwebp/    cwebp output with varied options from small sources
valid/enc/      tools/vp8enc output (libwebp encoder API: config.partitions
                0..3 = 1/2/4/8 token partitions, plus filter/segment options)
valid/bench/    ~1 MP files for benchmarking (bench_1MP_*.webp)
sources/        PPM sources (synthetic + converted PNGs)
corrupt/        mutated raw VP8 payloads (*.vp8), name encodes source+mutation
"""
import argparse, math, os, random, shutil, struct, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
TOOLS = os.path.join(ROOT, "build", "libwebp-tools")
CWEBP = os.path.join(TOOLS, "cwebp")
DWEBP = os.path.join(TOOLS, "dwebp")
VP8ENC = os.path.join(HERE, "tools", "vp8enc")
C = os.path.join(HERE, "corpus")


def sh(cmd):
    p = subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
    if p.returncode != 0:
        raise RuntimeError("%s: %s" % (" ".join(cmd), p.stderr.decode()[-300:]))


def write_ppm(path, w, h, rgb):
    with open(path, "wb") as f:
        f.write(b"P6\n%d %d\n255\n" % (w, h))
        f.write(bytes(rgb))


def clamp(v):
    return 0 if v < 0 else 255 if v > 255 else int(v)


def synth(kind, w, h, rnd):
    px = bytearray(w * h * 3)
    if kind == "noise":
        return bytearray(rnd.randbytes(w * h * 3))
    a, b, c = rnd.random() * 0.3, rnd.random() * 0.3, rnd.random() * 6
    cell = rnd.choice([1, 2, 3, 4, 7, 8, 16])
    rects = [(rnd.randrange(w), rnd.randrange(h), rnd.randrange(1, 6), rnd.randrange(1, 9))
             for _ in range(max(1, w * h // 60))] if kind == "text" else []
    col = [rnd.randrange(256) for _ in range(3)]
    if kind == "text":
        px = bytearray(b"\xf0" * (w * h * 3))
        for x0, y0, rw, rh in rects:
            for y in range(y0, min(h, y0 + rh)):
                for x in range(x0, min(w, x0 + rw)):
                    i = (y * w + x) * 3
                    px[i:i + 3] = b"\x10\x10\x10"
        return px
    for y in range(h):
        for x in range(w):
            i = (y * w + x) * 3
            if kind == "gradient":
                v = (x * 255 // max(1, w - 1), y * 255 // max(1, h - 1),
                     (x + y) * 255 // max(1, w + h - 2))
            elif kind == "checker":
                on = ((x // cell) + (y // cell)) & 1
                v = (255 * on, 255 * on, 255 - 255 * on)
            elif kind == "solid":
                v = col
            elif kind == "photo":
                s = 128 + 60 * math.sin(a * x + c) + 50 * math.cos(b * y) + rnd.gauss(0, 12)
                v = (clamp(s), clamp(s * 0.8 + 30 * math.sin(0.05 * x * y / max(1, w))),
                     clamp(255 - s + rnd.gauss(0, 8)))
            elif kind == "edges":
                v = (255 if (x * 7 + y * 3) % 23 < 11 else 0, 255 if x > w // 2 else 0,
                     255 if (x - w / 2) ** 2 + (y - h / 2) ** 2 < (min(w, h) / 3) ** 2 else 0)
            px[i:i + 3] = bytes(v)
    return px


SIZES = [(1, 1), (1, 17), (17, 1), (2, 2), (3, 5), (15, 15), (16, 16), (17, 17),
         (31, 33), (33, 47), (64, 64), (100, 75), (128, 128), (255, 3), (3, 255),
         (256, 256), (129, 67), (200, 150), (47, 211), (240, 16)]
KINDS = ["gradient", "noise", "text", "checker", "solid", "photo", "edges"]


def make_sources(rnd):
    d = os.path.join(C, "sources")
    os.makedirs(d, exist_ok=True)
    srcs = []
    for (w, h) in SIZES:
        for k in KINDS:
            if w * h < 300 or rnd.random() < 0.45:
                p = os.path.join(d, "syn_%s_%dx%d.ppm" % (k, w, h))
                write_ppm(p, w, h, synth(k, w, h, rnd))
                srcs.append((p, w, h))
    # real images -> PPM via lossless webp round trip
    real = ["corpus-src/libwebp-test-data/peak.png", "corpus-src/libwebp-test-data/grid.png",
            "libwebp/examples/test_ref.ppm"] + \
           ["image-webp/tests/reference/gallery1/%d.png" % i for i in range(1, 6)] + \
           ["image-webp/tests/reference/gallery2/%d_webp_a.png" % i for i in range(1, 6)] + \
           ["image-webp/tests/reference/regression/%s.png" % n for n in
            ("color_index", "tiny", "lossless_indexed_4bit_palette")]
    big = []
    for r in real:
        src = os.path.join(ROOT, r)
        name = r.replace("/", "_").rsplit(".", 1)[0]
        tmp = os.path.join(d, name + ".ll.webp")
        p = os.path.join(d, "real_" + name + ".ppm")
        sh([CWEBP, "-quiet", "-lossless", "-exact", src, "-o", tmp])
        sh([DWEBP, "-quiet", "-ppm", tmp, "-o", p])
        os.unlink(tmp)
        with open(p, "rb") as f:
            hdr = f.read(32).split()
        w, h = int(hdr[1]), int(hdr[2])
        (big if w * h > 256 * 256 else srcs).append((p, w, h))
    return srcs, big


def cwebp_args(rnd, w, h, big):
    a = ["-quiet", "-q", str(rnd.choice([0, 1, 5, 10, 25, 40, 50, 60, 75, 80, 90, 95, 99, 100]))]
    a += ["-m", str(rnd.randrange(7))]
    if rnd.random() < 0.5:
        a += ["-f", str(rnd.choice([0, 1, 10, 30, 60, 90, 100]))]
    if rnd.random() < 0.4:
        a += ["-sharpness", str(rnd.randrange(8))]
    if rnd.random() < 0.5:
        a += [rnd.choice(["-strong", "-nostrong"])]
    if rnd.random() < 0.5:
        a += ["-segments", str(rnd.randrange(1, 5))]
    if rnd.random() < 0.5:
        a += ["-sns", str(rnd.choice([0, 25, 50, 80, 100]))]
    if rnd.random() < 0.2:
        a += ["-partition_limit", str(rnd.choice([0, 50, 100]))]
    if rnd.random() < 0.2:
        a += ["-pass", str(rnd.randrange(1, 11))]
    if rnd.random() < 0.2:
        a += ["-af"]
    if rnd.random() < 0.15:
        a += ["-sharp_yuv"]
    if rnd.random() < 0.1:
        a += ["-pre", str(rnd.randrange(0, 3))]
    if big or rnd.random() < 0.3:
        # crop / resize to an odd size
        if rnd.random() < 0.5 and w > 2 and h > 2:
            cw, ch = rnd.randrange(1, min(w, 256) + 1), rnd.randrange(1, min(h, 256) + 1)
            a += ["-crop", str(rnd.randrange(w - cw + 1)), str(rnd.randrange(h - ch + 1)), str(cw), str(ch)]
        else:
            a += ["-resize", str(rnd.choice([1, 2, 7, 15, 17, 33, 63, 65, 100, 127, 255])),
                  str(rnd.choice([1, 3, 9, 16, 31, 47, 64, 99, 130, 250]))]
    return a


def enc_args(rnd):
    return ["q=%d" % rnd.choice([0, 5, 20, 50, 75, 90, 100]), "m=%d" % rnd.randrange(7),
            "partitions=%d" % rnd.randrange(4), "segments=%d" % rnd.randrange(1, 5),
            "sns=%d" % rnd.choice([0, 50, 100]), "f=%d" % rnd.choice([0, 20, 60, 100]),
            "sharpness=%d" % rnd.randrange(8), "strong=%d" % rnd.randrange(2),
            "af=%d" % (rnd.random() < 0.2), "pass=%d" % rnd.randrange(1, 4)]


def has_vp8(path):
    d = open(path, "rb").read()
    return b"VP8 " in d[12:] and d[:4] == b"RIFF"


def make_valid(rnd):
    v = os.path.join(C, "valid")
    shutil.rmtree(v, ignore_errors=True)
    for s in ("ext", "cwebp", "enc", "bench"):
        os.makedirs(os.path.join(v, s))
    n_ext = 0
    for base in ("corpus-src/libwebp-test-data", "image-webp/tests/images"):
        for dp, dn, fn in os.walk(os.path.join(ROOT, base)):
            for f in sorted(fn):
                p = os.path.join(dp, f)
                if f.endswith(".webp") and has_vp8(p):
                    rel = os.path.relpath(p, ROOT).replace("/", "__")
                    os.symlink(p, os.path.join(v, "ext", rel))
                    n_ext += 1
    srcs, big = make_sources(rnd)
    allsrc = srcs + big
    n = 0
    for i in range(300):
        p, w, h = rnd.choice(allsrc)
        args = cwebp_args(rnd, w, h, (p, w, h) in big)
        out = os.path.join(v, "cwebp", "c%03d_%s.webp" % (i, os.path.basename(p)[:-4]))
        try:
            sh([CWEBP] + args + [p, "-o", out])
            with open(out + ".args", "w") as f:
                f.write(" ".join(args) + "\n")
            n += 1
        except RuntimeError as e:
            print("cwebp failed:", e, file=sys.stderr)
    m = 0
    for i in range(160):
        p, w, h = rnd.choice(srcs)
        args = enc_args(rnd)
        if i < 8:   # make sure every partition count appears on multi-row images
            p, w, h = next(s for s in srcs if s[1] >= 64 and s[2] >= 64 and "real_" in s[0])
            args = [a if not a.startswith("partitions=") else "partitions=%d" % (i % 4) for a in args]
        out = os.path.join(v, "enc", "e%03d_%s_%s.webp" % (
            i, [a for a in args if a.startswith("partitions=")][0].replace("=", ""),
            os.path.basename(p)[:-4]))
        try:
            sh([VP8ENC, p, out] + args)
            with open(out + ".args", "w") as f:
                f.write(" ".join(args) + "\n")
            m += 1
        except RuntimeError as e:
            print("vp8enc failed:", e, file=sys.stderr)
    # benchmarks (~1 MP)
    bd = os.path.join(C, "sources")
    sp = os.path.join(bd, "syn_photo_1024x1024.ppm")
    write_ppm(sp, 1024, 1024, synth("photo", 1024, 1024, rnd))
    g = os.path.join(ROOT, "image-webp/tests/reference/gallery1/4.png")
    sh([CWEBP, "-quiet", "-q", "75", sp, "-o", os.path.join(v, "bench", "bench_1MP_synthphoto_q75.webp")])
    sh([CWEBP, "-quiet", "-q", "90", "-resize", "1024", "1024", g, "-o",
        os.path.join(v, "bench", "bench_1MP_gallery1-4_q90.webp")])
    sh([VP8ENC, sp, os.path.join(v, "bench", "bench_1MP_synthphoto_q50_4part.webp"), "q=50", "partitions=2"])
    sh([CWEBP, "-quiet", "-q", "100", "-m", "6", "-resize", "1024", "1024", g, "-o",
        os.path.join(v, "bench", "bench_1MP_gallery1-4_q100.webp")])
    print("valid: ext=%d cwebp=%d enc=%d bench=4" % (n_ext, n, m))


# ------------------------------------------------------------------ corrupt
def payload_of(path):
    d = open(path, "rb").read()
    off = 12
    while off + 8 <= len(d):
        sz = struct.unpack_from("<I", d, off + 4)[0]
        if d[off:off + 4] == b"VP8 ":
            return d[off + 8: off + 8 + sz]
        off += 8 + sz + (sz & 1)
    return None


def dims_ok(p):
    if len(p) < 10:
        return True
    raw = struct.unpack_from("<I", p, 6)[0]
    return (raw & 0x3FFF) * ((raw >> 16) & 0x3FFF) <= 2_000_000


def mutations(p, rnd):
    """Yield (tag, mutated_bytes)."""
    n = len(p)
    p0 = (p[0] | p[1] << 8 | p[2] << 16) >> 5
    tp = 10 + p0            # start of partition-size table / token data

    def flip(b, bit):
        q = bytearray(p); q[b] ^= 1 << bit; return bytes(q)

    def put(b, v):
        q = bytearray(p); q[b] = v; return bytes(q)

    # frame tag: every bit of bytes 0..2
    for byte in range(3):
        for bit in range(8):
            yield "tag_b%d_bit%d" % (byte, bit), flip(byte, bit)
    # first-partition size set to specific values
    for v in (0, 1, 2, p0 - 1, p0 + 1, n - 10, n - 9, n, (1 << 19) - 1):
        if 0 <= v < (1 << 19):
            q = bytearray(p)
            raw = (q[0] | q[1] << 8 | q[2] << 16) & 0x1F | (v << 5)
            q[0:3] = bytes([raw & 255, raw >> 8 & 255, raw >> 16])
            yield "p0size_%d" % v, bytes(q)
    # start code
    for b in (3, 4, 5):
        yield "start_b%d_flip" % b, flip(b, rnd.randrange(8))
    # width/height/scale: every bit of bytes 6..9
    for byte in range(6, 10):
        for bit in range(8):
            yield "dim_b%d_bit%d" % (byte, bit), flip(byte, bit)
    # first ~20 bytes of partition 0 (bool-coded header)
    for b in range(10, min(30, tp)):
        for bit in rnd.sample(range(8), 3):
            yield "hdr_b%d_bit%d" % (b, bit), flip(b, bit)
        yield "hdr_b%d_ff" % b, put(b, 0xFF)
        yield "hdr_b%d_00" % b, put(b, 0x00)
    # partition-size table and bytes right after partition 0
    for k in range(1, 8):
        for val in (b"\x00", b"\xff", None):
            q = bytearray(p)
            for j in range(tp, min(n, tp + 3 * k)):
                q[j] = val[0] if val else rnd.randrange(256)
            yield "ptab_k%d_%s" % (k, val.hex() if val else "rnd"), bytes(q)
    for j in range(tp, min(n, tp + 24)):
        yield "ptab_b%d_flip%d" % (j - tp, j % 8), flip(j, rnd.randrange(8))
    # token data: middle and end
    if n > tp + 4:
        for _ in range(12):
            b = rnd.randrange(tp, n)
            yield "tok_b%d_bit" % b, flip(b, rnd.randrange(8))
        for _ in range(4):
            b = rnd.randrange(tp, n)
            yield "tok_b%d_%s" % (b, "ff"), put(b, 0xFF)
        for b in (n - 1, n - 2):
            yield "tok_end%d_rnd" % (n - b), put(b, rnd.randrange(256))
    # random single/multi bit flips anywhere
    for k in (1, 2, 4, 8, 16):
        for _ in range(3):
            q = bytearray(p)
            for _ in range(k):
                q[rnd.randrange(n)] ^= 1 << rnd.randrange(8)
            yield "rflip%d_%d" % (k, rnd.randrange(10**6)), bytes(q)
    for _ in range(4):
        q = bytearray(p)
        for _ in range(rnd.randrange(1, 6)):
            q[rnd.randrange(n)] = rnd.choice([0, 255, rnd.randrange(256)])
        yield "rbyte_%d" % rnd.randrange(10**6), bytes(q)
    # truncations
    cuts = {0, 1, 2, 3, 5, 9, 10, 11, 12, 15, tp - 1, tp, tp + 1, tp + 2, tp + 3, tp + 6,
            n - 1, n - 2, n // 2, 10 + p0 // 2}
    cuts |= {rnd.randrange(n) for _ in range(4)}
    for c in sorted(cuts):
        if 0 <= c < n:
            yield "trunc_%d" % c, p[:c]
    # appended garbage
    yield "append_00x16", p + b"\0" * 16
    yield "append_ffx16", p + b"\xff" * 16
    yield "append_rnd100", p + rnd.randbytes(100)


def make_corrupt(rnd):
    cdir = os.path.join(C, "corrupt")
    shutil.rmtree(cdir, ignore_errors=True)
    os.makedirs(cdir)
    v = os.path.join(C, "valid")
    pool = []
    for sub in ("cwebp", "enc", "ext"):
        for f in sorted(os.listdir(os.path.join(v, sub))):
            if not f.endswith(".webp"):
                continue
            p = payload_of(os.path.join(v, sub, f))
            if p and len(p) >= 10 and len(p) <= 6000:
                raw = struct.unpack_from("<I", p, 6)[0]
                if (raw & 0x3FFF) * ((raw >> 16) & 0x3FFF) <= 160 * 160:
                    pool.append((sub + "_" + f[:-5], p, (raw >> 16) & 0x3FFF))
    rnd.shuffle(pool)
    # variety: 18 multi-partition streams with >= 2 MB rows, 22 others
    multi = [t for t in pool if "_partitions" in t[0] and "_partitions0" not in t[0] and t[2] > 16]
    other = [t for t in pool if t not in multi]
    chosen = [(a, b) for a, b, _ in multi[:18] + other[:22]]
    total = 0
    skipped = 0
    seen = set()
    for name, p in chosen:
        for tag, q in mutations(p, rnd):
            if q == p or (name, q) in seen:
                continue
            seen.add((name, q))
            if not dims_ok(q):
                skipped += 1
                continue
            with open(os.path.join(cdir, "%s__%s.vp8" % (name, tag)), "wb") as f:
                f.write(q)
            total += 1
    print("corrupt: %d files from %d sources (%d skipped: >2MP dims)" % (total, len(chosen), skipped))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--only", choices=["valid", "corrupt"])
    a = ap.parse_args()
    if a.only != "corrupt":
        make_valid(random.Random(a.seed))
    if a.only != "valid":
        make_corrupt(random.Random(a.seed + 1000))


if __name__ == "__main__":
    main()
