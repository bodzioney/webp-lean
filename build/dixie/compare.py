#!/usr/bin/env python3
"""Differential harness for VP8 key-frame decoders.

Every decoder produces the common output format
    u32 LE width, u32 LE height, Y (w*h), U ((w+1)/2*(h+1)/2), V (same)
and is classified per input file as
    ok       exit 0 and an output file was written
    reject   clean rejection (exit 1 for dixie/lean; nonzero exit for dwebp)
    crash    any other exit code / signal / exit 0 without output
    timeout  per-file timeout exceeded

Usage:
  python3 -I compare.py --decoders dixie,dwebp --files corpus/valid corpus/corrupt \
      [--jobs 32] [--timeout 20] [--report reports/run1] [--examples 20]
  --files takes directories (recursive: *.webp, *.vp8, *.bin), plain files, or
  list files ending in .txt / .list (one path per line, '#' comments).

Writes <report>.txt (summary + example file lists) and <report>.json (per-file
results).  Decoders (built in):
  dixie, dixie_asan, dixie_iconv  RFC 6386 reference decoder (build.sh)
  dwebp       libwebp dwebp -yuv on exactly the VP8 payload (raw bitstream if
              >= 12 bytes, else re-wrapped in a minimal RIFF/WEBP)
  dwebp_noasm as dwebp, with -noasm (plain C DSP code instead of SSE2/AVX2)
  dwebp_riff  dwebp on the payload re-wrapped in a minimal RIFF (pad byte of
              odd-sized payloads is visible to libwebp's VP8 decoder!)
  dwebp_file  libwebp dwebp -yuv on the original file as-is
  libwebp_vp8 tools/vp8err: libwebp internal VP8 decoder, accept/reject + error
              message only (no planes)
  lean_spec, lean_impl, lean_libwebp   vp8-check <in> frame <out> <mode>
Sanitizer reports (UBSan 'runtime error:' / AddressSanitizer) are collected for
every decoder whose stderr contains them and summarised by source location.
"""
import argparse, hashlib, json, os, re, shutil, signal, struct, subprocess, sys
import tempfile, time
from collections import Counter, defaultdict
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
DWEBP = os.path.join(ROOT, "build", "libwebp-tools", "dwebp")
LEAN = os.path.join(ROOT, "webp-lean", ".lake", "build", "bin", "vp8-check")

SAN_ENV = {
    "ASAN_OPTIONS": "exitcode=86:abort_on_error=0:detect_leaks=1:"
                    "allocator_may_return_null=1:symbolize=1",
    "UBSAN_OPTIONS": "print_stacktrace=1:halt_on_error=0:report_error_type=1",
}


# ---------------------------------------------------------------- input utils
def find_vp8(d, off, end):
    """First 'VP8 ' chunk payload (offset, size) in d[off:end], DFS into ANMF."""
    while off + 8 <= end:
        fourcc = d[off:off + 4]
        sz = struct.unpack_from("<I", d, off + 4)[0]
        pay = off + 8
        if fourcc == b"VP8 ":
            return pay, min(sz, end - pay)
        if fourcc == b"ANMF":
            r = find_vp8(d, pay + 16, min(pay + sz, end))
            if r:
                return r
        off = pay + sz + (sz & 1)
    return None


def vp8_payload(data):
    """Same input convention as dixie_dec / vp8-check. None = no VP8 chunk."""
    if len(data) >= 12 and data[:4] == b"RIFF" and data[8:12] == b"WEBP":
        r = find_vp8(data, 12, len(data))
        if r is None:
            return None
        return data[r[0]:r[0] + r[1]]
    return data


def wrap_riff(payload):
    pad = b"\0" if len(payload) & 1 else b""
    chunk = b"VP8 " + struct.pack("<I", len(payload)) + payload + pad
    return b"RIFF" + struct.pack("<I", 4 + len(chunk)) + b"WEBP" + chunk


# ------------------------------------------------------------- decoder defs
def run(cmd, timeout, env=None):
    e = dict(os.environ)
    if env:
        e.update(env)
    t0 = time.time()
    try:
        p = subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE,
                           timeout=timeout, env=e)
        return p.returncode, p.stderr.decode("latin-1"), time.time() - t0
    except subprocess.TimeoutExpired as ex:
        err = ex.stderr.decode("latin-1") if ex.stderr else ""
        return None, err, time.time() - t0


def classify_std(rc, out):
    """dixie / lean convention: 0+output = ok, 1 = reject, else crash."""
    if rc is None:
        return "timeout"
    if rc == 0:
        return "ok" if os.path.exists(out) else "crash"
    if rc == 1:
        return "reject"
    return "crash"


def dec_cmd(binary, env=None):
    def f(inp, out, tmp, timeout):
        rc, err, dt = run([binary, inp, out], timeout, env)
        return classify_std(rc, out), rc, err, dt
    return f


def dec_lean(mode):
    def f(inp, out, tmp, timeout):
        rc, err, dt = run([LEAN, inp, "frame", out, mode], timeout)
        return classify_std(rc, out), rc, err, dt
    return f


def dec_dwebp(mode, noasm=False):
    """mode: 'raw'  payload passed as a raw VP8 bitstream (no RIFF) when it is
                    >= 12 bytes (libwebp's minimum input size), else RIFF-wrapped;
                    libwebp then sees exactly the payload bytes.
             'riff' payload always re-wrapped in a minimal RIFF/WEBP; NOTE libwebp
                    hands the VP8 decoder everything up to the end of the buffer,
                    so for odd sizes the RIFF pad byte becomes visible to it.
             'file' the original file as-is."""
    def f(inp, out, tmp, timeout):
        data = open(inp, "rb").read()
        payload = vp8_payload(data)
        if payload is None:
            return "reject", 1, "error: harness no VP8 chunk\n", 0.0
        if mode == "file":
            src = inp
        else:
            src = os.path.join(tmp, "dwebp_in.webp")
            with open(src, "wb") as fh:
                if mode == "raw" and len(payload) >= 12:
                    fh.write(payload)
                else:
                    fh.write(wrap_riff(payload))
        yuv = os.path.join(tmp, "dwebp_out.yuv")
        rc, err, dt = run([DWEBP, "-nodither"] + (["-noasm"] if noasm else []) +
                          ["-yuv", src, "-o", yuv], timeout)
        if rc is None:
            return "timeout", rc, err, dt
        if rc < 0:
            return "crash", rc, err, dt
        if rc != 0 or not os.path.exists(yuv):
            return "reject", rc, err, dt
        if len(payload) < 10:
            return "crash", rc, err + "harness: dwebp ok on <10 byte payload\n", dt
        raw = struct.unpack_from("<I", payload, 6)[0]
        w, h = raw & 0x3FFF, (raw >> 16) & 0x3FFF
        need = w * h + 2 * ((w + 1) // 2) * ((h + 1) // 2)
        body = open(yuv, "rb").read()
        if len(body) < need:
            return "crash", rc, err + "harness: short dwebp yuv output\n", dt
        with open(out, "wb") as fh:
            fh.write(struct.pack("<II", w, h) + body[:need])
        return "ok", rc, err, dt
    return f


def dec_vp8err():
    """tools/vp8err: libwebp's internal VP8GetHeaders+VP8Decode on exactly the
    payload; status + libwebp error message only (no planes: 'ok' outputs are
    reported with a dummy hash, so only use it for accept/reject comparisons)."""
    def f(inp, out, tmp, timeout):
        rc, err, dt = 0, "", 0.0
        e = dict(os.environ)
        t0 = time.time()
        try:
            p = subprocess.run([os.path.join(HERE, "tools", "vp8err"), inp],
                               capture_output=True, timeout=timeout)
        except subprocess.TimeoutExpired:
            return "timeout", None, "", time.time() - t0
        msg = p.stdout.decode("latin-1").strip()
        if p.returncode == 0:
            with open(out, "wb") as fh:
                fh.write(b"vp8err-ok")
            return "ok", 0, msg, time.time() - t0
        if p.returncode == 1:
            return "reject", 1, "error: " + msg.split(" ", 1)[1] + "\n", time.time() - t0
        return "crash", p.returncode, msg + p.stderr.decode("latin-1"), time.time() - t0
    return f


HERE_BIN = lambda n: os.path.join(HERE, n)
DECODERS = {
    "dixie": dec_cmd(HERE_BIN("dixie_dec")),
    "dixie_asan": dec_cmd(HERE_BIN("dixie_dec_asan"), SAN_ENV),
    "dixie_iconv": dec_cmd(HERE_BIN("dixie_dec_iconv"), SAN_ENV),
    "dixie_nosetjmp": dec_cmd(HERE_BIN("dixie_dec_asan"),
                              dict(SAN_ENV, DIXIE_NO_SETJMP="1")),
    "dwebp": dec_dwebp("raw"),
    "dwebp_noasm": dec_dwebp("raw", noasm=True),
    "dwebp_riff": dec_dwebp("riff"),
    "dwebp_file": dec_dwebp("file"),
    "libwebp_vp8": dec_vp8err(),
    "lean_spec": dec_lean("spec"),
    "lean_impl": dec_lean("impl"),
    "lean_libwebp": dec_lean("libwebp"),
}

# --------------------------------------------------------- sanitizer parsing
UB_RE = re.compile(r"^(\S+?):(\d+):(\d+): runtime error: (.*)$", re.M)
ASAN_RE = re.compile(r"^SUMMARY: AddressSanitizer: (\S+) (\S+)", re.M)
ASAN_ERR = re.compile(r"ERROR: (AddressSanitizer|LeakSanitizer): (\S+)")


def norm_msg(m):
    m = re.sub(r"-?\b\d+\b", "N", m)
    m = re.sub(r"0x[0-9a-f]+", "ADDR", m)
    return m[:120]


def sanitizer_keys(err):
    """-> {normalised key: first raw message}"""
    keys = {}
    for m in UB_RE.finditer(err):
        keys.setdefault("UBSan %s:%s:%s: %s" % (os.path.basename(m.group(1)), m.group(2),
                                                m.group(3), norm_msg(m.group(4))), m.group(0))
    for m in ASAN_RE.finditer(err):
        keys.setdefault("ASan %s %s" % (m.group(1), os.path.basename(m.group(2))), m.group(0))
    if not ASAN_RE.search(err):
        for m in ASAN_ERR.finditer(err):
            keys.setdefault("%s %s" % (m.group(1), m.group(2)), m.group(0))
    return keys


def error_key(name, status, rc, err):
    if status != "reject":
        return None
    if name.startswith("dwebp"):
        m = re.search(r"Status: (\d+\(\w+\))", err)
        if m:
            return m.group(1)
        if "harness" in err:
            return err.strip().splitlines()[-1]
        return "rc=%s %s" % (rc, (err.strip().splitlines() or [""])[-1][:80])
    for line in err.splitlines():
        if line.startswith("error:"):
            return line[6:].strip()[:120]
    return (err.strip().splitlines() or ["?"])[-1][:120]


# ---------------------------------------------------------------- comparison
def read_planes(path):
    d = open(path, "rb").read()
    if len(d) < 8:
        return None
    w, h = struct.unpack_from("<II", d, 0)
    cw, ch = (w + 1) // 2, (h + 1) // 2
    if len(d) != 8 + w * h + 2 * cw * ch:
        return (w, h, None)
    return (w, h, d[8:])


def diff_info(pa, pb):
    a, b = read_planes(pa), read_planes(pb)
    if a is None or b is None or a[2] is None or b[2] is None:
        return {"kind": "malformed_output"}
    if (a[0], a[1]) != (b[0], b[1]):
        return {"kind": "dims", "a": [a[0], a[1]], "b": [b[0], b[1]]}
    w, h = a[0], a[1]
    ys = w * h
    cs = ((w + 1) // 2) * ((h + 1) // 2)
    da, db = a[2], b[2]
    first = None
    ndiff = 0
    maxd = 0
    planes = set()
    for off, plane, pw in ((0, "Y", w), (ys, "U", (w + 1) // 2), (ys + cs, "V", (w + 1) // 2)):
        n = ys if plane == "Y" else cs
        sa, sb = da[off:off + n], db[off:off + n]
        if sa == sb:
            continue
        planes.add(plane)
        for i in range(n):
            x, y = sa[i], sb[i]
            if x != y:
                ndiff += 1
                maxd = max(maxd, abs(x - y))
                if first is None:
                    first = [plane, i % pw, i // pw, x, y]
    return {"kind": "pixels", "ndiff": ndiff, "maxdiff": maxd,
            "planes": "".join(sorted(planes)), "first": first}


def process(args):
    path, names, timeout, workdir = args
    tmp = tempfile.mkdtemp(prefix="cmp_", dir=workdir)
    res = {"file": path, "dec": {}, "pairs": {}}
    outs = {}
    try:
        for n in names:
            out = os.path.join(tmp, n + ".out")
            status, rc, err, dt = DECODERS[n](path, out, tmp, timeout)
            r = {"status": status, "rc": rc, "time": round(dt, 3)}
            if status == "ok":
                with open(out, "rb") as fh:
                    content = fh.read()
                r["sha1"] = hashlib.sha1(content).hexdigest()
                if len(content) >= 8:
                    r["wh"] = list(struct.unpack_from("<II", content, 0))
                outs[n] = out
            ek = error_key(n, status, rc, err)
            if ek:
                r["err"] = ek
            if status in ("crash", "timeout"):
                r["stderr_tail"] = err[-1500:]
            sk = sanitizer_keys(err)
            if sk:
                r["san"] = sorted(sk)
                r["san_raw"] = sk
                if any(not k.startswith("UBSan") for k in sk):
                    r["stderr_tail"] = err[-4000:]
            res["dec"][n] = r
        for i, a in enumerate(names):
            for b in names[i + 1:]:
                ra, rb = res["dec"][a], res["dec"][b]
                if ra["status"] == "ok" and rb["status"] == "ok":
                    if "libwebp_vp8" in (a, b):
                        cat = "both_ok_nocmp"
                    elif ra["sha1"] == rb["sha1"]:
                        cat = "both_ok_same"
                    else:
                        cat = "both_ok_diff"
                        res.setdefault("diff", {})["%s|%s" % (a, b)] = diff_info(outs[a], outs[b])
                elif ra["status"] in ("crash", "timeout") or rb["status"] in ("crash", "timeout"):
                    cat = "crash_or_timeout"
                elif ra["status"] == "ok":
                    cat = "A_ok_B_reject"
                elif rb["status"] == "ok":
                    cat = "A_reject_B_ok"
                else:
                    cat = "both_reject"
                res["pairs"]["%s|%s" % (a, b)] = cat
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    return res


def mutation_class(path):
    """make_corpus.py corrupt names: <source>__<tag>.vp8 -> tag class."""
    b = os.path.basename(path)
    if "__" not in b or not b.endswith(".vp8"):
        return ""
    tag = b.rsplit("__", 1)[1][:-4]
    return tag.split("_")[0]


def collect_files(specs):
    files = []
    for s in specs:
        if os.path.isdir(s):
            for dp, dn, fn in os.walk(s, followlinks=True):
                dn.sort()
                for f in sorted(fn):
                    if f.endswith((".webp", ".vp8", ".bin")):
                        files.append(os.path.join(dp, f))
        elif s.endswith((".txt", ".list")):
            base = os.path.dirname(os.path.abspath(s))
            for line in open(s):
                line = line.strip()
                if line and not line.startswith("#"):
                    if not os.path.isabs(line) and not os.path.exists(line):
                        line = os.path.join(base, line)
                    files.append(line)
        else:
            files.append(s)
    return files


WORKDIR = None
CATS = ["both_ok_same", "both_ok_nocmp", "both_ok_diff", "A_ok_B_reject", "A_reject_B_ok",
        "both_reject", "crash_or_timeout"]


def main():
    global WORKDIR
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--decoders", default="dixie,dwebp")
    ap.add_argument("--files", nargs="+", required=True)
    ap.add_argument("--jobs", type=int, default=min(32, os.cpu_count() or 4))
    ap.add_argument("--timeout", type=float, default=20.0)
    ap.add_argument("--report", default=os.path.join(HERE, "reports", "report"))
    ap.add_argument("--examples", type=int, default=20,
                    help="example files listed per category in the .txt report")
    ap.add_argument("--tmpdir", default=None)
    a = ap.parse_args()
    names = [n.strip() for n in a.decoders.split(",") if n.strip()]
    for n in names:
        if n not in DECODERS:
            sys.exit("unknown decoder %s (known: %s)" % (n, ", ".join(DECODERS)))
    files = collect_files(a.files)
    os.makedirs(os.path.dirname(os.path.abspath(a.report)), exist_ok=True)
    WORKDIR = tempfile.mkdtemp(prefix="compare_", dir=a.tmpdir)
    t0 = time.time()
    results = []
    with Pool(a.jobs) as pool:
        for i, r in enumerate(pool.imap_unordered(process, [(f, names, a.timeout, WORKDIR) for f in files], chunksize=4)):
            results.append(r)
            if (i + 1) % 500 == 0:
                print("%d/%d files (%.0fs)" % (i + 1, len(files), time.time() - t0), flush=True)
    shutil.rmtree(WORKDIR, ignore_errors=True)
    results.sort(key=lambda r: r["file"])

    L = []
    L.append("files: %d  decoders: %s  time: %.1fs" % (len(files), ",".join(names), time.time() - t0))
    L.append("")
    L.append("== per-decoder status ==")
    for n in names:
        c = Counter(r["dec"][n]["status"] for r in results)
        L.append("  %-14s %s" % (n, "  ".join("%s=%d" % kv for kv in sorted(c.items()))))
    L.append("")
    L.append("== per-decoder rejection reasons ==")
    for n in names:
        c = Counter(r["dec"][n].get("err") for r in results if r["dec"][n]["status"] == "reject")
        if c:
            L.append("  %s:" % n)
            for k, v in c.most_common():
                L.append("    %6d  %s" % (v, k))
    L.append("")
    for i, A in enumerate(names):
        for B in names[i + 1:]:
            key = "%s|%s" % (A, B)
            by = defaultdict(list)
            for r in results:
                by[r["pairs"][key]].append(r)
            L.append("== pair A=%s B=%s ==" % (A, B))
            for c in CATS:
                L.append("  %-18s %d" % (c, len(by[c])))
            for c in CATS[1:]:
                if c in ("both_reject", "both_ok_nocmp") or not by[c]:
                    continue
                L.append("  -- %s (examples) --" % c)
                # sub-group by reason so categories are easy to read
                sub = defaultdict(list)
                for r in by[c]:
                    mclass = mutation_class(r["file"])
                    if c == "A_ok_B_reject":
                        k = "B: %s" % r["dec"][B].get("err")
                    elif c == "A_reject_B_ok":
                        k = "A: %s" % r["dec"][A].get("err")
                    elif c == "both_ok_diff":
                        d = r["diff"][key]
                        k = d["kind"] + ("" if d["kind"] != "pixels" else " planes=" + d["planes"])
                    else:
                        k = "A=%s B=%s" % (r["dec"][A]["status"], r["dec"][B]["status"])
                    sub[k + ("  <" + mclass + ">" if mclass else "")].append(r)
                for k, rs in sorted(sub.items(), key=lambda kv: -len(kv[1])):
                    L.append("    [%d] %s" % (len(rs), k))
                    for r in sorted(rs, key=lambda r: os.path.getsize(r["file"]) if os.path.exists(r["file"]) else 0)[:a.examples]:
                        extra = ""
                        if c == "both_ok_diff":
                            extra = " " + json.dumps(r["diff"][key])
                        L.append("       %s%s" % (r["file"], extra))
            L.append("")
    san = defaultdict(list)
    san_raw = {}
    for r in results:
        for n in names:
            for k in r["dec"][n].get("san", []):
                san[(n, k)].append(r["file"])
                san_raw.setdefault((n, k), r["dec"][n]["san_raw"][k])
    L.append("== sanitizer reports (decoder, location: message) -> #files, smallest examples ==")
    for (n, k), fs in sorted(san.items(), key=lambda kv: (kv[0][0], -len(kv[1]))):
        fs = sorted(fs, key=lambda f: os.path.getsize(f) if os.path.exists(f) else 0)
        L.append("  [%s] %d  %s" % (n, len(fs), k))
        L.append("       e.g. %s" % san_raw[(n, k)][:200])
        for f in fs[:3]:
            L.append("       %s" % f)
    text = "\n".join(L) + "\n"
    open(a.report + ".txt", "w").write(text)
    json.dump(results, open(a.report + ".json", "w"), indent=0)
    print(text)
    print("report: %s.txt / .json" % a.report)


if __name__ == "__main__":
    main()
