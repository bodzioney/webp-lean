#!/usr/bin/env python3
"""webp-lean decode vs dwebp -pam on still images (lossy and lossless).
Usage: python3 -I still_compare.py DIR_OR_FILE...   Prints counts and mismatches."""
import os, sys, subprocess, tempfile, concurrent.futures as cf
L = "/var/data/diff-fuzz/webp/webp-lean/.lake/build/bin/webp-lean"
D = "/var/data/diff-fuzz/webp/build/libwebp-tools/dwebp"
files = []
for a in sys.argv[1:]:
    if os.path.isdir(a):
        for r, _, fs in os.walk(a):
            files += [os.path.join(r, f) for f in fs if f.endswith(".webp")]
    else:
        files.append(a)
files = sorted(set(os.path.realpath(f) for f in files))
def one(f):
    with tempfile.TemporaryDirectory(dir="/tmp/claude-1000") as t:
        rd = subprocess.run([D, f, "-pam", "-o", t + "/d.pam"], capture_output=True, timeout=120).returncode
        rl = subprocess.run([L, "decode", f, t + "/l"], capture_output=True, timeout=300).returncode
        if not os.path.exists(t + "/l.pam") and rl == 0:
            return ("animated/other", f)
        if rd != 0 and rl != 0: return ("both reject", f)
        if rd != 0: return ("dwebp reject, lean ok", f)
        if rl != 0: return ("lean reject, dwebp ok", f)
        a = open(t + "/d.pam", "rb").read(); b = open(t + "/l.pam", "rb").read()
        return ("identical" if a == b else "PIXELS DIFFER", f)
with cf.ThreadPoolExecutor(8) as ex:
    res = list(ex.map(one, files))
cnt = {}
for k, f in res:
    cnt[k] = cnt.get(k, 0) + 1
    if k not in ("identical", "both reject", "animated/other"): print(k, f)
print(len(files), "files:", cnt)
