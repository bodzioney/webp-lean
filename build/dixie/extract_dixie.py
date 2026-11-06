#!/usr/bin/env python3
"""Extract the RFC 6386 §20 reference decoder ("dixie") sources from rfc6386.txt.

Usage: python3 -I extract_dixie.py rfc6386.txt outdir
Strips page footers ("Bankoski, et al. ... [Page N]"), page headers
("RFC 6386 ... November 2011"), the blank lines around page breaks, form feeds,
and the 3-space indentation of the code blocks.
"""
import re, sys, os

src, outdir = sys.argv[1], sys.argv[2]
lines = open(src, encoding="latin-1").read().split("\n")
footer = re.compile(r"^Bankoski, et al\..*\[Page \d+\]\s*$")
header = re.compile(r"^RFC 6386 .*November 2011\s*$")
sect = re.compile(r"^20\.(\d+)\.  (\S+)\s*$")

start = next(i for i, l in enumerate(lines) if l.startswith("20.  Attachment One"))
cur = None
files = {}
inblock = False
buf = []
i = start
while i < len(lines):
    l = lines[i].replace("\f", "")
    m = sect.match(l)
    if not inblock and m:
        cur = m.group(2)
    if "---- Begin code block" in l:
        inblock = True; buf = []
    elif "---- End code block" in l:
        inblock = False
        files.setdefault(cur, []).append(buf)
    elif inblock:
        if footer.match(l):
            # drop blank lines before the footer
            while buf and buf[-1].strip() == "":
                buf.pop()
            # skip until header, then skip blank lines after it
            i += 1
            while i < len(lines) and not header.match(lines[i].replace("\f", "")):
                i += 1
            i += 1
            while i < len(lines) and lines[i].replace("\f", "").strip() == "":
                i += 1
            continue
        if l.startswith("   "):
            l = l[3:]
        elif l.strip() == "":
            l = ""
        else:
            raise SystemExit(f"unexpected unindented line {i+1}: {l!r}")
        buf.append(l)
    i += 1

os.makedirs(outdir, exist_ok=True)
for name, blocks in files.items():
    if not re.search(r"\.(c|h)$", name):
        continue
    text = "\n".join("\n".join(b).strip("\n") for b in blocks) + "\n"
    with open(os.path.join(outdir, name), "w") as f:
        f.write(text)
    print(name, sum(len(b) for b in blocks))
