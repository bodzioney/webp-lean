#!/usr/bin/env python3
"""vp8craft: re-encode the first partition of a VP8 key frame with modified
header fields (RFC 6386 sections 9.2-9.11 / 19.2), keeping the per-macroblock
mode bools and the token partitions verbatim.

Library use (see make_crafted.py):
    f = parse(payload)              # dict of header fields + recorded MB bools
    f["seg"]["enabled"] = 1 ...     # modify
    out = build(f)                  # new payload bytes

Supported modifications: color_space, clamping_type, segmentation (all fields;
update_map changes insert/remove per-MB segment-id bools using f["seg_ids"]),
loop filter (all fields), number of partitions + explicit partition table and
token data (f["parts_override"]), quantizer (all fields), refresh_entropy,
coefficient-probability updates (f["coef_updates"] dict), mb_no_coeff_skip and
prob_skip_false (skip flags per MB via f["skip_flags"]).
"""
import os, re, struct, sys

HERE = os.path.dirname(os.path.abspath(__file__))
GEN = os.path.join(HERE, "..", "src")


def _c_numbers(header, name):
    t = open(os.path.join(GEN, header)).read()
    i = t.index(name)
    j = t.index("=", i)
    k = t.index("};", j)
    body = re.sub(r"/\*.*?\*/", "", t[j + 1:k], flags=re.S)
    return [int(x) for x in re.findall(r"-?\d+", body)]


COEF_UPD = _c_numbers("vp8_prob_data.h", "k_coeff_entropy_update_probs")
assert len(COEF_UPD) == 4 * 8 * 3 * 11
KF_B_PROBS = _c_numbers("modemv_data.h", "kf_b_mode_probs")
assert len(KF_B_PROBS) == 10 * 10 * 9
KF_Y_PROBS = [145, 156, 163, 128]
KF_UV_PROBS = [142, 114, 183]
DC, V, H, TM, B = 0, 1, 2, 3, 4
B_DC, B_TM, B_VE, B_HE = 0, 1, 2, 3
KF_Y_TREE = [-B, 2, 4, 6, -DC, -V, -H, -TM]
UV_TREE = [-DC, 2, -V, 4, -H, -TM]
B_TREE = [-0, 2, -1, 4, -2, 6, 8, 12, -3, 10, -5, -6, -4, 14, -7, 16, -8, -9]


class BoolDecoder:
    """RFC 6386 section 7.3 / 20.2 (reads zeros past the end, like dixie)."""
    def __init__(self, data):
        self.d = data
        self.pos = 2
        self.value = ((data[0] if len(data) > 0 else 0) << 8) | (data[1] if len(data) > 1 else 0)
        if len(data) < 2:
            self.value = 0
        self.range = 255
        self.bit_count = 0

    def get(self, prob):
        split = 1 + (((self.range - 1) * prob) >> 8)
        SPLIT = split << 8
        if self.value >= SPLIT:
            r = 1
            self.range -= split
            self.value -= SPLIT
        else:
            r = 0
            self.range = split
        while self.range < 128:
            self.value <<= 1
            self.range <<= 1
            self.bit_count += 1
            if self.bit_count == 8:
                self.bit_count = 0
                if self.pos < len(self.d):
                    self.value |= self.d[self.pos]
                    self.pos += 1
        return r


class BoolEncoder:
    """RFC 6386 section 7.3."""
    def __init__(self):
        self.out = bytearray()
        self.range = 255
        self.bottom = 0
        self.bit_count = 24

    def _add_one(self):
        i = len(self.out) - 1
        while i >= 0 and self.out[i] == 255:
            self.out[i] = 0
            i -= 1
        self.out[i] += 1

    def put(self, prob, b):
        split = 1 + (((self.range - 1) * prob) >> 8)
        if b:
            self.bottom += split
            self.range -= split
        else:
            self.range = split
        while self.range < 128:
            self.range <<= 1
            if self.bottom & (1 << 31):
                self._add_one()
            self.bottom = (self.bottom << 1) & 0xFFFFFFFF
            self.bit_count -= 1
            if not self.bit_count:
                self.out.append((self.bottom >> 24) & 0xFF)
                self.bottom &= (1 << 24) - 1
                self.bit_count = 8

    def flush(self):
        c = self.bit_count
        v = self.bottom
        if v & (1 << (32 - c)):
            self._add_one()
        v = (v << (c & 7)) & 0xFFFFFFFF
        c >>= 3
        while c > 0:
            v = (v << 8) & 0xFFFFFFFF
            c -= 1
        for _ in range(4):
            self.out.append((v >> 24) & 0xFF)
            v = (v << 8) & 0xFFFFFFFF
        return bytes(self.out)


class Rec:
    """Wraps a BoolDecoder and records (kind, prob, bit)."""
    def __init__(self, bd):
        self.bd, self.log, self.kind = bd, [], "hdr"

    def get(self, p):
        b = self.bd.get(p)
        self.log.append((self.kind, p, b))
        return b

    def lit(self, n):
        v = 0
        for _ in range(n):
            v = (v << 1) | self.get(128)
        return v

    def signed(self, n):
        v = self.lit(n)
        return -v if self.get(128) else v

    def maybe(self, n):
        return self.signed(n) if self.get(128) else 0

    def tree(self, t, probs):
        i = 0
        while True:
            i = t[i + self.get(probs[i >> 1])]
            if i <= 0:
                return -i


def parse(p):
    tag = p[0] | p[1] << 8 | p[2] << 16
    assert not (tag & 1), "not a key frame"
    part0 = tag >> 5
    w = struct.unpack_from("<H", p, 6)[0] & 0x3FFF
    h = struct.unpack_from("<H", p, 8)[0] & 0x3FFF
    f = {"tag_low": tag & 0x1F, "hdr7": p[3:10], "w": w, "h": h}
    r = Rec(BoolDecoder(p[10:10 + part0]))
    f["color_space"] = r.lit(1)
    f["clamping_type"] = r.lit(1)
    seg = {"enabled": r.lit(1), "update_map": 0, "update_data": 0, "abs": 0,
           "quant": [None] * 4, "lf": [None] * 4, "probs": [None] * 3}
    if seg["enabled"]:
        seg["update_map"] = r.lit(1)
        seg["update_data"] = r.lit(1)
        if seg["update_data"]:
            seg["abs"] = r.lit(1)
            seg["quant"] = [r.maybe(7) for _ in range(4)]
            seg["lf"] = [r.maybe(6) for _ in range(4)]
        if seg["update_map"]:
            seg["probs"] = [r.lit(8) if r.get(128) else 255 for _ in range(3)]
    f["seg"] = seg
    lf = {"simple": r.lit(1), "level": r.lit(6), "sharpness": r.lit(3),
          "delta_enabled": r.lit(1), "delta_update": 0, "ref": [0] * 4, "mode": [0] * 4}
    if lf["delta_enabled"]:
        lf["delta_update"] = r.lit(1)
        if lf["delta_update"]:
            lf["ref"] = [r.maybe(6) for _ in range(4)]
            lf["mode"] = [r.maybe(6) for _ in range(4)]
    f["lf"] = lf
    f["log2parts"] = r.lit(2)
    f["quant"] = {"q": r.lit(7), "y1dc": r.maybe(4), "y2dc": r.maybe(4), "y2ac": r.maybe(4),
                  "uvdc": r.maybe(4), "uvac": r.maybe(4)}
    f["refresh_entropy"] = r.lit(1)
    upd = {}
    for i in range(1056):
        if r.get(COEF_UPD[i]):
            upd[i] = r.lit(8)
    f["coef_updates"] = upd
    f["skip_enabled"] = r.lit(1)
    f["skip_prob"] = r.lit(8) if f["skip_enabled"] else 0
    # macroblock headers
    mbw, mbh = (w + 15) // 16, (h + 15) // 16
    above = [[B_DC] * 4 for _ in range(mbw)]
    mbs = []
    for y in range(mbh):
        left = [B_DC] * 4
        for x in range(mbw):
            mb = {}
            if seg["update_map"]:
                r.kind = "seg"
                pr = seg["probs"]
                mb["seg"] = 2 + r.get(pr[2]) if r.get(pr[0]) else r.get(pr[1])
            if f["skip_enabled"]:
                r.kind = "skip"
                mb["skip"] = r.get(f["skip_prob"])
            r.kind = "mode"
            start = len(r.log)
            ym = r.tree(KF_Y_TREE, KF_Y_PROBS)
            if ym == B:
                sub = [0] * 16
                for i in range(16):
                    a = above[x][i & 3] if i < 4 else sub[i - 4]
                    l = left[i >> 2] if (i & 3) == 0 else sub[i - 1]
                    sub[i] = r.tree(B_TREE, KF_B_PROBS[(a * 10 + l) * 9:(a * 10 + l) * 9 + 9])
                above[x] = sub[12:16]
                left = [sub[3], sub[7], sub[11], sub[15]]
            else:
                imp = {DC: B_DC, V: B_VE, H: B_HE, TM: B_TM}[ym]
                above[x] = [imp] * 4
                left = [imp] * 4
            r.tree(UV_TREE, KF_UV_PROBS)
            mb["mode_bools"] = [(p_, b_) for _, p_, b_ in r.log[start:]]
            mbs.append(mb)
    f["mbs"] = mbs
    f["seg_ids"] = [mb.get("seg", 0) for mb in mbs]
    f["skip_flags"] = [mb.get("skip", 0) for mb in mbs]
    # token partitions
    n = 1 << f["log2parts"]
    rest = p[10 + part0:]
    sizes = []
    off = 3 * (n - 1)
    for i in range(n - 1):
        s = rest[3 * i] | rest[3 * i + 1] << 8 | rest[3 * i + 2] << 16
        sizes.append(s)
    parts = []
    for s in sizes:
        parts.append(rest[off:off + s])
        off += s
    parts.append(rest[off:])
    f["parts"] = parts
    f["part0_orig"] = p[10:10 + part0]
    return f


def build(f, part_table=None):
    e = BoolEncoder()
    lit = lambda v, n: [e.put(128, (v >> (n - 1 - i)) & 1) for i in range(n)]

    def signed(v, n):
        lit(abs(v), n)
        e.put(128, 1 if v < 0 else 0)

    def maybe(v, n):
        if v is None:
            e.put(128, 0)
        else:
            e.put(128, 1)
            signed(v, n)

    lit(f["color_space"], 1)
    lit(f["clamping_type"], 1)
    s = f["seg"]
    lit(s["enabled"], 1)
    if s["enabled"]:
        lit(s["update_map"], 1)
        lit(s["update_data"], 1)
        if s["update_data"]:
            lit(s["abs"], 1)
            for v in s["quant"]:
                maybe(v, 7)
            for v in s["lf"]:
                maybe(v, 6)
        if s["update_map"]:
            for v in s["probs"]:
                if v == 255:
                    e.put(128, 0)
                else:
                    e.put(128, 1)
                    lit(v, 8)
    l = f["lf"]
    lit(l["simple"], 1)
    lit(l["level"], 6)
    lit(l["sharpness"], 3)
    lit(l["delta_enabled"], 1)
    if l["delta_enabled"]:
        lit(l["delta_update"], 1)
        if l["delta_update"]:
            for v in l["ref"] + l["mode"]:
                maybe(v, 6)
    lit(f["log2parts"], 2)
    q = f["quant"]
    lit(q["q"], 7)
    for k in ("y1dc", "y2dc", "y2ac", "uvdc", "uvac"):
        maybe(q[k] if q[k] != 0 else None, 4)
    lit(f["refresh_entropy"], 1)
    for i in range(1056):
        if i in f["coef_updates"]:
            e.put(COEF_UPD[i], 1)
            lit(f["coef_updates"][i], 8)
        else:
            e.put(COEF_UPD[i], 0)
    lit(f["skip_enabled"], 1)
    if f["skip_enabled"]:
        lit(f["skip_prob"], 8)
    for i, mb in enumerate(f["mbs"]):
        if s["enabled"] and s["update_map"]:
            sid = f["seg_ids"][i]
            pr = s["probs"]
            if sid >= 2:
                e.put(pr[0], 1)
                e.put(pr[2], sid - 2)
            else:
                e.put(pr[0], 0)
                e.put(pr[1], sid)
        if f["skip_enabled"]:
            e.put(f["skip_prob"], f["skip_flags"][i])
        for p_, b_ in mb["mode_bools"]:
            e.put(p_, b_)
    p0 = e.flush()
    tag = f["tag_low"] | (len(p0) << 5)
    out = bytearray(struct.pack("<I", tag)[:3]) + f["hdr7"] + p0
    parts = f["parts"]
    n = 1 << f["log2parts"]
    assert len(parts) == n, "parts list must have 2^log2parts entries"
    sizes = part_table if part_table is not None else [len(x) for x in parts[:-1]]
    for s_ in sizes:
        out += struct.pack("<I", s_)[:3]
    for x in parts:
        out += x
    return bytes(out)


def payload_of(path):
    d = open(path, "rb").read()
    if d[:4] == b"RIFF":
        off = 12
        while off + 8 <= len(d):
            sz = struct.unpack_from("<I", d, off + 4)[0]
            if d[off:off + 4] == b"VP8 ":
                return d[off + 8:off + 8 + sz]
            off += 8 + sz + (sz & 1)
        raise SystemExit("no VP8 chunk")
    return d


if __name__ == "__main__":
    # self-test: parse + rebuild must decode identically (checked by caller)
    p = payload_of(sys.argv[1])
    f = parse(p)
    q = build(f)
    open(sys.argv[2], "wb").write(q)
    print("orig part0=%d new part0=%d mbs=%d parts=%d" % (
        len(f["part0_orig"]), len(q) - 10 - sum(len(x) for x in f["parts"]) - 3 * (len(f["parts"]) - 1),
        len(f["mbs"]), len(f["parts"])))
