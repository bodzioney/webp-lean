#!/usr/bin/env python3
"""Targeted VP8 key-frame streams built with tools/vp8craft.py (first partition
re-encoded with modified header fields; mode bools / token data kept).

  python3 -I make_crafted.py      -> corpus/crafted/*.vp8 + corpus/crafted/NOTES.txt
"""
import copy, os, random, struct, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "tools"))
import vp8craft as vc  # noqa: E402

V = os.path.join(HERE, "corpus", "valid")
OUT = os.path.join(HERE, "corpus", "crafted")


def load(rel):
    return vc.parse(vc.payload_of(os.path.join(V, rel)))


def find(pred):
    for sub in ("cwebp", "enc"):
        for fn in sorted(os.listdir(os.path.join(V, sub))):
            if fn.endswith(".webp"):
                p = vc.payload_of(os.path.join(V, sub, fn))
                f = vc.parse(p)
                if pred(f):
                    return sub + "/" + fn, f
    raise SystemExit("no source matches")


notes = []


def emit(name, f, note, part_table=None, raw=None):
    data = raw if raw is not None else vc.build(f, part_table)
    with open(os.path.join(OUT, name + ".vp8"), "wb") as fh:
        fh.write(data)
    notes.append("%-40s %s" % (name + ".vp8", note))


def main():
    os.makedirs(OUT, exist_ok=True)
    for fn in os.listdir(OUT):
        os.unlink(os.path.join(OUT, fn))
    A = load("enc/e001_partitions1_real_corpus-src_libwebp-test-data_peak.webp")  # no seg, 2 parts
    Bs = load("enc/e000_partitions0_real_corpus-src_libwebp-test-data_peak.webp")  # seg map+data
    N = load("cwebp/c154_syn_noise_64x64.webp")                                  # normal filter
    _, R1 = find(lambda f: f["h"] <= 16 and f["w"] >= 48 and len(f["parts"]) == 1)  # one MB row

    emit("roundtrip_A", copy.deepcopy(A), "re-encode only (sanity: must equal source)")

    # --- dequantizer cache quirk: dixie dqf->quant_idx initialised to -1 ------
    for absmode in (0, 1):
        for base in (0, 3):
            f = copy.deepcopy(A)
            f["quant"] = {"q": base, "y1dc": 0, "y2dc": 0, "y2ac": 0, "uvdc": 0, "uvac": 0}
            seg = f["seg"]
            seg.update(enabled=1, update_map=0, update_data=1, abs=absmode,
                       quant=[(-1 - base) if not absmode else -1, 0, 0, 0], lf=[0, 0, 0, 0])
            emit("dq_minus1_abs%d_q%d" % (absmode, base), f,
                 "segment 0 effective q index = -1 (q_index=%d, %s); all quant deltas 0 so "
                 "delta_update=%d. dixie: dqf.quant_idx==-1==q -> factors never computed (0) "
                 "when delta_update=0; spec/libwebp: clamp(-1)=0" % (
                     base, "abs" if absmode else "delta", 1 if base else 0))
    f = copy.deepcopy(A)
    f["quant"] = {"q": 0, "y1dc": 1, "y2dc": 0, "y2ac": 0, "uvdc": 0, "uvac": 0}
    f["seg"].update(enabled=1, update_map=0, update_data=1, abs=0, quant=[-1, 0, 0, 0], lf=[0] * 4)
    emit("dq_minus1_control_y1dc1", f, "as dq_minus1_abs0_q0 but y1dc=+1 -> delta_update=1 (control)")
    f = copy.deepcopy(Bs)
    f["quant"] = {"q": 0, "y1dc": 0, "y2dc": 0, "y2ac": 0, "uvdc": 0, "uvac": 0}
    f["seg"].update(update_data=1, abs=0, quant=[-1, 0, -1, 5], lf=[0] * 4)
    emit("dq_minus1_segmap", f, "segment map kept; segments 0 and 2 have q=-1 (delta mode, q_index 0)")

    # --- segmentation enabled but update_data=0 on a key frame ---------------
    for um in (0, 1):
        f = copy.deepcopy(Bs if um else A)
        f["seg"].update(enabled=1, update_map=um, update_data=0)
        if not um:
            f["lf"]["level"] = 20
        emit("seg_no_data_map%d" % um, f,
             "segmentation enabled, update_data=0: dixie/libvpx use delta mode with zero "
             "values (q=q_index, lf=level); libwebp defaults absolute_delta=1 with zeros (q=0, lf=0)")

    # --- loop-filter level clamping order ------------------------------------
    for i, (absm, level, seglf, ref0, mode0) in enumerate([
            (1, 30, [-30, -63, 10, 63], 40, -10),
            (0, 50, [40, -60, 13, 0], -30, 20),
            (0, 63, [63, 63, 63, 63], -63, 0),
            (1, 10, [-5, -5, -5, -5], 30, 0)]):
        f = copy.deepcopy(Bs)
        f["lf"].update(simple=0, level=level, sharpness=i, delta_enabled=1, delta_update=1,
                       ref=[ref0, 7, -7, 3], mode=[mode0, 1, 2, 3])
        f["seg"].update(update_data=1, abs=absm, lf=seglf)
        emit("lf_clamp_%d" % i, f, "segment lf %s %s, level %d, ref_delta[0]=%d mode_delta[0]=%d: "
             "dixie clamps seg level to 0..63 before adding deltas, libwebp only after" % (
                 "abs" if absm else "delta", seglf, level, ref0, mode0))

    # --- reserved header bits --------------------------------------------------
    for cs, ct in ((1, 0), (0, 1), (1, 1)):
        f = copy.deepcopy(A)
        f["color_space"], f["clamping_type"] = cs, ct
        emit("reserved_cs%d_clamp%d" % (cs, ct), f,
             "color_space=%d clamping_type=%d: dixie rejects ('Reserved bits not supported'), "
             "libwebp ignores both" % (cs, ct))

    # --- quantizer index range / clamping ------------------------------------
    for name, q in (("qmax_deltas_plus", {"q": 127, "y1dc": 15, "y2dc": 15, "y2ac": 15, "uvdc": 15, "uvac": 15}),
                    ("qmin_deltas_minus", {"q": 0, "y1dc": -15, "y2dc": -15, "y2ac": -15, "uvdc": -15, "uvac": -15}),
                    ("q117_uvdc", {"q": 110, "y1dc": 0, "y2dc": 0, "y2ac": -15, "uvdc": 15, "uvac": 0})):
        f = copy.deepcopy(N)
        f["quant"] = q
        emit(name, f, "quantizer index clamping: %s" % q)
    f = copy.deepcopy(Bs)
    f["seg"].update(update_data=1, abs=0, quant=[127, -127, 100, -100])
    emit("seg_q_out_of_range", f, "segment q deltas push q far outside 0..127")

    # --- probabilities 0 / 255 for the skip flag, version / scale bits --------
    for sp in (0, 1, 255):
        f = copy.deepcopy(A)
        f["skip_enabled"], f["skip_prob"] = 1, sp
        f["skip_flags"] = [0] * len(f["mbs"])
        emit("skipprob_%d_noskip" % sp, f, "mb_no_coeff_skip=1, prob_skip_false=%d, all flags 0 "
             "(image must equal the source)" % sp)
    for ver in (1, 2, 3):
        f = copy.deepcopy(N)
        f["tag_low"] = (f["tag_low"] & ~0x0E) | (ver << 1)
        emit("version_%d" % ver, f, "frame-tag version=%d (normal loop filter still selected by "
             "filter_type bit; bilinear/full-pixel MC irrelevant for key frames)" % ver)
    f = copy.deepcopy(N)
    h7 = bytearray(f["hdr7"]); h7[4] |= 0xC0; h7[6] |= 0x40
    f["hdr7"] = bytes(h7)
    emit("scale_bits", f, "horizontal_scale=3, vertical_scale=1 (ignored by decoders)")

    # --- token partitions -------------------------------------------------------
    f = copy.deepcopy(R1)
    tok = f["parts"][0]
    f["log2parts"] = 3
    f["parts"] = [tok] + [b""] * 6 + [b"\x00"]
    emit("parts8_one_row", f, "8 partitions on a 1-MB-row image: partition 0 = all tokens, 1..6 "
         "empty, 7 = one 0x00 byte (unused)")
    f["parts"] = [tok] + [b""] * 7
    emit("parts8_one_row_last_empty", f, "as parts8_one_row but last partition empty "
         "(libwebp requires a non-empty last partition)")
    f["parts"] = [tok] + [b"\xff"] * 7
    emit("parts8_one_row_unused_ff", f, "unused partitions each = 0xFF (libwebp rejects a "
         "partition whose first byte is 0xFF even if never used)")
    f = copy.deepcopy(R1)
    f["parts"] = [f["parts"][0] + b"\xde\xad\xbe\xef" * 4]
    emit("trailing_garbage_in_part", f, "16 garbage bytes after the token data of the last partition")
    for n2, nrows in ((1, "2"), (2, "4"), (3, "8")):
        f = copy.deepcopy(A)  # 8 MB rows
        f["log2parts"] = n2
        f["skip_enabled"], f["skip_prob"] = 1, 200
        f["skip_flags"] = [1] * len(f["mbs"])
        f["parts"] = [b"\x00"] * (1 << n2)
        emit("allskip_parts%s" % nrows, f, "all MBs skipped (no tokens read), %s partitions of one "
             "0x00 byte: prediction + loop filter only" % nrows)
        f["parts"] = [b""] * ((1 << n2) - 1) + [b"\x00"]
        emit("allskip_parts%s_empty" % nrows, f, "all MBs skipped, partitions 0..n-2 empty (never "
             "read), last = 0x00. libwebp: empty partition -> eof flag set at init -> "
             "'Premature end-of-file' even though no token is read")
        f["lf"].update(level=63, simple=0, sharpness=0)
        f["parts"] = [b"\x00"] * (1 << n2)
        emit("allskip_parts%s_lf63" % nrows, f, "all MBs skipped, normal loop filter level 63")

    # --- random token data with big quantizers (IDCT / WHT overflow) ---------
    rnd = random.Random(7)
    for i in range(40):
        f = copy.deepcopy(N if i % 2 else A)
        f["quant"] = {"q": 127, "y1dc": 15, "y2dc": 15, "y2ac": 15, "uvdc": 15, "uvac": 15}
        f["seg"].update(enabled=0, update_map=0, update_data=0)
        f["skip_enabled"] = 0
        # bias coefficient probabilities towards large tokens
        upd = {}
        for k in range(1056):
            if rnd.random() < 0.7:
                upd[k] = rnd.choice([1, 2, 255, 254, 128]) if rnd.random() < 0.5 else rnd.randrange(256)
        f["coef_updates"] = upd
        f["parts"] = [rnd.randbytes(20000) for _ in f["parts"]]
        emit("bigcoef_%02d" % i, f, "random token data, q=127 + max deltas, random coefficient "
             "probabilities (exercises int16 coefficient / IDCT / WHT overflow paths)")

    with open(os.path.join(OUT, "NOTES.txt"), "w") as fh:
        fh.write("\n".join(notes) + "\n")
    print("crafted: %d files" % len(notes))


if __name__ == "__main__":
    main()
