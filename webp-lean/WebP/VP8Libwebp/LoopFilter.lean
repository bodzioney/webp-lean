import WebP.VP8Libwebp.Dsp
/-!
# VP8 loop filter (RFC 6386 §15), port of libwebp src/dsp/dec.c C filters

Filters operate in place on a plane (`ByteArray`, given `stride`). A pixel position `p`
addresses the first pixel *after* the edge (`q0`); `step` is the distance across the edge.
Callers guarantee `p ≥ 4*step` (edges are never on the frame border).
-/
namespace WebP.VP8Libwebp

/-- `VP8ksclip1`: clamp to `[-128, 127]`. -/
@[inline] def sclip1 (v : Int) : Int := if v < -128 then -128 else if v > 127 then 127 else v
/-- `VP8ksclip2`: clamp to `[-16, 15]`. -/
@[inline] def sclip2 (v : Int) : Int := if v < -16 then -16 else if v > 15 then 15 else v
/-- `VP8kclip1`: clamp to `[0, 255]`. -/
@[inline] def uclip1 (v : Int) : Nat := clip255 v
@[inline] def iabs (v : Int) : Int := if v < 0 then -v else v

@[inline] def at' (a : ByteArray) (p : Nat) (k : Int) (step : Nat) : Int :=
  (rd a ((p : Int) + k * step).toNat : Int)

@[inline] def put' (a : ByteArray) (p : Nat) (k : Int) (step : Nat) (v : Nat) : ByteArray :=
  wrN a ((p : Int) + k * step).toNat v

/-- `DoFilter2_C` (simple filter / high edge variance). -/
@[inline] def doFilter2 (a : ByteArray) (p step : Nat) : ByteArray :=
  let p1 := at' a p (-2) step; let p0 := at' a p (-1) step
  let q0 := at' a p 0 step; let q1 := at' a p 1 step
  let x := 3 * (q0 - p0) + sclip1 (p1 - q1)
  let a1 := sclip2 (asr (x + 4) 3)
  let a2 := sclip2 (asr (x + 3) 3)
  let a := put' a p (-1) step (uclip1 (p0 + a2))
  put' a p 0 step (uclip1 (q0 - a1))

/-- `DoFilter4_C` (inner edges). -/
@[inline] def doFilter4 (a : ByteArray) (p step : Nat) : ByteArray :=
  let p1 := at' a p (-2) step; let p0 := at' a p (-1) step
  let q0 := at' a p 0 step; let q1 := at' a p 1 step
  let x := 3 * (q0 - p0)
  let a1 := sclip2 (asr (x + 4) 3)
  let a2 := sclip2 (asr (x + 3) 3)
  let a3 := asr (a1 + 1) 1
  let a := put' a p (-2) step (uclip1 (p1 + a3))
  let a := put' a p (-1) step (uclip1 (p0 + a2))
  let a := put' a p 0 step (uclip1 (q0 - a1))
  put' a p 1 step (uclip1 (q1 - a3))

/-- `DoFilter6_C` (macroblock edges). -/
@[inline] def doFilter6 (a : ByteArray) (p step : Nat) : ByteArray :=
  let p2 := at' a p (-3) step; let p1 := at' a p (-2) step; let p0 := at' a p (-1) step
  let q0 := at' a p 0 step; let q1 := at' a p 1 step; let q2 := at' a p 2 step
  let x := sclip1 (3 * (q0 - p0) + sclip1 (p1 - q1))
  let a1 := asr (27 * x + 63) 7
  let a2 := asr (18 * x + 63) 7
  let a3 := asr (9 * x + 63) 7
  let a := put' a p (-3) step (uclip1 (p2 + a3))
  let a := put' a p (-2) step (uclip1 (p1 + a2))
  let a := put' a p (-1) step (uclip1 (p0 + a1))
  let a := put' a p 0 step (uclip1 (q0 - a1))
  let a := put' a p 1 step (uclip1 (q1 - a2))
  put' a p 2 step (uclip1 (q2 - a3))

@[inline] def hev (a : ByteArray) (p step : Nat) (thresh : Int) : Bool :=
  let p1 := at' a p (-2) step; let p0 := at' a p (-1) step
  let q0 := at' a p 0 step; let q1 := at' a p 1 step
  iabs (p1 - p0) > thresh || iabs (q1 - q0) > thresh

@[inline] def needsFilter (a : ByteArray) (p step : Nat) (t : Int) : Bool :=
  let p1 := at' a p (-2) step; let p0 := at' a p (-1) step
  let q0 := at' a p 0 step; let q1 := at' a p 1 step
  4 * iabs (p0 - q0) + iabs (p1 - q1) ≤ t

@[inline] def needsFilter2 (a : ByteArray) (p step : Nat) (t it : Int) : Bool :=
  let p3 := at' a p (-4) step; let p2 := at' a p (-3) step; let p1 := at' a p (-2) step
  let p0 := at' a p (-1) step; let q0 := at' a p 0 step
  let q1 := at' a p 1 step; let q2 := at' a p 2 step; let q3 := at' a p 3 step
  if 4 * iabs (p0 - q0) + iabs (p1 - q1) > t then false
  else iabs (p3 - p2) ≤ it && iabs (p2 - p1) ≤ it && iabs (p1 - p0) ≤ it &&
       iabs (q3 - q2) ≤ it && iabs (q2 - q1) ≤ it && iabs (q1 - q0) ≤ it

/-- Simple filter across one edge of 16 pixels: `hstride` across, `vstride` along. -/
def simpleFilter16 (a : ByteArray) (p hstride vstride : Nat) (thresh : Int) : ByteArray := Id.run do
  let t2 := 2 * thresh + 1
  let mut a := a
  for i in [0:16] do
    let q := p + i * vstride
    if needsFilter a q hstride t2 then a := doFilter2 a q hstride
  return a

/-- `FilterLoop26_C` (`mbEdge = true`) / `FilterLoop24_C` (`mbEdge = false`). -/
def filterLoop (a : ByteArray) (p hstride vstride size : Nat) (thresh ithresh hevT : Int)
    (mbEdge : Bool) : ByteArray := Id.run do
  let t2 := 2 * thresh + 1
  let mut a := a
  for i in [0:size] do
    let q := p + i * vstride
    if needsFilter2 a q hstride t2 ithresh then
      if hev a q hstride hevT then a := doFilter2 a q hstride
      else if mbEdge then a := doFilter6 a q hstride
      else a := doFilter4 a q hstride
  return a

/-- Per-macroblock filter parameters (libwebp `VP8FInfo`). `limit = 0` disables filtering. -/
structure FInfo where
  limit  : Nat
  ilevel : Nat
  inner  : Bool
  hevThresh : Nat

/-- `DoFilter` for macroblock `(mbx, mby)` on full planes.
`filterType`: 1 = simple (luma only), 2 = normal. -/
def doFilterMB (y u v : ByteArray) (yStride uvStride : Nat) (filterType : Nat) (f : FInfo)
    (mbx mby : Nat) : ByteArray × ByteArray × ByteArray := Id.run do
  if f.limit == 0 then return (y, u, v)
  let limit : Int := f.limit
  let yp := mby * 16 * yStride + mbx * 16
  let mut y := y; let mut u := u; let mut v := v
  if filterType == 1 then
    if mbx > 0 then y := simpleFilter16 y yp 1 yStride (limit + 4)
    if f.inner then
      for k in [1:4] do y := simpleFilter16 y (yp + 4 * k) 1 yStride limit
    if mby > 0 then y := simpleFilter16 y yp yStride 1 (limit + 4)
    if f.inner then
      for k in [1:4] do y := simpleFilter16 y (yp + 4 * k * yStride) yStride 1 limit
  else
    let up := mby * 8 * uvStride + mbx * 8
    let il : Int := f.ilevel
    let ht : Int := f.hevThresh
    if mbx > 0 then
      y := filterLoop y yp 1 yStride 16 (limit + 4) il ht true
      u := filterLoop u up 1 uvStride 8 (limit + 4) il ht true
      v := filterLoop v up 1 uvStride 8 (limit + 4) il ht true
    if f.inner then
      for k in [1:4] do y := filterLoop y (yp + 4 * k) 1 yStride 16 limit il ht false
      u := filterLoop u (up + 4) 1 uvStride 8 limit il ht false
      v := filterLoop v (up + 4) 1 uvStride 8 limit il ht false
    if mby > 0 then
      y := filterLoop y yp yStride 1 16 (limit + 4) il ht true
      u := filterLoop u up uvStride 1 8 (limit + 4) il ht true
      v := filterLoop v up uvStride 1 8 (limit + 4) il ht true
    if f.inner then
      for k in [1:4] do y := filterLoop y (yp + 4 * k * yStride) yStride 1 16 limit il ht false
      u := filterLoop u (up + 4 * uvStride) uvStride 1 8 limit il ht false
      v := filterLoop v (up + 4 * uvStride) uvStride 1 8 limit il ht false
  return (y, u, v)

end WebP.VP8Libwebp
