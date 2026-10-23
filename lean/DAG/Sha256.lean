/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Lean

/-!
# SHA-256 (FIPS 180-4)

A small, dependency-free SHA-256 used for DAG extraction keys and term digests.
It deliberately avoids Lean's builtin `hash` / `mixHash`, whose values are not
guaranteed stable across toolchains, so digests computed here are reproducible
by any standard SHA-256 implementation (e.g. Python `hashlib.sha256`).

A digest is a search/identity key for extraction, not a proof of anything.
-/

namespace DAG.Sha256

private def roundConstants : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

private def initialState : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

@[inline] private def rotr (x : UInt32) (n : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< (32 - n))

/-- Process one 64-byte block starting at `off`. -/
private def compress (st : Array UInt32) (block : ByteArray) (off : Nat) : Array UInt32 := Id.run do
  let mut w : Array UInt32 := Array.mkEmpty 64
  for i in [0:16] do
    let byte (j : Nat) : UInt32 := (block.get! (off + 4 * i + j)).toUInt32
    w := w.push ((byte 0 <<< 24) ||| (byte 1 <<< 16) ||| (byte 2 <<< 8) ||| byte 3)
  for i in [16:64] do
    let x := w[i - 15]!
    let y := w[i - 2]!
    let s0 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
    let s1 := rotr y 17 ^^^ rotr y 19 ^^^ (y >>> 10)
    w := w.push (w[i - 16]! + s0 + w[i - 7]! + s1)
  let mut a := st[0]!
  let mut b := st[1]!
  let mut c := st[2]!
  let mut d := st[3]!
  let mut e := st[4]!
  let mut f := st[5]!
  let mut g := st[6]!
  let mut h := st[7]!
  for i in [0:64] do
    let bigS1 := rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25
    let ch := (e &&& f) ^^^ ((~~~e) &&& g)
    let t1 := h + bigS1 + ch + roundConstants[i]! + w[i]!
    let bigS0 := rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22
    let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let t2 := bigS0 + maj
    h := g
    g := f
    f := e
    e := d + t1
    d := c
    c := b
    b := a
    a := t1 + t2
  return #[st[0]! + a, st[1]! + b, st[2]! + c, st[3]! + d,
           st[4]! + e, st[5]! + f, st[6]! + g, st[7]! + h]

/-- Message padding: `0x80`, zeros, then the 64-bit big-endian bit length. -/
private def pad (msg : ByteArray) : ByteArray := Id.run do
  let bitLen : UInt64 := (msg.size.toUInt64) * 8
  let mut out := msg.push 0x80
  while out.size % 64 != 56 do
    out := out.push 0
  for k in [0:8] do
    out := out.push ((bitLen >>> (8 * (7 - k)).toUInt64).toUInt8)
  return out

/-- SHA-256 digest (32 bytes). -/
def digest (msg : ByteArray) : ByteArray := Id.run do
  let padded := pad msg
  let mut st := initialState
  for blk in [0:padded.size / 64] do
    st := compress st padded (64 * blk)
  let mut out : ByteArray := ByteArray.emptyWithCapacity 32
  for word in st do
    out := out.push (word >>> 24).toUInt8
    out := out.push (word >>> 16).toUInt8
    out := out.push (word >>> 8).toUInt8
    out := out.push word.toUInt8
  return out

private def hexDigit (n : UInt8) : Char :=
  if n < 10 then Char.ofNat (48 + n.toNat) else Char.ofNat (87 + n.toNat)

/-- Lowercase hexadecimal rendering of a byte array. -/
def toHex (bytes : ByteArray) : String := Id.run do
  let mut s := ""
  for b in bytes do
    s := (s.push (hexDigit (b >>> 4))).push (hexDigit (b &&& 0x0f))
  return s

/-- Lowercase hex SHA-256 of a byte array. -/
def hexDigest (msg : ByteArray) : String :=
  toHex (digest msg)

/-- Lowercase hex SHA-256 of the UTF-8 encoding of a string. -/
def hexDigestString (s : String) : String :=
  hexDigest s.toUTF8

end DAG.Sha256
