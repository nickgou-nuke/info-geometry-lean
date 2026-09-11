import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# A finite `Z4` circulant mass ladder

This owner records the exact polynomial and real modulus identities for the
four-cycle matrix.  The phase is an algebraic parameter; no Klein-bottle or
physical-generation interpretation is assumed.
-/

namespace InfoGeometry.Canonical.Z4CirculantMassLadder

structure Mat4 (R : Type*) where
  m00 : R
  m01 : R
  m02 : R
  m03 : R
  m10 : R
  m11 : R
  m12 : R
  m13 : R
  m20 : R
  m21 : R
  m22 : R
  m23 : R
  m30 : R
  m31 : R
  m32 : R
  m33 : R

def det3 {R : Type*} [CommRing R]
    (a00 a01 a02 a10 a11 a12 a20 a21 a22 : R) : R :=
  a00 * (a11 * a22 - a12 * a21) -
    a01 * (a10 * a22 - a12 * a20) +
    a02 * (a10 * a21 - a11 * a20)

def det4 {R : Type*} [CommRing R] (M : Mat4 R) : R :=
  let d0 := det3 M.m11 M.m12 M.m13 M.m21 M.m22 M.m23 M.m31 M.m32 M.m33
  let d1 := det3 M.m10 M.m12 M.m13 M.m20 M.m22 M.m23 M.m30 M.m32 M.m33
  let d2 := det3 M.m10 M.m11 M.m13 M.m20 M.m21 M.m23 M.m30 M.m31 M.m33
  let d3 := det3 M.m10 M.m11 M.m12 M.m20 M.m21 M.m22 M.m30 M.m31 M.m32
  M.m00 * d0 - M.m01 * d1 + M.m02 * d2 - M.m03 * d3

def charMat4 {R : Type*} [CommRing R] (m ε phase x : R) : Mat4 R where
  m00 := x - m; m01 := -ε; m02 := 0; m03 := 0
  m10 := 0; m11 := x - m; m12 := -ε; m13 := 0
  m20 := 0; m21 := 0; m22 := x - m; m23 := -ε
  m30 := -ε * phase; m31 := 0; m32 := 0; m33 := x - m

theorem charMat4_det (m ε phase x : ℝ) :
    det4 (charMat4 m ε phase x) = (x - m) ^ 4 - ε ^ 4 * phase := by
  dsimp [det4, charMat4, det3]
  ring

theorem squared_modulus (m ε c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    (m + ε * c) ^ 2 + (ε * s) ^ 2 =
      m ^ 2 + ε ^ 2 + 2 * m * ε * c := by
  calc
    (m + ε * c) ^ 2 + (ε * s) ^ 2 =
        m ^ 2 + 2 * m * ε * c + ε ^ 2 * (c ^ 2 + s ^ 2) := by ring
    _ = m ^ 2 + 2 * m * ε * c + ε ^ 2 := by rw [h]; ring
    _ = m ^ 2 + ε ^ 2 + 2 * m * ε * c := by ring

theorem zero_phase_doublet (m ε : ℝ) :
    m ^ 2 + ε ^ 2 + 2 * m * ε * 0 = m ^ 2 + ε ^ 2 := by ring

theorem opposite_phase_separation (m ε c : ℝ) (hm : 0 < m) (hε : 0 < ε)
    (hc : 0 < c) :
    m ^ 2 + ε ^ 2 + 2 * m * ε * (-c) <
      m ^ 2 + ε ^ 2 + 2 * m * ε * c := by
  have hpos : 0 < 2 * m * ε := by positivity
  nlinarith

end InfoGeometry.Canonical.Z4CirculantMassLadder
