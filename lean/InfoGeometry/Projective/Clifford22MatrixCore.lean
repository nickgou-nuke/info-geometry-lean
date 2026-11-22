/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.VecNotation

/-!
# Shared matrix core for the split `Cl(2,2)` and twistor owners

This file collects the explicit `4 × 4` matrix frame, the six bivector
coordinates, the twistor bracket, and the elementary determinant identities
used by

* `InfoGeometry.Projective.Clifford22TwistorAmplituhedronPoset`
* `InfoGeometry.Projective.Clifford22YangMillsPositiveGrassmannianPoset`.

The frame is the one displayed in the proposal: `E₁² = E₂² = +1`,
`E₃² = E₄² = -1`, and `ω = E₁E₂E₃E₄ = diag(1,1,-1,-1)`.  The determinant is
the explicit six-term Laplace expansion; it is definitionally the usual
`4 × 4` determinant on this finite index type, and `det4_mul` records the
multiplicativity used by the twistor bracket.

Nothing in this file asserts a universal Clifford-algebra isomorphism.  The
results are statements about the displayed matrix representation over an
arbitrary commutative ring.

#### BUCKET 1: CLOSED FINITE THEOREMS
The vector and bivector identities, determinant formulas, nilpotent Cayley
identities, bracket transport, and five-twistor syzygies are proved for the
displayed `4 × 4` matrix model.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT PREMISES
The square-zero inverse and Cayley conclusions assume the stated vanishing
quadratic invariants. The carrier remains the finite matrix model.

#### BUCKET 3: OPEN CLOSURE DEBT
This file does not construct an amplituhedron, its canonical differential
form, a BCFW recursion, a scattering amplitude, or a Clifford universal
algebra isomorphism.
-/

namespace Clifford22

open Matrix

universe u

/- The Clifford generators are matrices over the coefficient ring.  Their
Clifford relations extend coefficientwise when coefficients are central; the
quadratic-form and determinant identities below therefore require a
commutative coefficient ring.  The matrix algebra itself remains
noncommutative.  Arbitrary operator coefficients are handled by the separate
generic block-operator owners, where no Clifford scalar-extension claim is
made. -/
variable {R : Type u} [CommRing R]

/-- The concrete `4 × 4` matrix carrier. -/
abbrev Mat4 (R : Type u) := Matrix (Fin 4) (Fin 4) R

namespace Mat4

/-- First positive-sign generator. -/
def E1 : Mat4 R :=
  !![0, 0, 1, 0;
     0, 0, 0, -1;
     1, 0, 0, 0;
     0, -1, 0, 0]

/-- Second positive-sign generator. -/
def E2 : Mat4 R :=
  !![0, 0, 0, 1;
     0, 0, 1, 0;
     0, 1, 0, 0;
     1, 0, 0, 0]

/-- First negative-sign generator. -/
def E3 : Mat4 R :=
  !![0, 0, 0, 1;
     0, 0, -1, 0;
     0, 1, 0, 0;
     -1, 0, 0, 0]

/-- Second negative-sign generator. -/
def E4 : Mat4 R :=
  !![0, 0, 1, 0;
     0, 0, 0, 1;
     -1, 0, 0, 0;
     0, -1, 0, 0]

/-- The six elementary bivectors. -/
def E12 : Mat4 R := (E1 : Mat4 R) * E2
/-- The bivector basis element `E₁E₃`. -/
def E13 : Mat4 R := (E1 : Mat4 R) * E3
/-- The bivector basis element `E₁E₄`. -/
def E14 : Mat4 R := (E1 : Mat4 R) * E4
/-- The bivector basis element `E₂E₃`. -/
def E23 : Mat4 R := (E2 : Mat4 R) * E3
/-- The bivector basis element `E₂E₄`. -/
def E24 : Mat4 R := (E2 : Mat4 R) * E4
/-- The bivector basis element `E₃E₄`. -/
def E34 : Mat4 R := (E3 : Mat4 R) * E4

/-- The four elementary trivectors and the chiral volume element. -/
def E234 : Mat4 R := (E2 : Mat4 R) * E3 * E4
/-- The trivector basis element `E₁E₃E₄`. -/
def E134 : Mat4 R := (E1 : Mat4 R) * E3 * E4
/-- The trivector basis element `E₁E₂E₄`. -/
def E124 : Mat4 R := (E1 : Mat4 R) * E2 * E4
/-- The trivector basis element `E₁E₂E₃`. -/
def E123 : Mat4 R := (E1 : Mat4 R) * E2 * E3
/-- The oriented volume element `E₁E₂E₃E₄`. -/
def omega : Mat4 R := (E1 : Mat4 R) * E2 * E3 * E4

/-- The displayed matrix frame witnesses noncommutative multiplication. -/
theorem generators_noncommute :
    (E1 : Mat4 ℝ) * E2 ≠ E2 * E1 := by
  intro h
  have h01 := congrArg (fun M : Mat4 ℝ => M 0 1) h
  norm_num [E1, E2, Matrix.mul_apply, Fin.sum_univ_four] at h01

/-- The first diagonal matrix unit. -/
def E00 : Mat4 R :=
  !![1, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0]

/-- The second diagonal matrix unit. -/
def E11 : Mat4 R :=
  !![0, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0]

/-- Scalar multiplication in the concrete matrix frame. -/
def smul (c : R) (X : Mat4 R) : Mat4 R := c • X

instance : SMul R (Mat4 R) := ⟨fun c M i j => c * M i j⟩

/-- The matrix trace. -/
def tr4 (X : Mat4 R) : R := X 0 0 + X 1 1 + X 2 2 + X 3 3

/-- The explicit six-term Laplace determinant. -/
def det4 (A : Mat4 R) : R :=
  (A 0 0 * A 1 1 - A 1 0 * A 0 1) * (A 2 2 * A 3 3 - A 3 2 * A 2 3) +
  (A 0 0 * A 2 1 - A 2 0 * A 0 1) * (A 3 2 * A 1 3 - A 1 2 * A 3 3) +
  (A 0 0 * A 3 1 - A 3 0 * A 0 1) * (A 1 2 * A 2 3 - A 2 2 * A 1 3) +
  (A 2 0 * A 3 1 - A 3 0 * A 2 1) * (A 0 2 * A 1 3 - A 1 2 * A 0 3) +
  (A 3 0 * A 1 1 - A 1 0 * A 3 1) * (A 0 2 * A 2 3 - A 2 2 * A 0 3) +
  (A 1 0 * A 2 1 - A 2 0 * A 1 1) * (A 0 2 * A 3 3 - A 3 2 * A 0 3)

/-- A general vector in the Clifford frame. -/
def clVec (x1 x2 x3 x4 : R) : Mat4 R :=
  smul x1 E1 + smul x2 E2 + smul x3 E3 + smul x4 E4

/-- A general bivector in the Clifford frame. -/
def clBivec (p12 p13 p14 p23 p24 p34 : R) : Mat4 R :=
  smul p12 E12 + smul p13 E13 + smul p14 E14 +
  smul p23 E23 + smul p24 E24 + smul p34 E34

/-- The `SO(4,2)` conformal norm of a bivector. -/
def bivecNormI1 (p12 p13 p14 p23 p24 p34 : R) : R :=
  - p12 * p12 + p13 * p13 + p14 * p14 +
    p23 * p23 + p24 * p24 - p34 * p34

/-- The Plücker relation of `Gr(2,4)`. -/
def plueckerRel (p12 p13 p14 p23 p24 p34 : R) : R :=
  p12 * p34 - p13 * p24 + p14 * p23

set_option maxHeartbeats 4000000 in
/-- The Clifford square of a vector is the scalar quadratic form. -/
theorem clVec_sq (x1 x2 x3 x4 : R) :
    clVec x1 x2 x3 x4 * clVec x1 x2 x3 x4 =
      smul (x1 * x1 + x2 * x2 - x3 * x3 - x4 * x4) 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [clVec, E1, E2, E3, E4, smul, Matrix.mul_apply, Fin.sum_univ_four] <;>
    first | ring | rfl

set_option maxHeartbeats 4000000 in
/-- The determinant of a Clifford vector is the square of its quadratic form. -/
theorem clVec_det4 (x1 x2 x3 x4 : R) :
    det4 (clVec x1 x2 x3 x4) =
      (x1 * x1 + x2 * x2 - x3 * x3 - x4 * x4) *
        (x1 * x1 + x2 * x2 - x3 * x3 - x4 * x4) := by
  simp [det4, clVec, E1, E2, E3, E4, smul]
  first | ring | rfl

set_option maxHeartbeats 4000000 in
/-- The Clifford square of a bivector is `I₁ • 1 + 2 Q_Pl • ω`. -/
theorem clBivec_sq (p12 p13 p14 p23 p24 p34 : R) :
    clBivec p12 p13 p14 p23 p24 p34 * clBivec p12 p13 p14 p23 p24 p34 =
      smul (bivecNormI1 p12 p13 p14 p23 p24 p34) 1 +
        smul (2 * plueckerRel p12 p13 p14 p23 p24 p34) omega := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [clBivec, omega, bivecNormI1, plueckerRel,
      E1, E2, E3, E4, E12, E13, E14, E23, E24, E34,
      smul, Matrix.mul_apply, Fin.sum_univ_four] <;>
    first | ring | rfl

set_option maxHeartbeats 4000000 in
/-- The determinant of a bivector factors through the two chiral norms. -/
theorem clBivec_det4_factor (p12 p13 p14 p23 p24 p34 : R) :
    det4 (clBivec p12 p13 p14 p23 p24 p34) =
      (bivecNormI1 p12 p13 p14 p23 p24 p34 +
          2 * plueckerRel p12 p13 p14 p23 p24 p34) *
        (bivecNormI1 p12 p13 p14 p23 p24 p34 -
          2 * plueckerRel p12 p13 p14 p23 p24 p34) := by
  have hpoly : det4 (clBivec p12 p13 p14 p23 p24 p34) = (bivecNormI1 p12 p13 p14 p23 p24 p34 + 2 * plueckerRel p12 p13 p14 p23 p24 p34) * (bivecNormI1 p12 p13 p14 p23 p24 p34 - 2 * plueckerRel p12 p13 p14 p23 p24 p34) := by
    simp [det4, clBivec, bivecNormI1, plueckerRel,
      E1, E2, E3, E4, E12, E13, E14, E23, E24, E34, smul]
    first | ring | rfl
  exact hpoly

set_option maxHeartbeats 4000000 in
/-- The determinant of a bivector equals `I₁² - 4 Q_Pl²`. -/
theorem clBivec_det4 (p12 p13 p14 p23 p24 p34 : R) :
    det4 (clBivec p12 p13 p14 p23 p24 p34) =
      bivecNormI1 p12 p13 p14 p23 p24 p34 *
          bivecNormI1 p12 p13 p14 p23 p24 p34 -
        4 * (plueckerRel p12 p13 p14 p23 p24 p34 *
          plueckerRel p12 p13 p14 p23 p24 p34) := by
  rw [clBivec_det4_factor]
  let I := bivecNormI1 p12 p13 p14 p23 p24 p34
  let Q := plueckerRel p12 p13 p14 p23 p24 p34
  have hpoly : (I + 2 * Q) * (I - 2 * Q) = I * I - 4 * (Q * Q) := by
    first | ring | rfl
  simpa [I, Q] using hpoly

/-- On the Plücker locus, a nonzero scalar bivector norm gives a nonzero
determinant. Thus decomposability alone does not put a bivector on the
determinant hypersurface. This is stated as a determinant criterion; a matrix
rank conclusion additionally needs a field and the usual rank/determinant
theorem. -/
theorem clBivec_det4_ne_zero_of_plucker_zero_norm_ne_zero
    [NoZeroDivisors R] (p12 p13 p14 p23 p24 p34 : R)
    (hQ : plueckerRel p12 p13 p14 p23 p24 p34 = 0)
    (hI : bivecNormI1 p12 p13 p14 p23 p24 p34 ≠ 0) :
    det4 (clBivec p12 p13 p14 p23 p24 p34) ≠ 0 := by
  rw [clBivec_det4, hQ]
  simpa using mul_ne_zero hI hI

/-- Over a domain, the determinant-zero locus of the displayed bivector
representation is exactly the union of its two chiral quadratic loci. This is
the algebraic rank-boundary statement: it does not identify either component
with a specific matrix rank stratum without additional hypotheses. -/
theorem clBivec_det4_eq_zero_iff_chiral_factor_eq_zero
    [NoZeroDivisors R] (p12 p13 p14 p23 p24 p34 : R) :
    det4 (clBivec p12 p13 p14 p23 p24 p34) = 0 ↔
      bivecNormI1 p12 p13 p14 p23 p24 p34 +
          2 * plueckerRel p12 p13 p14 p23 p24 p34 = 0 ∨
        bivecNormI1 p12 p13 p14 p23 p24 p34 -
          2 * plueckerRel p12 p13 p14 p23 p24 p34 = 0 := by
  rw [clBivec_det4_factor]
  exact mul_eq_zero

/-- Concrete counterexample to the implication `Q_Pl = 0 → B² = 0`:
the bivector with `p13 = 1` has vanishing Plücker relation and determinant
one in the displayed real `Cl(2,2)` matrix representation. -/
theorem plucker_zero_does_not_force_bivector_singular :
    plueckerRel (0 : ℝ) 1 0 0 0 0 = 0 ∧
      det4 (clBivec (0 : ℝ) 1 0 0 0 0) = 1 ∧
      clBivec (0 : ℝ) 1 0 0 0 0 * clBivec (0 : ℝ) 1 0 0 0 0 = 1 := by
  refine ⟨by norm_num [plueckerRel], ?_, ?_⟩
  · norm_num [det4, clBivec, E12, E13, E14, E23, E24, E34,
      E1, E2, E3, E4, smul]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [clBivec, E12, E13, E14, E23, E24, E34,
        E1, E2, E3, E4, smul, Matrix.mul_apply, Fin.sum_univ_four]

/-- The chiral norm ratio is identically one on the Plücker quadric wherever
its denominator is nonzero. Consequently its differential along that locus
cannot provide a nonzero intrinsic form. This algebraic lemma does not define
an ambient residue or a canonical amplituhedron form. -/
theorem chiral_norm_ratio_eq_one_on_plucker_locus
    (p12 p13 p14 p23 p24 p34 : ℝ)
    (hQ : plueckerRel p12 p13 p14 p23 p24 p34 = 0)
    (hden : bivecNormI1 p12 p13 p14 p23 p24 p34 -
      2 * plueckerRel p12 p13 p14 p23 p24 p34 ≠ 0) :
    (bivecNormI1 p12 p13 p14 p23 p24 p34 +
      2 * plueckerRel p12 p13 p14 p23 p24 p34) /
      (bivecNormI1 p12 p13 p14 p23 p24 p34 -
      2 * plueckerRel p12 p13 p14 p23 p24 p34) = 1 := by
  have hden' : bivecNormI1 p12 p13 p14 p23 p24 p34 ≠ 0 := by
    simpa [hQ] using hden
  rw [hQ]
  simpa using div_self hden'

/-- The real logarithm of the chiral norm ratio also vanishes on the
Plücker locus wherever the ratio is defined. This is a scalar restriction
statement; it does not identify an ambient residue or an amplituhedron form. -/
theorem log_chiral_norm_ratio_eq_zero_on_plucker_locus
    (p12 p13 p14 p23 p24 p34 : ℝ)
    (hQ : plueckerRel p12 p13 p14 p23 p24 p34 = 0)
    (hden : bivecNormI1 p12 p13 p14 p23 p24 p34 -
      2 * plueckerRel p12 p13 p14 p23 p24 p34 ≠ 0) :
    Real.log ((bivecNormI1 p12 p13 p14 p23 p24 p34 +
      2 * plueckerRel p12 p13 p14 p23 p24 p34) /
      (bivecNormI1 p12 p13 p14 p23 p24 p34 -
      2 * plueckerRel p12 p13 p14 p23 p24 p34)) = 0 := by
  rw [chiral_norm_ratio_eq_one_on_plucker_locus p12 p13 p14 p23 p24 p34 hQ hden]
  simp

/-- On the simultaneous scalar and Plücker null locus, the represented
bivector is square-zero. This is a finite-matrix statement in the displayed
`Cl(2,2)` frame. -/
theorem clBivec_sq_zero_of_norms_vanish
    (p12 p13 p14 p23 p24 p34 : R)
    (hI : bivecNormI1 p12 p13 p14 p23 p24 p34 = 0)
    (hQ : plueckerRel p12 p13 p14 p23 p24 p34 = 0) :
    clBivec p12 p13 p14 p23 p24 p34 *
      clBivec p12 p13 p14 p23 p24 p34 = 0 := by
  rw [clBivec_sq, hI, hQ]
  simp [smul]

/-- Over `ℝ`, the represented bivector is square-zero exactly on the
simultaneous scalar-null and Plücker-null locus.  The converse reads the
`(0,0)` and `(2,2)` diagonal entries of the Clifford-square identity; their
sum and difference recover the two scalar invariants.  Thus decomposability
(`Q_Pl = 0`) alone is not the nilpotence condition. -/
theorem clBivec_sq_eq_zero_iff_norms_vanish
    (p12 p13 p14 p23 p24 p34 : ℝ) :
    clBivec p12 p13 p14 p23 p24 p34 *
        clBivec p12 p13 p14 p23 p24 p34 = 0 ↔
      bivecNormI1 p12 p13 p14 p23 p24 p34 = 0 ∧
        plueckerRel p12 p13 p14 p23 p24 p34 = 0 := by
  constructor
  · intro hB
    rw [clBivec_sq] at hB
    have h00 := congrArg (fun M : Mat4 ℝ => M 0 0) hB
    have h22 := congrArg (fun M : Mat4 ℝ => M 2 2) hB
    simp [smul, omega, E1, E2, E3, E4] at h00 h22
    have h22' : bivecNormI1 p12 p13 p14 p23 p24 p34 -
        2 * plueckerRel p12 p13 p14 p23 p24 p34 = 0 := by
      simpa [sub_eq_add_neg] using h22
    have hI2 : 2 * bivecNormI1 p12 p13 p14 p23 p24 p34 = 0 := by
      calc
        2 * bivecNormI1 p12 p13 p14 p23 p24 p34 =
            (bivecNormI1 p12 p13 p14 p23 p24 p34 +
              2 * plueckerRel p12 p13 p14 p23 p24 p34) +
            (bivecNormI1 p12 p13 p14 p23 p24 p34 -
              2 * plueckerRel p12 p13 p14 p23 p24 p34) := by noncomm_ring
        _ = 0 := by rw [h00, h22']; simp
    have hQ4 : 4 * plueckerRel p12 p13 p14 p23 p24 p34 = 0 := by
      calc
        4 * plueckerRel p12 p13 p14 p23 p24 p34 =
            (bivecNormI1 p12 p13 p14 p23 p24 p34 +
              2 * plueckerRel p12 p13 p14 p23 p24 p34) -
            (bivecNormI1 p12 p13 p14 p23 p24 p34 -
              2 * plueckerRel p12 p13 p14 p23 p24 p34) := by noncomm_ring
        _ = 0 := by rw [h00, h22']; simp
    constructor
    · rcases mul_eq_zero.mp hI2 with htwo | hI
      · norm_num at htwo
      · exact hI
    · rcases mul_eq_zero.mp hQ4 with hfour | hQ
      · norm_num at hfour
      · exact hQ
  · rintro ⟨hI, hQ⟩
    exact clBivec_sq_zero_of_norms_vanish p12 p13 p14 p23 p24 p34 hI hQ

/-- For a square-zero matrix `B`, the two displayed factors are mutual
inverses. This gives an actual inverse witness for `1 - B`, without assuming
that an arbitrary matrix is invertible. -/
theorem one_sub_add_nilpotent_inverse (B : Mat4 R) (hB : B * B = 0) :
    ((1 : Mat4 R) - B) * ((1 : Mat4 R) + B) = 1 ∧
      ((1 : Mat4 R) + B) * ((1 : Mat4 R) - B) = 1 := by
  constructor
  · calc
      ((1 : Mat4 R) - B) * ((1 : Mat4 R) + B) =
          1 - B * B := by noncomm_ring
      _ = 1 := by rw [hB]; simp
  · calc
      ((1 : Mat4 R) + B) * ((1 : Mat4 R) - B) =
          1 - B * B := by noncomm_ring
      _ = 1 := by rw [hB]; simp

/-- The nilpotent Cayley numerator `1 + 2B` has determinant one when `B` is
a bivector whose scalar and Plücker quadratic invariants both vanish.

This proves unmodularity for this explicit finite matrix representation. It
does not assert a group membership theorem or construct an amplituhedron. -/
theorem clBivec_nilpotent_cayley_det_one
    (p12 p13 p14 p23 p24 p34 : R)
    (hI : bivecNormI1 p12 p13 p14 p23 p24 p34 = 0)
    (hQ : plueckerRel p12 p13 p14 p23 p24 p34 = 0) :
    det4 (1 + smul 2 (clBivec p12 p13 p14 p23 p24 p34)) = 1 := by
  have hdet :
      det4 (1 + smul 2 (clBivec p12 p13 p14 p23 p24 p34)) =
        (1 - 4 * (bivecNormI1 p12 p13 p14 p23 p24 p34 +
          2 * plueckerRel p12 p13 p14 p23 p24 p34)) *
        (1 - 4 * (bivecNormI1 p12 p13 p14 p23 p24 p34 -
          2 * plueckerRel p12 p13 p14 p23 p24 p34)) := by
    have hpoly : det4 (1 + smul 2 (clBivec p12 p13 p14 p23 p24 p34)) = (1 - 4 * (bivecNormI1 p12 p13 p14 p23 p24 p34 + 2 * plueckerRel p12 p13 p14 p23 p24 p34)) * (1 - 4 * (bivecNormI1 p12 p13 p14 p23 p24 p34 - 2 * plueckerRel p12 p13 p14 p23 p24 p34)) := by
      simp [det4, clBivec, E12, E13, E14, E23, E24, E34,
        E1, E2, E3, E4, smul, bivecNormI1, plueckerRel]
      first | ring | rfl
    exact hpoly
  rw [hdet, hI, hQ]
  norm_num

/-- For real bivectors, the square-zero condition alone supplies the two
vanishing quadratic invariants needed for the unipotent Cayley determinant.
The coefficient carrier is explicitly `ℝ`, where the diagonal chiral
readouts separate the scalar and Plücker parts. -/
theorem clBivec_nilpotent_cayley_det_one_of_sq_zero
    (p12 p13 p14 p23 p24 p34 : ℝ)
    (hB : clBivec p12 p13 p14 p23 p24 p34 *
      clBivec p12 p13 p14 p23 p24 p34 = 0) :
    det4 (1 + smul 2 (clBivec p12 p13 p14 p23 p24 p34)) = 1 := by
  rcases (clBivec_sq_eq_zero_iff_norms_vanish
    p12 p13 p14 p23 p24 p34).mp hB with ⟨hI, hQ⟩
  exact clBivec_nilpotent_cayley_det_one p12 p13 p14 p23 p24 p34 hI hQ

/-- The two scaled chiral projectors `2Π₊ = 1 + ω` and `2Π₋ = 1 - ω`. -/
def Pi_plus_2 : Mat4 R := (1 : Mat4 R) + omega
/-- Twice the negative-chirality projector, `1 - ω`. -/
def Pi_minus_2 : Mat4 R := (1 : Mat4 R) - omega

/-- The bivector square is scalar on the positive chiral summand.  The
projectors are stored doubled (`1 ± ω`), so this equation avoids division by
two and holds over every commutative coefficient ring. -/
theorem clBivec_sq_positive_chiral
    (p12 p13 p14 p23 p24 p34 : R) :
    Pi_plus_2 *
        (clBivec p12 p13 p14 p23 p24 p34 * clBivec p12 p13 p14 p23 p24 p34) =
      smul (bivecNormI1 p12 p13 p14 p23 p24 p34 +
        2 * plueckerRel p12 p13 p14 p23 p24 p34) Pi_plus_2 := by
  rw [clBivec_sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Pi_plus_2, smul, omega, E1, E2, E3, E4,
      bivecNormI1, plueckerRel, Matrix.mul_apply, Fin.sum_univ_four] <;>
    first | ring | rfl

/-- The bivector square is scalar on the negative chiral summand. -/
theorem clBivec_sq_negative_chiral
    (p12 p13 p14 p23 p24 p34 : R) :
    Pi_minus_2 *
        (clBivec p12 p13 p14 p23 p24 p34 * clBivec p12 p13 p14 p23 p24 p34) =
      smul (bivecNormI1 p12 p13 p14 p23 p24 p34 -
        2 * plueckerRel p12 p13 p14 p23 p24 p34) Pi_minus_2 := by
  rw [clBivec_sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Pi_minus_2, smul, omega, E1, E2, E3, E4,
      bivecNormI1, plueckerRel, Matrix.mul_apply, Fin.sum_univ_four] <;>
    first | ring | rfl

/-- The inverse trace reconstruction with the sixteen signed Clifford coordinates. -/
def clReconstruct4 (M : Mat4 R) : Mat4 R :=
  smul (tr4 M) 1 +
  smul (tr4 (E1 * M)) E1 + smul (tr4 (E2 * M)) E2 -
  smul (tr4 (E3 * M)) E3 - smul (tr4 (E4 * M)) E4 -
  smul (tr4 (E12 * M)) E12 + smul (tr4 (E13 * M)) E13 +
  smul (tr4 (E14 * M)) E14 + smul (tr4 (E23 * M)) E23 +
  smul (tr4 (E24 * M)) E24 - smul (tr4 (E34 * M)) E34 -
  smul (tr4 (E234 * M)) E234 - smul (tr4 (E134 * M)) E134 +
  smul (tr4 (E124 * M)) E124 + smul (tr4 (E123 * M)) E123 +
  smul (tr4 (omega * M)) omega

/-- A real four-component twistor / two-qubit state. -/
@[ext]
structure Twistor4 (R : Type u) where
  z0 : R
  z1 : R
  z2 : R
  z3 : R

instance : Zero (Twistor4 R) := ⟨⟨0, 0, 0, 0⟩⟩
instance : Inhabited (Twistor4 R) := ⟨0⟩

/-- A four-component twistor is zero exactly when each spinor coordinate is
zero. This converts the coordinatewise representation into an extensional
criterion used by later kernel arguments. -/
theorem Twistor4.eq_zero_iff_coordinates_zero (Z : Twistor4 R) :
    Z = 0 ↔ Z.z0 = 0 ∧ Z.z1 = 0 ∧ Z.z2 = 0 ∧ Z.z3 = 0 := by
  constructor
  · intro h
    subst Z
    exact ⟨rfl, rfl, rfl, rfl⟩
  · rintro ⟨h0, h1, h2, h3⟩
    ext <;> assumption

/-- The half-Wootters concurrence, i.e. the `2 × 2` Segre determinant. -/
def segreDet (Z : Twistor4 R) : R :=
  Z.z0 * Z.z3 - Z.z1 * Z.z2

/-- Matrix action on a four-component twistor. -/
def applyMat (A : Mat4 R) (Z : Twistor4 R) : Twistor4 R :=
  ⟨A 0 0 * Z.z0 + A 0 1 * Z.z1 + A 0 2 * Z.z2 + A 0 3 * Z.z3,
   A 1 0 * Z.z0 + A 1 1 * Z.z1 + A 1 2 * Z.z2 + A 1 3 * Z.z3,
   A 2 0 * Z.z0 + A 2 1 * Z.z1 + A 2 2 * Z.z2 + A 2 3 * Z.z3,
   A 3 0 * Z.z0 + A 3 1 * Z.z1 + A 3 2 * Z.z2 + A 3 3 * Z.z3⟩

/-- The matrix whose columns are four twistors. -/
def twistorMatrix (Z1 Z2 Z3 Z4 : Twistor4 R) : Mat4 R :=
  !![Z1.z0, Z2.z0, Z3.z0, Z4.z0;
     Z1.z1, Z2.z1, Z3.z1, Z4.z1;
     Z1.z2, Z2.z2, Z3.z2, Z4.z2;
     Z1.z3, Z2.z3, Z3.z3, Z4.z3]

/-- The `SL(4)`-invariant four-twistor bracket. -/
def twistor4Bracket (Z1 Z2 Z3 Z4 : Twistor4 R) : R :=
  det4 (twistorMatrix Z1 Z2 Z3 Z4)

/-- A two-component spinor. -/
structure Spinor2 (R : Type u) where
  s1 : R
  s2 : R

instance : Inhabited (Spinor2 R) := ⟨⟨0, 0⟩⟩

/-- The spinor bracket `⟨a b⟩ = a₁b₂ - a₂b₁`. -/
def spinBrk (a b : Spinor2 R) : R :=
  a.s1 * b.s2 - a.s2 * b.s1

/-- The real spinor-helicity null momentum operator in the Clifford frame. -/
def ymSlashMomentum (lam tildeLam : Spinor2 R) : Mat4 R :=
  let p1 := lam.s1 * tildeLam.s1 - lam.s2 * tildeLam.s2
  let p2 := lam.s1 * tildeLam.s2 + lam.s2 * tildeLam.s1
  let p3 := lam.s1 * tildeLam.s2 - lam.s2 * tildeLam.s1
  let p4 := lam.s1 * tildeLam.s1 + lam.s2 * tildeLam.s2
  clVec p1 p2 p3 p4

/-- The upper-right chiral block of the split-Clifford slash momentum is the
outer product `2 λ λ̃ᵀ`.  Its displayed `2 × 2` minor vanishes, giving an
algebraic rank-at-most-one criterion for this block (over a field, matrix
rank follows from the usual minor criterion). -/
theorem ymSlashMomentum_chiral_block_factorization
    (lam tildeLam : Spinor2 R) :
    let P := ymSlashMomentum lam tildeLam
    P 0 2 = 2 * (lam.s1 * tildeLam.s1) ∧
    P 0 3 = 2 * (lam.s1 * tildeLam.s2) ∧
    P 1 2 = 2 * (lam.s2 * tildeLam.s1) ∧
    P 1 3 = 2 * (lam.s2 * tildeLam.s2) ∧
    P 0 2 * P 1 3 - P 0 3 * P 1 2 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    dsimp [ymSlashMomentum, clVec, E1, E2, E3, E4, smul] <;>
    first | ring | rfl

/-- The upper-right chiral block of a spinor-helicity momentum matrix has
rank at most one over a field.  This turns the displayed outer-product
factorization into an actual linear-algebra rank statement, rather than
leaving the rank criterion implicit in the vanishing minor. -/
theorem ymSlashMomentum_chiral_block_rank_le_one
    {K : Type*} [Field K] (lam tildeLam : Spinor2 K) :
    (Matrix.of ![![ymSlashMomentum lam tildeLam 0 2,
                    ymSlashMomentum lam tildeLam 0 3],
                  ![ymSlashMomentum lam tildeLam 1 2,
                    ymSlashMomentum lam tildeLam 1 3]]).rank ≤ 1 := by
  let left : Fin 2 → K := ![2 * lam.s1, 2 * lam.s2]
  let right : Fin 2 → K := ![tildeLam.s1, tildeLam.s2]
  have hfactor :
      (Matrix.of ![![ymSlashMomentum lam tildeLam 0 2,
                      ymSlashMomentum lam tildeLam 0 3],
                    ![ymSlashMomentum lam tildeLam 1 2,
                      ymSlashMomentum lam tildeLam 1 3]]) =
        Matrix.vecMulVec left right := by
    obtain ⟨h02, h03, h12, h13, _⟩ :=
      ymSlashMomentum_chiral_block_factorization lam tildeLam
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [left, right, Matrix.vecMulVec, h02, h03, h12, h13] <;> ring
  rw [hfactor]
  exact Matrix.rank_vecMulVec_le left right

/-- Spinor-helicity parameters give a square-zero slash operator, and the
upper-right chiral block has vanishing determinant. The second conclusion is
deduced from the explicit outer-product factorization above. -/
theorem ymSlashMomentum_null_and_chiral_minor_zero
    (lam tildeLam : Spinor2 R) :
    ymSlashMomentum lam tildeLam * ymSlashMomentum lam tildeLam = 0 ∧
      (ymSlashMomentum lam tildeLam) 0 2 *
          (ymSlashMomentum lam tildeLam) 1 3 -
        (ymSlashMomentum lam tildeLam) 0 3 *
          (ymSlashMomentum lam tildeLam) 1 2 = 0 := by
  constructor
  · dsimp [ymSlashMomentum]
    rw [clVec_sq]
    have hq :
        (lam.s1 * tildeLam.s1 - lam.s2 * tildeLam.s2) *
            (lam.s1 * tildeLam.s1 - lam.s2 * tildeLam.s2) +
          (lam.s1 * tildeLam.s2 + lam.s2 * tildeLam.s1) *
            (lam.s1 * tildeLam.s2 + lam.s2 * tildeLam.s1) -
          (lam.s1 * tildeLam.s2 - lam.s2 * tildeLam.s1) *
            (lam.s1 * tildeLam.s2 - lam.s2 * tildeLam.s1) -
          (lam.s1 * tildeLam.s1 + lam.s2 * tildeLam.s2) *
            (lam.s1 * tildeLam.s1 + lam.s2 * tildeLam.s2) = 0 := by
      first | ring | rfl
    rw [hq]
    simp [smul]
  · exact (ymSlashMomentum_chiral_block_factorization lam tildeLam).2.2.2.2

/-- The slash map is additive in its four momentum coordinates. This explicit
linearity lemma lets the two-particle invariant reduce to the Clifford square
of the summed momentum. -/
theorem clVec_add (a1 a2 a3 a4 b1 b2 b3 b4 : R) :
    clVec a1 a2 a3 a4 + clVec b1 b2 b3 b4 =
      clVec (a1 + b1) (a2 + b2) (a3 + b3) (a4 + b4) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [clVec, smul, E1, E2, E3, E4, Matrix.add_apply] <;>
    first | ring | rfl

/-- The square of the sum of two real spinor-helicity slash momenta is the
Mandelstam quadratic, with the angle and square brackets supplied by the two
spinor factors. This is an identity in the displayed finite matrix model. -/
theorem ymSlashMomentum_pair_square
    (lam1 tlam1 lam2 tlam2 : Spinor2 R) :
    (ymSlashMomentum lam1 tlam1 + ymSlashMomentum lam2 tlam2) *
        (ymSlashMomentum lam1 tlam1 + ymSlashMomentum lam2 tlam2) =
      smul (-4 * spinBrk lam1 lam2 * spinBrk tlam1 tlam2) 1 := by
  have hsum :
      ymSlashMomentum lam1 tlam1 + ymSlashMomentum lam2 tlam2 =
        clVec
          ((lam1.s1 * tlam1.s1 - lam1.s2 * tlam1.s2) +
            (lam2.s1 * tlam2.s1 - lam2.s2 * tlam2.s2))
          ((lam1.s1 * tlam1.s2 + lam1.s2 * tlam1.s1) +
            (lam2.s1 * tlam2.s2 + lam2.s2 * tlam2.s1))
          ((lam1.s1 * tlam1.s2 - lam1.s2 * tlam1.s1) +
            (lam2.s1 * tlam2.s2 - lam2.s2 * tlam2.s1))
          ((lam1.s1 * tlam1.s1 + lam1.s2 * tlam1.s2) +
            (lam2.s1 * tlam2.s1 + lam2.s2 * tlam2.s2)) := by
    dsimp [ymSlashMomentum]
    rw [clVec_add]
  rw [hsum, clVec_sq]
  have hmandel :
      (((lam1.s1 * tlam1.s1 - lam1.s2 * tlam1.s2) +
          (lam2.s1 * tlam2.s1 - lam2.s2 * tlam2.s2)) *
            ((lam1.s1 * tlam1.s1 - lam1.s2 * tlam1.s2) +
              (lam2.s1 * tlam2.s1 - lam2.s2 * tlam2.s2)) +
        ((lam1.s1 * tlam1.s2 + lam1.s2 * tlam1.s1) +
          (lam2.s1 * tlam2.s2 + lam2.s2 * tlam2.s1)) *
            ((lam1.s1 * tlam1.s2 + lam1.s2 * tlam1.s1) +
              (lam2.s1 * tlam2.s2 + lam2.s2 * tlam2.s1)) -
        ((lam1.s1 * tlam1.s2 - lam1.s2 * tlam1.s1) +
          (lam2.s1 * tlam2.s2 - lam2.s2 * tlam2.s1)) *
            ((lam1.s1 * tlam1.s2 - lam1.s2 * tlam1.s1) +
              (lam2.s1 * tlam2.s2 - lam2.s2 * tlam2.s1)) -
        ((lam1.s1 * tlam1.s1 + lam1.s2 * tlam1.s2) +
          (lam2.s1 * tlam2.s1 + lam2.s2 * tlam2.s2)) *
            ((lam1.s1 * tlam1.s1 + lam1.s2 * tlam1.s2) +
              (lam2.s1 * tlam2.s1 + lam2.s2 * tlam2.s2))) =
      -4 * spinBrk lam1 lam2 * spinBrk tlam1 tlam2 := by
    dsimp [spinBrk]
    first | ring | rfl
  rw [hmandel]

set_option maxHeartbeats 8000000 in
/-- Matrix multiplication is compatible with the explicit determinant. -/
theorem det4_mul (A B : Mat4 R) :
    det4 (A * B) = det4 A * det4 B := by
  have hpoly : det4 (A * B) = det4 A * det4 B := by
    simp [det4, Matrix.mul_apply, Fin.sum_univ_four]
    first | ring | rfl
  exact hpoly

/-- The twistor matrix of the transformed columns is the matrix product. -/
theorem twistorMatrix_applyMat (A : Mat4 R) (Z1 Z2 Z3 Z4 : Twistor4 R) :
    twistorMatrix (applyMat A Z1) (applyMat A Z2) (applyMat A Z3) (applyMat A Z4) =
      A * twistorMatrix Z1 Z2 Z3 Z4 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twistorMatrix, applyMat, Matrix.mul_apply, Fin.sum_univ_four]

/-- The four-twistor bracket is multiplied by `det4 A` under a linear transformation. -/
theorem twistor4Bracket_applyMat (A : Mat4 R) (Z1 Z2 Z3 Z4 : Twistor4 R) :
    twistor4Bracket (applyMat A Z1) (applyMat A Z2) (applyMat A Z3) (applyMat A Z4) =
      det4 A * twistor4Bracket Z1 Z2 Z3 Z4 := by
  rw [twistor4Bracket, twistor4Bracket, twistorMatrix_applyMat, det4_mul]

/-- The Cayley transform `(1 + B)(1 - B)⁻¹` reduces to `1 + 2B` when
`B² = 0`: the inverse factor is `1 + B`, and the product is unipotent. -/
theorem nilpotent_cayley_formula (B : Mat4 R) (hB : B * B = 0) :
    ((1 : Mat4 R) + B) * ((1 : Mat4 R) + B) =
      (1 : Mat4 R) + smul 2 B := by
  calc
    ((1 : Mat4 R) + B) * ((1 : Mat4 R) + B) =
        1 + B + B + B * B := by noncomm_ring
    _ = (1 : Mat4 R) + smul 2 B := by
      rw [hB]
      ext i j
      simp [smul]
      first | ring | rfl

/-- The unipotent Cayley matrix `1 + 2B` has the explicit inverse `1 - 2B`
when `B` is square-zero. This is a two-sided matrix identity, with no
determinant or abstract group assumption. -/
theorem nilpotent_cayley_two_sided_inverse (B : Mat4 R) (hB : B * B = 0) :
    ((1 : Mat4 R) + smul 2 B) * ((1 : Mat4 R) - smul 2 B) = 1 ∧
      ((1 : Mat4 R) - smul 2 B) * ((1 : Mat4 R) + smul 2 B) = 1 := by
  have hdouble : smul 2 B = B + B := by
    ext i j
    simp [smul, two_mul]
  have hdouble_sq : smul 2 B * smul 2 B = 0 := by
    rw [hdouble]
    calc
      (B + B) * (B + B) = B * B + B * B + (B * B + B * B) := by noncomm_ring
      _ = 0 := by rw [hB]; simp
  constructor
  · calc
      ((1 : Mat4 R) + smul 2 B) * ((1 : Mat4 R) - smul 2 B) =
          1 - smul 2 B * smul 2 B := by noncomm_ring
      _ = 1 := by rw [hdouble_sq]; simp
  · calc
      ((1 : Mat4 R) - smul 2 B) * ((1 : Mat4 R) + smul 2 B) =
          1 - smul 2 B * smul 2 B := by noncomm_ring
      _ = 1 := by rw [hdouble_sq]; simp

/-- Matrix action on a twistor respects composition. -/
theorem applyMat_mul (A B : Mat4 R) (Z : Twistor4 R) :
    applyMat (A * B) Z = applyMat A (applyMat B Z) := by
  apply Twistor4.ext <;>
    simp [applyMat, Matrix.mul_apply, Fin.sum_univ_four] <;>
    first | ring | rfl

/-- The square-zero Cayley action on four-component twistors is invertible;
the inverse action is induced by the opposite unipotent matrix. This is the
finite column-spinor action associated with the displayed `4 × 4` model. -/
theorem nilpotent_cayley_twistor_action_equiv (B : Mat4 R) (hB : B * B = 0)
    (Z : Twistor4 R) :
    applyMat (1 - smul 2 B) (applyMat (1 + smul 2 B) Z) = Z ∧
      applyMat (1 + smul 2 B) (applyMat (1 - smul 2 B) Z) = Z := by
  have hinv := nilpotent_cayley_two_sided_inverse B hB
  constructor
  · rw [← applyMat_mul, hinv.2]
    simp [applyMat]
  · rw [← applyMat_mul, hinv.1]
    simp [applyMat]

/-- A null bivector in the displayed split-Clifford frame induces a
determinant-one linear map on four-coordinate twistors, so their alternating
four-bracket is preserved. This is the finite algebraic bridge to the
twistor bracket; it does not assert a canonical amplituhedron form. -/
theorem clBivec_nilpotent_cayley_preserves_twistor_bracket
    (p12 p13 p14 p23 p24 p34 : R)
    (hI : bivecNormI1 p12 p13 p14 p23 p24 p34 = 0)
    (hQ : plueckerRel p12 p13 p14 p23 p24 p34 = 0)
    (Z1 Z2 Z3 Z4 : Twistor4 R) :
    twistor4Bracket
        (applyMat (1 + smul 2 (clBivec p12 p13 p14 p23 p24 p34)) Z1)
        (applyMat (1 + smul 2 (clBivec p12 p13 p14 p23 p24 p34)) Z2)
        (applyMat (1 + smul 2 (clBivec p12 p13 p14 p23 p24 p34)) Z3)
        (applyMat (1 + smul 2 (clBivec p12 p13 p14 p23 p24 p34)) Z4) =
      twistor4Bracket Z1 Z2 Z3 Z4 := by
  rw [twistor4Bracket_applyMat, clBivec_nilpotent_cayley_det_one p12 p13 p14 p23 p24 p34 hI hQ]
  simp

/-- The alternating five-twistor Plücker (Cramer/BCFW) syzygy, vector form. -/
theorem five_twistor_syzygy_vec (Z1 Z2 Z3 Z4 Z5 : Twistor4 R) :
    let b1234 := twistor4Bracket Z1 Z2 Z3 Z4
    let b1235 := twistor4Bracket Z1 Z2 Z3 Z5
    let b1245 := twistor4Bracket Z1 Z2 Z4 Z5
    let b1345 := twistor4Bracket Z1 Z3 Z4 Z5
    let b2345 := twistor4Bracket Z2 Z3 Z4 Z5
    (⟨b1234 * Z5.z0 - b1235 * Z4.z0 + b1245 * Z3.z0 -
        b1345 * Z2.z0 + b2345 * Z1.z0,
      b1234 * Z5.z1 - b1235 * Z4.z1 + b1245 * Z3.z1 -
        b1345 * Z2.z1 + b2345 * Z1.z1,
      b1234 * Z5.z2 - b1235 * Z4.z2 + b1245 * Z3.z2 -
        b1345 * Z2.z2 + b2345 * Z1.z2,
      b1234 * Z5.z3 - b1235 * Z4.z3 + b1245 * Z3.z3 -
        b1345 * Z2.z3 + b2345 * Z1.z3⟩ : Twistor4 R) = 0 := by
  simp [twistor4Bracket, twistorMatrix, det4, Matrix.of_apply]
  apply (Twistor4.eq_zero_iff_coordinates_zero _).2
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (try ring_nf at *) <;>
    (try ring) <;>
    (try norm_num)

/-- The cyclic all-plus five-twistor Plücker syzygy, vector form. -/
theorem five_twistor_cyclic_syzygy_vec (Z1 Z2 Z3 Z4 Z5 : Twistor4 R) :
    let c1234 := twistor4Bracket Z1 Z2 Z3 Z4
    let c2345 := twistor4Bracket Z2 Z3 Z4 Z5
    let c3451 := twistor4Bracket Z3 Z4 Z5 Z1
    let c4512 := twistor4Bracket Z4 Z5 Z1 Z2
    let c5123 := twistor4Bracket Z5 Z1 Z2 Z3
    (⟨c1234 * Z5.z0 + c2345 * Z1.z0 + c3451 * Z2.z0 +
        c4512 * Z3.z0 + c5123 * Z4.z0,
      c1234 * Z5.z1 + c2345 * Z1.z1 + c3451 * Z2.z1 +
        c4512 * Z3.z1 + c5123 * Z4.z1,
      c1234 * Z5.z2 + c2345 * Z1.z2 + c3451 * Z2.z2 +
        c4512 * Z3.z2 + c5123 * Z4.z2,
      c1234 * Z5.z3 + c2345 * Z1.z3 + c3451 * Z2.z3 +
        c4512 * Z3.z3 + c5123 * Z4.z3⟩ : Twistor4 R) = 0 := by
  simp [twistor4Bracket, twistorMatrix, det4, Matrix.of_apply]
  apply (Twistor4.eq_zero_iff_coordinates_zero _).2
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (try ring_nf at *) <;>
    (try ring) <;>
    (try norm_num)

/-- Reordering the cyclic brackets to the ordered Cramer brackets absorbs the
signs from the odd cyclic permutation of four entries. Thus the cyclic
all-plus formula is exactly the usual alternating five-column relation:
`⟨3451⟩ = -⟨1345⟩`, `⟨4512⟩ = ⟨1245⟩`, and
`⟨5123⟩ = -⟨1235⟩`. -/
theorem five_twistor_cyclic_bracket_signs (Z1 Z2 Z3 Z4 Z5 : Twistor4 R) :
    twistor4Bracket Z3 Z4 Z5 Z1 = -twistor4Bracket Z1 Z3 Z4 Z5 ∧
    twistor4Bracket Z4 Z5 Z1 Z2 = twistor4Bracket Z1 Z2 Z4 Z5 ∧
    twistor4Bracket Z5 Z1 Z2 Z3 = -twistor4Bracket Z1 Z2 Z3 Z5 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [twistor4Bracket, twistorMatrix, det4, Matrix.of_apply] <;>
    (try ring_nf at *) <;>
    (try ring) <;>
    (try norm_num)

end Mat4

end Clifford22
