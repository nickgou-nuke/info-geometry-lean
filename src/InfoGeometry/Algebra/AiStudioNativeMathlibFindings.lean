/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Basic.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
import InfoGeometry.Algebra.ZornMatrix
import InfoGeometry.Canonical.SL2CZhukovsky

namespace InfoGeometry.Algebra.AiStudioNativeMathlibFindings

open Matrix
open InfoGeometry.Canonical.SL2CZhukovsky

/-!
# Native mathlib extraction of AI Studio algebraic findings

This file records the mathlib-native algebraic core of selected AI Studio code
blocks. Scalar discriminant results are stated as exact locus characterizations;
the Zorn pencil formula retains ordered commutator corrections over a general
ring, and the shear results concern explicit finite matrices.

## BUCKET 1: Proved
Exact discriminant loci, noncommutative Zorn characteristic and pencil
identities, finite shear laws, and `2 × 2` characteristic-root criteria.

## BUCKET 2: Conditional
Zorn Cayley–Hamilton vanishing is conditional on the four displayed anomaly
components vanishing; no commutativity of the coefficient ring is assumed.

## BUCKET 3: Open boundary
No infinite-dimensional representation, analytic spectrum, or physical
interpretation is established by these finite algebraic statements.
-/

/-! ## Complex scalar discriminant packet -/

/-- Trace scalar `a + b` for a two-eigenvalue shadow. -/
def scalarTrace (a b : ℂ) : ℂ :=
  a + b

/-- Determinant scalar `ab - q`, where `q` is the off-diagonal contraction. -/
def scalarDet (a b q : ℂ) : ℂ :=
  a * b - q

/-- Characteristic discriminant `tr² - 4 det`. -/
def scalarDisc (a b q : ℂ) : ℂ :=
  scalarTrace a b ^ 2 - 4 * scalarDet a b q

/-- The discriminant splits into diagonal gap squared plus off-diagonal contraction. -/
theorem scalarDisc_gap_split (a b q : ℂ) :
    scalarDisc a b q = (a - b) ^ 2 + 4 * q := by
  simp [scalarDisc, scalarTrace, scalarDet]
  ring

/-- A scalar loxodromic shadow is not parabolic. -/
theorem scalar_loxodromic_not_parabolic {a b q : ℂ}
    (h : (scalarDisc a b q).im ≠ 0) :
    scalarDisc a b q ≠ 0 := by
  intro hpara
  exact h (by rw [hpara]; simp)

/-- The imaginary part of the discriminant is the gap-square contribution
plus four times the imaginary part of the off-diagonal coupling. -/
theorem scalarDisc_imaginary_part (a b q : ℂ) :
    (scalarDisc a b q).im = ((a - b) ^ 2).im + 4 * q.im := by
  rw [scalarDisc_gap_split]
  simp [Complex.add_im, Complex.mul_im]

/-- Exact equation of the scalar parabolic locus in terms of the coupling. -/
theorem loxodromic_phase_split (a b q : ℂ) :
    scalarDisc a b q = 0 ↔ q = -((a - b) ^ 2) / 4 := by
  rw [scalarDisc_gap_split]
  constructor
  · intro h
    have hq : 4 * q = -((a - b) ^ 2) := by
      linear_combination h
    calc
      q = (4 * q) / 4 := by ring
      _ = -((a - b) ^ 2) / 4 := by rw [hq]
  · intro h
    rw [h]
    ring

/--
If the diagonal gap square has real value and the discriminant has nonzero
imaginary part, then the off-diagonal contraction has nonzero imaginary part.
-/
theorem scalar_bosonic_real_forces_coupling_imag {a b q : ℂ}
    (hgap : ((a - b) ^ 2).im = 0)
    (hdisc : (scalarDisc a b q).im ≠ 0) :
    q.im ≠ 0 := by
  intro hq
  apply hdisc
  rw [scalarDisc_gap_split]
  simp [Complex.add_im, Complex.mul_im, hgap, hq]

/-- Under a real-valued gap square, the discriminant is loxodromic exactly
when the coupling has nonzero imaginary part. -/
theorem bosonic_real_forces_fermionic_dissipation {a b q : ℂ}
    (hgap : ((a - b) ^ 2).im = 0)
    : q.im ≠ 0 ↔ (scalarDisc a b q).im ≠ 0 := by
  have him : (scalarDisc a b q).im = 4 * q.im := by
    rw [scalarDisc_imaginary_part, hgap]
    simp
  change q.im ≠ 0 ↔ (scalarDisc a b q).im ≠ 0
  rw [him]
  constructor
  · intro h
    exact mul_ne_zero (by norm_num : (4 : ℝ) ≠ 0) h
  · intro h
    by_contra hq
    exact h (by simp [hq])

/-! ## Zorn spectral packet -/

/-- A Zorn matrix satisfies its characteristic equation over a possibly
noncommutative ring whenever each component of the exact characteristic
anomaly vanishes. -/
theorem zorn_cayley_hamilton {R : Type*} [Ring R]
    (X : InfoGeometry.Algebra.ZornMatrix R)
    (h_ab : X.a * X.b = X.b * X.a)
    (h_ww : InfoGeometry.Algebra.Vec3.cross X.w X.w = 0)
    (h_vv : InfoGeometry.Algebra.Vec3.cross X.v X.v = 0)
    (h_dot : InfoGeometry.Algebra.Vec3.dot X.w X.v =
      InfoGeometry.Algebra.Vec3.dot X.v X.w) :
    X * X - (InfoGeometry.Algebra.ZornMatrix.zornTrace X) • X +
        (InfoGeometry.Algebra.ZornMatrix.zornNorm X) •
          (InfoGeometry.Algebra.ZornMatrix.I : InfoGeometry.Algebra.ZornMatrix R) = 0 := by
  rw [InfoGeometry.Algebra.ZornMatrix.zorn_characteristic_anomaly_over_noncomm_ring]
  have hvec0 : (0 : InfoGeometry.Algebra.Vec3 R) = ![0, 0, 0] := by
    funext i
    fin_cases i <;> rfl
  apply InfoGeometry.Algebra.ZornMatrix.ext
  · change X.a * X.b - X.b * X.a = 0
    exact sub_eq_zero.mpr h_ab
  · change InfoGeometry.Algebra.Vec3.sub ![0, 0, 0]
      (InfoGeometry.Algebra.Vec3.cross X.w X.w) = ![0, 0, 0]
    funext i
    fin_cases i <;>
      simp [InfoGeometry.Algebra.Vec3.sub, h_ww]
  · change InfoGeometry.Algebra.Vec3.cross X.v X.v = ![0, 0, 0]
    exact h_vv.trans hvec0
  · change InfoGeometry.Algebra.Vec3.dot X.w X.v -
      InfoGeometry.Algebra.Vec3.dot X.v X.w = 0
    exact sub_eq_zero.mpr h_dot

/-- Ordered coordinate expansion of the Zorn pencil norm, valid without any
commutativity assumption on `t` or the operator entries. -/
theorem zorn_fredholm_expansion {R : Type*} [Ring R]
    (t : R) (X : InfoGeometry.Algebra.ZornMatrix R) :
    InfoGeometry.Algebra.ZornMatrix.zornNorm
        ((InfoGeometry.Algebra.ZornMatrix.I : InfoGeometry.Algebra.ZornMatrix R) - t • X) =
      (1 - t * X.a) * (1 - t * X.b) -
        ((0 - t * X.v 0) * (0 - t * X.w 0) +
          (0 - t * X.v 1) * (0 - t * X.w 1) +
          (0 - t * X.v 2) * (0 - t * X.w 2)) := by
  simp [InfoGeometry.Algebra.ZornMatrix.zornNorm,
    InfoGeometry.Algebra.ZornMatrix.I,
    InfoGeometry.Algebra.Vec3.dot, InfoGeometry.Algebra.Vec3.sub,
    InfoGeometry.Algebra.Vec3.smul]

/-- The chiral scalar gap used by the extracted Brillouin-zone proposal. -/
def chiralGap (a b : ℂ) : ℂ :=
  a - b

/-- The off-diagonal inter-sheet coupling scalar. -/
def interSheetCoupling (q : ℂ) : ℂ :=
  q

/-- The discriminant is gap squared plus four times the inter-sheet coupling. -/
theorem scalarDisc_chiral_split (a b q : ℂ) :
    scalarDisc a b q = chiralGap a b ^ 2 + 4 * interSheetCoupling q := by
  simpa [chiralGap, interSheetCoupling] using scalarDisc_gap_split a b q

/-- The chiral discriminant vanishes exactly on the corresponding affine
coupling locus. -/
theorem discZ_chiral_split (a b q : ℂ) :
    scalarDisc a b q = 0 ↔
      interSheetCoupling q = -(chiralGap a b) ^ 2 / 4 := by
  rw [scalarDisc_chiral_split]
  constructor
  · intro h
    have hq : 4 * interSheetCoupling q = -(chiralGap a b) ^ 2 := by
      linear_combination h
    calc
      interSheetCoupling q = (4 * interSheetCoupling q) / 4 := by ring
      _ = -(chiralGap a b) ^ 2 / 4 := by rw [hq]
  · intro h
    rw [h]
    ring

/-- If the gap and coupling vanish, the scalar shadow is parabolic. -/
theorem scalar_gap_and_coupling_zero_imply_parabolic {a b q : ℂ}
    (hgap : chiralGap a b = 0) (hcoup : interSheetCoupling q = 0) :
    scalarDisc a b q = 0 := by
  rw [scalarDisc_chiral_split, hgap, hcoup]
  ring

/-- On the zero-gap boundary, parabolicity is equivalent to vanishing coupling. -/
theorem pgg_defect_implies_parabolic {a b q : ℂ}
    (h_pgg : chiralGap a b = 0) :
    scalarDisc a b q = 0 ↔ interSheetCoupling q = 0 := by
  rw [scalarDisc_chiral_split, h_pgg]
  simp [interSheetCoupling]

/-! ## Native `2 × 2` square-zero shear packet -/

/-- The standard square-zero `2 × 2` shear generator. -/
def shearGenerator {R : Type*} [Zero R] [One R] : Matrix (Fin 2) (Fin 2) R :=
  !![0, 1; 0, 0]

/-- The opposite matrix unit used to witness noncommutativity with the shear. -/
def lowerShearGenerator {R : Type*} [Zero R] [One R] : Matrix (Fin 2) (Fin 2) R :=
  !![0, 0; 1, 0]

/-- The standard shear generator is square-zero. -/
theorem shearGenerator_sq_zero {R : Type*} [NonAssocSemiring R] :
    (shearGenerator : Matrix (Fin 2) (Fin 2) R) * shearGenerator = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [shearGenerator, Matrix.mul_apply, Fin.sum_univ_two]

/-- The native unipotent shear `I + tN`. -/
def unipotentShear (R : Type*) [Ring R] (t : R) : Matrix (Fin 2) (Fin 2) R :=
  1 + t • (shearGenerator : Matrix (Fin 2) (Fin 2) R)

/-- Coordinate form of the native unipotent shear. -/
theorem unipotentShear_apply {R : Type*} [Ring R] (t : R) :
    unipotentShear R t = !![1, t; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unipotentShear, shearGenerator]

/-- Additive composition law for native unipotent shears. -/
theorem unipotentShear_mul {R : Type*} [Ring R] (s t : R) :
    unipotentShear R s * unipotentShear R t = unipotentShear R (s + t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unipotentShear_apply, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

/-- The parameter-negated shear is both a left and right inverse. -/
theorem unipotentShear_inverse {R : Type*} [Ring R] (t : R) :
    unipotentShear R t * unipotentShear R (-t) = 1 ∧
      unipotentShear R (-t) * unipotentShear R t = 1 := by
  constructor
  · rw [unipotentShear_mul, add_neg_cancel, unipotentShear_apply]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  · rw [unipotentShear_mul, neg_add_cancel, unipotentShear_apply]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

/-- The native unipotent shear has determinant one. -/
theorem det_unipotentShear {R : Type*} [CommRing R] (t : R) :
    (unipotentShear R t).det = 1 := by
  rw [unipotentShear_apply]
  simp

/-- The shear laws combine nilpotency, additive composition, inversion, and
the determinant-one property over a commutative coefficient ring. -/
theorem native_unipotent_shear_packet {R : Type*} [CommRing R] (s t : R) :
    (shearGenerator : Matrix (Fin 2) (Fin 2) R) * shearGenerator = 0 ∧
      unipotentShear R s * unipotentShear R t = unipotentShear R (s + t) ∧
      (unipotentShear R t * unipotentShear R (-t) = 1) ∧
      (unipotentShear R t).det = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [shearGenerator_sq_zero]
  · exact unipotentShear_mul s t
  · exact (unipotentShear_inverse t).1
  · rw [det_unipotentShear]

/-! ## Native `2 × 2` characteristic-polynomial packet -/

/-- A complex number is a characteristic root exactly when it satisfies the
explicit trace-determinant quadratic for this `2 × 2` matrix. -/
theorem native_charPoly2x2_root_iff_quadratic
    (M : Matrix (Fin 2) (Fin 2) ℂ) (x : ℂ) :
    charPoly2x2 M x = 0 ↔
      x ^ 2 - Matrix.trace M * x + det2x2 M = 0 := by
  rw [charPoly2x2_eq]

/-- For a determinant-one matrix, nonzero characteristic roots are exactly
the solutions of its Zhukovsky trace relation. -/
theorem native_char_poly_eq_zhukovsky (M : Matrix (Fin 2) (Fin 2) ℂ) (x Tr : ℂ)
    (h_tr : Matrix.trace M = Tr) (h_det : det2x2 M = 1) :
    x ≠ 0 → (charPoly2x2 M x = 0 ↔ x + x⁻¹ = Tr) := by
  intro hx
  exact charPoly2x2_root_iff_zhukovsky_relation M x Tr h_tr h_det hx

/-! ## Non-commutativity witness (T16 compliance) -/

/-- The `2×2` matrix algebra is non-commutative over a nontrivial ring. -/
theorem matrix_fin2_noncommutative {R : Type*} [Ring R] [Nontrivial R] :
    (shearGenerator : Matrix (Fin 2) (Fin 2) R) *
        (lowerShearGenerator : Matrix (Fin 2) (Fin 2) R) ≠
      lowerShearGenerator * shearGenerator := by
  apply ne_of_apply_ne (fun M => M 0 0)
  simp [shearGenerator, lowerShearGenerator, Matrix.mul_apply,
    Fin.sum_univ_two]

end InfoGeometry.Algebra.AiStudioNativeMathlibFindings
