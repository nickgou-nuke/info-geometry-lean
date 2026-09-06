import Mathlib.Data.Complex.Basic
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
blocks.  The statements are scalar or matrix identities over standard mathlib
objects: complex scalar discriminants and the standard `2 × 2` square-zero
unipotent shear.
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

/-- Parabolic scalar shadow: vanishing characteristic discriminant. -/
def IsScalarParabolic (a b q : ℂ) : Prop :=
  scalarDisc a b q = 0

/-- Loxodromic scalar shadow: nonzero imaginary part of the discriminant. -/
def IsScalarStrictlyLoxodromic (a b q : ℂ) : Prop :=
  (scalarDisc a b q).im ≠ 0

/-- The discriminant splits into diagonal gap squared plus off-diagonal contraction. -/
theorem scalarDisc_gap_split (a b q : ℂ) :
    scalarDisc a b q = (a - b) ^ 2 + 4 * q := by
  simp [scalarDisc, scalarTrace, scalarDet]
  ring

/-- A scalar loxodromic shadow is not parabolic. -/
theorem scalar_loxodromic_not_parabolic {a b q : ℂ}
    (h : IsScalarStrictlyLoxodromic a b q) :
    ¬ IsScalarParabolic a b q := by
  intro hpara
  exact h (by simpa [IsScalarParabolic] using congrArg Complex.im hpara)

/-- AI Studio alias: a loxodromic shadow is never parabolic. -/
theorem loxodromic_never_parabolic {a b q : ℂ}
    (h : IsScalarStrictlyLoxodromic a b q) :
    ¬ IsScalarParabolic a b q :=
  scalar_loxodromic_not_parabolic h

/-- AI Studio alias: the loxodromic phase split. -/
theorem loxodromic_phase_split (a b q : ℂ) :
    scalarDisc a b q = (a - b) ^ 2 + 4 * q :=
  scalarDisc_gap_split a b q

/--
If the diagonal gap square has real value and the discriminant has nonzero
imaginary part, then the off-diagonal contraction has nonzero imaginary part.
-/
theorem scalar_bosonic_real_forces_coupling_imag {a b q : ℂ}
    (hgap : ((a - b) ^ 2).im = 0)
    (hdisc : IsScalarStrictlyLoxodromic a b q) :
    q.im ≠ 0 := by
  intro hq
  apply hdisc
  rw [scalarDisc_gap_split]
  simp [Complex.add_im, Complex.mul_im, hgap, hq]

/-- AI Studio alias: bosonic reality forces an imaginary coupling. -/
theorem bosonic_real_forces_fermionic_dissipation {a b q : ℂ}
    (hgap : ((a - b) ^ 2).im = 0)
    (hdisc : IsScalarStrictlyLoxodromic a b q) :
    q.im ≠ 0 :=
  scalar_bosonic_real_forces_coupling_imag hgap hdisc

/-! ## Zorn spectral packet -/

/-- AI Studio alias: Cayley-Hamilton for split Zorn matrices. -/
theorem zorn_cayley_hamilton {R : Type*} [CommRing R]
    (X : InfoGeometry.Algebra.ZornMatrix R) :
    X * X - (InfoGeometry.Algebra.ZornMatrix.zornTrace X) • X +
        (InfoGeometry.Algebra.ZornMatrix.zornNorm X) •
          (InfoGeometry.Algebra.ZornMatrix.I : InfoGeometry.Algebra.ZornMatrix R) = 0 :=
  InfoGeometry.Algebra.ZornMatrix.cayley_hamilton X

/-- AI Studio alias: Fredholm-style quadratic determinant expansion. -/
theorem zorn_fredholm_expansion {R : Type*} [CommRing R]
    (t : R) (X : InfoGeometry.Algebra.ZornMatrix R) :
    InfoGeometry.Algebra.ZornMatrix.zornNorm
        ((InfoGeometry.Algebra.ZornMatrix.I : InfoGeometry.Algebra.ZornMatrix R) - t • X) =
      1 - t * InfoGeometry.Algebra.ZornMatrix.zornTrace X + t ^ 2 *
        InfoGeometry.Algebra.ZornMatrix.zornNorm X :=
  InfoGeometry.Algebra.ZornMatrix.fredholm_expansion t X

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

/-- AI Studio alias: the chiral discriminant split. -/
theorem discZ_chiral_split (a b q : ℂ) :
    scalarDisc a b q = chiralGap a b ^ 2 + 4 * interSheetCoupling q :=
  scalarDisc_chiral_split a b q

/-- If the gap and coupling vanish, the scalar shadow is parabolic. -/
theorem scalar_gap_and_coupling_zero_imply_parabolic {a b q : ℂ}
    (hgap : chiralGap a b = 0) (hcoup : interSheetCoupling q = 0) :
    IsScalarParabolic a b q := by
  dsimp [IsScalarParabolic]
  rw [scalarDisc_chiral_split, hgap, hcoup]
  ring

/-- AI Studio alias: pgg boundary plus defect node forces parabolicity. -/
theorem pgg_defect_implies_parabolic {a b q : ℂ}
    (h_pgg : chiralGap a b = 0) (h_node : interSheetCoupling q = 0) :
    IsScalarParabolic a b q :=
  scalar_gap_and_coupling_zero_imply_parabolic h_pgg h_node

/-! ## Native `2 × 2` square-zero shear packet -/

/-- The standard square-zero `2 × 2` shear generator. -/
def shearGenerator (R : Type*) [Zero R] [One R] : Matrix (Fin 2) (Fin 2) R :=
  !![0, 1; 0, 0]

/-- The standard shear generator is square-zero. -/
theorem shearGenerator_sq_zero {R : Type*} [NonAssocSemiring R] :
    shearGenerator R * shearGenerator R = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [shearGenerator, Matrix.mul_apply, Fin.sum_univ_two]

/-- The native unipotent shear `I + tN`. -/
def unipotentShear (R : Type*) [CommRing R] (t : R) : Matrix (Fin 2) (Fin 2) R :=
  1 + t • shearGenerator R

/-- Coordinate form of the native unipotent shear. -/
theorem unipotentShear_apply {R : Type*} [CommRing R] (t : R) :
    unipotentShear R t = !![1, t; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unipotentShear, shearGenerator]

/-- Additive composition law for native unipotent shears. -/
theorem unipotentShear_mul {R : Type*} [CommRing R] (s t : R) :
    unipotentShear R s * unipotentShear R t = unipotentShear R (s + t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unipotentShear_apply, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

/-- The native unipotent shear has determinant one. -/
theorem det_unipotentShear {R : Type*} [CommRing R] (t : R) :
    (unipotentShear R t).det = 1 := by
  rw [unipotentShear_apply]
  simp

/-- Packet bundling the square-zero, additive-flow, and determinant laws. -/
theorem native_unipotent_shear_packet {R : Type*} [CommRing R] (s t : R) :
    shearGenerator R * shearGenerator R = 0 ∧
      unipotentShear R s * unipotentShear R t = unipotentShear R (s + t) ∧
      (unipotentShear R t).det = 1 := by
  exact ⟨shearGenerator_sq_zero, unipotentShear_mul s t, det_unipotentShear t⟩

/-! ## Native `2 × 2` characteristic-polynomial packet -/

/-- Native mathlib characteristic-polynomial formula for a `2 × 2` complex matrix. -/
theorem native_charPoly2x2_eq (M : Matrix (Fin 2) (Fin 2) ℂ) (x : ℂ) :
    charPoly2x2 M x = x ^ 2 - Matrix.trace M * x + det2x2 M := by
  simpa using charPoly2x2_eq M x

/-- Determinant-one specialization of the native `2 × 2` characteristic polynomial. -/
theorem native_char_poly_eq_zhukovsky (M : Matrix (Fin 2) (Fin 2) ℂ) (x Tr : ℂ)
    (h_tr : Matrix.trace M = Tr) (h_det : det2x2 M = 1) :
    charPoly2x2 M x = x ^ 2 - Tr * x + 1 := by
  simpa [h_tr, h_det] using
    (char_poly_eq_zhukovsky M x Tr h_tr h_det)

end InfoGeometry.Algebra.AiStudioNativeMathlibFindings
