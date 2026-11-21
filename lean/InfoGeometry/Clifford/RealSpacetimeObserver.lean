/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Clifford.RealSpacetimeSpinor
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Reversion, observer positivity, and a real two-plane bound

Both forms are defined by noncommutative Clifford products before the scalar
readout. The proved quaternion coordinate equivalence gives the complete
split and positive normal forms, including all cross terms. Positivity and
the two-plane inequality concern the fixed timelike observer form.
-/

noncomputable section

namespace InfoGeometry.Clifford.RealSpacetimeObserver

open HestenesCl14 HestenesKreinMatrixBridge HestenesHermitianAdjoint
open RealSpacetimeQuaternion RealSpacetimeSpinor

def quaternionDot (p q : Quaternion ℝ) : ℝ := (p * star q).re

theorem quaternionDot_coordinates (p q : Quaternion ℝ) :
    quaternionDot p q = p.re * q.re + p.imI * q.imI +
      p.imJ * q.imJ + p.imK * q.imK := by
  simp [quaternionDot]

theorem quaternionDot_comm (p q : Quaternion ℝ) : quaternionDot p q = quaternionDot q p := by
  simp only [quaternionDot_coordinates]
  ring

theorem quaternionDot_neg_right (p q : Quaternion ℝ) :
    quaternionDot p (-q) = -quaternionDot p q := by
  simp [quaternionDot_coordinates]
  ring

@[simp] theorem quaternionDot_self (p : Quaternion ℝ) :
    quaternionDot p p = Quaternion.normSq p := rfl

/-- The scalar part of the product with native Clifford reversion. -/
def krein (x y : ClPlus14) : ℝ := scalar ((x : Cl14) * (reverseEven y : Cl14))

/-- The scalar part of the product with the existing observer adjoint. -/
def observer (x y : ClPlus14) : ℝ := scalar ((x : Cl14) * (hestenesAdjoint y : Cl14))

theorem krein_coordinates (x y : ClPlus14) :
    krein x y = quaternionDot (spinorCoordinates x).1 (spinorCoordinates y).1 -
      quaternionDot (spinorCoordinates x).2 (spinorCoordinates y).2 := by
  change scalar ((x * reverseEven y : ClPlus14) : Cl14) = _
  rw [scalar_even, spinorCoordinates_mul, spinorCoordinates_reverseEven]
  simp [quaternionDot]

theorem observer_coordinates (x y : ClPlus14) :
    observer x y = quaternionDot (spinorCoordinates x).1 (spinorCoordinates y).1 +
      quaternionDot (spinorCoordinates x).2 (spinorCoordinates y).2 := by
  change scalar ((x * hestenesAdjoint y : ClPlus14) : Cl14) = _
  rw [scalar_even, spinorCoordinates_mul, spinorCoordinates_hestenesAdjoint]
  simp [quaternionDot]

/-- The complete reversion normal form: four positive and four negative real coordinates. -/
theorem krein_self (x : ClPlus14) :
    krein x x = Quaternion.normSq (spinorCoordinates x).1 -
      Quaternion.normSq (spinorCoordinates x).2 := by
  simp [krein_coordinates]

/-- The observer form is the sum of all eight coordinate squares. -/
theorem observer_self (x : ClPlus14) :
    observer x x = Quaternion.normSq (spinorCoordinates x).1 +
      Quaternion.normSq (spinorCoordinates x).2 := by
  simp [observer_coordinates]

theorem observer_nonneg (x : ClPlus14) : 0 ≤ observer x x := by
  rw [observer_self]
  exact add_nonneg Quaternion.normSq_nonneg Quaternion.normSq_nonneg

@[simp] theorem observer_self_eq_zero (x : ClPlus14) : observer x x = 0 ↔ x = 0 := by
  rw [observer_self, add_eq_zero_iff_of_nonneg
    Quaternion.normSq_nonneg Quaternion.normSq_nonneg,
    Quaternion.normSq_eq_zero, Quaternion.normSq_eq_zero]
  constructor
  · rintro ⟨hp, hq⟩
    apply spinorCoordinates_injective
    simpa only [map_zero] using Prod.ext hp hq
  · rintro rfl
    simp

theorem observer_pos {x : ClPlus14} (hx : x ≠ 0) : 0 < observer x x :=
  lt_of_le_of_ne (observer_nonneg x) (Ne.symm ((observer_self_eq_zero x).not.mpr hx))

theorem observer_comm (x y : ClPlus14) : observer x y = observer y x := by
  simp only [observer_coordinates, quaternionDot_comm]

@[simp] theorem observer_zero_left (x : ClPlus14) : observer 0 x = 0 := by
  simp [observer]

@[simp] theorem observer_zero_right (x : ClPlus14) : observer x 0 = 0 := by
  rw [observer_comm]
  exact observer_zero_left x

theorem observer_add_left (x y z : ClPlus14) : observer (x + y) z = observer x z + observer y z := by
  simp [observer, add_mul]

theorem observer_add_right (x y z : ClPlus14) : observer x (y + z) = observer x y + observer x z := by
  simp [observer, mul_add]

theorem observer_smul_left (r : ℝ) (x y : ClPlus14) : observer (r • x) y = r * observer x y := by
  simp [observer, smul_mul_assoc]

theorem observer_smul_right (r : ℝ) (x y : ClPlus14) : observer x (r • y) = r * observer x y := by
  simp [observer, mul_smul_comm]

theorem observer_sub_left (x y z : ClPlus14) : observer (x - y) z = observer x z - observer y z := by
  simp [observer, sub_mul]

theorem observer_sub_right (x y z : ClPlus14) : observer x (y - z) = observer x y - observer x z := by
  rw [observer_comm, observer_sub_left, observer_comm y x, observer_comm z x]

/-- A native real bilinear form on the native even Clifford algebra. -/
def observerForm : LinearMap.BilinForm ℝ ClPlus14 :=
  LinearMap.mk₂ ℝ observer observer_add_left observer_smul_left
    observer_add_right observer_smul_right

/-- Conjugation by the timelike vector, using the existing native involutions. -/
def observerConjugation (x : ClPlus14) : ClPlus14 := reverseEven (hestenesAdjoint x)

theorem observerConjugation_val (x : ClPlus14) :
    (observerConjugation x : Cl14) = gamma 0 * (x : Cl14) * gamma 0 := by
  change CliffordAlgebra.reverse (hestenesAdjoint x : Cl14) = _
  rw [hestenesAdjoint_val]
  simp [CliffordAlgebra.reverse.map_mul, gamma, mul_assoc]

theorem spinorCoordinates_observerConjugation (x : ClPlus14) :
    spinorCoordinates (observerConjugation x) =
      ((spinorCoordinates x).1, -(spinorCoordinates x).2) := by
  simp [observerConjugation, spinorCoordinates_reverseEven,
    spinorCoordinates_hestenesAdjoint]

theorem observerConjugation_involutive (x : ClPlus14) :
    observerConjugation (observerConjugation x) = x := by
  apply spinorCoordinates_injective
  simp [spinorCoordinates_observerConjugation]

theorem krein_observerConjugation (x y : ClPlus14) :
    krein x (observerConjugation y) = observer x y := by
  rw [krein_coordinates, spinorCoordinates_observerConjugation,
    observer_coordinates]
  simp [quaternionDot_neg_right]

theorem krein_nondegenerate (x : ClPlus14) (hx : ∀ y, krein x y = 0) : x = 0 := by
  have h := hx (observerConjugation x)
  rw [krein_observerConjugation] at h
  exact (observer_self_eq_zero x).mp h

/-- Closed null-vector counterexample to the indefinite Cauchy--Schwarz bound. -/
theorem krein_cauchy_schwarz_fails :
    ∃ x y : ClPlus14, krein x x * krein y y < (krein x y) ^ 2 := by
  refine ⟨spinorOfCoordinates (1, 1), spinorOfCoordinates (1, -1), ?_⟩
  norm_num [krein_coordinates, quaternionDot, spinorCoordinates_spinorOfCoordinates]

/-- The fixed right spin-plane bivector is the actual native product `γ₂γ₁`. -/
def phaseBivector : ClPlus14 := evenPair 2 1

@[simp] theorem spinorCoordinates_phaseBivector :
    spinorCoordinates phaseBivector = (-quaternionK, 0) := by
  change (quaternionRep (gamma 2 * gamma 1) 0 0,
    quaternionRep (gamma 2 * gamma 1) 0 1) = _
  simp only [map_mul, quaternionRep_gamma]
  ext <;> simp [vectorMatrix, basisVec, quaternionK, Matrix.mul_apply, Fin.sum_univ_two]

theorem phaseBivector_sq : phaseBivector * phaseBivector = -1 := by
  apply spinorCoordinates_injective
  rw [spinorCoordinates_mul, spinorCoordinates_phaseBivector]
  ext <;> simp [spinorCoordinates, quaternionK]

/-- Right multiplication is a real linear operator, with no commutation assumption. -/
def rightPhase : ClPlus14 →ₗ[ℝ] ClPlus14 where
  toFun x := x * phaseBivector
  map_add' x y := add_mul x y phaseBivector
  map_smul' r x := smul_mul_assoc r x phaseBivector

theorem rightPhase_sq (x : ClPlus14) : rightPhase (rightPhase x) = -x := by
  change (x * phaseBivector) * phaseBivector = -x
  rw [mul_assoc, phaseBivector_sq]
  simp

theorem rightPhase_left_mul (a x : ClPlus14) : rightPhase (a * x) = a * rightPhase x :=
  mul_assoc a x phaseBivector

theorem spinorCoordinates_rightPhase (x : ClPlus14) :
    spinorCoordinates (rightPhase x) =
      ((spinorCoordinates x).1 * (-quaternionK), (spinorCoordinates x).2 * (-quaternionK)) := by
  change spinorCoordinates (x * phaseBivector) = _
  rw [spinorCoordinates_mul, spinorCoordinates_phaseBivector]
  simp

theorem observer_rightPhase (x y : ClPlus14) :
    observer (rightPhase x) (rightPhase y) = observer x y := by
  simp only [observer_coordinates, spinorCoordinates_rightPhase]
  simp [quaternionDot_coordinates, quaternionK]
  ring

theorem observer_rightPhase_skew (x y : ClPlus14) :
    observer (rightPhase x) y = -observer x (rightPhase y) := by
  simp only [observer_coordinates, spinorCoordinates_rightPhase]
  simp [quaternionDot_coordinates, quaternionK]
  ring

@[simp] theorem observer_rightPhase_self (x : ClPlus14) : observer x (rightPhase x) = 0 := by
  have h := observer_rightPhase_skew x x
  rw [observer_comm (rightPhase x) x] at h
  linarith

/-- Symplectic normalization: `omega(x,y) = 2 G(Jx,y)`. -/
def omega (x y : ClPlus14) : ℝ := 2 * observer (rightPhase x) y

/-- The right-phase pairing as a native real bilinear form. -/
def omegaForm : LinearMap.BilinForm ℝ ClPlus14 :=
  LinearMap.mk₂ ℝ omega
    (by intro x y z; simp [omega, observer_add_left, mul_add])
    (by
      intro r x y
      simpa only [omega, map_smul, observer_smul_left, smul_eq_mul] using
        mul_left_comm (2 : ℝ) r (observer (rightPhase x) y))
    (by intro x y z; simp [omega, observer_add_right, mul_add])
    (by
      intro r x y
      simpa only [omega, observer_smul_right, smul_eq_mul] using
        mul_left_comm (2 : ℝ) r (observer (rightPhase x) y))

@[simp] theorem omegaForm_apply (x y : ClPlus14) : omegaForm x y = omega x y := rfl

theorem omega_alternating (x : ClPlus14) : omega x x = 0 := by
  rw [omega, observer_comm, observer_rightPhase_self, mul_zero]

theorem omega_skew (x y : ClPlus14) : omega x y = -omega y x := by
  rw [omega, omega, observer_rightPhase_skew, observer_comm x (rightPhase y)]
  ring

theorem omega_nondegenerate (x : ClPlus14) (hx : ∀ y, omega x y = 0) : x = 0 := by
  have h := hx (rightPhase x)
  rw [omega, observer_rightPhase] at h
  apply (observer_self_eq_zero x).mp
  linarith

/-- Alternation is recorded at Mathlib's bilinear-form interface. -/
theorem omegaForm_isAlt : omegaForm.IsAlt := omega_alternating

/-- Both left and right separation hold for the native alternating form. -/
theorem omegaForm_nondegenerate : omegaForm.Nondegenerate := by
  constructor
  · intro x hx
    exact omega_nondegenerate x hx
  · intro x hx
    apply omega_nondegenerate x
    intro y
    rw [omega_skew]
    exact neg_eq_zero.mpr (hx y)

/-- Real two-plane Bessel inequality, proved from positivity of an explicit residual. -/
theorem observer_two_plane_bound (x y : ClPlus14) :
    (observer x y) ^ 2 + (observer (rightPhase x) y) ^ 2 ≤ observer x x * observer y y := by
  by_cases hx : x = 0
  · simp [hx]
  have hpos := observer_pos hx
  let r := observer x x • y - observer x y • x - observer (rightPhase x) y • rightPhase x
  have hres : observer r r = observer x x *
      (observer x x * observer y y - (observer x y) ^ 2 -
        (observer (rightPhase x) y) ^ 2) := by
    simp only [r, observer_sub_left, observer_sub_right,
      observer_smul_left, observer_smul_right]
    rw [observer_rightPhase, observer_rightPhase_self,
      observer_comm (rightPhase x) x, observer_rightPhase_self,
      observer_comm y x, observer_comm y (rightPhase x)]
    ring
  have hnonneg := observer_nonneg r
  rw [hres] at hnonneg
  have h := nonneg_of_mul_nonneg_right hnonneg hpos
  linarith

/-- The same bound with the explicitly doubled symplectic normalization. -/
theorem observer_symplectic_bound (x y : ClPlus14) :
    (observer x y) ^ 2 + (omega x y) ^ 2 / 4 ≤ observer x x * observer y y := by
  have h := observer_two_plane_bound x y
  dsimp [omega]
  nlinarith

/-- The time component of the algebraic current is the positive observer norm. -/
theorem current_time_eq_observer (x : ClPlus14) :
    scalar ((x : Cl14) * gamma 0 * CliffordAlgebra.reverse (x : Cl14) * gamma 0) =
      observer x x := by
  rw [observer, hestenesAdjoint_val]
  simp only [mul_assoc]

end InfoGeometry.Clifford.RealSpacetimeObserver
