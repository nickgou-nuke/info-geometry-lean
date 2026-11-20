/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.HestenesClPlus14
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction

/-!
# Native real Hestenes currents and a singular even spinor

The carrier is the existing `HestenesCl14.ClPlus14`, the even subalgebra of
Mathlib's real Clifford algebra for signature `(+---)`. Reversion is
`CliffordAlgebra.reverse`; `sigmaEven 2` is the native product `γ₃ γ₀`.

The explicit spinor `ψ = 1 + γ₃ γ₀` satisfies `ψ reverse ψ = 0`, while both
its time-axis and third-axis sandwiches are the nonzero null vector
`2 (γ₀ + γ₃)`. Thus nonzero spinors need not have timelike Dirac current or
strictly spacelike axial current. The current is identified with the image
of an actual vector under the injective Clifford generator.

The final algebraic calculation isolates a right phase factor with square
`-1`, preserving multiplication order and the signs of both source terms.
It is not a differentiability or current-conservation theorem.

No general Fierz identity, scalar-part positivity theorem, hypersurface
norm, spectral energy bound, or field equation is asserted here.
-/

noncomputable section

namespace InfoGeometry.Canonical.HestenesNativeDiracCurrent

open HestenesCl14

/-- The native Clifford sandwich defining the Dirac current. -/
def diracCurrent (ψ : ClPlus14) : Cl14 :=
  (ψ : Cl14) * gamma 0 * CliffordAlgebra.reverse (ψ : Cl14)

/-- The axial sandwich with the explicitly chosen third spatial axis. -/
def axialCurrent (ψ : ClPlus14) : Cl14 :=
  (ψ : Cl14) * gamma 3 * CliffordAlgebra.reverse (ψ : Cl14)

private theorem reverse_gamma (i : Fin 4) :
    CliffordAlgebra.reverse (gamma i) = gamma i := by
  simp [gamma]

private theorem gamma_zero_three :
    gamma 0 * gamma 3 = -(gamma 3 * gamma 0) :=
  eq_neg_of_add_eq_zero_left (gamma_anticomm (i := 0) (j := 3) (by decide))

private theorem gamma_three_zero_sq :
    (gamma 3 * gamma 0) * (gamma 3 * gamma 0) = (1 : Cl14) := by
  calc
    (gamma 3 * gamma 0) * (gamma 3 * gamma 0) =
        gamma 3 * (gamma 0 * gamma 3) * gamma 0 := by noncomm_ring
    _ = -(gamma 3 * gamma 3) * (gamma 0 * gamma 0) := by
      rw [gamma_zero_three]
      noncomm_ring
    _ = 1 := by rw [gamma_three_sq, gamma_zero_sq]; norm_num

/-- A native even spinor with vanishing product with its reverse. -/
def singularSpinor : ClPlus14 := 1 + sigmaEven 2

@[simp] theorem singularSpinor_val :
    (singularSpinor : Cl14) = 1 + gamma 3 * gamma 0 := rfl

@[simp] theorem reverse_singularSpinor :
    CliffordAlgebra.reverse (singularSpinor : Cl14) =
      1 - gamma 3 * gamma 0 := by
  rw [singularSpinor_val]
  simp only [map_add, CliffordAlgebra.reverse.map_one,
    CliffordAlgebra.reverse.map_mul, reverse_gamma, gamma_zero_three,
    sub_eq_add_neg]

/-- Singularity is an equality in the full native Clifford algebra. -/
theorem singularSpinor_mul_reverse :
    (singularSpinor : Cl14) * CliffordAlgebra.reverse (singularSpinor : Cl14) =
      0 := by
  rw [reverse_singularSpinor, singularSpinor_val]
  calc
    (1 + gamma 3 * gamma 0) * (1 - gamma 3 * gamma 0) =
        1 - (gamma 3 * gamma 0) * (gamma 3 * gamma 0) := by noncomm_ring
    _ = 0 := by rw [gamma_three_zero_sq]; simp

private theorem singularSpinor_mul_time :
    (singularSpinor : Cl14) * gamma 0 = gamma 0 + gamma 3 := by
  rw [singularSpinor_val]
  calc
    (1 + gamma 3 * gamma 0) * gamma 0 =
        gamma 0 + gamma 3 * (gamma 0 * gamma 0) := by noncomm_ring
    _ = gamma 0 + gamma 3 := by rw [gamma_zero_sq]; simp

private theorem singularSpinor_mul_space :
    (singularSpinor : Cl14) * gamma 3 = gamma 0 + gamma 3 := by
  rw [singularSpinor_val]
  calc
    (1 + gamma 3 * gamma 0) * gamma 3 =
        gamma 3 + gamma 3 * (gamma 0 * gamma 3) := by noncomm_ring
    _ = gamma 3 - (gamma 3 * gamma 3) * gamma 0 := by
      rw [gamma_zero_three]
      noncomm_ring
    _ = gamma 0 + gamma 3 := by rw [gamma_three_sq]; noncomm_ring

/-- The Dirac sandwich is computed using the noncommutative Clifford product. -/
theorem diracCurrent_singularSpinor :
    diracCurrent singularSpinor = (2 : ℝ) • (gamma 0 + gamma 3) := by
  rw [diracCurrent, singularSpinor_mul_time, reverse_singularSpinor]
  calc
    (gamma 0 + gamma 3) * (1 - gamma 3 * gamma 0) =
        gamma 0 + gamma 3 - (gamma 0 * gamma 3) * gamma 0 -
          (gamma 3 * gamma 3) * gamma 0 := by noncomm_ring
    _ = gamma 0 + gamma 3 + gamma 3 * (gamma 0 * gamma 0) + gamma 0 := by
      rw [gamma_zero_three, gamma_three_sq]
      noncomm_ring
    _ = (2 : ℝ) • (gamma 0 + gamma 3) := by
      rw [gamma_zero_sq]
      simp only [mul_one, two_smul]
      abel

/-- In this singular case the axial and Dirac currents coincide. -/
theorem axialCurrent_singularSpinor_eq_diracCurrent :
    axialCurrent singularSpinor = diracCurrent singularSpinor := by
  simp only [axialCurrent, diracCurrent, singularSpinor_mul_time,
    singularSpinor_mul_space]

/-- The actual Minkowski vector represented by the singular spinor's current. -/
def singularCurrentVector : V14 := (2 : ℝ) • (basisVec 0 + basisVec 3)

theorem diracCurrent_singularSpinor_eq_iota :
    diracCurrent singularSpinor = ι14 singularCurrentVector := by
  rw [diracCurrent_singularSpinor]
  simp [singularCurrentVector, gamma]

@[simp] theorem singularCurrentVector_time : singularCurrentVector 0 = 2 := by
  norm_num [singularCurrentVector, basisVec]

@[simp] theorem singularCurrentVector_quadratic : Q14 singularCurrentVector = 0 := by
  norm_num [Q14_apply, singularCurrentVector, basisVec, qCoeff, Fin.sum_univ_succ]

/-- The native Clifford generator is injective, via Mathlib's exterior equivalence. -/
theorem iota_injective : Function.Injective ι14 := by
  intro x y h
  have he := congrArg (CliffordAlgebra.equivExterior Q14) h
  exact (ExteriorAlgebra.ι_inj ℝ x y).mp (by
    simpa [CliffordAlgebra.equivExterior, CliffordAlgebra.changeForm_ι] using he)

/-- The vanishing current square is not caused by the current being zero. -/
theorem diracCurrent_singularSpinor_ne_zero : diracCurrent singularSpinor ≠ 0 := by
  intro h
  have hi : ι14 singularCurrentVector = ι14 (0 : V14) := by
    rw [← diracCurrent_singularSpinor_eq_iota, map_zero]
    exact h
  have hv : singularCurrentVector = 0 := iota_injective hi
  have ht := congrFun hv 0
  norm_num at ht

theorem singularSpinor_ne_zero : singularSpinor ≠ 0 := by
  intro h
  apply diracCurrent_singularSpinor_ne_zero
  simp [h, diracCurrent]

/-- Nullness is the native Clifford vector-square identity. -/
theorem diracCurrent_singularSpinor_sq :
    diracCurrent singularSpinor * diracCurrent singularSpinor = 0 := by
  calc
    diracCurrent singularSpinor * diracCurrent singularSpinor =
        ι14 singularCurrentVector * ι14 singularCurrentVector :=
      congrArg (fun x : Cl14 => x * x) diracCurrent_singularSpinor_eq_iota
    _ = 0 := by
      rw [CliffordAlgebra.ι_sq_scalar, singularCurrentVector_quadratic]
      simp

theorem axialCurrent_singularSpinor_ne_zero : axialCurrent singularSpinor ≠ 0 := by
  rw [axialCurrent_singularSpinor_eq_diracCurrent]
  exact diracCurrent_singularSpinor_ne_zero

theorem axialCurrent_singularSpinor_sq :
    axialCurrent singularSpinor * axialCurrent singularSpinor = 0 := by
  simpa only [axialCurrent_singularSpinor_eq_diracCurrent] using
    diracCurrent_singularSpinor_sq

/-- A concrete counterexample to excluding null currents for all nonzero spinors. -/
theorem exists_nonzero_spinor_with_nonzero_null_current :
    ∃ ψ : ClPlus14, ψ ≠ 0 ∧ diracCurrent ψ ≠ 0 ∧
      diracCurrent ψ * diracCurrent ψ = 0 :=
  ⟨singularSpinor, singularSpinor_ne_zero,
    diracCurrent_singularSpinor_ne_zero, diracCurrent_singularSpinor_sq⟩

/-! ## Isolating a right phase factor -/

/-- Both source terms acquire the same negative sign when a right factor
whose square is `-1` is removed. No factors are commuted. -/
theorem right_phase_equation_iff {A : Type*} [Ring A]
    (D B G M : A) (hB : B * B = -1) :
    D * B - G = M ↔ D = -(M + G) * B := by
  constructor
  · intro h
    have hDB : D * B = M + G := sub_eq_iff_eq_add.mp h
    have hm := congrArg (fun x : A => x * (-B)) hDB
    simpa only [mul_neg, neg_mul, mul_assoc, hB, mul_one, neg_neg] using hm
  · intro h
    rw [h]
    calc
      (-(M + G) * B) * B - G = -(M + G) * (B * B) - G := by
        rw [mul_assoc]
      _ = M := by rw [hB]; noncomm_ring

/-- The fixed real Hestenes phase bivector `γ₂ γ₁`. -/
def phasePlane : Cl14 := gamma 2 * gamma 1

@[simp] theorem phasePlane_sq : phasePlane * phasePlane = (-1 : Cl14) := by
  have h12 : gamma 1 * gamma 2 = -(gamma 2 * gamma 1) :=
    eq_neg_of_add_eq_zero_left (gamma_anticomm (i := 1) (j := 2) (by decide))
  change (gamma 2 * gamma 1) * (gamma 2 * gamma 1) = (-1 : Cl14)
  calc
    (gamma 2 * gamma 1) * (gamma 2 * gamma 1) =
        gamma 2 * (gamma 1 * gamma 2) * gamma 1 := by noncomm_ring
    _ = -(gamma 2 * gamma 2) * (gamma 1 * gamma 1) := by
      rw [h12]
      noncomm_ring
    _ = -1 := by rw [gamma_two_sq, gamma_one_sq]; norm_num

/-- Algebraic isolation for the real minimally coupled Dirac-Hestenes equation.
`D` is only an algebra element here; an analytic derivative is not supplied. -/
theorem hestenes_equation_isolate
    (D A : Cl14) (ψ : ClPlus14) (charge mass : ℝ)
    (h : D * phasePlane - charge • (A * (ψ : Cl14)) =
      mass • ((ψ : Cl14) * gamma 0)) :
    D = -(mass • ((ψ : Cl14) * gamma 0) + charge • (A * (ψ : Cl14))) *
      phasePlane :=
  (right_phase_equation_iff D phasePlane
    (charge • (A * (ψ : Cl14))) (mass • ((ψ : Cl14) * gamma 0)) phasePlane_sq).mp h

end InfoGeometry.Canonical.HestenesNativeDiracCurrent

end noncomputable section
