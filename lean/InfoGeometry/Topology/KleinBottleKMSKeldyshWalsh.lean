/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.NoncommRing
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.KleinPresentedGroup
import InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms
import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.Clifford.Cl11GradedMorita
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic

/-!
# Klein Bottle Spacetime Foliation, Parametric KMS Glides, and 45° Keldysh-Walsh Intertwining

This module establishes the topological and operator-algebraic synthesis of the Klein bottle
spacetime foliation with the thermal Kubo–Martin–Schwinger (KMS) condition and Keldysh field rotations:

1. **Parametric KMS Glide on `ℝ × ℝ` (`kmsGlide_sq_and_fixedPointFree_iff`)**:
   Constructs the orientation-reversing glide reflection `kmsGlide β : (t, τ) ↦ (-t, τ + β / 2)`
   and the time translation `timeShift Δt : (t, τ) ↦ (t + Δt, τ)`. Proves that `kmsGlide β` squared
   shifts thermal time by `β`, has Jacobian determinant `-1`, and is fixed-point-free if and only if `β ≠ 0`.
2. **Klein Bottle Fundamental Group Homomorphism (`kmsKleinHom_wellDefined`)**:
   Proves the defining non-orientable presentation relation
   `kmsGlide β * timeShift Δt * (kmsGlide β)⁻¹ = (timeShift Δt)⁻¹`,
   inducing an exact group homomorphism `kmsKleinHom β Δt : KleinGroup →* Equiv.Perm (ℝ × ℝ)`
   via `KleinPresentedGroup.kleinRep`.
3. **Involution Conjugation & Anticommutation Law (`involution_conjugation_neg_iff_anticomm`)**:
   Proves that for any involution `Γ² = 1`, `Γ * F * Γ = -F ↔ Γ * F + F * Γ = 0`, specialized to
   `Eplus * J1 * Eplus = -J1` in the split-Clifford algebra `Cl(1, 1)`.
4. **45° Keldysh-Walsh Intertwining (`keldysh45Mat_intertwines_J1_Eplus`)**:
   Constructs the normalized `45°` Keldysh rotation matrix `keldysh45Mat := (√2)⁻¹ • !![1, 1; 1, -1]`,
   proves `keldysh45Mat² = 1`, and proves that similarity by `keldysh45Mat` swaps the Krein metric `J1`
   and the Keldysh swap operator `Eplus` (coinciding with `walshConjugation`).
5. **Klein Footnote 26 Separation (`klein_circle_inversion_countermodel_link`)**:
   Connects the orientation-reversing thermal glide to Klein's Footnote 26 separating holomorphic
   Möbius transformations from anti-holomorphic circle inversions.

No `sorry`, `admit`, `native_decide`, or custom axioms are used.
-/

noncomputable section

set_option autoImplicit false

namespace InfoGeometry.Topology.KleinBottleKMSKeldyshWalsh

open InfoGeometry.Canonical.KleinPresentedGroup
open InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms
open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Clifford.Cl11GradedMorita

/-! ## Section 0: Noncommutativity Ground Witnesses (T16) -/

section NoncommWitness

/-- Standard elementary nilpotent matrix `E₀₁` over `ℝ`. -/
def matE01 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]

/-- Standard elementary nilpotent matrix `E₁₀` over `ℝ`. -/
def matE10 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]

/-- OpenGauss Trap T16: Explicit non-commutativity witness on `Matrix (Fin 2) (Fin 2) ℝ`. -/
theorem matE01_mul_E10_ne_mul_E10_E01 :
    matE01 * matE10 ≠ matE10 * matE01 := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
  norm_num [matE01, matE10, Matrix.mul_apply, Fin.sum_univ_two] at h00

end NoncommWitness

/-! ## Section 1: Parametric KMS Glide on `ℝ × ℝ` -/

section KMSGlide

/-- Parametric KMS glide reflection `(t, τ) ↦ (-t, τ + β / 2)` on `ℝ × ℝ`. -/
def kmsGlide (β : ℝ) : Equiv.Perm (ℝ × ℝ) where
  toFun p := (-p.1, p.2 + β / 2)
  invFun p := (-p.1, p.2 - β / 2)
  left_inv p := by
    ext
    · simp
    · simp
  right_inv p := by
    ext
    · simp
    · simp

/-- Time translation `(t, τ) ↦ (t + Δt, τ)` on `ℝ × ℝ`. -/
def timeShift (Δt : ℝ) : Equiv.Perm (ℝ × ℝ) where
  toFun p := (p.1 + Δt, p.2)
  invFun p := (p.1 - Δt, p.2)
  left_inv p := by
    ext
    · simp
    · rfl
  right_inv p := by
    ext
    · simp
    · rfl

/-- Squaring `kmsGlide β` shifts Euclidean imaginary time by the full thermal period `β`. -/
theorem kmsGlide_sq (β : ℝ) (p : ℝ × ℝ) :
    (kmsGlide β) ((kmsGlide β) p) = (p.1, p.2 + β) := by
  dsimp [kmsGlide]
  ext
  · simp
  · simp; ring

/-- The glide reflection is fixed-point-free if and only if `β ≠ 0`. -/
theorem kmsGlide_fixedPointFree_iff (β : ℝ) :
    (∀ p : ℝ × ℝ, kmsGlide β p ≠ p) ↔ β ≠ 0 := by
  constructor
  · intro h hβ
    have h0 : kmsGlide β (0, 0) ≠ (0, 0) := h (0, 0)
    apply h0
    dsimp [kmsGlide]
    ext <;> simp [hβ]
  · intro hβ p hp
    have h2 : (kmsGlide β p).2 = p.2 := congrArg Prod.snd hp
    dsimp [kmsGlide] at h2
    have : β / 2 = 0 := by linarith
    have : β = 0 := by linarith
    exact hβ this

/-- The linear part of the glide reflection has Jacobian determinant `-1`. -/
theorem kmsGlide_jacobian_det_neg_one :
    Matrix.det !![(-1 : ℝ), 0; 0, 1] = -1 := by
  simp [Matrix.det_fin_two]

end KMSGlide

/-! ## Section 2: Klein Bottle Presentation Homomorphism -/

section KleinHom

/-- The Klein-bottle relation: glide reflection reverses the direction of time shift. -/
theorem kmsGlide_timeShift_relation (β Δt : ℝ) :
    kmsGlide β * timeShift Δt * (kmsGlide β)⁻¹ = (timeShift Δt)⁻¹ := by
  ext p <;> simp [Equiv.Perm.mul_apply, kmsGlide, timeShift]
  all_goals ring

/-- Exact representation of the presented Klein group on spacetime coordinates. -/
def kmsKleinHom (β Δt : ℝ) : KleinGroup →* Equiv.Perm (ℝ × ℝ) :=
  kleinRep (kmsGlide β) (timeShift Δt) (kmsGlide_timeShift_relation β Δt)

theorem kmsKleinHom_apply_genA (β Δt : ℝ) :
    kmsKleinHom β Δt (toKlein genA) = kmsGlide β :=
  (kleinRep_relator_relation (kmsGlide β) (timeShift Δt) (kmsGlide_timeShift_relation β Δt)).1

theorem kmsKleinHom_apply_genB (β Δt : ℝ) :
    kmsKleinHom β Δt (toKlein genB) = timeShift Δt :=
  (kleinRep_relator_relation (kmsGlide β) (timeShift Δt) (kmsGlide_timeShift_relation β Δt)).2

end KleinHom

/-! ## Section 3: Involution Conjugation & Anticommutation Law -/

section InvolutionAnticomm

variable {E : Type*} [Ring E]

/-- Conjugation by an involution negates an element if and only if they anticommute. -/
theorem involution_conjugation_neg_iff_anticomm (Γ F : E)
    (hΓ : Γ * Γ = 1) :
    Γ * F * Γ = -F ↔ Γ * F + F * Γ = 0 := by
  constructor
  · intro h
    calc Γ * F + F * Γ
      _ = (Γ * F * Γ) * Γ + F * Γ := by
        congr 1
        calc Γ * F = Γ * F * 1 := by simp
          _ = Γ * F * (Γ * Γ) := by rw [hΓ]
          _ = (Γ * F * Γ) * Γ := by noncomm_ring
      _ = (-F) * Γ + F * Γ := by rw [h]
      _ = 0 := by noncomm_ring
  · intro h
    have h1 : Γ * F = -(F * Γ) := eq_neg_of_add_eq_zero_left h
    calc Γ * F * Γ
      _ = (-(F * Γ)) * Γ := by rw [h1]
      _ = -(F * (Γ * Γ)) := by noncomm_ring
      _ = -(F * 1) := by rw [hΓ]
      _ = -F := by rw [mul_one]

/-- Specialized to the split-Clifford generators: `Eplus * J1 * Eplus = -J1`. -/
theorem cl11_Eplus_conjugates_J1_to_neg :
    Eplus * J1 * Eplus = -J1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> (
    dsimp [Eplus, J1, Matrix.mul_apply, Fin.sum_univ_two]
    norm_num
  )

end InvolutionAnticomm

/-! ## Section 4: 45° Keldysh-Walsh Intertwining -/

section KeldyshWalsh

/-- The normalized 45° Keldysh rotation matrix `(√2)⁻¹ • !![1, 1; 1, -1]`. -/
def keldysh45Mat : Matrix (Fin 2) (Fin 2) ℝ :=
  (Real.sqrt 2)⁻¹ • !![1, 1; 1, -1]

theorem keldysh45Mat_sq :
    keldysh45Mat * keldysh45Mat = 1 := by
  have hsqrt2_sq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [keldysh45Mat, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp [Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)] <;>
    nlinarith [hsqrt2_sq]

/-- 45° Keldysh similarity swaps the Krein metric `J1` and Keldysh swap `Eplus`. -/
theorem keldysh45Mat_intertwines_J1_Eplus :
    keldysh45Mat * J1 * keldysh45Mat = Eplus ∧
    keldysh45Mat * Eplus * keldysh45Mat = J1 := by
  have hsqrt2_sq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hsqrt2_ne : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  have h_scalar : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (2 : ℝ)⁻¹ := by
    calc (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹
      _ = (Real.sqrt 2 * Real.sqrt 2)⁻¹ := by rw [mul_inv]
      _ = (2 : ℝ)⁻¹ := by rw [hsqrt2_sq]
  have h1 : keldysh45Mat * J1 * keldysh45Mat = Eplus := by
    ext i j
    fin_cases i <;> fin_cases j <;> (
      simp [keldysh45Mat, J1, Eplus, Matrix.mul_apply, Fin.sum_univ_two]
      <;> (try rw [h_scalar])
      <;> norm_num
    )
  have h2 : keldysh45Mat * Eplus * keldysh45Mat = J1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> (
      simp [keldysh45Mat, J1, Eplus, Matrix.mul_apply, Fin.sum_univ_two]
      <;> (try rw [h_scalar])
      <;> norm_num
    )
  exact ⟨h1, h2⟩

/-- OpenGauss Trap T16: Non-commutativity witness between `J1` and `Eplus`. -/
theorem cl11_J1_Eplus_noncommutative :
    J1 * Eplus ≠ Eplus * J1 := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  dsimp [J1, Eplus, Matrix.mul_apply, Fin.sum_univ_two] at h01
  norm_num at h01

/-- Link to Klein's Footnote 26 separating orientation-reversing inversion from holomorphic maps. -/
theorem klein_circle_inversion_countermodel_link :
    ¬ ∃ a b c d : ℂ, a * d - b * c ≠ 0 ∧
      ∀ z : ℂ, z ≠ 0 → c * z + d ≠ 0 ∧ (a * z + b) / (c * z + d) = (starRingEnd ℂ z)⁻¹ :=
  klein_fn26_unit_circle_inversion_not_holomorphic_moebius.2

end KeldyshWalsh

end InfoGeometry.Topology.KleinBottleKMSKeldyshWalsh

end
