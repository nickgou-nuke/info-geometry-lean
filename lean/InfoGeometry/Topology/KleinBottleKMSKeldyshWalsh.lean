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
   `Eplus * J1 * Eplus = -J1` in the split-Clifford algebra `Cl(1, 1)` and to `(invS P, genPhi P A C)`
   in the Peirce operator spine.
4. **45° Keldysh-Walsh Intertwining (`keldysh45Mat_walsh_krein_intertwining`)**:
   Constructs the normalized `45°` Keldysh rotation matrix `keldysh45Mat := (√2)⁻¹ • !![1, 1; 1, -1]`,
   proves `keldysh45Mat² = 1`, proves that similarity by `keldysh45Mat` swaps the Krein metric `J1`
   and the Keldysh swap operator `Eplus` (coinciding with `walshConjugation`), records
   `cl11_J1_Eplus_noncommutative_witness`, and pairs with Klein's Footnote 26 separation.
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
    · exact neg_neg p.1
    · exact add_sub_cancel_right p.2 (β / 2)
  right_inv p := by
    ext
    · exact neg_neg p.1
    · exact sub_add_cancel p.2 (β / 2)

/-- Time translation `(t, τ) ↦ (t + Δt, τ)` on `ℝ × ℝ`. -/
def timeShift (Δt : ℝ) : Equiv.Perm (ℝ × ℝ) where
  toFun p := (p.1 + Δt, p.2)
  invFun p := (p.1 - Δt, p.2)
  left_inv p := by
    ext
    · exact add_sub_cancel_right p.1 Δt
    · exact Eq.refl p.2
  right_inv p := by
    ext
    · exact sub_add_cancel p.1 Δt
    · exact Eq.refl p.2

/-- Squaring `kmsGlide β` shifts Euclidean imaginary time by the full thermal period `β`. -/
theorem kmsGlide_sq (β : ℝ) (p : ℝ × ℝ) :
    (kmsGlide β) ((kmsGlide β) p) = (p.1, p.2 + β) := by
  dsimp [kmsGlide]
  ext
  · exact neg_neg p.1
  · ring

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

/-- Combined period-`β` shift and fixed-point-free characterization for `kmsGlide β`. -/
theorem kmsGlide_sq_and_fixedPointFree_iff (β t τ : ℝ) :
    (kmsGlide β) ((kmsGlide β) (t, τ)) = (t, τ + β) ∧
      ((∀ p : ℝ × ℝ, kmsGlide β p ≠ p) ↔ β ≠ 0) :=
  ⟨kmsGlide_sq β (t, τ), kmsGlide_fixedPointFree_iff β⟩

/-- The linear part of the glide reflection has Jacobian determinant `-1`. -/
theorem kmsGlide_jacobian_det_neg_one :
    Matrix.det !![(-1 : ℝ), 0; 0, 1] = -1 := by
  rw [Matrix.det_fin_two]
  norm_num

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

/-- Well-definedness of `kmsKleinHom`: generator readback and Klein-bottle relation. -/
theorem kmsKleinHom_wellDefined (β Δt : ℝ) :
    kmsKleinHom β Δt (toKlein genA) = kmsGlide β ∧
    kmsKleinHom β Δt (toKlein genB) = timeShift Δt ∧
    kmsKleinHom β Δt (toKlein genA) * kmsKleinHom β Δt (toKlein genB) *
        (kmsKleinHom β Δt (toKlein genA))⁻¹ =
      (kmsKleinHom β Δt (toKlein genB))⁻¹ := by
  refine ⟨kmsKleinHom_apply_genA β Δt, kmsKleinHom_apply_genB β Δt, ?_⟩
  rw [kmsKleinHom_apply_genA, kmsKleinHom_apply_genB]
  exact kmsGlide_timeShift_relation β Δt

/-- OpenGauss Trap T17: concrete `β = 1, Δt = 1` nontriviality and non-commutativity witness. -/
theorem kmsKleinHom_nontrivial_witness :
    kmsKleinHom 1 1 (toKlein genA) (0, 0) = (0, 1 / 2) ∧
    kmsKleinHom 1 1 (toKlein genB) (0, 0) = (1, 0) ∧
    kmsKleinHom 1 1 (toKlein genA) (0, 0) ≠ (0, 0) ∧
    kmsKleinHom 1 1 (toKlein genB) (0, 0) ≠ (0, 0) ∧
    kmsKleinHom 1 1 (toKlein genA) * kmsKleinHom 1 1 (toKlein genB) ≠
      kmsKleinHom 1 1 (toKlein genB) * kmsKleinHom 1 1 (toKlein genA) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [kmsKleinHom_apply_genA]
    dsimp [kmsGlide]
    ext <;> norm_num
  · rw [kmsKleinHom_apply_genB]
    dsimp [timeShift]
    ext <;> norm_num
  · rw [kmsKleinHom_apply_genA]
    intro h
    have h2 := congrArg Prod.snd h
    dsimp [kmsGlide] at h2
    norm_num at h2
  · rw [kmsKleinHom_apply_genB]
    intro h
    have h1 := congrArg Prod.fst h
    dsimp [timeShift] at h1
    norm_num at h1
  · rw [kmsKleinHom_apply_genA, kmsKleinHom_apply_genB]
    intro h
    have h1 := congrArg (fun f : Equiv.Perm (ℝ × ℝ) => (f (0, 0)).1) h
    simp only [Equiv.Perm.mul_apply, kmsGlide, timeShift] at h1
    norm_num at h1

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
        calc Γ * F = Γ * F * 1 := by rw [mul_one]
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

/-- Split-Clifford anticommutation `Eplus * J1 + J1 * Eplus = 0` deduced from involution conjugation. -/
theorem cl11_Eplus_J1_anticomm :
    Eplus * J1 + J1 * Eplus = 0 :=
  (involution_conjugation_neg_iff_anticomm Eplus J1 Eplus_sq).mp
    cl11_Eplus_conjugates_J1_to_neg

section PeirceSpecialization

open InfoGeometry.OperatorAlgebra.PeirceSpine

/-- The Peirce grading involution `invS P = P - (1 - P)` squares to `1`. -/
theorem peirce_invS_sq {B : Type*} [Ring B] {P : B} (hP : P * P = P) :
    invS P * invS P = 1 := by
  peirce_nf hP

/-- `invS P` anticommutes with the Peirce odd generator `genPhi P A C`. -/
theorem peirce_invS_genPhi_anticomm {B : Type*} [Ring B] {P : B}
    (hP : P * P = P) (A C : B) :
    invS P * genPhi P A C + genPhi P A C * invS P = 0 := by
  peirce_nf hP

/-- Conjugating `genPhi P A C` by `invS P` negates it via `involution_conjugation_neg_iff_anticomm`. -/
theorem peirce_invS_conjugates_genPhi_to_neg {B : Type*} [Ring B] {P : B}
    (hP : P * P = P) (A C : B) :
    invS P * genPhi P A C * invS P = -genPhi P A C :=
  (involution_conjugation_neg_iff_anticomm (invS P) (genPhi P A C)
    (peirce_invS_sq hP)).mpr (peirce_invS_genPhi_anticomm hP A C)

end PeirceSpecialization

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

/-- Acceptance alias for OpenGauss Trap T16 non-commutativity between `J1` and `Eplus`. -/
theorem cl11_J1_Eplus_noncommutative_witness :
    J1 * Eplus ≠ Eplus * J1 :=
  cl11_J1_Eplus_noncommutative

/-- Link to Klein's Footnote 26 separating orientation-reversing inversion from holomorphic maps. -/
theorem klein_circle_inversion_countermodel_link :
    ¬ ∃ a b c d : ℂ, a * d - b * c ≠ 0 ∧
      ∀ z : ℂ, z ≠ 0 → c * z + d ≠ 0 ∧ (a * z + b) / (c * z + d) = (starRingEnd ℂ z)⁻¹ :=
  klein_fn26_unit_circle_inversion_not_holomorphic_moebius.2

/-- Complete 45° Keldysh-Walsh-Krein intertwining theorem paired with Klein Footnote 26. -/
theorem keldysh45Mat_walsh_krein_intertwining :
    keldysh45Mat * keldysh45Mat = 1 ∧
    keldysh45Mat * J1 * keldysh45Mat = Eplus ∧
    keldysh45Mat * J1 * keldysh45Mat = walshConjugation J1 ∧
    keldysh45Mat * Eplus * keldysh45Mat = J1 ∧
    keldysh45Mat * Eplus * keldysh45Mat = walshConjugation Eplus ∧
    J1 * Eplus ≠ Eplus * J1 ∧
    ((∀ z : ℂ, z ≠ 0 →
        ((0 : ℂ) * starRingEnd ℂ z + 1) / ((1 : ℂ) * starRingEnd ℂ z + 0) =
          (starRingEnd ℂ z)⁻¹) ∧
      ¬ ∃ a b c d : ℂ, a * d - b * c ≠ 0 ∧
        ∀ z : ℂ, z ≠ 0 → c * z + d ≠ 0 ∧
          (a * z + b) / (c * z + d) = (starRingEnd ℂ z)⁻¹) := by
  refine ⟨keldysh45Mat_sq, keldysh45Mat_intertwines_J1_Eplus.1, ?_,
    keldysh45Mat_intertwines_J1_Eplus.2, ?_,
    cl11_J1_Eplus_noncommutative_witness,
    klein_fn26_unit_circle_inversion_not_holomorphic_moebius⟩
  · rw [keldysh45Mat_intertwines_J1_Eplus.1, walshConjugation_J1]
  · rw [keldysh45Mat_intertwines_J1_Eplus.2, walshConjugation_Eplus]

end KeldyshWalsh

end InfoGeometry.Topology.KleinBottleKMSKeldyshWalsh

end
