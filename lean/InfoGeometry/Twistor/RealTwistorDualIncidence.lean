/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.RealTwistorIncidence
import InfoGeometry.Twistor.RealDualTwistor

/-!
# Incidence planes and their genuine dual annihilators

For `x : S' →ₗ[ℝ] S`, every covector annihilating the real graph-incidence
plane is uniquely `(φ, -φ ∘ x)`.  This is realized as the actual functional
`φ ∘ residual x` on `S × S'`.  Thus the graph-incidence and dual-ambitwistor
constructions are related by an explicit map, including translation
covariance and the rank-one square-zero criterion.

One covector tests one component of incidence.  Membership in the whole
incidence plane is characterized by *all* residual covectors, not by an
arbitrarily chosen single functional.
-/

noncomputable section

namespace InfoGeometry.Twistor.RealTwistorDualIncidence

open RealTwistorIncidence

variable {S S' : Type*} [AddCommGroup S] [Module ℝ S]
  [AddCommGroup S'] [Module ℝ S']

/-- The actual total covector represented by `(φ, -φ ∘ x)`. -/
def incidenceCovector (x : S' →ₗ[ℝ] S) (φ : Module.Dual ℝ S) :
    Module.Dual ℝ (Carrier S S') := φ.comp (residual x)

@[simp] theorem incidenceCovector_apply
    (x : S' →ₗ[ℝ] S) (φ : Module.Dual ℝ S) (z : Carrier S S') :
    incidenceCovector x φ z = φ z.1 - φ (x z.2) := by
  simp [incidenceCovector]

@[simp] theorem incidenceCovector_incidenceMap
    (x : S' →ₗ[ℝ] S) (φ : Module.Dual ℝ S) (π : S') :
    incidenceCovector x φ (incidenceMap x π) = 0 := by simp

/-- The first-spinor component recovers the original covector exactly. -/
@[simp] theorem incidenceCovector_first_sheet
    (x : S' →ₗ[ℝ] S) (φ : Module.Dual ℝ S) (ω : S) :
    incidenceCovector x φ (ω, 0) = φ ω := by simp

theorem incidenceCovector_injective (x : S' →ₗ[ℝ] S) :
    Function.Injective (incidenceCovector x) := by
  intro φ ψ h
  ext ω
  simpa using congrArg (fun Φ : Module.Dual ℝ (Carrier S S') => Φ (ω, 0)) h

theorem incidenceCovector_ne_zero (x : S' →ₗ[ℝ] S)
    {φ : Module.Dual ℝ S} (hφ : φ ≠ 0) : incidenceCovector x φ ≠ 0 := by
  intro h
  apply hφ
  apply incidenceCovector_injective x
  simpa [incidenceCovector] using h

/-- Every graph-annihilating functional has the displayed dual form. -/
theorem annihilating_covector_eq (x : S' →ₗ[ℝ] S)
    (Φ : Module.Dual ℝ (Carrier S S'))
    (hΦ : ∀ π : S', Φ (incidenceMap x π) = 0) :
    Φ = incidenceCovector x (Φ.comp (LinearMap.inl ℝ S S')) := by
  apply LinearMap.ext
  intro z
  have hz : z = (residual x z, 0) + incidenceMap x z.2 := by
    apply Prod.ext <;> simp
  calc
    Φ z = Φ ((residual x z, 0) + incidenceMap x z.2) := congrArg Φ hz
    _ = Φ (residual x z, 0) := by rw [map_add, hΦ, add_zero]
    _ = incidenceCovector x (Φ.comp (LinearMap.inl ℝ S S')) z := rfl

/-- The native dual annihilator has the unique parameter `φ`. -/
theorem mem_dualAnnihilator_iff_existsUnique (x : S' →ₗ[ℝ] S)
    (Φ : Module.Dual ℝ (Carrier S S')) :
    Φ ∈ (incidenceSpace x).dualAnnihilator ↔
      ∃! φ : Module.Dual ℝ S, incidenceCovector x φ = Φ := by
  constructor
  · intro hΦ
    have h : ∀ π : S', Φ (incidenceMap x π) = 0 := by
      intro π
      exact (Submodule.mem_dualAnnihilator Φ).mp hΦ _ ⟨π, rfl⟩
    refine ⟨Φ.comp (LinearMap.inl ℝ S S'), (annihilating_covector_eq x Φ h).symm, ?_⟩
    intro ψ hψ
    apply incidenceCovector_injective x
    exact hψ.trans (annihilating_covector_eq x Φ h)
  · rintro ⟨φ, rfl, _⟩
    apply (Submodule.mem_dualAnnihilator _).mpr
    rintro z ⟨π, rfl⟩
    exact incidenceCovector_incidenceMap x φ π

/-- Whole-plane incidence is recovered from all genuine residual covectors. -/
theorem mem_incidenceSpace_iff_all_covectors
    (x : S' →ₗ[ℝ] S) (z : Carrier S S') :
    z ∈ incidenceSpace x ↔
      ∀ φ : Module.Dual ℝ S, incidenceCovector x φ z = 0 := by
  rw [incidenceSpace_eq_ker]
  change residual x z = 0 ↔ ∀ φ : Module.Dual ℝ S, φ (residual x z) = 0
  constructor
  · intro h φ
    simp [h]
  · exact RealDualTwistor.eq_zero_of_dual_vanishes (residual x z)

/-- The map connecting real incidence data to genuine-dual ambitwistor data. -/
def dualPair (x : S' →ₗ[ℝ] S) (φ : Module.Dual ℝ S) (z : Carrier S S') :
    RealDualTwistor.Carrier (Carrier S S') := (z, incidenceCovector x φ)

@[simp] theorem dualPair_incident_iff
    (x : S' →ₗ[ℝ] S) (φ : Module.Dual ℝ S) (z : Carrier S S') :
    RealDualTwistor.Incident (dualPair x φ z) ↔ φ (residual x z) = 0 := Iff.rfl

/-- A nonzero residual covector and twistor give a nonzero rank-one operator. -/
theorem dualPair_dyad_ne_zero
    (x : S' →ₗ[ℝ] S) (φ : Module.Dual ℝ S) (z : Carrier S S')
    (hφ : φ ≠ 0) (hz : z ≠ 0) : RealDualTwistor.dyad (dualPair x φ z) ≠ 0 :=
  RealDualTwistor.dyad_ne_zero _ hz (incidenceCovector_ne_zero x hφ)

/-- For a nonzero pair, residual incidence is exactly rank-one nilpotence. -/
theorem dualPair_dyad_sq_zero_iff
    (x : S' →ₗ[ℝ] S) (φ : Module.Dual ℝ S) (z : Carrier S S')
    (hφ : φ ≠ 0) (hz : z ≠ 0) :
    RealDualTwistor.dyad (dualPair x φ z) * RealDualTwistor.dyad (dualPair x φ z) = 0 ↔
      φ (residual x z) = 0 := by
  rw [RealDualTwistor.dyad_sq_zero_iff _ hz (incidenceCovector_ne_zero x hφ),
    dualPair_incident_iff]

/-- Full plane incidence implies square-zero for every dual test operator,
including the zero covector. -/
theorem dualPair_dyad_sq_zero_of_mem
    (x : S' →ₗ[ℝ] S) (φ : Module.Dual ℝ S) (z : Carrier S S')
    (hz : z ∈ incidenceSpace x) :
    RealDualTwistor.dyad (dualPair x φ z) * RealDualTwistor.dyad (dualPair x φ z) = 0 := by
  rw [RealDualTwistor.dyad_sq]
  have h := (mem_incidenceSpace_iff_all_covectors x z).mp hz φ
  change incidenceCovector x φ z • RealDualTwistor.dyad (dualPair x φ z) = 0
  rw [h, zero_smul]

/-- Residual covectors transform by the inverse dual shear. -/
theorem incidenceCovector_translation
    (d x : S' →ₗ[ℝ] S) (φ : Module.Dual ℝ S) (z : Carrier S S') :
    incidenceCovector (x + d) φ (translation d z) = incidenceCovector x φ z := by
  simp [translation, map_add]

/-- Translation of spacetime incidence agrees with the contragredient lift on
the actual dual ambitwistor carrier. -/
theorem dualPair_translation
    (d x : S' →ₗ[ℝ] S) (φ : Module.Dual ℝ S) (z : Carrier S S') :
    dualPair (x + d) φ (translation d z) =
      RealDualTwistor.frameAction (translation d) (dualPair x φ z) := by
  apply Prod.ext
  · rfl
  · apply LinearMap.ext
    intro w
    have h := incidenceCovector_translation d x φ ((translation d).symm w)
    simpa [dualPair] using h

end InfoGeometry.Twistor.RealTwistorDualIncidence
