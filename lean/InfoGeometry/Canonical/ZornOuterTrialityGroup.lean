import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ZornIntegralTrialityEquivariance
import InfoGeometry.Canonical.ZornIntegralSpinTrialityClosure

/-!
# The related-triples group and outer Cartan triality
-/

noncomputable section

namespace ZornOuterTrialityGroup

open InfoGeometry.Canonical
open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Canonical.ZornClifford
open InfoGeometry.Canonical.ZornIntegralTrialityEquivariance
open InfoGeometry.Canonical.ZornIntegralSpinTrialityClosure

variable (R : Type*) [CommRing R]

abbrev ZornGL := LinearMap.GeneralLinearGroup R (ZornMatrix R)

/-- Ambient group of independently invertible maps on the three triality carriers. -/
abbrev TrialityGL := ZornGL R × ZornGL R × ZornGL R

def zornTrace (Z : ZornMatrix R) : R := Z.a + Z.b

@[simp]
theorem zornTrace_triality (Z : ZornMatrix R) : zornTrace (R := R) (zornTriality Z) = zornTrace (R := R) Z := by rfl

def trialityForm (V S C : ZornMatrix R) : R :=
  zornTrace (R := R) ((V * S) * C)

/-- A related triple preserves the three quadratic forms and the trilinear composition form. -/
def IsRelatedTriple (g : TrialityGL R) : Prop :=
  (∀ V, zornNorm (g.1.val V) = zornNorm V) ∧
  (∀ S, zornNorm (g.2.1.val S) = zornNorm S) ∧
  (∀ C, zornNorm (g.2.2.val C) = zornNorm C) ∧
  (∀ V S C, trialityForm R (g.1.val V) (g.2.1.val S) (g.2.2.val C) = trialityForm R V S C)

/-- The canonical related-triples subgroup. -/
def relatedTriples : Subgroup (TrialityGL R) where
  carrier := {g | IsRelatedTriple R g}
  one_mem' := by
    dsimp [IsRelatedTriple]
    exact ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩
  mul_mem' {g h} hg hh := by
    dsimp [IsRelatedTriple] at hg hh ⊢
    rcases hg with ⟨hgv, hgs, hgc, hgf⟩
    rcases hh with ⟨hhv, hhs, hhc, hhf⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro V; change zornNorm (g.1.val (h.1.val V)) = zornNorm V; rw [hgv, hhv]
    · intro S; change zornNorm (g.2.1.val (h.2.1.val S)) = zornNorm S; rw [hgs, hhs]
    · intro C; change zornNorm (g.2.2.val (h.2.2.val C)) = zornNorm C; rw [hgc, hhc]
    · intro V S C
      change trialityForm R (g.1.val (h.1.val V)) (g.2.1.val (h.2.1.val S)) (g.2.2.val (h.2.2.val C)) = trialityForm R V S C
      rw [hgf, hhf]
  inv_mem' {g} hg := by
    dsimp [IsRelatedTriple] at hg ⊢
    rcases hg with ⟨hgv, hgs, hgc, hgf⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro V
      have h1 : zornNorm (g.1.val (g.1⁻¹.val V)) = zornNorm (g.1⁻¹.val V) := hgv _
      have h2 : g.1.val (g.1⁻¹.val V) = V := by
        change (g.1.val * g.1⁻¹.val) V = V
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
        rfl
      rw [h2] at h1
      exact h1.symm
    · intro S
      have h1 : zornNorm (g.2.1.val (g.2.1⁻¹.val S)) = zornNorm (g.2.1⁻¹.val S) := hgs _
      have h2 : g.2.1.val (g.2.1⁻¹.val S) = S := by
        change (g.2.1.val * g.2.1⁻¹.val) S = S
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
        rfl
      rw [h2] at h1
      exact h1.symm
    · intro C
      have h1 : zornNorm (g.2.2.val (g.2.2⁻¹.val C)) = zornNorm (g.2.2⁻¹.val C) := hgc _
      have h2 : g.2.2.val (g.2.2⁻¹.val C) = C := by
        change (g.2.2.val * g.2.2⁻¹.val) C = C
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
        rfl
      rw [h2] at h1
      exact h1.symm
    · intro V S C
      have h1 : trialityForm R (g.1.val (g.1⁻¹.val V)) (g.2.1.val (g.2.1⁻¹.val S)) (g.2.2.val (g.2.2⁻¹.val C)) =
                  trialityForm R (g.1⁻¹.val V) (g.2.1⁻¹.val S) (g.2.2⁻¹.val C) := hgf _ _ _
      have h2 : g.1.val (g.1⁻¹.val V) = V := by
        change (g.1.val * g.1⁻¹.val) V = V
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
        rfl
      have h3 : g.2.1.val (g.2.1⁻¹.val S) = S := by
        change (g.2.1.val * g.2.1⁻¹.val) S = S
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
        rfl
      have h4 : g.2.2.val (g.2.2⁻¹.val C) = C := by
        change (g.2.2.val * g.2.2⁻¹.val) C = C
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
        rfl
      rw [h2, h3, h4] at h1
      exact h1.symm

abbrev CartanTrialityGroup := relatedTriples R

/-! ## The outer order-three permutation -/

attribute [local simp] Matrix.vecHead Matrix.vecTail Matrix.cons_val_zero Matrix.cons_val_one Matrix.cons_val_two Matrix.cons_val_succ Pi.smul_apply Pi.add_apply Pi.sub_apply Pi.neg_apply

/-- Cyclically transport the three components `(V, S, C) ↦ (C, V, S)`.
Since they act on identically structured spaces `ZornMatrix R`, no coordinate translation is required. -/
def trialityCycleAmbient : TrialityGL R →* TrialityGL R where
  toFun g := (g.2.2, g.1, g.2.1)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem trialityForm_cyclic (V S C : ZornMatrix R) :
    trialityForm R C V S = trialityForm R V S C := by
  simp [trialityForm, zornTrace, mul_def, mul, dot, cross, smul_eq_mul]
  ring

theorem trialityCycleAmbient_related {g : TrialityGL R} (hg : IsRelatedTriple R g) :
    IsRelatedTriple R (trialityCycleAmbient R g) := by
  dsimp [IsRelatedTriple] at hg ⊢
  rcases hg with ⟨hgv, hgs, hgc, hgf⟩
  refine ⟨hgc, hgv, hgs, ?_⟩
  intro V S C
  change trialityForm R (g.2.2.val V) (g.1.val S) (g.2.1.val C) = trialityForm R V S C
  rw [trialityForm_cyclic R (g.1.val S) (g.2.1.val C) (g.2.2.val V)]
  rw [hgf S C V]
  exact (trialityForm_cyclic R S C V).symm

/-- Outer cyclic transport as an endomorphism of the related-triples group. -/
def cartanTrialityCycle : CartanTrialityGroup R →* CartanTrialityGroup R where
  toFun g := ⟨trialityCycleAmbient R g.1, trialityCycleAmbient_related R g.2⟩
  map_one' := Subtype.ext (map_one (trialityCycleAmbient R))
  map_mul' g h := Subtype.ext (map_mul (trialityCycleAmbient R) g.1 h.1)

theorem cartanTrialityCycle_order_three (g : CartanTrialityGroup R) :
    cartanTrialityCycle R (cartanTrialityCycle R (cartanTrialityCycle R g)) = g := by
  apply Subtype.ext
  rfl

/-- The outer Cartan triality automorphism of the related-triples group. -/
def cartanTrialityOuterEquiv : CartanTrialityGroup R ≃* CartanTrialityGroup R where
  toFun := cartanTrialityCycle R
  invFun g := cartanTrialityCycle R (cartanTrialityCycle R g)
  left_inv := cartanTrialityCycle_order_three R
  right_inv := cartanTrialityCycle_order_three R
  map_mul' := map_mul (cartanTrialityCycle R)

/-! ## The internal Zorn-axis symmetry as a related triple -/

def axisRelatedTripleAmbient : TrialityGL R :=
  (zornTrialityUnit, zornTrialityUnit, zornTrialityUnit)

theorem trialityForm_axisCycle (V S C : ZornMatrix R) :
    trialityForm R (zornTriality V) (zornTriality S) (zornTriality C) = trialityForm R V S C := by
  change zornTrace R ((zornTriality V * zornTriality S) * zornTriality C) = zornTrace R ((V * S) * C)
  rw [← zornTriality_mul, ← zornTriality_mul]
  exact zornTrace_triality R _

theorem axisRelatedTriple_isRelated : IsRelatedTriple R (axisRelatedTripleAmbient R) := by
  exact ⟨zornTriality_norm, zornTriality_norm, zornTriality_norm, trialityForm_axisCycle R⟩

/-- The internal order-three Zorn-axis automorphism is a concrete point of
the outer related-triples group. -/
def axisRelatedTriple : CartanTrialityGroup R :=
  ⟨axisRelatedTripleAmbient R, axisRelatedTriple_isRelated R⟩

/-- The internal Zorn-axis symmetry is exactly fixed by the outer permutation because
the exact same identical coordinate automorphism acts natively on all three carriers simultaneously. -/
theorem cartanTrialityCycle_axisRelatedTriple :
    cartanTrialityCycle R (axisRelatedTriple R) = axisRelatedTriple R := by
  apply Subtype.ext
  rfl

end ZornOuterTrialityGroup

end noncomputable section
