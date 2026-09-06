import InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimit

/-!
# Topological coordinate readouts for compatible real stage families

The compatible-family carrier is an induced subspace of the product of
continuous readout spaces.  This owner exposes its coordinate projections as
native `TopCat` morphisms and records their stage compatibility.  It does not
assert a state-space, KMS, or C*-completion theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitTopCat

open CategoryTheory
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimit
open InfoGeometry.Clifford.Cl11TensorTower

def coordinateTopCatHom (n : ℕ) :
    TopCat.of CompatibleContinuousReadoutFamily ⟶
      TopCat.of (MatStage n →L[ℝ] ℝ) :=
  TopCat.ofHom
    { toFun := fun ρ => ρ.1 n
      continuous_toFun := continuous_readout_coordinate n }

@[simp] theorem coordinateTopCatHom_apply
    (n : ℕ) (ρ : CompatibleContinuousReadoutFamily) :
    coordinateTopCatHom n ρ = ρ.1 n := rfl

theorem coordinateTopCatHom_compatibility_apply
    (n : ℕ) (ρ : CompatibleContinuousReadoutFamily)
    (X : MatStage (n + 1)) :
    coordinateTopCatHom n ρ (stageRestrictCLM n X) =
      coordinateTopCatHom (n + 1) ρ X := by
  exact compatible_apply ρ n X

end RealUHFCompatibleStateInverseLimitTopCat

end Canonical
