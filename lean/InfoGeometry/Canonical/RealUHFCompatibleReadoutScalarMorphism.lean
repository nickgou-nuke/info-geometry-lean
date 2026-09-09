import InfoGeometry.Canonical.RealUHFCompatibleReadoutFamilyMorphism

/-!
# Scalar rescaling of compatible real readout families

This is a concrete non-identity morphism in the restriction-preserving
readout-family layer.  The same scalar acts at every finite stage, so the
restriction equations are preserved by linearity.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleReadoutScalarMorphism

open InfoGeometry.Canonical.RealUHFCompatibleReadoutFamilyMorphism
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimit
open InfoGeometry.Canonical.Cl11CompatibleLocalStateNet
open InfoGeometry.Clifford.Cl11TensorTower

noncomputable def scalarRescaling (c : ℝ) :
    CompatibleReadoutFamilyMap where
  map := fun n => c • ContinuousLinearMap.id ℝ (ReadoutSpace n)
  map_compatibility := by
    intro ρ hρ n
    ext X
    change c • ρ n (stageRestrict n X) = c • ρ (n + 1) X
    have h := congrArg
      (fun f : MatStage (n + 1) →L[ℝ] ℝ => f X) (hρ n)
    simpa [stageRestrictCLM_apply] using congrArg (fun y : ℝ => c • y) h
  continuous_map := by
    apply continuous_induced_rng.mpr
    change Continuous (fun ρ : CompatibleContinuousReadoutFamily =>
      fun n => c • ρ.1 n)
    exact continuous_pi (fun n =>
      (continuous_const.smul (continuous_apply n)).comp
        continuous_subtype_val)

@[simp] theorem scalarRescaling_map_apply
    (c : ℝ) (ρ : CompatibleContinuousReadoutFamily) (n : ℕ) :
    (mapFamily (scalarRescaling c).map
      (scalarRescaling c).map_compatibility ρ).1 n =
      c • ρ.1 n := by
  ext X
  rfl

theorem scalarRescaling_compatible_apply
    (c : ℝ) (ρ : CompatibleContinuousReadoutFamily) (n : ℕ)
    (X : MatStage (n + 1)) :
    (mapFamily (scalarRescaling c).map
      (scalarRescaling c).map_compatibility ρ).1 n
        (stageRestrict n X) =
      (mapFamily (scalarRescaling c).map
        (scalarRescaling c).map_compatibility ρ).1 (n + 1) X := by
  exact compatible_apply
    (mapFamily (scalarRescaling c).map
      (scalarRescaling c).map_compatibility ρ) n X

end InfoGeometry.Canonical.RealUHFCompatibleReadoutScalarMorphism
