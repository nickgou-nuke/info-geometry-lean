import InfoGeometry.Canonical.RealUHFCompatibleReadoutScalarMorphism
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RealUHFCompatibleReadoutDynamics

/-!
# Scalar readout morphisms and compatible stage dynamics

The scalar rescaling morphism is the contravariant pullback of the compatible
stage dilation.  This is an equality of the existing readout-family actions;
it does not assert a C*-completion or a KMS theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleReadoutScalarDynamicsBridge

open InfoGeometry.Canonical.RealUHFCompatibleReadoutFamilyMorphism
open InfoGeometry.Canonical.RealUHFCompatibleReadoutScalarMorphism
open InfoGeometry.Canonical.RealUHFCompatibleReadoutDynamics
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimit
open InfoGeometry.Clifford.Cl11TensorTower

theorem scalarRescaling_exp_matches_pullback
    (t : ℝ) (ρ : CompatibleContinuousReadoutFamily) :
    mapFamily (scalarRescaling (Real.exp t)).map
        (scalarRescaling (Real.exp t)).map_compatibility ρ =
      pullback scalarDilationStageFlow t ρ := by
  apply Subtype.ext
  funext n
  ext X
  change (Real.exp t) • ρ.1 n X = _
  simp [pullback, scalarDilationStageFlow]

theorem pullback_scalarDilation_matches_scalarRescaling
    (t : ℝ) (ρ : CompatibleContinuousReadoutFamily) (n : ℕ)
    (X : MatStage n) :
    (pullback scalarDilationStageFlow t ρ).1 n X =
      (mapFamily (scalarRescaling (Real.exp t)).map
        (scalarRescaling (Real.exp t)).map_compatibility ρ).1 n X := by
  rw [scalarRescaling_exp_matches_pullback t ρ]

theorem scalarRescaling_exp_add
    (s t : ℝ) (ρ : CompatibleContinuousReadoutFamily) :
    mapFamily (scalarRescaling (Real.exp (s + t))).map
        (scalarRescaling (Real.exp (s + t))).map_compatibility ρ =
      mapFamily (scalarRescaling (Real.exp s)).map
        (scalarRescaling (Real.exp s)).map_compatibility
        (mapFamily (scalarRescaling (Real.exp t)).map
          (scalarRescaling (Real.exp t)).map_compatibility ρ) := by
  apply Subtype.ext
  funext n
  ext X
  change (Real.exp (s + t)) • ρ.1 n X =
    (Real.exp s) • ((Real.exp t) • ρ.1 n X)
  rw [Real.exp_add, smul_smul]

end InfoGeometry.Canonical.RealUHFCompatibleReadoutScalarDynamicsBridge
