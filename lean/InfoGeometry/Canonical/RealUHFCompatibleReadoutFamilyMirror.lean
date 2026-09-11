import InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitReversal
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RealUHFCompatibleReadoutFamilyMorphism

/-!
# Stagewise mirror data for compatible readout families

The mirror is not assumed to exist canonically.  This owner packages the
stronger data needed to construct one: a restriction-preserving continuous
readout-family map, involutivity, and (separately) reversal of the scalar
flow.  The resulting symbolic-latent reversal is then obtained through the
existing generic adapter.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleReadoutFamilyMirror

open InfoGeometry.Canonical.RealUHFCompatibleReadoutFamilyMorphism
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimit
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitReversal
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitSymbolicLatentFlow
open InfoGeometry.Topology

abbrev carrier := CompatibleContinuousReadoutFamily
abbrev flow := scalarDilationCompatibleReadoutFamilyFlow

structure Data where
  familyMap : CompatibleReadoutFamilyMap
  involutive : ∀ ρ : carrier,
    mapFamily familyMap.map familyMap.map_compatibility
        (mapFamily familyMap.map familyMap.map_compatibility ρ) = ρ

def involution (M : Data) : SymbolicLatentInvolution carrier where
  toFun := mapFamily M.familyMap.map M.familyMap.map_compatibility
  continuous_toFun := M.familyMap.continuous_map
  involutive := M.involutive

@[simp] theorem involution_apply (M : Data) (ρ : carrier) :
    involution M ρ =
      mapFamily M.familyMap.map M.familyMap.map_compatibility ρ :=
  rfl

theorem involution_stage_apply
    (M : Data) (ρ : carrier) (n : ℕ) :
    (involution M ρ).1 n = M.familyMap.map n (ρ.1 n) :=
  rfl

def reversal
    (M : Data)
    (hM : ∀ (t : ℝ) (ρ : carrier),
      involution M (flow.act t ρ) = flow.act (-t) (involution M ρ)) :
    SymbolicLatentModularReversal flow :=
  reversalData (involution M) hM

theorem reversal_reverses_flow
    (M : Data)
    (hM : ∀ (t : ℝ) (ρ : carrier),
      involution M (flow.act t ρ) = flow.act (-t) (involution M ρ))
    (t : ℝ) (ρ : carrier) :
    (reversal M hM).involution (flow.act t ρ) =
      flow.act (-t) ((reversal M hM).involution ρ) :=
  hM t ρ

end InfoGeometry.Canonical.RealUHFCompatibleReadoutFamilyMirror
end
