import InfoGeometry.Twistor.ChiralTwistorSheets
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Twistor.RealSplitOctonionCarrierBridge
import Mathlib.Tactic.FinCases

/-!
# Integration surface for the existing chiral twistor and Zorn owners

The carrier, flattening map, real Peirce maps, and the carrier bridge are owned
by `ChiralTwistorSheets`.  This file contains only the direct `Twistor4`
sheet inclusions needed by the native Zorn coupling owner; it does not define a
second twistor or Peirce carrier.
-/

noncomputable section

namespace InfoGeometry.Twistor.ChiralTwistorPeirceSheets

open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Twistor.ChiralTwistorSheets
open InfoGeometry.Twistor.RealSplitOctonionCarrierBridge
open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge

/-- The already-owned positive-sheet real coordinate map. -/
def spinor2ToPeirce4 : Spinor2 →ₗ[ℝ] (ℝ × V3) :=
  twistorPlusRealEquiv.toLinearMap

/-- Its already-owned inverse, exposed for the coupling owner. -/
def peirce4ToSpinor2 : (ℝ × V3) →ₗ[ℝ] Spinor2 :=
  twistorPlusRealEquiv.symm.toLinearMap

@[simp] theorem peirce4ToSpinor2_spinor2ToPeirce4 (z : Spinor2) :
    peirce4ToSpinor2 (spinor2ToPeirce4 z) = z :=
  twistorPlusRealEquiv.symm_apply_apply z

@[simp] theorem spinor2ToPeirce4_peirce4ToSpinor2 (q : ℝ × V3) :
    spinor2ToPeirce4 (peirce4ToSpinor2 q) = q :=
  twistorPlusRealEquiv.apply_symm_apply q

/-- Inclusion of the first existing factor of `Twistor4`. -/
def plusInclusion : Spinor2 →ₗ[ℝ] Twistor4 where
  toFun ω := (ω, 0)
  map_add' ω ρ := by
    apply Prod.ext <;> simp
  map_smul' r ω := by
    apply Prod.ext <;> simp

/-- Inclusion of the second existing factor of `Twistor4`. -/
def minusInclusion : Spinor2 →ₗ[ℝ] Twistor4 where
  toFun π := (0, π)
  map_add' π ρ := by
    apply Prod.ext <;> simp
  map_smul' r π := by
    apply Prod.ext <;> simp

@[simp] theorem plusInclusion_fst (ω : Spinor2) :
    (plusInclusion ω).1 = ω := rfl

@[simp] theorem plusInclusion_snd (ω : Spinor2) :
    (plusInclusion ω).2 = 0 := rfl

@[simp] theorem minusInclusion_fst (π : Spinor2) :
    (minusInclusion π).1 = 0 := rfl

@[simp] theorem minusInclusion_snd (π : Spinor2) :
    (minusInclusion π).2 = π := rfl

/-- The two existing spinor factors reconstruct the existing `Twistor4`. -/
theorem twistor_sheet_decomposition (Z : Twistor4) :
    plusInclusion Z.1 + minusInclusion Z.2 = Z := by
  apply Prod.ext <;> simp [plusInclusion, minusInclusion]

/-- The established direct realified `Twistor4 → Zorn` map on one sheet. -/
noncomputable def plusZornMap :
    Spinor2 →ₗ[ℝ] CanonicalSplitOctonion :=
  twistorRealEquivZorn.toLinearMap.comp plusInclusion

/-- The established direct realified `Twistor4 → Zorn` map on the other sheet. -/
noncomputable def minusZornMap :
    Spinor2 →ₗ[ℝ] CanonicalSplitOctonion :=
  twistorRealEquivZorn.toLinearMap.comp minusInclusion

theorem twistor_zorn_sheet_decomposition (Z : Twistor4) :
    twistorRealEquivZorn Z =
      plusZornMap Z.1 + minusZornMap Z.2 := by
  rw [← twistor_sheet_decomposition Z, map_add]
  simp [plusZornMap, minusZornMap, plusInclusion, minusInclusion]

/-- Compatibility with the separately-owned `Fin 4 → ℂ` carrier bridge. -/
theorem twistor4_sheet_bridge
    (p : Twistor4) :
    twistorChiralDecomposition (penroseTwistor4CarrierEquiv p) = (p.1, p.2) :=
  twistorChiralDecomposition_carrierBridge p

end InfoGeometry.Twistor.ChiralTwistorPeirceSheets
