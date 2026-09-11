import InfoGeometry.Categorical.LambdaBraidHestenesKreinBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.PolarizedBraidFibration
import InfoGeometry.Canonical.KitaevChainMajoranaZeroModes

/-!
# Chiral braid and two-sheet bundle interface

This module closes the typed integration boundary between the compiled
lambda/DAG packet and the repository's existing polarized braid and Kitaev
lanes.  The source modules provide a two-sheet carrier action and an algebraic
boundary zero-mode theorem.  They do not assert a topological fibre bundle,
analytic holonomy, or a Sugawara central-charge derivation; those stronger
claims remain explicit future interfaces.
-/

noncomputable section

namespace InfoGeometry.Canonical.ChiralBraidBundleKitaevBridge

open CategoryTheory
open InfoGeometry.Canonical.LambdaCausalNetNegativeGrammarBridge
open InfoGeometry.Categorical.LambdaBraidHestenesKreinBridge
open InfoGeometry.Categorical.LambdaBraidHestenesKreinBridge.CompiledTheoryBridge
open InfoGeometry.Categorical.HadjiivanovBraidGroupColimit
open InfoGeometry.Physics.PolarizedBraidFibration
open InfoGeometry.Canonical.KitaevChainMajoranaZeroModes
open InfoGeometry.Krein

universe u

/-- A chiral sheet transport datum attached to a previously compiled
lambda--braid--Hestenes--Krein packet. -/
structure ChiralCompiledTheoryBridge where
  core : CompiledTheoryBridge.{u}
  braidAction : InfoGeometry.Physics.B3PresentedGroup.B3 →* ChiralPerm

namespace ChiralCompiledTheoryBridge

variable (P : ChiralCompiledTheoryBridge.{u})

/-- The existing polarized braid action is equivariant with respect to the
sheet-swap involution. -/
  theorem sheet_swap_equivariance
      (g : InfoGeometry.Physics.B3PresentedGroup.B3) (z : Phase) :
    sheetSwap (polarizedBraidAction P.braidAction g z) =
      polarizedBraidAction P.braidAction g⁻¹ (sheetSwap z) :=
    InfoGeometry.Physics.PolarizedBraidFibration.sheetSwap_intertwining
      P.braidAction g z

/-- Five fermionic modes contribute five to the mode-count calibration.
This is a cardinality identity, not a Virasoro/Sugawara theorem. -/
def modeCountCentralCharge (𝕜 : Type*) [Field 𝕜] (N : ℕ) : 𝕜 :=
  (Fintype.card (Fin N) : 𝕜)

theorem five_mode_count (𝕜 : Type*) [Field 𝕜] :
    modeCountCentralCharge 𝕜 5 = (5 : 𝕜) := by
  rfl

/-- The existing Kitaev algebraic boundary theorem, exposed through the
integrated chiral bridge. -/
theorem kitaev_boundary_zero_mode
    {R : Type*} [Ring R]
    (gamma0 gamma1 gamma2 : R)
    (h01 : gamma0 * gamma1 + gamma1 * gamma0 = 0)
    (h02 : gamma0 * gamma2 + gamma2 * gamma0 = 0) :
    gamma0 * (gamma1 * gamma2) - (gamma1 * gamma2) * gamma0 = 0 :=
  left_boundary_majorana_zero_mode gamma0 gamma1 gamma2 h01 h02

/-- Master closure packet: compiled DAG/braid/Hestenes laws together with
the native chiral sheet law and the five-mode cardinality calibration. -/
theorem chiral_compiled_closure :
    ((lambdaToCausalNet P.core.term).IsDAG ∧
      causalNetToPolarity P.core.net =
        LambdaCausalNetNegativeGrammarBridge.Polarity.negative ∧
      (∀ n : ℕ, stageInjection P.core.braidDiagram n ≫
          descendedEndomorphism P.core.braidDiagram P.core.braidData.braid1 =
        P.core.braidData.braid1.app n ≫ stageInjection P.core.braidDiagram n) ∧
      (∀ n m : ℕ, ∀ x : DoubledSpace (P.core.hestenesCone.Base n),
        P.core.analyticFamily.colimitReadout (n + m)
            (P.core.hestenesCone.toFilteredPhaseCone.bondIterate n m x) =
          P.core.analyticFamily.colimitReadout n x)) ∧
    (∀ g : InfoGeometry.Physics.B3PresentedGroup.B3, ∀ z : Phase,
      sheetSwap (polarizedBraidAction P.braidAction g z) =
        polarizedBraidAction P.braidAction g⁻¹ (sheetSwap z)) ∧
    modeCountCentralCharge ℝ 5 = (5 : ℝ) := by
  refine ⟨⟨P.core.lambda_lane_dag, P.core.negative_grammar_lane,
    (P.core.braid_lane).1, P.core.hestenes_lane⟩, ?_, ?_⟩
  · intro g z
    exact P.sheet_swap_equivariance g z
  · exact five_mode_count ℝ

end ChiralCompiledTheoryBridge

end InfoGeometry.Canonical.ChiralBraidBundleKitaevBridge
