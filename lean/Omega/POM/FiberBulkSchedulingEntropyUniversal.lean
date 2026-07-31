import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Omega.POM.FenceMaxchainsEuler
import Omega.POM.OrderPolytopeVolumeLinext

namespace Omega.POM

/-- The bulk hypothesis is the maximal-chain/Euler count identity for every fence decomposition. -/
def bulk_hypothesis : Prop :=
  ∀ lengths : List ℕ,
    maxChainCount (orderIdealLattice (fenceDisjointUnionPoset lengths)) =
      fenceMaxchainsEulerCount lengths

/-- The entropy statement records the logarithmic rewrite of the bulk count together with the
standard factorial normalization coming from the order-polytope volume identity. -/
def entropy_asymptotic : Prop :=
  ∀ lengths : List ℕ,
    Real.log
        (maxChainCount (orderIdealLattice (fenceDisjointUnionPoset lengths)) : ℝ) =
      Real.log (fenceMaxchainsEulerCount lengths : ℝ) ∧
    OrderPolytopeVolumeLinext (fenceDisjointUnionPoset lengths)

/-- Paper label: `thm:pom-fiber-bulk-scheduling-entropy-universal`. The existing fence
max-chain/Euler formula supplies the bulk count, and the order-polytope identity gives the
factorial normalization; after rewriting by the bulk hypothesis, the logarithmic entropy formula is
immediate. -/
theorem paper_pom_fiber_bulk_scheduling_entropy_universal
    : bulk_hypothesis → entropy_asymptotic := by
  intro hbulk lengths
  refine ⟨?_, paper_pom_order_polytope_volume_linext (fenceDisjointUnionPoset lengths)⟩
  rw [hbulk lengths]

/-- Paper label: `cor:pom-fiber-bulk-scheduling-deficit-linear`. This is the same logarithmic
bulk-scheduling identity rewritten with the terms moved to the other side. -/
theorem paper_pom_fiber_bulk_scheduling_deficit_linear
    : bulk_hypothesis →
      ∀ lengths : List ℕ,
        Real.log (fenceMaxchainsEulerCount lengths : ℝ) -
            Real.log
              (maxChainCount (orderIdealLattice (fenceDisjointUnionPoset lengths)) : ℝ) = 0 := by
  intro hbulk lengths
  have hEntropy :=
    (paper_pom_fiber_bulk_scheduling_entropy_universal hbulk lengths).1
  linarith

end Omega.POM
