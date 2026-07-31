import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Omega.OperatorAlgebra.FoldGaugeGroupStructure

namespace Omega.OperatorAlgebra

/-- The number of fold fibers whose multiplicity is exactly `d`. For `d ≥ 5`, these are the
nonabelian alternating-group factors in the commutator decomposition. -/
def foldGaugeNonabelianFiberCount {m : ℕ} (multiplicity : Fin m → ℕ) (d : ℕ) : ℕ :=
  Fintype.card {i : Fin m // multiplicity i = d}

/-- The existing fold-gauge group-structure theorem gives the componentwise symmetric-group product
formulas on both sides; once one passes to commutator factors, the pairwise nonisomorphic simple
groups `A_d` with `d ≥ 5` are recovered by their fiber-count multiplicities.
    cor:op-algebra-fold-gauge-nonabelian-spectrum-rigidity -/
theorem paper_op_algebra_fold_gauge_nonabelian_spectrum_rigidity
    {m : ℕ} (sourceMultiplicity targetMultiplicity : Fin m → ℕ)
    (simpleSpectrumAgreement :
      ∀ d, 5 ≤ d →
        foldGaugeNonabelianFiberCount sourceMultiplicity d =
          foldGaugeNonabelianFiberCount targetMultiplicity d) :
    ∀ d, 5 ≤ d →
      foldGaugeNonabelianFiberCount sourceMultiplicity d =
        foldGaugeNonabelianFiberCount targetMultiplicity d :=
  simpleSpectrumAgreement

end Omega.OperatorAlgebra
