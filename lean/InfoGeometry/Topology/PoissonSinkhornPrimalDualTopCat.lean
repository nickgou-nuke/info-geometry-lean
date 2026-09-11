import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Inference.PoissonSinkhornPotentials
import InfoGeometry.Topology.PoissonSinkhornBregmanTopCat

/-!
# Balanced Poisson Sinkhorn primal-dual readout in `TopCat`

The native finite owner identifies the primal-dual gap with a nonnegative
Bregman gap under strict positivity and unit marginals.  This file packages
that result over the corresponding subtype as a continuous `TopCat` readout.
It is a property surface, not a convergence theorem.
-/

open scoped BigOperators

namespace InfoGeometry.Topology.PoissonSinkhornPrimalDualTopCat

open CategoryTheory
open InfoGeometry.Inference
open InfoGeometry.Topology.PoissonSinkhornBregmanTopCat

variable {n : Nat} [Nonempty (Fin n)]

abbrev BalancedBregmanParameter (n : Nat) :=
  {p : BregmanParameter n //
    (∀ i : Fin n, ∑ j : Fin n, p.2.2.2.1 i j = 1) ∧
    (∀ j : Fin n, ∑ i : Fin n, p.2.2.2.1 i j = 1)}

noncomputable def balancedBregmanGapTopCatHom
    (C : PoissonTransportCost (Observation := Fin n) (Component := Fin n)) :
    TopCat.of (BalancedBregmanParameter n) ⟶ TopCat.of ℝ :=
  TopCat.ofHom
    { toFun := fun p => bregmanGapReadout C p.1
      continuous_toFun :=
        (continuous_bregmanGapReadout C).comp continuous_subtype_val }

theorem balancedBregmanGapTopCatHom_apply
    (C : PoissonTransportCost (Observation := Fin n) (Component := Fin n))
    (p : BalancedBregmanParameter n) :
    balancedBregmanGapTopCatHom C p = bregmanGapReadout C p.1 :=
  rfl

theorem balancedBregmanGapTopCatHom_nonneg
    (C : PoissonTransportCost (Observation := Fin n) (Component := Fin n))
    (p : BalancedBregmanParameter n) :
    0 ≤ balancedBregmanGapTopCatHom C p := by
  rw [balancedBregmanGapTopCatHom_apply]
  exact poissonSinkhornBregmanGap_nonneg C p.1.1.1 p.1.1.2.le
    p.1.2.1 p.1.2.2.1 p.1.2.2.2.1
    (fun i j => (p.1.2.2.2.2 i j).le)

theorem balancedBregmanGapTopCatHom_eq_primalDualGap
    (C : PoissonTransportCost (Observation := Fin n) (Component := Fin n))
    (p : BalancedBregmanParameter n) :
    balancedBregmanGapTopCatHom C p =
      poissonSinkhornPrimalObjective C p.1.1.1 p.1.2.2.2.1 -
        poissonSinkhornDualObjective C p.1.1.1 p.1.2.1 p.1.2.2.1 := by
  rw [balancedBregmanGapTopCatHom_apply]
  unfold bregmanGapReadout
  symm
  exact poissonSinkhornPrimalDual_gap_eq_bregmanGap C p.1.1.1
    p.1.1.2 p.1.2.1 p.1.2.2.1 p.1.2.2.2.1
    p.1.2.2.2.2 p.2.1 p.2.2

end InfoGeometry.Topology.PoissonSinkhornPrimalDualTopCat
