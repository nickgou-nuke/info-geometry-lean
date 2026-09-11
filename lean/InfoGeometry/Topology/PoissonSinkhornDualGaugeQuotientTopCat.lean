import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.PoissonSinkhornDualTopCat

/-!
# Gauge quotient of finite Poisson Sinkhorn dual potentials

The dual objective is invariant under the additive potential gauge.  This
owner turns that equality into an actual quotient carrier and descends the
continuous objective through `Quotient.lift` in `TopCat`.
-/

namespace InfoGeometry.Topology.PoissonSinkhornDualGaugeQuotientTopCat

open CategoryTheory
open InfoGeometry.Inference
open InfoGeometry.Topology.PoissonSinkhornDualTopCat

variable {n : Nat} [Nonempty (Fin n)]

def dualGaugeRel (p q : DualParameter n) : Prop :=
  ∃ t : ℝ,
    q = (p.1, (fun i => p.2.1 i + t), (fun j => p.2.2 j - t))

def dualGaugeSetoid : Setoid (DualParameter n) where
  r := dualGaugeRel
  iseqv := by
    constructor
    · intro p
      refine ⟨0, ?_⟩
      ext <;> simp
    · intro p q h
      rcases h with ⟨t, rfl⟩
      refine ⟨-t, ?_⟩
      ext <;> simp <;> ring
    · intro p q r hpq hqr
      rcases hpq with ⟨t, rfl⟩
      rcases hqr with ⟨u, rfl⟩
      refine ⟨t + u, ?_⟩
      ext <;> simp <;> ring

abbrev DualGaugeQuotient := Quotient (dualGaugeSetoid (n := n))

def dualGaugeQuotientMap :
    DualParameter n → DualGaugeQuotient (n := n) :=
  Quotient.mk (dualGaugeSetoid (n := n))

theorem continuous_dualGaugeQuotientMap :
    Continuous (dualGaugeQuotientMap (n := n)) :=
  continuous_quot_mk

theorem isQuotientMap_dualGaugeQuotientMap :
    Topology.IsQuotientMap (dualGaugeQuotientMap (n := n)) :=
  isQuotientMap_quot_mk

def dualGaugeQuotientMapTopCatHom :
    TopCat.of (DualParameter n) ⟶ TopCat.of (DualGaugeQuotient (n := n)) :=
  TopCat.ofHom
    { toFun := dualGaugeQuotientMap (n := n)
      continuous_toFun := continuous_dualGaugeQuotientMap (n := n) }

theorem dualObjectiveReadout_respects_gauge
    (C : PoissonTransportCost (Observation := Fin n) (Component := Fin n))
    {p q : DualParameter n} (hpq : dualGaugeRel p q) :
    dualObjectiveReadout C p = dualObjectiveReadout C q := by
  rcases hpq with ⟨t, rfl⟩
  exact (dualObjectiveReadout_gauge_invariant C p.1 t p.2.1 p.2.2).symm

noncomputable def dualObjectiveGaugeQuotient
    (C : PoissonTransportCost (Observation := Fin n) (Component := Fin n)) :
    DualGaugeQuotient (n := n) → ℝ :=
  Quotient.lift (dualObjectiveReadout C)
    (fun _ _ h => dualObjectiveReadout_respects_gauge C h)

theorem dualObjectiveGaugeQuotient_mk
    (C : PoissonTransportCost (Observation := Fin n) (Component := Fin n))
    (p : DualParameter n) :
    dualObjectiveGaugeQuotient C (dualGaugeQuotientMap p) =
      dualObjectiveReadout C p := by
  rfl

theorem continuous_dualObjectiveGaugeQuotient
    (C : PoissonTransportCost (Observation := Fin n) (Component := Fin n)) :
    Continuous (dualObjectiveGaugeQuotient C) := by
  exact Continuous.quotient_lift (continuous_dualObjectiveReadout C)
    (fun _ _ h => dualObjectiveReadout_respects_gauge C h)

noncomputable def dualObjectiveGaugeQuotientTopCatHom
    (C : PoissonTransportCost (Observation := Fin n) (Component := Fin n)) :
    TopCat.of (DualGaugeQuotient (n := n)) ⟶ TopCat.of ℝ :=
  TopCat.ofHom
    { toFun := dualObjectiveGaugeQuotient C
      continuous_toFun := continuous_dualObjectiveGaugeQuotient C }

theorem dualGaugeQuotient_objective_factorization
    (C : PoissonTransportCost (Observation := Fin n) (Component := Fin n)) :
    dualGaugeQuotientMapTopCatHom (n := n) ≫
        dualObjectiveGaugeQuotientTopCatHom C =
      dualObjectiveTopCatHom C := by
  ext p
  rfl

theorem dualGaugeQuotient_objective_factorization_unique
    (C : PoissonTransportCost (Observation := Fin n) (Component := Fin n))
    (u : TopCat.of (DualGaugeQuotient (n := n)) ⟶ TopCat.of ℝ)
    (hu : dualGaugeQuotientMapTopCatHom (n := n) ≫ u =
      dualObjectiveTopCatHom C) :
    u = dualObjectiveGaugeQuotientTopCatHom C := by
  apply TopCat.hom_ext
  ext q
  induction q using Quotient.inductionOn with
  | _ p =>
      have hp := congrArg (fun m => m p) hu
      simpa [dualGaugeQuotientMapTopCatHom,
        dualObjectiveGaugeQuotientTopCatHom,
        dualObjectiveTopCatHom, TopCat.comp_app, TopCat.ofHom] using hp

end InfoGeometry.Topology.PoissonSinkhornDualGaugeQuotientTopCat
