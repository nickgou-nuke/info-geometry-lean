import InfoGeometry.Topology.ToeplitzCuntzCoxeterInvariantContinuousMapEquiv

/-!
# The theorem-backed topological projection of the Coxeter construction

This owner is the conservative projection of the surrounding narrative onto
the facts actually proved in the topology subsystem.  Its graph contains only
the ternary boundary, the order-three orbit quotient, the continuous quotient
projection, and the descent/equivalence of invariant continuous observables.

No algebraic, causal, (M_2), octonionic, holonomy, or physical claim is
silently projected into this graph.  Those claims require independent owners
and hypotheses.
-/

noncomputable section

namespace InfoGeometry.Topology.CoxeterTopologicalTruthProjection

open InfoGeometry.Topology.ToeplitzCuntzThreeCoxeterBoundaryOrbitQuotient
open InfoGeometry.Topology.ToeplitzCuntzCoxeterInvariantContinuousMapEquiv
open InfoGeometry.Canonical.ToeplitzCuntzThreeCoxeterBoundaryAction
open InfoGeometry.Topology.ToeplitzCuntzThreeTriality

/-- The theorem-backed topological graph of the concrete Coxeter quotient. -/
structure CoxeterTopologicalTruthGraph where
  projection : TernaryBoundary → CoxeterBoundaryOrbitSpace
  projection_eq_canonical :
    projection = coxeterOrbitProjection
  projection_continuous : Continuous projection
  projection_invariant :
    ∀ x, projection (coxeterBoundaryHomeomorph x) = projection x

/-- The canonical graph assembled entirely from existing proved owners. -/
def canonicalTruthGraph : CoxeterTopologicalTruthGraph where
  projection := coxeterOrbitProjection
  projection_eq_canonical := rfl
  projection_continuous := continuous_coxeterOrbitProjection
  projection_invariant := coxeterOrbitProjection_identifies_cycle

@[simp] theorem canonicalTruthGraph_projection (x : TernaryBoundary) :
    canonicalTruthGraph.projection x = coxeterOrbitProjection x := rfl

theorem canonicalTruthGraph_projection_continuous :
    Continuous canonicalTruthGraph.projection := by
  simpa [canonicalTruthGraph] using continuous_coxeterOrbitProjection

theorem canonicalTruthGraph_projection_invariant (x : TernaryBoundary) :
    canonicalTruthGraph.projection (coxeterBoundaryHomeomorph x) =
      canonicalTruthGraph.projection x := by
  exact canonicalTruthGraph.projection_invariant x

/-- The universal topological observable statement attached to the graph. -/
def invariantObservableEquiv {Y : Type*} [TopologicalSpace Y] :
    C(CoxeterBoundaryOrbitSpace, Y) ≃
      InvariantContinuousMap (Y := Y) :=
  orbitContinuousMapEquiv (Y := Y)

@[simp] theorem descended_observable_projects
    {Y : Type*} [TopologicalSpace Y]
    (f : InvariantContinuousMap (Y := Y)) (x : TernaryBoundary) :
    (invariantObservableEquiv (Y := Y)).symm f
        (canonicalTruthGraph.projection x) = f.val x := by
  exact descendOrbitObservable_apply_projection f x

theorem observable_projection_bijection
    {Y : Type*} [TopologicalSpace Y] :
    Function.Bijective (invariantObservableEquiv (Y := Y)) := by
  exact (invariantObservableEquiv (Y := Y)).bijective

end InfoGeometry.Topology.CoxeterTopologicalTruthProjection
