import Mathlib.Topology.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SpinorOrbitStratumTopological

/-!
# Consolidation of the rational quadratic-stratum presentations

The rational `(5,5)` topology owner and the proposition-level stratum owner
use two presentations of the same polynomial.  This file records their
coherence and the generic set-theoretic transport facts, without asserting an
orbit classification or a manifold structure.
-/

namespace InfoGeometry.Canonical.QuadraticStratumTopologicalBridge

open InfoGeometry.Physics.Pin55Formal
open InfoGeometry.Topology.Pin55ReflectionGlide
open InfoGeometry.Topology.SpinorOrbitStratum
open InfoGeometry.Topology.SpinorOrbitStratumTopological

abbrev Vec55 := InfoGeometry.Algebra.FiniteSpin.Vec10Q

theorem splitNorm55_eq_q55 (x : Vec55) :
    splitNorm55 x = q55 x := by
  simp [splitNorm55, q55, QuadraticMap.proj_apply]

@[simp] theorem mem_q55NonzeroNullLocus_iff (x : Vec55) :
    x ∈ q55NonzeroNullLocus ↔ x ≠ 0 ∧ q55 x = 0 := by
  simp [q55NonzeroNullLocus, q55NullLocus, and_comm]

@[simp] theorem mem_q55GenericLocus_iff (x : Vec55) :
    x ∈ q55GenericLocus ↔ q55 x ≠ 0 := by
  rfl

theorem q55GenericLocus_eq_positive_union_negative :
    q55GenericLocus = q55PositiveLocus ∪ q55NegativeLocus := by
  ext x
  simp only [mem_q55GenericLocus_iff, q55PositiveLocus, q55NegativeLocus,
    Set.mem_union]
  constructor
  · intro h
    rcases lt_or_gt_of_ne h with hneg | hpos
    · exact Or.inr hneg
    · exact Or.inl hpos
  · intro h
    rcases h with hpos | hneg
    · exact ne_of_gt hpos
    · exact ne_of_lt hneg

theorem q55PositiveLocus_disjoint_q55NegativeLocus :
    Disjoint q55PositiveLocus q55NegativeLocus := by
  rw [Set.disjoint_left]
  intro x hx hy
  change 0 < q55 x at hx
  change q55 x < 0 at hy
  exact (not_lt_of_ge (le_of_lt hx)) hy

theorem preimage_eq_zeroLocus
    {X : Type*} {R : Type*} [TopologicalSpace X] [Zero R]
    (Q : X → R) (h : X ≃ₜ X)
    (hQ : ∀ x, Q (h x) = Q x) :
    h ⁻¹' {x | Q x = 0} = {x | Q x = 0} := by
  ext x
  change Q (h x) = 0 ↔ Q x = 0
  rw [hQ]

end InfoGeometry.Canonical.QuadraticStratumTopologicalBridge
