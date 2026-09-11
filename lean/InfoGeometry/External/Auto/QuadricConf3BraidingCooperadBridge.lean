import InfoGeometry.External.Auto.VertexAlgebraBraidingCocycle
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Exact edge cochains on the two oriented three-vertex cycles

This module specializes the existing finite edge-system theorem to the two
orientations of a three-vertex triangle and packages the corresponding exact
cochain and potential-construction identities.
-/

namespace QuadricConf3BraidingCooperadBridge

open VertexAlgebraBraidingCocycle
open VertexAlgebraBraidingCocycle.EdgeSystem

/-- Three labelled vertices. -/
abbrev Vertex3 := Fin 3

/-- The cycle `0 → 1 → 2 → 0`. -/
def triangle012 : SpinNetCycle Vertex3 :=
  ⟨0, [1, 2]⟩

/-- The opposite cycle `0 → 2 → 1 → 0`. -/
def triangle021 : SpinNetCycle Vertex3 :=
  ⟨0, [2, 1]⟩

/-- An exact edge system has zero cycle functional on `0 → 1 → 2 → 0`. -/
theorem exact_cochain_kills_triangle012
    (S : EdgeSystem Vertex3) (potential : Vertex3 → ℝ)
    (hExact : IsExact S potential) :
    cycleEntropyProduction S triangle012 = 0 :=
  detailed_balance_implies_zero_cycle S potential hExact triangle012

/-- An exact edge system has zero cycle functional on `0 → 2 → 1 → 0`. -/
theorem exact_cochain_kills_triangle021
    (S : EdgeSystem Vertex3) (potential : Vertex3 → ℝ)
    (hExact : IsExact S potential) :
    cycleEntropyProduction S triangle021 = 0 :=
  detailed_balance_implies_zero_cycle S potential hExact triangle021

/-- If all finite cycle affinities vanish, the existing owner constructs a
potential after choosing a base vertex. -/
theorem zero_cycles_give_potential_on_three_vertices
    (S : EdgeSystem Vertex3) (base : Vertex3)
    (hzero : ∀ C : SpinNetCycle Vertex3, cycleAffinity S C = 0) :
    ∃ potential : Vertex3 → ℝ, IsExact S potential :=
  zero_cycle_affinity_implies_detailed_balance S base hzero

/-- Consolidated exact-cochain specialization to the two triangle orientations. -/
theorem exact_three_vertex_cycle_summary
    (S : EdgeSystem Vertex3) (potential : Vertex3 → ℝ)
    (hExact : IsExact S potential) :
    cycleEntropyProduction S triangle012 = 0 ∧
    cycleEntropyProduction S triangle021 = 0 :=
  ⟨exact_cochain_kills_triangle012 S potential hExact,
    exact_cochain_kills_triangle021 S potential hExact⟩

end QuadricConf3BraidingCooperadBridge
