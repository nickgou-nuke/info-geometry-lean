import Mathlib.Tactic
import DAG.HodgeTheorems
import DAG.GraphHodgeBridge
import InfoGeometry.Topology.EckmannDiscreteHodge

/-!
# Discrete Dirac-Hodge Chiral Bridge

Theorem-safe discrete Dirac-Hodge / chiral / Hodge-decomposition readbacks for
the finite `K₃` (triangle) simplicial model.

This file reuses the repository's existing finite graph-Hodge owners:

* `DAG.HodgeTheorems` for boundary-squared-zero, graph Dirac square, Betti, and
  chiral anticommutation checks on the canonical triangle complex;
* `InfoGeometry.Topology.EckmannDiscreteHodge` for the matrix-level closed /
  coclosed ⇒ harmonic and Betti-one-zero readbacks.

It does **not** claim a continuum Dirac operator, a smooth Hodge theorem, or a
full supersymmetric field theory.  The closed content is the finite simplicial
readback needed by the repository's topological and thermodynamic lanes.
-/

namespace InfoGeometry.Canonical.DiscreteDiracHodgeChiralBridge

open Matrix
open DAG
open InfoGeometry.Topology.EckmannDiscreteHodge

/-- The canonical `K₃` / triangle two-complex already owned by `DAG.HodgeTheorems`. -/
abbrev K3Complex : DAG.TwoComplex Nat :=
  DAG.canonicalTriangleComplex

/-- Explicit boundary `∂₁ : C₁ → C₀` for the oriented triangle edges. -/
def triangleBoundary1 : Matrix (Fin 3) (Fin 3) ℝ :=
  !![(-1 : ℝ), 1, 0;
      0, -1, 1;
      1, 0, -1]

/-- Explicit boundary `∂₂ : C₂ → C₁` for the filled triangle face. -/
def triangleBoundary2 : Matrix (Fin 1) (Fin 3) ℝ :=
  !![(1 : ℝ), 1, 1]

/-- The explicit triangle boundaries form a degree-one cochain complex. -/
theorem triangle_degree_one_cochain_complex :
    eckmannDegreeOneCochainComplex triangleBoundary1 triangleBoundary2 := by
  ext i j
  fin_cases i
  fin_cases j <;> simp [triangleBoundary1, triangleBoundary2]

/-- Every closed `1`-cochain on the filled triangle is exact. -/
theorem triangle_betti1_zero :
    eckmannBetti1Zero triangleBoundary1 triangleBoundary2 := by
  refine ⟨triangle_degree_one_cochain_complex, ?_⟩
  intro x hx
  have hsum : x 0 + x 1 + x 2 = 0 := by
    have h := congrFun hx 0
    simpa [triangleBoundary2, Matrix.mulVec, dotProduct, Fin.sum_univ_one, Fin.sum_univ_three] using h
  refine ⟨![0, x 0, x 0 + x 1], ?_⟩
  ext i
  fin_cases i
  · simp [triangleBoundary1, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · simp [triangleBoundary1, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · have hx2 : x 2 = -(x 0 + x 1) := by linarith
    simp [triangleBoundary1, Matrix.mulVec, dotProduct, Fin.sum_univ_three, hx2]

/-- Closed and coclosed `1`-forms on the filled triangle are trivial. -/
theorem triangle_harmonic_one_forms_vanish
    (x : Fin 3 → ℝ)
    (hClosed : triangleBoundary2.mulVec x = 0)
    (hCoClosed : triangleBoundary1.transpose.mulVec x = 0) :
    x = 0 :=
  eckmann_discrete_hodge_betti1_zero_of_closed_coclosed
    triangleBoundary1 triangleBoundary2 triangle_betti1_zero x hClosed hCoClosed

/-- Readback: the owner `K₃` boundary operator squares to zero. -/
theorem boundary_squared_zero_K3 :
    DAG.boundarySquaredZero K3Complex = true :=
  DAG.boundary_squared_zero_triangle

/-- Readback: the owner `K₃` graph Dirac squares to the expected block Laplacian. -/
theorem dirac_square_check_K3 :
    DAG.diracSquareCheck K3Complex = true :=
  by
    simpa [K3Complex] using DAG.dirac_square_check_triangle

/-- Readback: the owner `K₃` Hodge Laplacians are self-adjoint. -/
theorem laplacian_self_adjoint_K3 :
    DAG.laplacian0SelfAdjointCheck K3Complex = true ∧
      DAG.laplacian1SelfAdjointCheck K3Complex = true := by
  exact ⟨DAG.laplacian0_self_adjoint_triangle, DAG.laplacian1_self_adjoint_triangle⟩

/-- Readback: the owner constant chirality grading anticommutes with the graph Dirac operator. -/
theorem chiral_anticommutes_K3 :
    DAG.chiralAnticommutes K3Complex DAG.constantPlusTriangleGrading = true :=
  DAG.chiral_anticommutes_constant_triangle

/-- Readback: the triangle has no harmonic `1`-forms (`β₁ = 0`). -/
theorem betti1_zero_K3 :
    DAG.betti1 K3Complex = 0 := by
  simpa [K3Complex] using DAG.betti1_zero_triangle

/--
Exact/coexact/harmonic interpretation packet for a discrete `1`-form on the
filled triangle.
-/
def K3HarmonicMode (ω : Fin 3 → ℝ) : Prop :=
  triangleBoundary2.mulVec ω = 0 ∧
  triangleBoundary1.transpose.mulVec ω = 0

/-- Any `1`-form that is both closed and coclosed on the filled triangle vanishes. -/
theorem K3HarmonicMode.eq_zero {ω : Fin 3 → ℝ}
    (h : K3HarmonicMode ω) : ω = 0 :=
  triangle_harmonic_one_forms_vanish ω h.1 h.2

/-- Closed `1`-forms on the filled triangle are exact. -/
theorem K3HarmonicMode.exact_readout {ω : Fin 3 → ℝ}
    (h : K3HarmonicMode ω) :
    ∃ y : Fin 3 → ℝ, triangleBoundary1.mulVec y = ω :=
  triangle_betti1_zero.2 ω h.1

end InfoGeometry.Canonical.DiscreteDiracHodgeChiralBridge
