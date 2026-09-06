import DAG.TwoComplex
import DAG.GraphHodge
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open Matrix
open DAG

/-! ## Test: determinant approach on a concrete chain graph -/

-- Build a simple 3-vertex chain: 0 → 1 → 2
def myGraph : HydratedGraph Unit := Id.run do
  let mut g : HydratedGraph Unit := { nodes := #[(), (), ()], forward := #[], backward := #[], labels := #[], nodeLabels := #[] }
  -- Edge 0→1
  g := { g with forward := g.forward.set! 0 #[(1, ())] }
  g := { g with backward := g.backward.set! 1 #[(0, ())] }
  -- Edge 1→2
  g := { g with forward := g.forward.set! 1 #[(2, ())] }
  g := { g with backward := g.backward.set! 2 #[(1, ())] }
  return g

def myTC : TwoComplex Unit := buildTwoComplex myGraph

-- Check that boundary squared is zero
#eval boundarySquaredZero myTC

-- Check betti1
#eval betti1 myTC

-- Define matrix boundary operators
def ∂₁ : Matrix (Fin myTC.edges.size) (Fin myTC.base.toGraph.nodes.size) ℚ :=
  λ i j =>
    let (u, v) := myTC.edges[i.val]
    if j.val = u then (-1 : ℚ) else if j.val = v then 1 else 0

def laplacian1 : Matrix (Fin myTC.edges.size) (Fin myTC.edges.size) ℚ :=
  ∂₁ * ∂₁ᵀ

-- Test: can native_decide prove det ≠ 0 → trivial kernel?
example (ψ : Fin myTC.edges.size → ℚ) (h : laplacian1.mulVec ψ = 0) : ψ = 0 := by
  have h_det : laplacian1.det ≠ 0 := by
    native_decide
  have h_unit : IsUnit laplacian1 :=
    (Matrix.isUnit_iff_isUnit_det laplacian1).mpr <| by
      rwa [isUnit_iff_ne_zero]
  calc
    ψ = (1 : Matrix (Fin myTC.edges.size) (Fin myTC.edges.size) ℚ).mulVec ψ := by simp
    _ = ((laplacian1⁻¹ : Matrix (Fin myTC.edges.size) (Fin myTC.edges.size) ℚ) * laplacian1).mulVec ψ := by
      rw [h_unit.unit_spec.mul_inv_cancel]
    _ = (laplacian1⁻¹ : Matrix (Fin myTC.edges.size) (Fin myTC.edges.size) ℚ).mulVec (laplacian1.mulVec ψ) := by
      rw [Matrix.mulVec_mulVec]
    _ = (laplacian1⁻¹ : Matrix (Fin myTC.edges.size) (Fin myTC.edges.size) ℚ).mulVec 0 := by rw [h]
    _ = 0 := by simp

-- Test: can native_decide prove boundary_squared_zero on concrete matrix?
example : boundary2Matrix myTC * boundary1Matrix myTC = 0 := by
  native_decide
