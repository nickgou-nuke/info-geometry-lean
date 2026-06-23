import DAG.HodgeTheorems

namespace DAG.DiracLaplacian

open DAG

/-- Canonical chain complex `0 -> 1 -> 2` reused from the Hodge owner file. -/
abbrev chainComplex : TwoComplex Nat :=
  canonicalChainComplex

/--
On the canonical chain, the graph Dirac square is the explicit block-diagonal
matrix `Δ₀ ⊕ (∂₁∂₁ᵀ)`.
-/
theorem dirac_squared_block_diagonal_chain :
    let D := graphDirac chainComplex
    matMul D D =
      #[#[(1 : Rat), -1, 0, 0, 0],
        #[-1, 2, -1, 0, 0],
        #[0, -1, 1, 0, 0],
        #[0, 0, 0, 2, -1],
        #[0, 0, 0, -1, 2]] := by
  native_decide

/-- The exported Boolean owner check also verifies `D² = Δ` on the chain. -/
theorem dirac_square_check_chain :
    diracSquareCheck chainComplex = true := by
  native_decide

/-- The upper-left entry of `D²` agrees with the vertex Laplacian. -/
theorem dirac_sq_upper_left_is_laplacian0_chain :
    let D := graphDirac chainComplex
    let Dsq := matMul D D
    let Δ₀ := laplacian0 chainComplex
    (Dsq[0]!)[0]! = (Δ₀[0]!)[0]! := by
  native_decide

/-- The lower-right entry of `D²` agrees with the down-Laplacian on 1-chains. -/
theorem dirac_sq_lower_right_is_down_laplacian1_chain :
    let D := graphDirac chainComplex
    let Dsq := matMul D D
    let downΔ₁ := matMul (boundary1 chainComplex) (matTranspose (boundary1 chainComplex))
    (Dsq[3]!)[3]! = (downΔ₁[0]!)[0]! := by
  native_decide

/-- The upper-right off-diagonal block of `D²` vanishes on the chain. -/
theorem dirac_sq_upper_right_is_zero_chain :
    let D := graphDirac chainComplex
    let Dsq := matMul D D
    (Dsq[0]!)[3]! = 0 := by
  native_decide

/-- The lower-left off-diagonal block of `D²` vanishes on the chain. -/
theorem dirac_sq_lower_left_is_zero_chain :
    let D := graphDirac chainComplex
    let Dsq := matMul D D
    (Dsq[3]!)[0]! = 0 := by
  native_decide

/-- The trace of `D²` is the sum of the two diagonal Laplacian block traces. -/
theorem trace_D_sq_equals_trace_laplacians_chain :
    let D := graphDirac chainComplex
    let Dsq := matMul D D
    matTrace Dsq = matTrace (laplacian0 chainComplex)
      + matTrace (matMul (boundary1 chainComplex) (matTranspose (boundary1 chainComplex))) := by
  native_decide

end DAG.DiracLaplacian
