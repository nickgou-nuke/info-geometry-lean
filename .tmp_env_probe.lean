import Mathlib.Analysis.InnerProductSpace.Adjoint

example {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →L[ℝ] H) (u v : H) : ⟪ContinuousLinearMap.adjoint A u, v⟫ = ⟪u, A v⟫ := 
  ContinuousLinearMap.inner_adjoint_left A u v
