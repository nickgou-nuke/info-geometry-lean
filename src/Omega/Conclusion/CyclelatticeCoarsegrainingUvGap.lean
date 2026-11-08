import Omega.Graph.CoarsegrainingCycleRankDecomposition

namespace Omega.Conclusion

/-
The source theorem additionally asserts a theta-series small-parameter
asymptotic with an exponential remainder.  Its proved finite algebraic core is
the cycle-rank decomposition below; the analytic asymptotic is intentionally
not represented as a proved Lean theorem.
-/
/-- Algebraic core of `thm:conclusion-cyclelattice-coarsegraining-uv-gap`. -/
theorem paper_conclusion_cyclelattice_coarsegraining_uv_gap (k : Nat)
    (V E cG eIn : Int) (fiberRank : Fin k -> Int)
    (hEin : eIn = (V - (k : Int)) + Finset.univ.sum fiberRank) :
    (E - eIn) - (k : Int) + cG =
      (E - V + cG) - Finset.univ.sum fiberRank := by
  exact Omega.Graph.paper_graph_coarsegraining_cycle_rank_decomposition
    k V E cG eIn fiberRank hEin

end Omega.Conclusion
