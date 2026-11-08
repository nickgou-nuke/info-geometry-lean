/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.FiniteMarkovHittingCost

/-! # Kernel axiom audit for finite Markov first-hit costs -/

namespace InfoGeometry.QuantumContext.FiniteMarkovHittingCost

#print axioms truncatedFirstHitCost
#print axioms truncatedFirstHitCost_nonneg
#print axioms truncatedFirstHitCost_le_length
#print axioms finiteHistoryToList
#print axioms finiteHistoryTail
#print axioms finiteHistoryToList_succ
#print axioms truncatedFirstHitCost_finiteHistory_succ
#print axioms firstHitApproximation_succ_eq_transition_expectation
#print axioms firstHitApproximation_succ_eq_target

end InfoGeometry.QuantumContext.FiniteMarkovHittingCost
