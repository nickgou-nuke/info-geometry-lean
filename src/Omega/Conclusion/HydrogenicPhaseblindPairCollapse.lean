/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-hydrogenic-phaseblind-pair-collapse`. -/
theorem paper_conclusion_hydrogenic_phaseblind_pair_collapse {State Value : Type}
    (F : State → Value) (phase conjState : State → State) (ψ : ℕ → ℕ → ℤ → State)
    (pbClasses : ℕ → ℕ) (hphase : ∀ s, F (phase s) = F s)
    (hconj : ∀ s, F (conjState s) = F s)
    (hpair : ∀ n l m, ψ n l (-m) = phase (conjState (ψ n l m)))
    (hcount : ∀ n, pbClasses n = n * (n + 1) / 2) :
    (∀ n l m, F (ψ n l m) = F (ψ n l (-m))) ∧
      ∀ n, pbClasses n = n * (n + 1) / 2 := by
  constructor
  · intro n l m
    rw [hpair, hphase, hconj]
  · exact hcount

end Omega.Conclusion
