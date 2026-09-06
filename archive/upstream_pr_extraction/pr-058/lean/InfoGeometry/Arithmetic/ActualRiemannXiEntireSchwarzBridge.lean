import InfoGeometry.Arithmetic.ActualRiemannXiEntireBridge

/-!
# Global Schwarz conjugation for the entire completed xi representative

The regular `riemannXi` Schwarz theorem is transported to the pole-removed
entire representative away from `0` and `1`.  At those two exceptional
points the explicit `+ 1` correction in `entireRiemannXi` gives the same real
value directly.  No zero-location or Riemann-hypothesis statement is used.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.ActualRiemannXiEntireSchwarzBridge

open Complex
open InfoGeometry.Arithmetic.RiemannZetaEquivalences
open InfoGeometry.Arithmetic.ActualRiemannXiEntireBridge
open InfoGeometry.Arithmetic.ActualRiemannXiSchwarzBridge

theorem entireRiemannXi_conj (s : ℂ) :
    star (entireRiemannXi s) = entireRiemannXi (star s) := by
  by_cases hs0 : s = 0
  · subst s
    simp [entireRiemannXi]
  by_cases hs1 : s = 1
  · subst s
    simp [entireRiemannXi]
  have hstar0 : star s ≠ 0 := by
    intro h
    apply hs0
    simpa using congrArg star h
  have hstar1 : star s ≠ 1 := by
    intro h
    apply hs1
    simpa using congrArg star h
  calc
    star (entireRiemannXi s) = star (riemannXi s) := by
      rw [entireRiemannXi_eq_riemannXi hs0 hs1]
    _ = riemannXi (star s) :=
      (riemannXi_conj_of_completed actualCompletedRiemannZetaSchwarz s).symm
    _ = entireRiemannXi (star s) :=
      (entireRiemannXi_eq_riemannXi hstar0 hstar1).symm

end InfoGeometry.Arithmetic.ActualRiemannXiEntireSchwarzBridge
