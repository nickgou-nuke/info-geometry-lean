import InfoGeometry.Modular.FiniteSimplexModularTime

/-!
# Fixed observables of a finite diagonal modular flow

This file extends the existing finite faithful diagonal modular flow.  It proves
that, at a time when no off-diagonal modular phase is resonant, its fixed
observables are exactly the diagonal matrices.  This is a finite matrix
statement; it makes no identification with Wheeler--DeWitt dynamics or the
general Tomita--Takesaki modular operator.
-/

namespace InfoGeometry.Experimental.FiniteModularFixedPoints

open InfoGeometry.Modular.FiniteSimplexModularTime
open InfoGeometry.Probability.AitchisonFinite

variable {n : ℕ}

/-- A matrix has no off-diagonal coefficients. -/
def IsDiagonal (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ i j, i ≠ j → A i j = 0

/-- At a nonresonant time, the fixed-point algebra of a faithful diagonal
modular flow consists precisely of diagonal observables.  The nonresonance
hypothesis is necessary: modular frequencies can have period-dependent
resonances even when the density weights are distinct. -/
theorem flow_fixed_iff_diagonal (p : PositiveSimplex n) (t : ℝ)
    (hnonres : ∀ i j : Fin n, i ≠ j → phase p t i j ≠ 1)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    flow p t A = A ↔ IsDiagonal A := by
  constructor
  · intro hfixed i j hij
    have hentry := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j) hfixed
    change phase p t i j * A i j = A i j at hentry
    have hprod : (phase p t i j - 1) * A i j = 0 := by
      calc
        (phase p t i j - 1) * A i j = phase p t i j * A i j - A i j := by ring
        _ = 0 := by rw [hentry]; ring
    rcases mul_eq_zero.mp hprod with hphase | hA
    · exact False.elim ((hnonres i j hij) (sub_eq_zero.mp hphase))
    · exact hA
  · intro hA
    ext i j
    by_cases hij : i = j
    · subst j
      simp [flow]
    · simp [flow, hA i j hij]

end InfoGeometry.Experimental.FiniteModularFixedPoints
