import InfoGeometry.Clifford.LogCftMonodromy

/-!
# RestoreMonodromyPowers2

Small sandbox packet for the Hadjiivanov monodromy power laws.
-/

namespace InfoGeometry.Restore.MonodromyPowers2

open Matrix
open InfoGeometry.Clifford.LogCftMonodromy

/-- One-wrap monodromy determinant readout. -/
theorem monodromy_is_parabolic_restore (h : ℂ) :
    (hadjiivanovMonodromy h).det = lcftPhase h ^ 2 := by
  exact monodromy_is_parabolic h

/-- Winding-number monodromy power law. -/
theorem hadjiivanovMonodromy_pow_winding_restore (h : ℂ) (n : ℕ) :
    hadjiivanovMonodromy h ^ n =
      lcftPhase h ^ n •
        ((1 : Matrix (Fin 2) (Fin 2) ℂ) +
          ((n : ℂ) * logShearBase) • jordanNilpotent) := by
  exact hadjiivanovMonodromy_pow_winding h n

/-- Algebraic power-form wrapper. -/
theorem hadjiivanovMonodromy_pow_algebraic_restore (h : ℂ) (n : ℕ) :
    hadjiivanovMonodromy h ^ n =
      lcftPhase h ^ n •
        ((1 : Matrix (Fin 2) (Fin 2) ℂ) +
          ((n : ℂ) * logShearBase) • jordanNilpotent) := by
  exact hadjiivanovMonodromy_pow_algebraic h n

/-- Binomial-facing nilpotent power law. -/
theorem one_plus_c_epsilon_pow_restore (c : ℂ) (n : ℕ) :
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) + c • epsilon) ^ n =
      1 + ((n : ℂ) * c) • epsilon := by
  exact one_plus_c_epsilon_pow c n

/-- Equivalent subtraction form. -/
theorem one_minus_c_epsilon_pow_restore (c : ℂ) (n : ℕ) :
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) - c • epsilon) ^ n =
      1 - ((n : ℂ) * c) • epsilon := by
  exact one_minus_c_epsilon_pow c n

/-- Coefficient readout for the `n`-fold monodromy. -/
theorem hadjiivanovMonodromy_genuine_coefficient_readout_restore (h : ℂ) (n : ℕ) :
    hadjiivanovMonodromy h ^ n =
        lcftPhase h ^ n •
          ((1 : Matrix (Fin 2) (Fin 2) ℂ) +
            ((n : ℂ) * logShearBase) • jordanNilpotent)
      ∧ (hadjiivanovMonodromy h ^ n) 0 0 = lcftPhase h ^ n
      ∧ (hadjiivanovMonodromy h ^ n) 0 1 =
          lcftPhase h ^ n * ((n : ℂ) * logShearBase)
      ∧ (hadjiivanovMonodromy h ^ n) 1 0 = 0
      ∧ (hadjiivanovMonodromy h ^ n) 1 1 = lcftPhase h ^ n := by
  exact hadjiivanovMonodromy_genuine_coefficient_readout h n

end InfoGeometry.Restore.MonodromyPowers2
