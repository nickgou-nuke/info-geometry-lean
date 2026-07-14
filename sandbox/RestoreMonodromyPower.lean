import InfoGeometry.Clifford.LogCftMonodromy

/-!
# RestoreMonodromyPower

Small sandbox packet for the Hadjiivanov monodromy power law.
-/

namespace InfoGeometry.Restore.MonodromyPower

open Matrix
open InfoGeometry.Clifford.LogCftMonodromy

/-- One-wrap monodromy determinant readout. -/
theorem monodromy_is_parabolic_restore (h : ℂ) :
    (hadjiivanovMonodromy h).det = lcftPhase h ^ 2 := by
  exact monodromy_is_parabolic h

/-- Winding-number form of the compounded monodromy. -/
theorem hadjiivanovMonodromy_pow_winding_restore (h : ℂ) (n : ℕ) :
    hadjiivanovMonodromy h ^ n =
      lcftPhase h ^ n •
        ((1 : Matrix (Fin 2) (Fin 2) ℂ) +
          ((n : ℂ) * logShearBase) • jordanNilpotent) := by
  exact hadjiivanovMonodromy_pow_winding h n

/-- Readout of all coefficients in the `n`-fold monodromy. -/
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

end InfoGeometry.Restore.MonodromyPower
