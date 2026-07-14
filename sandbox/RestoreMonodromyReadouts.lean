import InfoGeometry.Clifford.LogCftMonodromy

/-!
# RestoreMonodromyReadouts

Small sandbox packet for monodromy determinant/power readouts.
-/

namespace InfoGeometry.Restore.MonodromyReadouts

open Matrix
open InfoGeometry.Clifford.LogCftMonodromy

/-- The nilpotent Jordan shear squares to zero. -/
theorem jordanNilpotent_sq :
    (jordanNilpotent : Matrix (Fin 2) (Fin 2) ℂ) * jordanNilpotent = 0 := by
  exact InfoGeometry.Clifford.LogCftMonodromy.jordanNilpotent_sq

/-- The monodromy determinant is the repeated phase square. -/
theorem monodromy_is_parabolic (h : ℂ) :
    (hadjiivanovMonodromy h).det = lcftPhase h ^ 2 := by
  exact InfoGeometry.Clifford.LogCftMonodromy.monodromy_is_parabolic h

/-- The compounded monodromy winding law. -/
theorem hadjiivanovMonodromy_pow_winding (h : ℂ) (n : ℕ) :
    hadjiivanovMonodromy h ^ n =
      lcftPhase h ^ n •
        ((1 : Matrix (Fin 2) (Fin 2) ℂ) +
          ((n : ℂ) * logShearBase) • jordanNilpotent) := by
  exact InfoGeometry.Clifford.LogCftMonodromy.hadjiivanovMonodromy_pow_winding h n

/-- Full coefficient readout for the `n`-fold monodromy. -/
theorem hadjiivanovMonodromy_genuine_coefficient_readout (h : ℂ) (n : ℕ) :
    hadjiivanovMonodromy h ^ n =
        lcftPhase h ^ n •
          ((1 : Matrix (Fin 2) (Fin 2) ℂ) +
            ((n : ℂ) * logShearBase) • jordanNilpotent)
      ∧ (hadjiivanovMonodromy h ^ n) 0 0 = lcftPhase h ^ n
      ∧ (hadjiivanovMonodromy h ^ n) 0 1 =
          lcftPhase h ^ n * ((n : ℂ) * logShearBase)
      ∧ (hadjiivanovMonodromy h ^ n) 1 0 = 0
      ∧ (hadjiivanovMonodromy h ^ n) 1 1 = lcftPhase h ^ n := by
  exact InfoGeometry.Clifford.LogCftMonodromy.hadjiivanovMonodromy_genuine_coefficient_readout h n

end InfoGeometry.Restore.MonodromyReadouts
