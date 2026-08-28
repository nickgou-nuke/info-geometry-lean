import InfoGeometry.Clifford.LogCftMonodromy

/-! Explicit phase/shear readouts for the existing upper-Jordan monodromy.

The phase projection is the only component compared with a pure rotor here;
the nilpotent shear remains a separate observable. -/

noncomputable section

namespace InfoGeometry.Clifford.Cl55LCFTPhaseProjection

open InfoGeometry.Clifford.LogCftMonodromy

def phaseProjection (M : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := M 0 0

def shearProjection (M : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := M 0 1

theorem hadjiivanovMonodromy_phaseProjection (h : ℂ) :
    phaseProjection (hadjiivanovMonodromy h) = lcftPhase h := by
  rfl

theorem hadjiivanovMonodromy_shearProjection (h : ℂ) :
    shearProjection (hadjiivanovMonodromy h) = logShear h := by
  rfl

theorem hadjiivanovMonodromy_eq_upperJordan_readouts (h : ℂ) :
    hadjiivanovMonodromy h =
      upperJordan (phaseProjection (hadjiivanovMonodromy h))
        (shearProjection (hadjiivanovMonodromy h)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

end InfoGeometry.Clifford.Cl55LCFTPhaseProjection
