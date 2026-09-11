import InfoGeometry.Clifford.LogCftMonodromy
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Cl55ComplexStructureRealification

/-! Explicit phase/shear readouts for the existing upper-Jordan monodromy.

The phase projection is the only component compared with a pure rotor here;
the nilpotent shear remains a separate observable. -/

noncomputable section

namespace InfoGeometry.Clifford.Cl55LCFTPhaseProjection

open InfoGeometry.Clifford.LogCftMonodromy
open InfoGeometry.Clifford.Cl55ComplexStructureRealification

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

theorem lcftPhase_realified (B : ℂ) (r : ℝ) :
    complexRealification B (lcftPhase (r : ℂ)) =
      (Real.cos (-2 * Real.pi * r)) • (1 : ℂ) +
        (Real.sin (-2 * Real.pi * r)) • B := by
  unfold lcftPhase
  have harg :
      -(2 : ℂ) * Complex.I * (Real.pi : ℂ) * (r : ℂ) =
        ((-2 * Real.pi * r : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, complexRealification_phase]

end InfoGeometry.Clifford.Cl55LCFTPhaseProjection
