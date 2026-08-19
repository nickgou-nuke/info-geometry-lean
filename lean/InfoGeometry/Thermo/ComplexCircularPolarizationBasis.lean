import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Thermo.ComplexCircularPolarizationBasis

Proof-only circular polarization basis on the complex temperature plane.

This module formalizes the real-linear split

* `s + star s` for the amplitude/real lane,
* `s - star s` for the phase/imaginary lane,

and the corresponding factorization of the elementary Boltzmann weight.

No interface.
No property.
No zeta claim.
-/

noncomputable section

namespace InfoGeometry.Thermo.ComplexCircularPolarizationBasis

/-- Circular-plus coordinate `s + s̄`. -/
@[rep_depth thermo]
def circlePlus (s : ℂ) : ℂ :=
  s + star s

/-- Circular-minus coordinate `s - s̄`. -/
@[rep_depth thermo]
def circleMinus (s : ℂ) : ℂ :=
  s - star s

/-- Real/amplitude coordinate. -/
@[rep_depth thermo]
def circleAmplitudeCoord (s : ℂ) : ℂ :=
  circlePlus s / 2

/-- Imaginary/phase coordinate. -/
@[rep_depth thermo]
def circlePhaseCoord (s : ℂ) : ℂ :=
  circleMinus s / 2

/-- The circular split reconstructs the original complex coordinate. -/
@[rep_depth thermo]
theorem circle_reconstruct (s : ℂ) :
    s = circleAmplitudeCoord s + circlePhaseCoord s := by
  unfold circleAmplitudeCoord circlePhaseCoord circlePlus circleMinus
  ring

/-- Circular plus is conjugation-invariant. -/
@[rep_depth thermo]
theorem circlePlus_star (s : ℂ) :
    star (circlePlus s) = circlePlus s := by
  simp [circlePlus, add_comm]

/-- Circular minus is conjugation-odd. -/
@[rep_depth thermo]
theorem circleMinus_star (s : ℂ) :
    star (circleMinus s) = - circleMinus s := by
  simp [circleMinus, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

/-- Elementary complex Boltzmann weight `exp (-s E)`. -/
@[rep_depth thermo]
def complexBoltzmannWeight (E : ℝ) (s : ℂ) : ℂ :=
  Complex.exp (-(s * (E : ℂ)))

/-- Circular amplitude factor. -/
@[rep_depth thermo]
def circularBoltzmannAmplitude (E : ℝ) (s : ℂ) : ℂ :=
  Complex.exp (-(circleAmplitudeCoord s * (E : ℂ)))

/-- Circular phase factor. -/
@[rep_depth thermo]
def circularBoltzmannPhase (E : ℝ) (s : ℂ) : ℂ :=
  Complex.exp (-(circlePhaseCoord s * (E : ℂ)))

/-- The Boltzmann weight factors through the circular basis. -/
@[rep_depth thermo]
theorem complexBoltzmannWeight_eq_circular
    (E : ℝ) (s : ℂ) :
    complexBoltzmannWeight E s =
      circularBoltzmannAmplitude E s *
        circularBoltzmannPhase E s := by
  unfold complexBoltzmannWeight circularBoltzmannAmplitude
    circularBoltzmannPhase
  have hs :
      -(s * (E : ℂ)) =
        -(circleAmplitudeCoord s * (E : ℂ)) +
          -(circlePhaseCoord s * (E : ℂ)) := by
    unfold circleAmplitudeCoord circlePhaseCoord circlePlus circleMinus
    ring
  rw [hs, ← Complex.exp_add]

end InfoGeometry.Thermo.ComplexCircularPolarizationBasis
