import InfoGeometry.Topology.FractalCantorFockWitness
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Krein.Superalgebra

/-!
# InfoGeometry.Canonical.CelikKocakKreinSupergradedLift

Theorem-only supergraded/Krein readbacks for the Celik--Koçak carrier.

This file does not define a new structure. It states the grading consequences
directly from explicit oddness hypotheses on the relevant endomorphisms.
-/

noncomputable section

namespace InfoGeometry.Canonical.CelikKocakKreinSupergradedLift

open InfoGeometry.Topology.FractalCantorFockWitness
open InfoGeometry.Krein
open KreinGradedModule

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [CompleteSpace H] [KreinSpace H] [KreinGradedModule H]

variable (tiltSwitch : TiltSwitchSystem (H →L[ℝ] H))
variable (clifford : RealDoubledCantorCliffordRepresentation (H →L[ℝ] H))

/-- Tilt generators are odd, so their even part vanishes. -/
theorem tilt_evenPart_eq_zero (tiltOdd : ∀ p : ℕ, IsOdd (H := H) (tiltSwitch.T p))
    (p : ℕ) :
    evenPart (tiltSwitch.T p) = 0 :=
  evenPart_eq_zero_of_isOdd (tiltOdd p)

/-- Switch generators are odd, so their even part vanishes. -/
theorem switch_evenPart_eq_zero (switchOdd : ∀ p : ℕ, IsOdd (H := H) (tiltSwitch.S p))
    (p : ℕ) :
    evenPart (tiltSwitch.S p) = 0 :=
  evenPart_eq_zero_of_isOdd (switchOdd p)

/-- Clifford generators are odd, so their even part vanishes. -/
theorem gamma_evenPart_eq_zero (gammaOdd : ∀ i : ℕ, IsOdd (H := H) (clifford.gamma i))
    (i : ℕ) :
    evenPart (clifford.gamma i) = 0 :=
  evenPart_eq_zero_of_isOdd (gammaOdd i)

/-- Clifford generators are odd, so their odd part is the generator itself. -/
theorem gamma_oddPart_eq (gammaOdd : ∀ i : ℕ, IsOdd (H := H) (clifford.gamma i))
    (i : ℕ) :
    oddPart (clifford.gamma i) =
      clifford.gamma i :=
  oddPart_eq_of_isOdd (gammaOdd i)

/-- Tilt generators are supercommutator-anticommutator equivalent in the odd sector. -/
theorem tilt_superComm_eq_anticomm
    (tiltOdd : ∀ p : ℕ, IsOdd (H := H) (tiltSwitch.T p))
    (p q : ℕ) :
    superComm (tiltSwitch.T p)
      (tiltSwitch.T q)
      =
      anticomm (tiltSwitch.T p)
        (tiltSwitch.T q) := by
  exact superComm_odd_odd (tiltOdd p) (tiltOdd q)

/-- Switch generators are supercommutator-anticommutator equivalent in the odd sector. -/
theorem switch_superComm_eq_anticomm
    (switchOdd : ∀ p : ℕ, IsOdd (H := H) (tiltSwitch.S p))
    (p q : ℕ) :
    superComm (tiltSwitch.S p)
      (tiltSwitch.S q)
      =
      anticomm (tiltSwitch.S p)
        (tiltSwitch.S q) := by
  exact superComm_odd_odd (switchOdd p) (switchOdd q)

/-- Clifford generators are supercommutator-anticommutator equivalent in the odd sector. -/
theorem gamma_superComm_eq_anticomm
    (gammaOdd : ∀ i : ℕ, IsOdd (H := H) (clifford.gamma i))
    (i j : ℕ) :
    superComm (clifford.gamma i)
      (clifford.gamma j)
      =
      anticomm (clifford.gamma i)
        (clifford.gamma j) := by
  exact superComm_odd_odd (gammaOdd i) (gammaOdd j)

end InfoGeometry.Canonical.CelikKocakKreinSupergradedLift

