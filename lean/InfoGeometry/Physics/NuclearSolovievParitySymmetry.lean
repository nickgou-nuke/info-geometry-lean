import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.NuclearParityGradedHamiltonian
import InfoGeometry.Physics.NuclearFiniteCARCartanSolovievBridge

/-!
# Soloviev parity symmetry from the generic parity-graded Hamiltonian theorem

This file removes the model-specific algebraic duplication from the conceptual
statement of the finite Soloviev symmetry.  The existing concrete CAR model
supplies:

* an involution `finiteParity`;
* a parity-even one-mode quasiparticle Hamiltonian;
* a parity-odd off-diagonal CAR interaction generator.

The generic `NuclearParityGradedHamiltonian` theorem then gives

`P H(epsilon,v) P = H(epsilon,-v)`.

The representation remains the existing concrete `2 × 2` finite-CAR model.
No claim about a more general phenomenological Soloviev Hamiltonian is made.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearSolovievParitySymmetry

open InfoGeometry.Physics.NuclearParityGradedHamiltonian
open InfoGeometry.Physics.NuclearFiniteCARProjection
open InfoGeometry.Physics.NuclearFiniteCARCartanSolovievBridge

/-- The parameter-independent odd interaction generator `a + a†`. -/
def interactionGenerator : M2R :=
  annihilation + creation

/-- The concrete finite-CAR parity is an involution. -/
theorem finiteParity_isInvolution :
    IsInvolution finiteParity := by
  exact finiteParity_sq

/-- The diagonal quasiparticle Hamiltonian is in the even parity sector. -/
theorem oneModeHamiltonian_even (epsilon : ℝ) :
    EvenUnderConjugation finiteParity (oneModeHamiltonian epsilon) := by
  simpa [EvenUnderConjugation, conjugate] using
    parity_conj_oneModeHamiltonian epsilon

/-- The bare off-diagonal CAR transition generator is parity-odd. -/
theorem interactionGenerator_odd :
    OddUnderConjugation finiteParity interactionGenerator := by
  have h := parity_conj_carInteraction (1 : ℝ)
  simpa [OddUnderConjugation, conjugate, interactionGenerator,
    carInteraction] using h

/-- The concrete Soloviev/CAR Hamiltonian is exactly the generic affine
parity-graded Hamiltonian with odd generator `a + a†`. -/
theorem coupledHamiltonian_eq_parameterHamiltonian
    (epsilon v : ℝ) :
    coupledHamiltonian epsilon v =
      parameterHamiltonian (oneModeHamiltonian epsilon)
        interactionGenerator v := by
  rfl

/-- Native derivation of the Soloviev coupling-sign symmetry from the generic
parity-graded Hamiltonian theorem. -/
theorem conjugate_coupledHamiltonian
    (epsilon v : ℝ) :
    conjugate finiteParity (coupledHamiltonian epsilon v) =
      coupledHamiltonian epsilon (-v) := by
  rw [coupledHamiltonian_eq_parameterHamiltonian epsilon v,
    coupledHamiltonian_eq_parameterHamiltonian epsilon (-v)]
  exact
    conjugate_parameterHamiltonian
      (oneModeHamiltonian_even epsilon)
      interactionGenerator_odd
      v

/-- Multiplicative matrix form of the same theorem. -/
theorem parity_conj_coupledHamiltonian_native
    (epsilon v : ℝ) :
    finiteParity * coupledHamiltonian epsilon v * finiteParity =
      coupledHamiltonian epsilon (-v) := by
  simpa [conjugate] using conjugate_coupledHamiltonian epsilon v

/-- The pre-existing concrete theorem and the generic derivation have the same
proposition.  This theorem is intentionally trivial: it records owner-level
agreement without duplicating a second physical statement. -/
theorem generic_and_concrete_parity_theorems_agree
    (epsilon v : ℝ) :
    (finiteParity * coupledHamiltonian epsilon v * finiteParity =
      coupledHamiltonian epsilon (-v)) :=
  parity_conj_coupledHamiltonian_native epsilon v

/-- The generic involutive conjugation theorem specializes to the full finite
Soloviev Hamiltonian family. -/
theorem parity_action_twice
    (epsilon v : ℝ) :
    conjugate finiteParity
        (conjugate finiteParity (coupledHamiltonian epsilon v)) =
      coupledHamiltonian epsilon v := by
  exact conjugate_involutive finiteParity_isInvolution _

end InfoGeometry.Physics.NuclearSolovievParitySymmetry

end noncomputable section
