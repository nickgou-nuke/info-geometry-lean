import InfoGeometry.Quantum.CuntzPoincareLorentzSupercharge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Rest-frame Cuntz/primon Poincare-Lorentz packet

This file links the Cuntz/primon Hamiltonian spectral projector calculation to
the finite Pauli super-Poincare readout in the rest frame.

No analytic or infinite-dimensional claim is made: the result is the finite
algebraic statement that the Cuntz Hamiltonian square eigenvalue on a range
projector matches the rest-frame Pauli Minkowski Casimir, while the already
proved finite Cuntz supercharge anticommutator and exact Lorentz determinant
invariance remain available in one packet.
-/

noncomputable section

namespace InfoGeometry.Quantum.CuntzPrimonRestPoincare

open Matrix
open InfoGeometry.Algebra.CuntzPrimonHamiltonian
open InfoGeometry.Algebra.SupergradedSUSY
open InfoGeometry.Algebra.LorentzBiquaternionEquivalence
open InfoGeometry.Algebra.CuntzLorentzPoincarePresentation
open InfoGeometry.Canonical.PauliHestenesSpinMomentum
open InfoGeometry.Quantum.PoincareSupercharge
open InfoGeometry.Quantum.CuntzPoincareLorentzSupercharge

/-- Rest-frame Pauli paravector carried by one real Cuntz/primon energy. -/
def restPauliParavector (E : ℝ) : PauliParavector where
  energy := E
  px := 0
  py := 0
  pz := 0

/-- Rest-frame Minkowski norm is the energy square. -/
theorem restPauliParavector_minkowskiNormSq (E : ℝ) :
    (restPauliParavector E).minkowskiNormSq = E ^ 2 := by
  simp [restPauliParavector, PauliParavector.minkowskiNormSq]

/-- Rest-frame Pauli supercharge determinant is four times energy square. -/
theorem restPauli_supercharge_det (E : ℝ) :
    Matrix.det (restPauliParavector E).superPoincareAnticommutatorMatrix = ((4 * E ^ 2 : ℝ) : ℂ) := by
  rw [PauliParavector.det_superPoincareAnticommutatorMatrix_eq_four_minkowskiNormSq]
  rw [restPauliParavector_minkowskiNormSq]

/-- Trace readout of the rest-frame supercharge anticommutator gives zero spatial momentum. -/
theorem restPauli_supercharge_trace_readout (E : ℝ) (a : Fin 4) :
    PauliParavector.superchargeMomentumReadout a (restPauliParavector E) =
      (match a with
      | 0 => (E : ℂ)
      | 1 => 0
      | 2 => 0
      | 3 => 0) := by
  rw [pauli_supercharge_trace_recovers_four_momentum]
  fin_cases a <;> simp [restPauliParavector]

/-- Twice-composed exact Lorentz transport preserves rest-frame energy square determinant. -/
theorem restPauli_exactBoost_comp_self_det (E : ℝ) :
    Matrix.det (exactBoostTransport (exactBoostTransport (restPauliParavector E).pauliMatrix)) =
      (E ^ 2 : ℂ) := by
  rw [exactBoostTransport_comp_self_pauli_minkowski]
  rw [restPauliParavector_minkowskiNormSq]
  norm_num

/-- Cuntz primon Hamiltonian square eigenvalue matches rest-frame Pauli Casimir. -/
theorem primon_cuntz_casimir_matches_rest_pauli
    (n : ℕ) (ε : Fin n → ℝ) (i : Fin n) :
    (hamiltonian n (fun j => (ε j : ℂ)) * hamiltonian n (fun j => (ε j : ℂ))) * P n i =
        (((ε i : ℂ) ^ 2) • P n i) ∧
      (restPauliParavector (ε i)).minkowskiNormSq = (ε i) ^ 2 := by
  refine ⟨?_, restPauliParavector_minkowskiNormSq (ε i)⟩
  simpa [pow_two] using
    casimir_eigenvalue n (fun j => (ε j : ℂ)) i

end InfoGeometry.Quantum.CuntzPrimonRestPoincare

end noncomputable section
