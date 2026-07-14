import InfoGeometry.Arithmetic.PrimeSuperalgebraReadback
import InfoGeometry.Canonical.PrimeMertensDefectBoundary
import InfoGeometry.Meta.SocketTarget

/-!
# InfoGeometry.Canonical.PrimeSUSYVacuum

SUSY vacuum readout capstone for the prime Lee--Yang architecture.

This module keeps the finite arithmetic facts separate from the analytic
spectral laws:

* finite Mobius parity is owned by
  `InfoGeometry.Arithmetic.PrimeSuperalgebraReadback`;
* analytic and spectral interpretations must be imported from their concrete
  owner files.

It does not prove RH, does not assert a completed-`xi` determinant identity, and
does not identify inverse-zeta Witten poles with zero modes.
-/

noncomputable section

namespace PrimeSUSYVacuum

open InfoGeometry.Arithmetic.PrimeSuperalgebraReadback
open InfoGeometry.Canonical.PrimeMertensDefectBoundary

/-! ## Finite arithmetic parity readback -/

/-- Finite fermion parity readout from the arithmetic prime-superalgebra layer. -/
abbrev finiteFermionParity
    (P : FermionicPrimeRegister)
    (psi : FermionicPrimeState P) : ℤ :=
  fermionParity P psi

/-- Mobius equals finite fermion parity on represented square-free prime-bit states. -/
theorem finite_mobius_eq_fermionParity
    (P : FermionicPrimeRegister)
    (psi : FermionicPrimeState P) :
    ArithmeticFunction.moebius (representedSquarefreeNat P psi) =
      finiteFermionParity P psi := by
  exact mobius_eq_fermionParity P psi

/-- Finite Witten-index cancellation over a nonempty prime register. -/
theorem finite_wittenIndex_cancel
    (P : FermionicPrimeRegister)
    (hP : P.primes.Nonempty) :
    (∑ S ∈ P.primes.powerset, (-1 : ℤ) ^ S.card) = 0 :=
  finiteBooleanWittenIndex_cancel P hP

/-- Finite Witten-index sum over all fermionic prime subsets. -/
def finiteWittenIndexSum (P : FermionicPrimeRegister) : ℤ :=
  ∑ S ∈ P.primes.powerset, (-1 : ℤ) ^ S.card

/-- Lemma 1: the finite Witten-index sum is exactly the powerset parity sum. -/
theorem finiteWittenIndexSum_eq_powerset_sum
    (P : FermionicPrimeRegister) :
    finiteWittenIndexSum P =
      ∑ S ∈ P.primes.powerset, (-1 : ℤ) ^ S.card := by
  rfl

/-- Lemma 2: a nonempty finite fermion register has a cancelling parity powerset sum. -/
theorem powerset_parity_sum_cancel_of_nonempty
    (P : FermionicPrimeRegister)
    (hP : P.primes.Nonempty) :
    (∑ S ∈ P.primes.powerset, (-1 : ℤ) ^ S.card) = 0 := by
  exact finiteBooleanWittenIndex_cancel P hP

/-- Lemma 3: therefore the named finite Witten-index sum vanishes. -/
theorem finiteWittenIndexSum_cancel_of_nonempty
    (P : FermionicPrimeRegister)
    (hP : P.primes.Nonempty) :
    finiteWittenIndexSum P = 0 := by
  rw [finiteWittenIndexSum_eq_powerset_sum]
  exact powerset_parity_sum_cancel_of_nonempty P hP

/-- Theorem: finite SUSY vacuum cancellation is a theorem of finite fermion parity. -/
theorem finiteSUSYVacuum_wittenIndexCancellation
    (P : FermionicPrimeRegister)
    (hP : P.primes.Nonempty) :
    finiteWittenIndexSum P = 0 ∧
      (∑ S ∈ P.primes.powerset, (-1 : ℤ) ^ S.card) = 0 := by
  exact ⟨finiteWittenIndexSum_cancel_of_nonempty P hP,
    powerset_parity_sum_cancel_of_nonempty P hP⟩

end PrimeSUSYVacuum
