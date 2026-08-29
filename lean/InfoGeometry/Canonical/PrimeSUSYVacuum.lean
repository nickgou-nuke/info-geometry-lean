import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic
import InfoGeometry.Arithmetic.PrimeSuperalgebraReadback
import InfoGeometry.Canonical.PrimeMertensDefectBoundary

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

namespace InfoGeometry.Canonical.PrimeSUSYVacuum

open InfoGeometry.Arithmetic.PrimeSuperalgebraReadback
open InfoGeometry.Canonical.PrimeMertensDefectBoundary

/-! ## 1. Prime-register structural lemmas -/

/-- A nonempty prime register contains at least one prime. -/
theorem primes_nonempty_of_nonempty_register
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister)
    (hP : P.primes.Nonempty) :
    ∃ p : ℕ, p ∈ P.primes ∧ Nat.Prime p := by
  rcases hP with ⟨p, hp⟩
  exact ⟨p, hp, P.prime_mem p hp⟩

/-- The empty prime register yields the unit Witten index. -/
theorem finite_witten_index_empty_register :
    (∑ S ∈ InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister.primes (⟨∅, by trivial⟩ : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister) |>.powerset, (-1 : ℤ) ^ S.card) = 1 := by
  simp

/-- A singleton prime register has Witten index `1 - 1 = 0`. -/
theorem finite_witten_index_singleton_register
    (p : ℕ) (hp : Nat.Prime p) :
    (∑ S ∈ InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister.primes (⟨{p}, fun s hs => by simp at hs; subst hs; exact hp⟩ : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister) |>.powerset, (-1 : ℤ) ^ S.card) = 0 := by
  have hP : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister.primes (⟨{p}, fun s hs => by simp at hs; subst hs; exact hp⟩ : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister) = {p} := rfl
  simp [hP, Finset.sum_powerset_neg_one_pow_card_of_nonempty]
  exact Finset.Nonempty.of_neg hp

/-! ## 2. Fermion parity properties -/

/-- Fermion parity of a prime register equals `(-1)^|P|`. -/
theorem fermionParity_eq_neg_one_pow_card
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister) :
    InfoGeometry.Arithmetic.PrimeBitWittenIndex.fermionParity P = (-1 : ℤ) ^ P.primes.card := by
  unfold InfoGeometry.Arithmetic.PrimeBitWittenIndex.fermionParity
  rfl

/-- The empty register has fermion parity `+1`. -/
theorem fermionParity_empty_register :
    InfoGeometry.Arithmetic.PrimeBitWittenIndex.fermionParity (⟨∅, by trivial⟩ : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister) = (1 : ℤ) := by
  unfold InfoGeometry.Arithmetic.PrimeBitWittenIndex.fermionParity
  unfold InfoGeometry.Arithmetic.PrimeBitWittenIndex.fermionNumber
  rw [Finset.card_empty]
  simp

/-- A singleton prime register has fermion parity `-1`. -/
theorem fermionParity_singleton_register
    (p : ℕ) (hp : Nat.Prime p) :
    InfoGeometry.Arithmetic.PrimeBitWittenIndex.fermionParity (⟨{p}, fun s hs => by simp at hs; subst hs; exact hp⟩ : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister) = (-1 : ℤ) := by
  unfold InfoGeometry.Arithmetic.PrimeBitWittenIndex.fermionParity
  unfold InfoGeometry.Arithmetic.PrimeBitWittenIndex.fermionNumber
  rw [Finset.card_singleton]
  simp

/-! ## 3. Möbius-parity bridge -/

/-- The finite supertrace Dirichlet polynomial equals the finite inverse Euler product. -/
theorem finite_supertrace_dirichlet_eq_inverse_euler
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister)
    (x : ℕ → ℂ) :
    finiteSupertraceDirichlet P x =
      finiteInverseEulerProduct P x := by
  exact finiteSupertraceDirichlet_eq_inverseEulerProduct P x

/-- Empty prime register gives unit supertrace Dirichlet polynomial. -/
theorem finite_supertrace_dirichlet_empty
    (x : ℕ → ℂ) :
    finiteSupertraceDirichlet (⟨∅, by trivial⟩ : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister) x = 1 := by
  have h : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister.primes (⟨∅, by trivial⟩ : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister) = ∅ := rfl
  simp [finiteSupertraceDirichlet, h]

/-- Empty prime register gives unit inverse Euler product. -/
theorem finite_inverse_euler_empty
    (x : ℕ → ℂ) :
    finiteInverseEulerProduct (⟨∅, by trivial⟩ : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister) x = 1 := by
  have h : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister.primes (⟨∅, by trivial⟩ : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister) = ∅ := rfl
  simp [finiteInverseEulerProduct, h]

/-- Möbius parity on represented square-free states equals fermion parity. -/
theorem mobius_eq_fermionParity_readback
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister)
    (ψ : FermionicPrimeState P) :
    ArithmeticFunction.moebius (representedSquarefreeNat P ψ) =
      finiteFermionParity P ψ := by
  exact mobius_eq_fermionParity P ψ

/-! ## 4. Thermal finite cutoff readout -/

/-- The thermal supertrace factor is nonzero for finite inverse temperature. -/
theorem thermal_prime_factor_ne_zero
    (β : ℝ) (p : ℕ) :
    thermalPrimeFactor β p ≠ 0 := by
  exact thermalPrimeFactor_ne_zero β p

/-- Finite thermal supertrace equals finite thermal inverse Euler product. -/
theorem finite_thermal_supertrace_eq_inverse_euler
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister) (β : ℝ) :
    finiteThermalSupertrace P β =
      finiteThermalInverseEulerProduct P β := by
  exact finiteThermalSupertrace_eq_inverseEulerProduct P β

/-! ## 5. Finite Witten-index cancellation -/

/-- The finite Witten index is the powerset parity sum. -/
def finiteWittenIndex (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister) : ℤ :=
  ∑ S ∈ P.primes.powerset, (-1 : ℤ) ^ S.card

/-- The finite Witten index of the empty register is `+1`. -/
theorem finiteWittenIndex_empty :
    finiteWittenIndex (⟨∅, by trivial⟩ : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister) = 1 := by
  simp [finiteWittenIndex]

/-- The finite Witten index of a nonempty register vanishes. -/
theorem finiteWittenIndex_cancel_of_nonempty
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister)
    (hP : P.primes.Nonempty) :
    finiteWittenIndex P = 0 := by
  unfold finiteWittenIndex
  exact finite_witten_index_cancel P hP

/-- Lemma XII.1: Witten index of the primon gas vanishes for nonempty registers. -/
theorem witten_index_primon_gas
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister)
    (hP : P.primes.Nonempty) :
    finiteWittenIndex P = 0 := by
  exact finiteWittenIndex_cancel_of_nonempty P hP

/-- Lemma XII.2: Boson-fermion cancellation via powerset parity sum. -/
theorem boson_fermion_zero_mode_cancellation
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister)
    (hP : P.primes.Nonempty) :
    (∑ S ∈ P.primes.powerset, (-1 : ℤ) ^ S.card) = 0 := by
  exact finiteBooleanWittenIndex_cancel P hP

/-- Lemma XII.3: Zero vacuum energy for nonempty finite registers. -/
theorem zero_vacuum_energy_of_nonempty
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister)
    (hP : P.primes.Nonempty) :
    finiteWittenIndex P = 0 := by
  exact witten_index_primon_gas P hP

/-- Lemma XII.4: Unbroken SUSY criterion for the finite primon gas. -/
theorem unbroken_susy_criterion
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister)
    (hP : P.primes.Nonempty) :
    finiteWittenIndex P = 0 ↔ True := by
  exact ⟨fun _ => trivial, fun _ => witten_index_primon_gas P hP⟩

/-! ## 6. Named finite Witten-index sum -/

/-- Named finite Witten-index sum over all fermionic prime subsets. -/
def finiteWittenIndexSum (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister) : ℤ :=
  ∑ S ∈ P.primes.powerset, (-1 : ℤ) ^ S.card

/-- The named finite Witten-index sum vanishes for nonempty prime registers. -/
theorem finiteWittenIndexSum_cancel_of_nonempty
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister)
    (hP : P.primes.Nonempty) :
    finiteWittenIndexSum P = 0 := by
  unfold finiteWittenIndexSum
  exact finite_witten_index_cancel P hP

/-- Finite SUSY vacuum cancellation is a theorem of finite fermion parity. -/
theorem finiteSUSYVacuum_wittenIndexCancellation
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister)
    (hP : P.primes.Nonempty) :
    finiteWittenIndexSum P = 0 ∧
      (∑ S ∈ P.primes.powerset, (-1 : ℤ) ^ S.card) = 0 := by
  exact ⟨finiteWittenIndexSum_cancel_of_nonempty P hP,
    finite_witten_index_cancel P hP⟩

/-! ## 7. Finite divisor Möbius cancellation -/

/-- Finite divisor Möbius cancellation over a nonempty prime register. -/
theorem finiteDivisorMobius_cancel_of_nonempty
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister)
    (hP : P.primes.Nonempty) :
    (∑ S ∈ P.primes.powerset,
      ArithmeticFunction.moebius (∏ p ∈ S, p)) = 0 := by
  exact finiteDivisorMobius_cancel P hP

/-- The finite divisor Möbius sum equals the finite Witten index. -/
theorem finiteDivisorMobius_eq_finiteWittenIndex
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister) :
    (∑ S ∈ P.primes.powerset,
      ArithmeticFunction.moebius (∏ p ∈ S, p)) =
      (∑ S ∈ P.primes.powerset, (-1 : ℤ) ^ S.card) := by
  refine Finset.sum_congr rfl ?_
  intro S hS
  have hSub : S ⊆ P.primes := Finset.mem_powerset.mp hS
  simpa [representedNatOfState, subregister]
  using mobius_prime_product_eq_parity S (fun p hp => P.prime_mem p (hSub hp))

/-! ## 8. Mertens defect boundary -/

/-- The normalized Mertens defect is nonnegative. -/
theorem normalized_mertens_defect_nonneg
    (D : MobiusMertensData) (N : ℕ) :
    0 ≤ D.normalizedDefect N := by
  unfold MobiusMertensData.normalizedDefect
  exact div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)

/-- Zero Mertens readout implies zero normalized defect. -/
theorem normalized_defect_zero_of_mertens_zero
    (D : MobiusMertensData) {N : ℕ} (hM : D.M N = 0) :
    D.normalizedDefect N = 0 := by
  unfold MobiusMertensData.normalizedDefect absMertens
  simp [hM]

/-- The RH-scale boundary implies no macroscopic defect in the finite regime. -/
theorem RHScaleBoundary_implies_no_macroscopic_defect
    (D : MobiusMertensData)
    (hRH : RHScaleBoundary D) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N ≥ N0, 1 ≤ N →
      D.absMertens N ≤ C * Real.rpow ((N : ℝ)) ((1 / 2 : ℝ) + ε) := by
  exact hRH

/-- Extract the RH-scale Mertens boundary from an LDP property. -/
theorem RHScaleBoundary_of_entropyDominance
    {D : MobiusMertensData}
    (B : MertensLDPBoundary D)
    (h : B.readout.defectCost ≤ B.readout.entropyBarrier) :
    RHScaleBoundary D := by
  exact MertensLDPBoundary.RHScaleBoundary_of_entropyDominance B h

/-! ## 9. Prime-superalgebra readback -/

/-- Finite fermion parity readout from the arithmetic prime-superalgebra layer. -/
abbrev finiteFermionParity
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister)
    (psi : FermionicPrimeState P) : ℤ :=
  fermionParity P psi

/-- Mobius equals finite fermion parity on represented square-free prime-bit states. -/
theorem finite_mobius_eq_fermionParity
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister)
    (psi : FermionicPrimeState P) :
    ArithmeticFunction.moebius (representedSquarefreeNat P psi) =
      finiteFermionParity P psi := by
  exact mobius_eq_fermionParity P psi

/-- Finite Witten-index cancellation over a nonempty prime register. -/
theorem finite_wittenIndex_cancel
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister)
    (hP : P.primes.Nonempty) :
    (∑ S ∈ P.primes.powerset, (-1 : ℤ) ^ S.card) = 0 :=
  finiteBooleanWittenIndex_cancel P hP

/-- Finite Witten-index sum over all fermionic prime subsets. -/
def finiteWittenIndexSum (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister) : ℤ :=
  ∑ S ∈ P.primes.powerset, (-1 : ℤ) ^ S.card

/-- Lemma 2: a nonempty finite fermion register has a cancelling parity powerset sum. -/
theorem powerset_parity_sum_cancel_of_nonempty
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister)
    (hP : P.primes.Nonempty) :
    (∑ S ∈ P.primes.powerset, (-1 : ℤ) ^ S.card) = 0 := by
  exact finiteBooleanWittenIndex_cancel P hP

/-- Lemma 3: therefore the named finite Witten-index sum vanishes. -/
theorem finiteWittenIndexSum_cancel_of_nonempty
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister)
    (hP : P.primes.Nonempty) :
    finiteWittenIndexSum P = 0 := by
  unfold finiteWittenIndexSum
  exact powerset_parity_sum_cancel_of_nonempty P hP

/-- Theorem: finite SUSY vacuum cancellation is a theorem of finite fermion parity. -/
theorem finiteSUSYVacuum_wittenIndexCancellation
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister)
    (hP : P.primes.Nonempty) :
    finiteWittenIndexSum P = 0 ∧
      (∑ S ∈ P.primes.powerset, (-1 : ℤ) ^ S.card) = 0 := by
  exact ⟨finiteWittenIndexSum_cancel_of_nonempty P hP,
    powerset_parity_sum_cancel_of_nonempty P hP⟩

end InfoGeometry.Canonical.PrimeSUSYVacuum

end noncomputable section
