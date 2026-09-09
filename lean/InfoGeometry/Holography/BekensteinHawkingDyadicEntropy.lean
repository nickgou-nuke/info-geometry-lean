import InfoGeometry.Holography.AdSCFTCuntzBridge
import InfoGeometry.Thermodynamics.FiniteGibbsRelative
import InfoGeometry.Arithmetic.PrimeBitWittenIndex

/-!
# Bekenstein--Hawking dyadic entropy bridge

This file is a theorem-safe scalar readout connecting two already verified
finite surfaces:

* the Bekenstein--Hawking area law, represented only by the scalar formula
  `S = A / (4G)`;
* the two-branch Cuntz/Gibbs finite Massieu readout, whose symmetric value is
  `log 2` in `FiniteGibbsRelative`.

It does not prove a black-hole information theorem, a full AdS/CFT theorem, or a
classification of KMS states.  It records the exact finite calibration identities
that are available to Lean.

#### BUCKET 1: CLOSED FINITE THEOREMS

* `twoBranch_massieu_eq_dyadicEntropyQuantum`
* `dyadicEntropyBits_eq_nat_mul_twoBranch_massieu`
* `dyadicEntropyQuantum_pos`
* `dyadicEntropyBits_nonneg`
* `finiteWittenCancel_and_bekensteinHawkingDyadic`
* `finiteWittenCancel_and_bekensteinHawkingDyadicBits`
* `primeBitState_mobiusParity_wittenCancel_bhDyadic`
* `primeBitState_mobiusParity_wittenCancel_bhDyadicBits`

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES

* `bekensteinHawkingEntropy_eq_dyadicEntropyQuantum`
* `bekensteinHawkingEntropy_eq_twoBranch_massieu`
* `bekensteinHawkingEntropy_eq_dyadicEntropyBits`
* `bekensteinHawkingEntropy_eq_nat_mul_twoBranch_massieu`

#### BUCKET 3: OPEN CLOSURE DEBT

* Constructing a continuum horizon area measure from the Cuntz/UHF boundary.
* Proving any physical `O(5,5)` compactification, Witten-index thermodynamic
  limit, AdS/CFT, or black-hole information theorem from these finite scalar
  identities.
-/

noncomputable section

namespace InfoGeometry.Holography.BekensteinHawkingDyadicEntropy

open InfoGeometry.Thermodynamics.FiniteGibbsRelative
open InfoGeometry.Arithmetic.PrimeBitWittenIndex

/-- Scalar Bekenstein--Hawking entropy readout `S = A / (4G)`. -/
def bekensteinHawkingEntropy (area G : ℝ) : ℝ :=
  area / (4 * G)

/-- The dyadic one-bit entropy quantum. -/
def dyadicEntropyQuantum : ℝ :=
  Real.log 2

/-- The two-branch symmetric finite Gibbs/Massieu readout is the dyadic entropy quantum. -/
theorem twoBranch_massieu_eq_dyadicEntropyQuantum :
    massieuPotential (ι := Fin 2) (fun _ => (0 : ℝ)) = dyadicEntropyQuantum := by
  exact massieuPotential_zero_fin_two_eq_log_two

/--
If the horizon area is calibrated as `4G log 2`, the scalar
Bekenstein--Hawking entropy is exactly the dyadic entropy quantum.
-/
theorem bekensteinHawkingEntropy_eq_dyadicEntropyQuantum
    {area G : ℝ} (hG : G ≠ 0)
    (harea : area = 4 * G * dyadicEntropyQuantum) :
    bekensteinHawkingEntropy area G = dyadicEntropyQuantum := by
  unfold bekensteinHawkingEntropy
  rw [harea]
  field_simp [hG]

/--
Equivalently, under the same area calibration, the Bekenstein--Hawking scalar
readout matches the symmetric two-branch finite Gibbs/Massieu readout.
-/
theorem bekensteinHawkingEntropy_eq_twoBranch_massieu
    {area G : ℝ} (hG : G ≠ 0)
    (harea : area = 4 * G * dyadicEntropyQuantum) :
    bekensteinHawkingEntropy area G =
      massieuPotential (ι := Fin 2) (fun _ => (0 : ℝ)) := by
  rw [bekensteinHawkingEntropy_eq_dyadicEntropyQuantum hG harea,
    twoBranch_massieu_eq_dyadicEntropyQuantum]

/-- `n` dyadic branch bits have scalar entropy `n * log 2`. -/
def dyadicEntropyBits (n : ℕ) : ℝ :=
  n * dyadicEntropyQuantum

/-- The `n`-bit dyadic entropy is `n` copies of the two-branch Massieu readout. -/
theorem dyadicEntropyBits_eq_nat_mul_twoBranch_massieu (n : ℕ) :
    dyadicEntropyBits n =
      n * massieuPotential (ι := Fin 2) (fun _ => (0 : ℝ)) := by
  rw [twoBranch_massieu_eq_dyadicEntropyQuantum]
  rfl

/--
The area calibration `A_n = 4G n log 2` gives the `n`-bit dyadic entropy.
-/
theorem bekensteinHawkingEntropy_eq_dyadicEntropyBits
    {area G : ℝ} (n : ℕ) (hG : G ≠ 0)
    (harea : area = 4 * G * dyadicEntropyBits n) :
    bekensteinHawkingEntropy area G = dyadicEntropyBits n := by
  unfold bekensteinHawkingEntropy
  rw [harea]
  field_simp [hG]

/--
Under the `n`-bit area calibration, the Bekenstein--Hawking scalar readout is
`n` copies of the symmetric two-branch finite Gibbs/Massieu readout.
-/
theorem bekensteinHawkingEntropy_eq_nat_mul_twoBranch_massieu
    {area G : ℝ} (n : ℕ) (hG : G ≠ 0)
    (harea : area = 4 * G * dyadicEntropyBits n) :
    bekensteinHawkingEntropy area G =
      n * massieuPotential (ι := Fin 2) (fun _ => (0 : ℝ)) := by
  rw [bekensteinHawkingEntropy_eq_dyadicEntropyBits n hG harea,
    dyadicEntropyBits_eq_nat_mul_twoBranch_massieu n]

/-- Positivity of the one-bit dyadic entropy quantum. -/
theorem dyadicEntropyQuantum_pos : 0 < dyadicEntropyQuantum := by
  unfold dyadicEntropyQuantum
  exact Real.log_pos (by norm_num : (1 : ℝ) < 2)

/-- Nonnegativity of the `n`-bit dyadic entropy readout. -/
theorem dyadicEntropyBits_nonneg (n : ℕ) :
    0 ≤ dyadicEntropyBits n := by
  unfold dyadicEntropyBits
  exact mul_nonneg (Nat.cast_nonneg n) (le_of_lt dyadicEntropyQuantum_pos)

/--
Finite Witten-cancelled dyadic horizon certificate.

For a nonempty finite prime register, the owned Möbius/Witten supertrace cancels,
and under the scalar area calibration `A = 4G log 2`, the Bekenstein--Hawking
readout matches the two-branch dyadic Massieu entropy.  This is a finite
synchronized certificate, not a thermodynamic-limit theorem.
-/
theorem finiteWittenCancel_and_bekensteinHawkingDyadic
    (P : PrimeRegister) (hP : P.primes.Nonempty)
    {area G : ℝ} (hG : G ≠ 0)
    (harea : area = 4 * G * dyadicEntropyQuantum) :
    (∑ S ∈ P.primes.powerset, (-1 : ℤ) ^ S.card) = 0 ∧
      bekensteinHawkingEntropy area G =
        massieuPotential (ι := Fin 2) (fun _ => (0 : ℝ)) := by
  exact ⟨finite_witten_index_cancel P hP,
    bekensteinHawkingEntropy_eq_twoBranch_massieu hG harea⟩

/--
Finite Witten cancellation synchronized with an `n`-bit dyadic horizon
calibration.  The Witten cancellation is finite arithmetic; the
Bekenstein--Hawking equality uses only the explicit scalar area premise.
-/
theorem finiteWittenCancel_and_bekensteinHawkingDyadicBits
    (P : PrimeRegister) (hP : P.primes.Nonempty)
    {area G : ℝ} (n : ℕ) (hG : G ≠ 0)
    (harea : area = 4 * G * dyadicEntropyBits n) :
    (∑ S ∈ P.primes.powerset, (-1 : ℤ) ^ S.card) = 0 ∧
      bekensteinHawkingEntropy area G = dyadicEntropyBits n := by
  exact ⟨finite_witten_index_cancel P hP,
    bekensteinHawkingEntropy_eq_dyadicEntropyBits n hG harea⟩

/--
State-level Möbius/Fermion parity plus finite Witten cancellation and dyadic
Bekenstein--Hawking calibration, bundled as one finite certificate.
-/
theorem primeBitState_mobiusParity_wittenCancel_bhDyadic
    (P : PrimeRegister) (hP : P.primes.Nonempty) (ψ : PrimeBitState P)
    {area G : ℝ} (hG : G ≠ 0)
    (harea : area = 4 * G * dyadicEntropyQuantum) :
    ArithmeticFunction.moebius (representedNatOfState P ψ) = fermionParityOfState P ψ ∧
    (∑ S ∈ P.primes.powerset, (-1 : ℤ) ^ S.card) = 0 ∧
      bekensteinHawkingEntropy area G =
        massieuPotential (ι := Fin 2) (fun _ => (0 : ℝ)) := by
  exact ⟨mobius_representedNatOfState_eq_fermionParity P ψ,
    finite_witten_index_cancel P hP,
    bekensteinHawkingEntropy_eq_twoBranch_massieu hG harea⟩

/--
State-level Möbius/Fermion parity plus finite Witten cancellation and an
`n`-bit dyadic Bekenstein--Hawking calibration.
-/
theorem primeBitState_mobiusParity_wittenCancel_bhDyadicBits
    (P : PrimeRegister) (hP : P.primes.Nonempty) (ψ : PrimeBitState P)
    {area G : ℝ} (n : ℕ) (hG : G ≠ 0)
    (harea : area = 4 * G * dyadicEntropyBits n) :
    ArithmeticFunction.moebius (representedNatOfState P ψ) = fermionParityOfState P ψ ∧
    (∑ S ∈ P.primes.powerset, (-1 : ℤ) ^ S.card) = 0 ∧
      bekensteinHawkingEntropy area G = dyadicEntropyBits n := by
  exact ⟨mobius_representedNatOfState_eq_fermionParity P ψ,
    finite_witten_index_cancel P hP,
    bekensteinHawkingEntropy_eq_dyadicEntropyBits n hG harea⟩

end InfoGeometry.Holography.BekensteinHawkingDyadicEntropy

end noncomputable section
