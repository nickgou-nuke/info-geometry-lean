import Mathlib

/-!
# Six-prime cyclotomic Galois-tower certificates

This file is the kernel-side certificate layer for the finite prime corridor
`2, 3, 5, 7, 11, 13`.

The individual prime conductors do not form an inclusion tower.  The directed
cyclotomic conductors are the cumulative primorials

`2 | 6 | 30 | 210 | 2310 | 30030`.

External GAP/Sage computations may discover/check these values, but no CAS
output is trusted here.  Lean independently proves primality, the directed
divisibility relation, the terminal normal form, and the Euler-totient degree
ledger used by the cyclotomic Galois groups `(Z/NZ)ˣ`.

This owner intentionally stops before asserting field inclusions between
`CyclotomicField N ℚ`; that bridge requires the corresponding native Mathlib
cyclotomic embedding API.
-/

namespace InfoGeometry.Canonical.PrimeCyclotomicGaloisTowerCertificates

/-- The fixed six stages of the prime corridor. -/
inductive PrimeStage where
  | p2
  | p3
  | p5
  | p7
  | p11
  | p13
deriving DecidableEq, Repr, Fintype

/-- The prime introduced at a stage. -/
def stagePrime : PrimeStage → ℕ
  | .p2 => 2
  | .p3 => 3
  | .p5 => 5
  | .p7 => 7
  | .p11 => 11
  | .p13 => 13

/-- Cumulative primorial conductor at each stage. -/
def conductor : PrimeStage → ℕ
  | .p2 => 2
  | .p3 => 6
  | .p5 => 30
  | .p7 => 210
  | .p11 => 2310
  | .p13 => 30030

/-- Expected cyclotomic degree `φ(N)` at each primorial conductor. -/
def galoisDegree : PrimeStage → ℕ
  | .p2 => 1
  | .p3 => 2
  | .p5 => 8
  | .p7 => 48
  | .p11 => 480
  | .p13 => 5760

/-- Rank used only to orient the fixed finite directed system. -/
def rank : PrimeStage → ℕ
  | .p2 => 0
  | .p3 => 1
  | .p5 => 2
  | .p7 => 3
  | .p11 => 4
  | .p13 => 5

/-- Every listed stage really introduces a prime. -/
theorem stagePrime_prime (s : PrimeStage) : Nat.Prime (stagePrime s) := by
  cases s <;> norm_num [stagePrime]

/-- The cumulative conductors are exactly the successive prime products. -/
theorem conductor_successor_3 : conductor .p3 = conductor .p2 * stagePrime .p3 := by
  norm_num [conductor, stagePrime]

theorem conductor_successor_5 : conductor .p5 = conductor .p3 * stagePrime .p5 := by
  norm_num [conductor, stagePrime]

theorem conductor_successor_7 : conductor .p7 = conductor .p5 * stagePrime .p7 := by
  norm_num [conductor, stagePrime]

theorem conductor_successor_11 : conductor .p11 = conductor .p7 * stagePrime .p11 := by
  norm_num [conductor, stagePrime]

theorem conductor_successor_13 : conductor .p13 = conductor .p11 * stagePrime .p13 := by
  norm_num [conductor, stagePrime]

/-- Directed divisibility is completely classified by the six stage ranks.
This is the finite O(1) normal-form theorem consumed by later tower maps. -/
theorem conductor_dvd_of_rank_le
    {a b : PrimeStage} (h : rank a ≤ rank b) : conductor a ∣ conductor b := by
  cases a <;> cases b <;> norm_num [rank, conductor] at h ⊢

/-- Every stage contracts to the fixed terminal conductor `30030`. -/
theorem conductor_dvd_terminal (s : PrimeStage) :
    conductor s ∣ conductor .p13 := by
  apply conductor_dvd_of_rank_le
  cases s <;> norm_num [rank]

/-- The exact Euler-totient/Galois-degree ledger.  `native_decide` merely
recomputes these closed arithmetic propositions inside Lean; it does not
import a CAS theorem. -/
theorem totient_conductor (s : PrimeStage) :
    Nat.totient (conductor s) = galoisDegree s := by
  cases s <;> native_decide

/-- The final six-prime primorial conductor. -/
theorem terminal_conductor : conductor .p13 = 30030 := rfl

/-- The final cyclotomic degree is `φ(30030)=5760`. -/
theorem terminal_galoisDegree : galoisDegree .p13 = 5760 := rfl

/-- Closed readout of the six prime stages. -/
theorem stagePrime_values :
    (stagePrime .p2, stagePrime .p3, stagePrime .p5,
      stagePrime .p7, stagePrime .p11, stagePrime .p13) =
      (2, 3, 5, 7, 11, 13) := rfl

/-- Closed readout of the directed primorial conductors. -/
theorem conductor_values :
    (conductor .p2, conductor .p3, conductor .p5,
      conductor .p7, conductor .p11, conductor .p13) =
      (2, 6, 30, 210, 2310, 30030) := rfl

/-- Closed readout of the corresponding unit-group/cyclotomic degrees. -/
theorem galoisDegree_values :
    (galoisDegree .p2, galoisDegree .p3, galoisDegree .p5,
      galoisDegree .p7, galoisDegree .p11, galoisDegree .p13) =
      (1, 2, 8, 48, 480, 5760) := rfl

end InfoGeometry.Canonical.PrimeCyclotomicGaloisTowerCertificates
