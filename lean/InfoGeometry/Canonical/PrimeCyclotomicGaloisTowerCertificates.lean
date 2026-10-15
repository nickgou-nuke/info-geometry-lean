import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

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
deriving DecidableEq, Repr

instance : Fintype PrimeStage where
  elems := {.p2, .p3, .p5, .p7, .p11, .p13}
  complete := by
    intro stage
    cases stage <;> simp

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
  cases a <;> cases b <;> simp_all [rank, conductor]

/-- Every stage contracts to the fixed terminal conductor `30030`. -/
theorem conductor_dvd_terminal (s : PrimeStage) :
    conductor s ∣ conductor .p13 := by
  apply conductor_dvd_of_rank_le
  cases s <;> norm_num [rank]

/-- The first cyclotomic degree is Euler's totient of the first conductor. -/
theorem totient_conductor_p2 : Nat.totient (conductor .p2) = galoisDegree .p2 := by
  norm_num [conductor, galoisDegree, Nat.totient_prime Nat.prime_two]

/-- The next degree follows from multiplicativity of Euler's totient on coprime factors. -/
theorem totient_conductor_p3 : Nat.totient (conductor .p3) = galoisDegree .p3 := by
  rw [conductor_successor_3,
    Nat.totient_mul (by norm_num [Nat.Coprime, conductor, stagePrime])]
  norm_num [conductor, stagePrime, galoisDegree, Nat.totient_prime]

theorem totient_conductor_p5 : Nat.totient (conductor .p5) = galoisDegree .p5 := by
  rw [conductor_successor_5,
    Nat.totient_mul (by norm_num [Nat.Coprime, conductor, stagePrime]),
    totient_conductor_p3]
  norm_num [stagePrime, galoisDegree, Nat.totient_prime]

theorem totient_conductor_p7 : Nat.totient (conductor .p7) = galoisDegree .p7 := by
  rw [conductor_successor_7,
    Nat.totient_mul (by norm_num [Nat.Coprime, conductor, stagePrime]),
    totient_conductor_p5]
  norm_num [stagePrime, galoisDegree, Nat.totient_prime]

theorem totient_conductor_p11 : Nat.totient (conductor .p11) = galoisDegree .p11 := by
  rw [conductor_successor_11,
    Nat.totient_mul (by norm_num [Nat.Coprime, conductor, stagePrime]),
    totient_conductor_p7]
  norm_num [stagePrime, galoisDegree, Nat.totient_prime]

theorem totient_conductor_p13 : Nat.totient (conductor .p13) = galoisDegree .p13 := by
  rw [conductor_successor_13,
    Nat.totient_mul (by norm_num [Nat.Coprime, conductor, stagePrime]),
    totient_conductor_p11]
  norm_num [stagePrime, galoisDegree, Nat.totient_prime]

/-- The exact Euler-totient/Galois-degree ledger, proved using native
multiplicativity rather than evaluating the largest totient by reduction. -/
theorem totient_conductor (s : PrimeStage) :
    Nat.totient (conductor s) = galoisDegree s := by
  cases s with
  | p2 => exact totient_conductor_p2
  | p3 => exact totient_conductor_p3
  | p5 => exact totient_conductor_p5
  | p7 => exact totient_conductor_p7
  | p11 => exact totient_conductor_p11
  | p13 => exact totient_conductor_p13

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
