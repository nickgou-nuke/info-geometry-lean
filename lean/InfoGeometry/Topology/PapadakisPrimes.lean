import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Papadakis prime encodings

Theorem-safe finite arithmetic core for Ioannis Papadakis,
“On the Discrete and Continuous Harmonic Encoding of Primes”
(`Mathematics and Computer Science` 11(3), 45-56, 2026,
DOI `10.11648/j.mcs.20261103.11`).

#### BUCKET 1: CLOSED FINITE THEOREMS
* `prime_of_no_small_prime_divisor_and_sq_bound`: the elementary least-prime
  factor certificate behind the paper's Complete HPF certification bound.
* `hpf_certification_prime`: the same certificate stated in HPF notation.
* `goldbachPairingValue_example_twenty`: the paper's `L(C_10)=273` example.
* `goldbachPairingRecover_example_twenty`: exact finite recovery of the
  `20 = 3+17 = 7+13` Goldbach state from the encoded fields.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
* `hpf_certification_prime` depends on the explicit HPF divisor-exclusion
  premise.  A separate file may prove that premise from concrete exponent
  vectors for a given HPF support.

#### BUCKET 3: OPEN CLOSURE DEBT
* Full formalization of Complete HPF exponent vectors over the first `k`
  primes and derivation of the divisor-exclusion premise from disjoint support.
* Injectivity of the paper's global Goldbach product map from canonical sorted
  prime-factor recovery.
* Analytic formalization of the harmonic kernels `G_P`, `GI₂`, `J`, `J_P`,
  their integer-limit behavior, and the claimed continuous prime-counting
  readout.
-/

namespace InfoGeometry.Topology.PapadakisPrimes

/-! ## Hybrid Prime Factorization certificate -/

/-- Additive or subtractive HPF branch. -/
inductive HPFBranch where
  | add
  | sub
  deriving DecidableEq, Repr

/-- Absolute difference on natural numbers. -/
def natAbsDiff (A B : ℕ) : ℕ :=
  if B ≤ A then A - B else B - A

/-- HPF evaluated from its two multiplicative components and a branch. -/
def hpfValue (branch : HPFBranch) (A B : ℕ) : ℕ :=
  match branch with
  | HPFBranch.add => A + B
  | HPFBranch.sub => natAbsDiff A B

/--
The elementary prime certificate beneath the paper's Complete HPF theorem.

If `n > 1`, every prime divisor of `n` is at least `pNext`, and
`n < pNext^2`, then `n` is prime.  In HPF applications, the disjoint complete
support supplies the prime-divisor exclusion premise.
-/
theorem prime_of_no_small_prime_divisor_and_sq_bound
    {n pNext : ℕ}
    (hn : 2 ≤ n)
    (hdiv : ∀ p : ℕ, Nat.Prime p → p ∣ n → pNext ≤ p)
    (hbound : n < pNext ^ 2) :
    Nat.Prime n := by
  by_contra hnot
  have hpos : 0 < n := lt_of_lt_of_le (by decide) hn
  have hn_ne_one : n ≠ 1 := by omega
  have hpmin : Nat.Prime n.minFac := Nat.minFac_prime hn_ne_one
  have hmin_dvd : n.minFac ∣ n := Nat.minFac_dvd n
  have hpNext_le : pNext ≤ n.minFac := hdiv n.minFac hpmin hmin_dvd
  have hsq_min : n.minFac ^ 2 ≤ n := Nat.minFac_sq_le_self hpos hnot
  have hsq_next : pNext ^ 2 ≤ n.minFac ^ 2 := by
    nlinarith [hpNext_le]
  have : pNext ^ 2 ≤ n := le_trans hsq_next hsq_min
  omega

/--
HPF-shaped certification theorem.

`hExclude` is the theorem-level form of the paper's Complete HPF support
argument: every prime divisor of the evaluated HPF output lies beyond the
canonical base.
-/
theorem hpf_certification_prime
    {A B pNext : ℕ} {branch : HPFBranch}
    (hn : 2 ≤ hpfValue branch A B)
    (hExclude :
      ∀ p : ℕ, Nat.Prime p → p ∣ hpfValue branch A B → pNext ≤ p)
    (hbound : hpfValue branch A B < pNext ^ 2) :
    Nat.Prime (hpfValue branch A B) :=
  prime_of_no_small_prime_divisor_and_sq_bound hn hExclude hbound

/-! ## Goldbach product encoding -/

/--
Finite data for the paper's Goldbach pairing map.

The `smalls` list stores the smaller components before the anchor pair; the
anchor pair is `(anchorSmall, anchorLarge)`.  The encoded scalar is
`anchorLarge * (anchorSmall :: smalls).prod`, matching the paper's convention
that the final large component is appended once as the structural anchor.
-/
structure GoldbachPairingData where
  smalls : List ℕ
  anchorSmall : ℕ
  anchorLarge : ℕ
  deriving Repr

namespace GoldbachPairingData

/-- Multiplicative scalar encoding `L(C_N)`. -/
def value (G : GoldbachPairingData) : ℕ :=
  G.anchorLarge * (G.anchorSmall :: G.smalls).prod

/-- Recovered even target from the anchor pair. -/
def targetEven (G : GoldbachPairingData) : ℕ :=
  G.anchorSmall + G.anchorLarge

/-- Recovered Goldbach pairs from the encoded fields. -/
def recoveredPairs (G : GoldbachPairingData) : List (ℕ × ℕ) :=
  G.smalls.map (fun x => (x, G.targetEven - x)) ++ [(G.anchorSmall, G.anchorLarge)]

end GoldbachPairingData

/-- The paper's example `20 = 3+17 = 7+13`. -/
def C10GoldbachState : GoldbachPairingData where
  smalls := [3]
  anchorSmall := 7
  anchorLarge := 13

/-- The paper's scalar encoding example: `L(C_10)=3·7·13=273`. -/
theorem goldbachPairingValue_example_twenty :
    C10GoldbachState.value = 273 := by
  norm_num [C10GoldbachState, GoldbachPairingData.value]

/-- Recovery of the ordered Goldbach pairs for `2N=20`. -/
theorem goldbachPairingRecover_example_twenty :
    C10GoldbachState.recoveredPairs = [(3, 17), (7, 13)] := by
  norm_num [C10GoldbachState, GoldbachPairingData.recoveredPairs,
    GoldbachPairingData.targetEven]

/--
Definitional recovery readout for any finite state.

This is not the global injectivity theorem; it records the exact deterministic
decoder used by the finite product encoding once the sorted factor fields have
been recovered.
-/
theorem goldbachPairingRecover_readout (G : GoldbachPairingData) :
    G.recoveredPairs =
      G.smalls.map (fun x => (x, G.anchorSmall + G.anchorLarge - x)) ++
        [(G.anchorSmall, G.anchorLarge)] := by
  rfl

/-! ## Continuous harmonic sieve boundary -/

/--
Discrete classifier shadow for the paper's single-prime discriminant limit:
primes read as `0`, composites/non-primes as `1`.

The analytic statement that the trigonometric kernel has this limit behavior is
open closure debt; this is only the finite endpoint classifier.
-/
def primeDiscriminantEndpoint (n : ℕ) : ℕ :=
  if Nat.Prime n then 0 else 1

/-- The endpoint classifier is `0` at primes. -/
theorem primeDiscriminantEndpoint_of_prime {p : ℕ} (hp : Nat.Prime p) :
    primeDiscriminantEndpoint p = 0 := by
  simp [primeDiscriminantEndpoint, hp]

/-- The endpoint classifier is `1` away from primes. -/
theorem primeDiscriminantEndpoint_of_not_prime {n : ℕ} (hn : ¬ Nat.Prime n) :
    primeDiscriminantEndpoint n = 1 := by
  simp [primeDiscriminantEndpoint, hn]

end InfoGeometry.Topology.PapadakisPrimes
