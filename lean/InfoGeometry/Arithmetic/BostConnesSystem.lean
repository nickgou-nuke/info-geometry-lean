import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Bost-Connes System — Liouville Grading and Prime Factor Parity

The Bost-Connes system encodes arithmetic through operators graded by the
Liouville function λ(n) = (-1)^{Ω(n)}.

## Key Property: Anticommutation with Primes

For any prime p and n ≥ 1:
    λ(pn) = -λ(n)

This follows from Ω(pn) = Ω(p) + Ω(n) = 1 + Ω(n).

This is the arithmetic analogue of fermionic creation operators: multiplying
by a prime flips the "fermion parity" (Liouville sign).

## Literature References

- [BostConnes1995] J.-B. Bost, A. Connes, "Hecke Algebras, Type III Factors and Phase Transitions", Selecta Math. 1 (1995)
- The Liouville function appears implicitly in the grading structure

-/

open scoped ArithmeticFunction.Omega

namespace InfoGeometry.Arithmetic.BostConnesSystem

/-!
## Positive-index multiplicative generators for Bost--Connes lanes

These structures package the positive-integer indexed generators used by the
canonical Bost--Connes files.  The minimal owner surface is a monoid
homomorphism `ℕ+ →* Op`; the Cuntz-style extension adds the isometry and
orthogonality laws used by downstream projection/KMS readbacks.
-/

/-- Positive integer corresponding to a prime. -/
def MultiplicativeIndexing.primePNat (p : ℕ) (hp : Nat.Prime p) : ℕ+ :=
  ⟨p, hp.pos⟩

/-- Positive-integer indexed multiplicative generators. -/
structure MultiplicativeIndexing (Op : Type*) [Monoid Op] where
  S : ℕ+ →* Op

namespace MultiplicativeIndexing

variable {Op : Type*} [Monoid Op]

/-- The generator at index `n`. -/
def generator (C : MultiplicativeIndexing Op) (n : ℕ+) : Op :=
  C.S n

@[simp] theorem generator_one (C : MultiplicativeIndexing Op) :
    C.generator 1 = 1 := by
  simp [generator]

@[simp] theorem generator_mul (C : MultiplicativeIndexing Op) (n m : ℕ+) :
    C.generator (n * m) = C.generator n * C.generator m := by
  simp [generator]

@[simp] theorem generator_pow (C : MultiplicativeIndexing Op) (n : ℕ+) (k : ℕ) :
    C.generator (n ^ k) = C.generator n ^ k := by
  simp [generator]

/-- Ordered product readback for multiplicative generators. -/
theorem generator_list_prod (C : MultiplicativeIndexing Op) (l : List ℕ+) :
    C.generator l.prod = (l.map C.generator).prod := by
  induction l with
  | nil => simp [generator]
  | cons a rest ih =>
      simpa [generator] using congrArg (fun x => C.S a * x) ih

/-- Prime-indexed generator notation. -/
def S_prime (C : MultiplicativeIndexing Op) (p : ℕ) [Fact p.Prime] : Op :=
  C.generator (primePNat p (Fact.out : p.Prime))

@[simp] theorem S_prime_power (C : MultiplicativeIndexing Op)
    (p k : ℕ) (hp : Nat.Prime p) :
    C.generator ((primePNat p hp) ^ k) = C.generator (primePNat p hp) ^ k := by
  simp [generator]

end MultiplicativeIndexing

/--
Multiplicatively indexed Bost--Connes isometries.

There is deliberately no pairwise-orthogonality field here.  Since the index
map is a monoid homomorphism, its value at `1` is the unit; demanding
`star (S 1) * S n = 0` for `n ≠ 1` would force every non-unit generator to be
zero and collapse any nontrivial ring.
-/
structure CuntzMultiplicativeIndexing (Op : Type*) [Ring Op] [StarRing Op]
    extends MultiplicativeIndexing Op where
  generator_isometry : ∀ n : ℕ+, star (toMultiplicativeIndexing.generator n) *
      toMultiplicativeIndexing.generator n = 1

namespace CuntzMultiplicativeIndexing

variable {Op : Type*} [Ring Op] [StarRing Op]

/-- Re-export the indexed generator. -/
def generator (C : CuntzMultiplicativeIndexing Op) (n : ℕ+) : Op :=
  C.toMultiplicativeIndexing.generator n

@[simp] theorem generator_one (C : CuntzMultiplicativeIndexing Op) :
    C.generator 1 = 1 :=
  C.toMultiplicativeIndexing.generator_one

@[simp] theorem generator_mul (C : CuntzMultiplicativeIndexing Op) (n m : ℕ+) :
    C.generator (n * m) = C.generator n * C.generator m :=
  C.toMultiplicativeIndexing.generator_mul n m

/-- The range projection of the isometry indexed by `n`. -/
def rangeProjection (C : CuntzMultiplicativeIndexing Op) (n : ℕ+) : Op :=
  C.generator n * star (C.generator n)

/-- Range projections are idempotent, by the isometry law. -/
@[simp] theorem rangeProjection_idempotent (C : CuntzMultiplicativeIndexing Op)
    (n : ℕ+) : C.rangeProjection n * C.rangeProjection n = C.rangeProjection n := by
  have hIso : star (C.generator n) * C.generator n = 1 := by
    simpa [generator] using C.generator_isometry n
  calc
    C.rangeProjection n * C.rangeProjection n =
        C.generator n * (star (C.generator n) * C.generator n) * star (C.generator n) := by
          simp only [rangeProjection, mul_assoc]
    _ = C.generator n * 1 * star (C.generator n) := by rw [hIso]
    _ = C.rangeProjection n := by simp [rangeProjection]

/-- Range projections are self-adjoint. -/
@[simp] theorem rangeProjection_star (C : CuntzMultiplicativeIndexing Op)
    (n : ℕ+) : star (C.rangeProjection n) = C.rangeProjection n := by
  simp [rangeProjection]

/-- Least common multiple in the positive-natural index monoid. -/
def pnatLcm (n m : ℕ+) : ℕ+ :=
  ⟨Nat.lcm n m, Nat.lcm_pos n.pos m.pos⟩

@[simp] theorem pnatLcm_val (n m : ℕ+) :
    (pnatLcm n m).val = Nat.lcm n.val m.val :=
  rfl

theorem pnatLcm_comm (n m : ℕ+) : pnatLcm n m = pnatLcm m n := by
  exact Subtype.ext (Nat.lcm_comm n m)

/--
The range projections of a concrete multiplicative-isometry representation
commute pairwise.  This is deliberately an external predicate rather than a
field of `CuntzMultiplicativeIndexing`: isometry and multiplicativity alone do
not imply it.
-/
def RangeProjectionsCommute (C : CuntzMultiplicativeIndexing Op) : Prop :=
  ∀ n m : ℕ+, Commute (C.rangeProjection n) (C.rangeProjection m)

/--
The Nica meet law for positive-integer indexed range projections.  In a
concrete Bost--Connes representation, the product of the `n` and `m` range
projections is the range projection indexed by `lcm n m`.

This is a predicate on a representation, not an additional owner axiom.
-/
def IsNicaCovariant (C : CuntzMultiplicativeIndexing Op) : Prop :=
  ∀ n m : ℕ+,
    C.rangeProjection n * C.rangeProjection m =
      C.rangeProjection (pnatLcm n m)

/-- Nica covariance implies pairwise commutativity of the range projections. -/
theorem rangeProjectionsCommute_of_isNicaCovariant
    (C : CuntzMultiplicativeIndexing Op) (hNica : IsNicaCovariant C) :
    RangeProjectionsCommute C := by
  intro n m
  show C.rangeProjection n * C.rangeProjection m =
    C.rangeProjection m * C.rangeProjection n
  rw [hNica n m, hNica m n, pnatLcm_comm]

/-- Prime generators inherit the isometry law. -/
theorem prime_generator_isometry (C : CuntzMultiplicativeIndexing Op)
    (p : ℕ) [Fact p.Prime] :
    star (C.generator (MultiplicativeIndexing.primePNat p (Fact.out : p.Prime))) *
        C.generator (MultiplicativeIndexing.primePNat p (Fact.out : p.Prime)) = 1 :=
  C.generator_isometry _

end CuntzMultiplicativeIndexing

/-!
## Ω(n) — Total Number of Prime Factors (Re-exports from Mathlib)
-/

/--
Ω(n) = total number of prime factors of n, counted with multiplicity.

This re-exports Mathlib's `ArithmeticFunction.cardFactors` (notation: Ω).
-/
def Omega := ArithmeticFunction.cardFactors

@[simp]
theorem Omega_one : Omega 1 = 0 :=
  ArithmeticFunction.cardFactors_one

/--
Ω is completely additive: Ω(mn) = Ω(m) + Ω(n) for m,n ≠ 0.
-/
theorem Omega_mul (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) :
    Omega (m * n) = Omega m + Omega n :=
  ArithmeticFunction.cardFactors_mul hm hn

/--
For a prime p: Ω(p) = 1.
-/
theorem Omega_prime (p : ℕ) (hp : Nat.Prime p) : Omega p = 1 :=
  ArithmeticFunction.cardFactors_apply_prime hp

/--
For a prime p and any k: Ω(p^k) = k.
-/
theorem Omega_prime_pow (p k : ℕ) (hp : Nat.Prime p) : Omega (p ^ k) = k :=
  ArithmeticFunction.cardFactors_apply_prime_pow hp

/-- Positive-integer prime-factor count used by the Bost--Connes lanes. -/
abbrev totalPrimeFactors (n : ℕ+) : ℕ :=
  Omega n

@[simp] theorem totalPrimeFactors_eq_cardFactors (n : ℕ+) :
    totalPrimeFactors n = ArithmeticFunction.cardFactors n :=
  rfl

@[simp] theorem totalPrimeFactors_one : totalPrimeFactors 1 = 0 :=
  Omega_one

theorem totalPrimeFactors_prime (p : ℕ+) (hp : Nat.Prime p.val) :
    totalPrimeFactors p = 1 := by
  simpa [totalPrimeFactors] using Omega_prime p.val hp

theorem totalPrimeFactors_mul (m n : ℕ+) :
    totalPrimeFactors (m * n) = totalPrimeFactors m + totalPrimeFactors n := by
  exact Omega_mul m n m.ne_zero n.ne_zero

/-!
## λ(n) — The Liouville Function
-/

/--
The Liouville function λ(n) = (-1)^{Ω(n)}.

This is completely multiplicative: λ(mn) = λ(m)·λ(n).
-/
noncomputable def liouville (n : ℕ) : ℤ :=
  (-1 : ℤ) ^ (Omega n)

@[simp]
theorem liouville_one : liouville 1 = 1 := by
  simp [liouville]

/--
λ(n)² = 1 for all n ≥ 1.

The Liouville function takes values in {+1, -1}.
-/
theorem liouville_sq (n : ℕ) (_hn : n ≥ 1) : liouville n * liouville n = 1 := by
  unfold liouville
  rw [← pow_add]
  have : Omega n + Omega n = 2 * Omega n := by omega
  rw [this, pow_mul, show ((-1 : ℤ)^2) = 1 by norm_num, one_pow]

/--
λ is completely multiplicative: λ(mn) = λ(m)·λ(n) for m,n ≥ 1.

This follows from Ω(mn) = Ω(m) + Ω(n).
-/
theorem liouville_mul (m n : ℕ) (_hm : m ≥ 1) (_hn : n ≥ 1) (hm0 : m ≠ 0) (hn0 : n ≠ 0) :
    liouville (m * n) = liouville m * liouville n := by
  unfold liouville
  rw [Omega_mul m n hm0 hn0, pow_add]

/--
For a prime p: λ(p) = -1.

This follows from Ω(p) = 1.
-/
theorem liouville_prime (p : ℕ) (hp : Nat.Prime p) : liouville p = -1 := by
  unfold liouville
  rw [Omega_prime p hp]
  norm_num

/--
FUNDAMENTAL PROPERTY: For a prime p and any n ≥ 1: λ(pn) = -λ(n).

Multiplying by a prime flips the Liouville sign. This is the arithmetic
analogue of fermionic creation: a prime acts like a fermion creation operator,
changing the parity of the total number of prime factors.

This is the KEY LEMMA for the Bost-Connes anticommutation theorem.
-/
theorem liouville_prime_mul (p n : ℕ) (hp : Nat.Prime p) (hn : n ≥ 1) :
    liouville (p * n) = - liouville n := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hn0 : n ≠ 0 := by omega
  rw [liouville_mul p n (by omega) hn hp0 hn0, liouville_prime p hp]
  ring

/--
λ(n²) = 1 for all n ≥ 1.

Since Ω(n²) = 2·Ω(n) is always even, the Liouville sign is +1.
-/
theorem liouville_sq' (n : ℕ) (_hn : n ≥ 1) : liouville (n ^ 2) = 1 := by
  unfold liouville Omega
  have : ArithmeticFunction.cardFactors (n ^ 2) = 2 * ArithmeticFunction.cardFactors n := by
    rw [ArithmeticFunction.cardFactors_pow, mul_comm]
  rw [this, pow_mul, show ((-1 : ℤ)^2) = 1 by norm_num, one_pow]

end InfoGeometry.Arithmetic.BostConnesSystem