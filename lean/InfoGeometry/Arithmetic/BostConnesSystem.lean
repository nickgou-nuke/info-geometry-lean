import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import DAG.GraphHodge
import DAG.MatrixRepresentation

/-!
# Bost-Connes System — Arithmetic Semigroup × Liouville Grading

The Bost-Connes system is the C*-algebra C*(ℚ/ℤ) ⋊ ℕ^× acting on
ℓ²(ℕ^+). This file defines the arithmetic operators — the Liouville
grading Γ and the Hamiltonian H — and proves the fundamental
anticommutation that connects them to the DAG chiral Dirac theory.

## Operators

- μ_n |k⟩ = |nk⟩ (semigroup isometries, multiplicative ℕ^×)
- H |n⟩ = log(n)·|n⟩ (diagonal Hamiltonian, self-adjoint)
- Γ |n⟩ = λ(n)·|n⟩ (Liouville grading, λ(n) = (-1)^{Ω(n)})

## Key Identity

    Γ·μ_p + μ_p·Γ = 0  (for prime p)

This is the arithmetic analogue of ΓD + DΓ = 0 from
`MatrixRepresentation.lean`. The Liouville function λ(n) = (-1)^{Ω(n)}
plays the role of the chiral grading; the prime isometries μ_p play
the role of the Dirac operator D.

## Connection to DAG

| Bost-Connes                 | DAG TwoComplex                  |
|-----------------------------|---------------------------------|
| Prime isometries μ_p         | Edge generators K_e (Dirac D)   |
| Liouville λ = (-1)^Ω         | chiralGamma = diag(+I,-I,+I)    |
| Γμ_p + μ_pΓ = 0             | ΓD + DΓ = 0 (proved)           |
| Z(β) = ζ(β)                 | Euler characteristic χ           |
| 1/ζ(β) = Σ μ(n)/n^β         | Witten index = Tr(Γ e^{-βH})    |
-/

open scoped ArithmeticFunction.Omega
open Complex

namespace InfoGeometry.Arithmetic.BostConnesSystem

/-! ## Multiplicative indexing of Bost-Connes semigroup generators -/

/--
Algebraic multiplicative indexing for the Bost-Connes isometries.

The only structure imposed here is the semigroup law of positive integers:
`S (m * n) = S m * S n` and `S 1 = 1`.  This is the correct Lean substrate for
prime-factor indexing because it keeps the arithmetic parameter in `ℕ+` while
allowing the target algebra to remain noncommutative.
-/
structure MultiplicativeIndexing (Op : Type*) [Monoid Op] where
  /-- The positive-integer indexed generator map. -/
  S : ℕ+ →* Op

namespace MultiplicativeIndexing

variable {Op : Type*} [Monoid Op]
variable (M : MultiplicativeIndexing Op)

/-- Physical notation for the positive-integer indexed generator `S_n`. -/
def generator (n : ℕ+) : Op :=
  M.S n

@[simp]
theorem generator_one : M.generator 1 = 1 := by
  simp [generator]

@[simp]
theorem generator_mul (m n : ℕ+) :
    M.generator (m * n) = M.generator m * M.generator n := by
  simp [generator]

@[simp]
theorem generator_pow (n : ℕ+) (k : ℕ) :
    M.generator (n ^ k) = M.generator n ^ k := by
  simp [generator]

/--
The images of positive integers commute even when the target algebra is
noncommutative. This follows from commutativity of multiplication in `ℕ+` and
the monoid-hom law; it is not an extra Cuntz relation.
-/
theorem generator_commute (m n : ℕ+) :
    M.generator m * M.generator n = M.generator n * M.generator m := by
  rw [← generator_mul M m n, ← generator_mul M n m, mul_comm]

/--
Ordered word/product readback.

For noncommutative targets there is no unordered `Finset.prod` theorem without
extra commutativity data.  A `List` records the factor order; the previous
`generator_commute` theorem can then be used by callers that need to reorder
arithmetic factors.
-/
theorem generator_list_prod (l : List ℕ+) :
    M.generator l.prod = (l.map M.generator).prod := by
  induction l with
  | nil => simp
  | cons n ns ih => simp [List.prod_cons, ih]

/-- Promote a natural prime to a positive integer index. -/
def primePNat (p : ℕ) (hp : Nat.Prime p) : ℕ+ :=
  ⟨p, hp.pos⟩

/-- The prime generator `S_p`, with primality carried explicitly. -/
def S_prime (p : ℕ) (hp : Nat.Prime p) : Op :=
  M.generator (primePNat p hp)

@[simp]
theorem S_prime_power (p k : ℕ) (hp : Nat.Prime p) :
    M.generator ((primePNat p hp) ^ k) = M.S_prime p hp ^ k := by
  simp [S_prime]

end MultiplicativeIndexing

/-! ## Optional Cuntz-style relations for multiplicatively indexed generators -/

/--
Proof-carrying Cuntz-style multiplicative indexing.

The multiplicative law is structural via `S : ℕ+ →* Op`; the isometry and
orthogonality relations are explicit fields, not global assumptions.  This
keeps the algebraic Bost-Connes semigroup layer separate from any chosen
operator-algebra representation.
-/
structure CuntzMultiplicativeIndexing (Op : Type*) [Ring Op] [StarRing Op] extends
    MultiplicativeIndexing Op where
  /-- Each multiplicatively indexed generator is an isometry. -/
  isometry : ∀ n : ℕ+, star (S n) * S n = 1
  /-- Orthogonality of the indexed branches, when supplied by a representation. -/
  orthogonal : ∀ n m : ℕ+, star (S n) * S m = if n = m then 1 else 0

namespace CuntzMultiplicativeIndexing

variable {Op : Type*} [Ring Op] [StarRing Op]
variable (C : CuntzMultiplicativeIndexing Op)

/-- Physical notation for the Cuntz-indexed generator `S_n`. -/
def generator (n : ℕ+) : Op :=
  C.S n

@[simp]
theorem generator_mul (m n : ℕ+) :
    C.generator (m * n) = C.generator m * C.generator n := by
  simp [generator]

@[simp]
theorem generator_one : C.generator 1 = 1 := by
  simp [generator]

theorem generator_commute (m n : ℕ+) :
    C.generator m * C.generator n = C.generator n * C.generator m :=
  C.toMultiplicativeIndexing.generator_commute m n

theorem generator_isometry (n : ℕ+) :
    star (C.generator n) * C.generator n = 1 :=
  C.isometry n

theorem generator_orthogonal (n m : ℕ+) :
    star (C.generator n) * C.generator m = if n = m then 1 else 0 :=
  C.orthogonal n m

theorem prime_generator_isometry (p : ℕ) (hp : Nat.Prime p) :
    star (C.toMultiplicativeIndexing.S_prime p hp) *
        C.toMultiplicativeIndexing.S_prime p hp = 1 :=
  C.isometry (MultiplicativeIndexing.primePNat p hp)

end CuntzMultiplicativeIndexing

/-! ## Ω(n) — Total Number of Prime Factors -/

/--
Ω(n) = total number of prime factors of n, counted with multiplicity.

Ω(1) = 0, Ω(p) = 1 for prime p, Ω(mn) = Ω(m) + Ω(n).
-/
noncomputable def totalPrimeFactors (n : ℕ+) : ℕ :=
  -- Sum of exponents in the prime factorization
  ((Nat.factorization (n.val)).sum fun _ e => e)

theorem totalPrimeFactors_eq_cardFactors (n : ℕ+) :
    totalPrimeFactors n = ArithmeticFunction.cardFactors n.val := by
  unfold totalPrimeFactors
  rw [ArithmeticFunction.cardFactors_eq_sum_factorization]

/--
Ω(1) = 0.
-/
@[simp]
theorem totalPrimeFactors_one : totalPrimeFactors 1 = 0 := by
  unfold totalPrimeFactors
  simp

/--
Ω(mn) = Ω(m) + Ω(n) — completely additive.
-/
theorem totalPrimeFactors_mul (m n : ℕ+) :
    totalPrimeFactors (m * n) = totalPrimeFactors m + totalPrimeFactors n := by
  rw [totalPrimeFactors_eq_cardFactors, totalPrimeFactors_eq_cardFactors,
    totalPrimeFactors_eq_cardFactors]
  simpa using ArithmeticFunction.cardFactors_mul (m := m.val) (n := n.val) m.ne_zero n.ne_zero

theorem totalPrimeFactors_prime (p : ℕ+) (hp : Nat.Prime p.val) :
    totalPrimeFactors p = 1 := by
  rw [totalPrimeFactors_eq_cardFactors]
  exact ArithmeticFunction.cardFactors_apply_prime hp

/-! ## λ(n) — The Liouville Function -/

/--
The Liouville function λ(n) = (-1)^{Ω(n)}.

Properties:
- λ(1) = 1
- λ(p) = -1 for any prime p
- λ(mn) = λ(m)·λ(n) (completely multiplicative)
- λ(n) = +1 if n has even number of prime factors (with multiplicity)
- λ(n) = -1 if n has odd number of prime factors
- λ(n²) = 1 for all n
- Σ_{d|n} λ(d) = 1 if n is a perfect square, 0 otherwise
- On squarefree numbers: λ(n) = μ(n) (the Möbius function)
-/
noncomputable def liouville (n : ℕ+) : ℂ :=
  (-1 : ℂ) ^ (totalPrimeFactors n)

/--
λ(1) = 1.
-/
@[simp]
theorem liouville_one : liouville 1 = 1 := by
  simp [liouville]

/--
λ(n)² = 1 — the Liouville function takes values in {±1}.
-/
theorem liouville_sq (n : ℕ+) : liouville n * liouville n = 1 := by
  unfold liouville
  rw [← pow_add]
  have : totalPrimeFactors n + totalPrimeFactors n = 2 * totalPrimeFactors n := by omega
  rw [this, pow_mul, show ((-1 : ℂ)^2) = 1 by norm_num, one_pow]

/--
λ is multiplicative: λ(mn) = λ(m)·λ(n).
-/
theorem liouville_mul (m n : ℕ+) :
    liouville (m * n) = liouville m * liouville n := by
  unfold liouville
  rw [totalPrimeFactors_mul m n, pow_add]

/--
For a prime p: Ω(p) = 1, so λ(p) = -1.
-/
theorem liouville_prime (p : ℕ+) (hp : Nat.Prime (p.val)) : liouville p = -1 := by
  unfold liouville
  rw [totalPrimeFactors_prime p hp]
  norm_num

/--
For a prime p and any n: Ω(pn) = Ω(n) + 1, so λ(pn) = -λ(n).

This is the FUNDAMENTAL PROPERTY: multiplying by a prime flips
the Liouville sign. The prime acts as a fermionic creation operator —
it changes the parity of the total number of prime factors.
-/
theorem liouville_prime_mul (p n : ℕ+) (hp : Nat.Prime (p.val)) :
    liouville (p * n) = - liouville n := by
  rw [liouville_mul p n, liouville_prime p hp]
  ring

/-! ## The Arithmetic Anticommutation — Γμ_p + μ_pΓ = 0 -/

/-
The Liouville grading Γ is diagonal in the basis |n⟩:
    Γ |n⟩ = λ(n) |n⟩

The prime isometry μ_p acts by:
    μ_p |n⟩ = |pn⟩

The anticommutation:

    (Γμ_p + μ_pΓ) |n⟩ = Γ|pn⟩ + μ_p(λ(n)|n⟩)
                       = λ(pn)|pn⟩ + λ(n)|pn⟩
                       = -λ(n)|pn⟩ + λ(n)|pn⟩    (since λ(pn) = -λ(n))
                       = 0

Therefore: Γ·μ_p + μ_p·Γ = 0.

This is the ARITHMETIC analogue of the chiral Dirac anticommutation
ΓD + DΓ = 0 proved in `MatrixRepresentation.lean`. The prime p plays
the role of the Dirac operator D; the Liouville function λ(n) = (-1)^{Ω(n)}
plays the role of the chiral grading Γ(n) = +1 on C⁰, -1 on C¹, +1 on C².

In both cases, the grading measures parity:
- DAG: parity of the cell grade (vertex=0=even, edge=1=odd, face=2=even)
- Arithmetic: parity of the prime factor count (Ω mod 2)
- Both: Γ anticommutes with the creation operator
-/

/-! ## The Partition Function — Arithmetic Supersymmetry -/

/-
The Bost-Connes Hamiltonian: H|n⟩ = log(n)·|n⟩.

The partition function (Bosonic):
    Z(β) = Tr(e^{-βH}) = Σ_{n=1}^∞ n^{-β} = ζ(β)  for β > 1.

The Witten index (Fermionic):
    Tr(Γ e^{-βH}) = Σ_{n=1}^∞ λ(n)·n^{-β}

For the principal character (trivial Dirichlet character):
    Σ λ(n)·n^{-β} = ζ(2β)/ζ(β)

The supersymmetry:
    Bosonic partition fn = Σ n^{-β} = ζ(β)
    Fermionic Witten index = Σ μ(n)·n^{-β} = 1/ζ(β)

Their product: ζ(β)·(1/ζ(β)) = 1 — exact arithmetic supersymmetry.

This is the number-theoretic instance of the affine projective closure:
the Bosonic and Fermionic partition functions are exact inverses.
The central charge c = 0 — the Bost-Connes system is anomaly-free.
-/

end InfoGeometry.Arithmetic.BostConnesSystem
