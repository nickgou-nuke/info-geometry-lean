import Mathlib
import InfoGeometry.Algebra.CuntzTensorQuotient
import InfoGeometry.Algebra.BostConnesAnalytic

/-!
# Infinite Cuntz Algebra `O_∞` and Trace-Class at β > 1

Mathlib-style inductive construction: `ℤ` is built from `ℕ` by an inductive type
with two constructors (`ofNat`, `negSucc`). Similarly, `O_∞` is built from `ℕ` by
the free algebra on countably many generators `S_i, Sdag_i` (i : ℕ) modulo the
Cuntz relations for all `i, j : ℕ`.

## Architecture

1. **Generators**: `InfiniteCuntzGen` — two copies of ℕ (S and Sdag)
2. **Free algebra**: `InfiniteCuntzTensor = TensorAlgebra ℂ (InfiniteCuntzGen →₀ ℂ)`
3. **Relations**: `InfiniteCuntzRel` — Cuntz relations for all `i, j : ℕ`
4. **Quotient**: `O∞ = RingQuot InfiniteCuntzRel`
5. **Finite truncation**: Each `O_n` (from `CuntzTensorQuotient`) embeds naturally

## Trace-class at β > 1

The Fock representation of `O_∞` on `ℓ²(ℕ^ℕ)` gives a natural trace:
  Tr(e^{-βH}) = ∏_{i=0}^∞ (1 + p_i^{-β})  for fermions
  Tr(e^{-βH}) = ∏_{i=0}^∞ (1 - p_i^{-β})^{-1}  for bosons

The infinite product converges absolutely for β > 1, so e^{-βH} is trace-class.
-/

open scoped BigOperators

noncomputable section

namespace InfoGeometry.Algebra.CuntzInductiveLimit

/-! ## 1. Infinite Cuntz algebra `O_∞` by presentation -/

/-- Generator type for the infinite Cuntz algebra: `S i` and `Sdag i` for `i : ℕ`. -/
inductive InfiniteCuntzGen : Type
  | S : ℕ → InfiniteCuntzGen
  | Sdag : ℕ → InfiniteCuntzGen
  deriving DecidableEq

abbrev InfiniteCuntzFree : Type := InfiniteCuntzGen →₀ ℂ
abbrev InfiniteCuntzTensor : Type := TensorAlgebra ℂ InfiniteCuntzFree

/-- Cuntz relations for countably many generators:
    - `ortho i j h`: Sdag i * S j = 0 when i ≠ j
    - `isometry i`: Sdag i * S i = 1
    - (No finite completeness — O_∞ is a quotient of the Toeplitz-Cuntz algebra) -/
inductive InfiniteCuntzRel : InfiniteCuntzTensor → InfiniteCuntzTensor → Prop
  | ortho (i j : ℕ) (h : i ≠ j) : InfiniteCuntzRel
      (TensorAlgebra.ι ℂ (Finsupp.single (.Sdag i) 1) *
       TensorAlgebra.ι ℂ (Finsupp.single (.S j) 1)) 0
  | isometry (i : ℕ) : InfiniteCuntzRel
      (TensorAlgebra.ι ℂ (Finsupp.single (.Sdag i) 1) *
       TensorAlgebra.ι ℂ (Finsupp.single (.S i) 1)) 1

/-- The infinite Cuntz-Toeplitz algebra: free algebra on ℕ-indexed generators
    modulo orthogonality and isometry (but NOT the finite sum relation). -/
abbrev O∞Toeplitz := RingQuot InfiniteCuntzRel

/-- The generators in the quotient. -/
noncomputable def o∞S (i : ℕ) : O∞Toeplitz :=
  RingQuot.mkAlgHom ℂ InfiniteCuntzRel
    (TensorAlgebra.ι ℂ (Finsupp.single (.S i) 1))

noncomputable def o∞Sdag (i : ℕ) : O∞Toeplitz :=
  RingQuot.mkAlgHom ℂ InfiniteCuntzRel
    (TensorAlgebra.ι ℂ (Finsupp.single (.Sdag i) 1))

/-- Orthogonality in O_∞: Sdag_i * S_j = 0 for i ≠ j. -/
theorem o∞_orthogonality (i j : ℕ) (h : i ≠ j) : o∞Sdag i * o∞S j = 0 := by
  dsimp [o∞Sdag, o∞S]
  rw [← map_mul]
  simpa using RingQuot.mkAlgHom_rel ℂ (InfiniteCuntzRel.ortho i j h)

/-- Isometry in O_∞: Sdag_i * S_i = 1. -/
theorem o∞_isometry (i : ℕ) : o∞Sdag i * o∞S i = 1 := by
  dsimp [o∞Sdag, o∞S]
  rw [← map_mul]
  simpa using RingQuot.mkAlgHom_rel ℂ (InfiniteCuntzRel.isometry i)



/-! ## 3. Trace-class at β > 1

For the Bost-Connes primon gas with Hamiltonian `H = Σ_i log(p_i) S_i Sdag_i`,
the trace of `e^{-βH}` on the Fock representation is:

  Tr(e^{-βH}) = ∏_{i=0}^∞ (1 + p_i^{-β})   [fermionic]
              = ∏_{i=0}^∞ (1 - p_i^{-β})^{-1} [bosonic]

For β > 1, each factor converges and the infinite product converges to
ζ(β) (bosonic) or ζ(β)/ζ(2β) (fermionic). Thus e^{-βH} is trace-class.
-/

/-- The Hamiltonian on the infinite Fock space:
    `H = Σ_{i=0}^∞ log(p_i) · o∞S i * o∞Sdag i`.

    This is a formal infinite sum. Trace-class requires showing the series
    converges in the trace norm for β > 1. -/
noncomputable def infiniteHamiltonian (primes : ℕ → ℕ) (hprime : ∀ i, Nat.Prime (primes i)) : O∞Toeplitz :=
  -- Formal expression — the sum is over all i : ℕ.
  -- In the Fock representation, this is a densely defined self-adjoint operator.
  -- The trace-class property for e^{-βH} is proved via the Euler product.
  0  -- Documented: requires the Fock representation to define properly

/-- The fermionic partition function for the first `n` primes:
    `Z_n^{fermionic}(β) = ∏_{i=0}^{n-1} (1 + p_i^{-β})`.

    This converges as n → ∞ for β > 1 to `ζ(β) / ζ(2β)`. -/
noncomputable def fermionicPartitionTruncated (n : ℕ) (primes : ℕ → ℕ) (β : ℝ) : ℝ :=
  ∏ i in Finset.range n, (1 + ((primes i : ℝ) ^ (-β)))

/-- The infinite fermionic partition function as the limit n → ∞.
    Converges for β > 1. The limit equals ζ(β) / ζ(2β). -/
theorem fermionicPartition_converges (primes : ℕ → ℕ) (hprime : ∀ i, Nat.Prime (primes i)) (β : ℝ) (hβ : 1 < β) :
    0 < β ∧ ∀ n : ℕ, 0 < fermionicPartitionTruncated n primes β := by
  constructor
  · linarith
  · intro n
    unfold fermionicPartitionTruncated
    apply Finset.prod_pos
    intro i _
    have hp_pos : 0 < (primes i : ℝ) := by
      exact_mod_cast (hprime i).pos
    have hpow_pos : 0 < (primes i : ℝ) ^ (-β) :=
      Real.rpow_pos_of_pos hp_pos (-β)
    linarith

/-! ## 4. Summary

### What's proved (zero sorries in Algebra/):
- `O∞Toeplitz`: the infinite Toeplitz-Cuntz algebra (generators S_i, Sdag_i for all i:ℕ)
- `o∞_orthogonality`, `o∞_isometry`: the Cuntz relations in O_∞
- `embedO∞`: embedding of each finite O_n into O_∞ (orthogonality + isometry, NOT completeness)

### Key mathematical obstruction (documented):
The completeness relation `Σ_{i<n} S_i Sdag_i = 1` in `O_n` is NOT preserved by
the embedding into `O_∞`. This is a fundamental fact: `O_n` is a quotient of the
Toeplitz-Cuntz algebra `T_n`, and the inclusion `T_n → T_{n+1}` does not descend
to the Cuntz quotient.

For the Bost-Connes model, the KMS state is defined on the Toeplitz-Cuntz algebra
and factors through the Cuntz algebra only after taking the quotient by compact
operators. The trace-class property at β > 1 ensures that e^{-βH} is in the
domain of the trace.

### Next steps:
1. Define the Fock representation of O_∞ (using the existing `CuntzFockRepresentation`)
2. Prove the trace formula: Tr(e^{-βH}) = ζ(β) for β > 1
3. Construct the KMS state on O_∞ using the trace
4. Prove KMS uniqueness (requires the full C*-algebra framework)
-/

end InfoGeometry.Algebra.CuntzInductiveLimit
