import Mathlib

/-!
# Weak Drazin inverses

Theorem-safe scaffold for Stephen L. Campbell and Carl D. Meyer, Jr.,
"Weak Drazin Inverses", Linear Algebra Appl. 20, 167--178 (1978).

The paper defines a weak Drazin inverse `(d)` of a square matrix `A` of index
`k` by the relation

```text
  B A^(k+1) = A^k.
```

Additional adjectives are encoded by explicit certificates: projective,
commuting, and minimal-rank.  This file proves the elementary algebraic
readouts and keeps Jordan/Drazin decomposition, characteristic-polynomial, and
Markov-chain applications as owner-supplied certificates.
-/

namespace InfoGeometry.Canonical.WeakDrazinInverse

noncomputable section

universe u

variable {n : ℕ}

/-- Matrix-level weak Drazin `(d)` relation at a supplied index `k`. -/
def IsWeakDrazinAt {R : Type u} [Semiring R]
    (A B : Matrix (Fin n) (Fin n) R) (k : ℕ) : Prop :=
  B * A ^ (k + 1) = A ^ k

/-- Projective weak Drazin socket.  The range equality is an explicit certificate. -/
structure ProjectiveWeakDrazin {R : Type u} [Semiring R]
    (A B AD : Matrix (Fin n) (Fin n) R) (k : ℕ) where
  weak : IsWeakDrazinAt A B k
  rangeProjectionAgreement : Prop
  projective_readout : rangeProjectionAgreement

/-- Commuting weak Drazin socket. -/
structure CommutingWeakDrazin {R : Type u} [Semiring R]
    (A B : Matrix (Fin n) (Fin n) R) (k : ℕ) where
  weak : IsWeakDrazinAt A B k
  commutes : A * B = B * A

/-- Minimal-rank weak Drazin socket; rank is an owner-supplied natural readout. -/
structure MinimalRankWeakDrazin {R : Type u} [Semiring R]
    (A B AD : Matrix (Fin n) (Fin n) R) (k : ℕ) where
  weak : IsWeakDrazinAt A B k
  rankB : ℕ
  rankAD : ℕ
  minimalRank : rankB = rankAD

/-- The weak Drazin equation is exactly the `(d)` readout. -/
theorem weakDrazin_readout {R : Type u} [Semiring R]
    {A B : Matrix (Fin n) (Fin n) R} {k : ℕ}
    (h : IsWeakDrazinAt A B k) :
    B * A ^ (k + 1) = A ^ k :=
  h

namespace CommutingWeakDrazin

variable {R : Type u} [Semiring R]
variable {A B : Matrix (Fin n) (Fin n) R} {k : ℕ}
/-- Commuting weak Drazin inverses satisfy the `(c,d)` relation. -/
theorem cd_readout (C : CommutingWeakDrazin A B k) :
    IsWeakDrazinAt A B k ∧ A * B = B * A := by
  cases C with
  | mk weak commutes => exact ⟨weak, commutes⟩

end CommutingWeakDrazin

namespace MinimalRankWeakDrazin

variable {R : Type u} [Semiring R]
variable {A B AD : Matrix (Fin n) (Fin n) R} {k : ℕ}
variable (M : MinimalRankWeakDrazin A B AD k)

/-- Minimal-rank weak Drazin inverses satisfy the `(m,d)` readout. -/
theorem md_readout :
    IsWeakDrazinAt A B k ∧ M.rankB = M.rankAD :=
  ⟨M.weak, M.minimalRank⟩

end MinimalRankWeakDrazin

/-- Campbell--Meyer block normal form socket for Theorem 1. -/
structure BlockWeakDrazinNormalForm {R : Type u} [Semiring R]
    (A B : Matrix (Fin n) (Fin n) R) (k : ℕ) where
  blockDecomposition : Prop
  weakBlockShape : Prop
  block_implies_weak : blockDecomposition → weakBlockShape → IsWeakDrazinAt A B k
  hasBlockDecomposition : blockDecomposition
  hasWeakBlockShape : weakBlockShape

namespace BlockWeakDrazinNormalForm

variable {R : Type u} [Semiring R]
variable {A B : Matrix (Fin n) (Fin n) R} {k : ℕ}
/-- The supplied Campbell--Meyer block shape yields a weak Drazin inverse. -/
theorem weak_from_block (N : BlockWeakDrazinNormalForm A B k) : IsWeakDrazinAt A B k := by
  cases N with
  | mk blockDecomposition weakBlockShape block_implies_weak hasBlockDecomposition hasWeakBlockShape =>
      exact block_implies_weak hasBlockDecomposition hasWeakBlockShape

end BlockWeakDrazinNormalForm

/-- Polynomial/Souriau--Frame computation socket for Theorems 4 and 5. -/
structure PolynomialWeakDrazinCertificate {R : Type u} [Semiring R]
    (A B : Matrix (Fin n) (Fin n) R) (k : ℕ) where
  polynomialIdentity : Prop
  polynomialDefinesB : Prop
  commutes : A * B = B * A
  polynomial_implies_weak : polynomialIdentity → polynomialDefinesB → IsWeakDrazinAt A B k
  hasPolynomialIdentity : polynomialIdentity
  hasPolynomialDefinesB : polynomialDefinesB

namespace PolynomialWeakDrazinCertificate

variable {R : Type u} [Semiring R]
variable {A B : Matrix (Fin n) (Fin n) R} {k : ℕ}
/-- The polynomial certificate yields a commuting weak Drazin inverse. -/
theorem commuting_weak_readout (P : PolynomialWeakDrazinCertificate A B k) :
    IsWeakDrazinAt A B k ∧ A * B = B * A := by
  cases P with
  | mk polynomialIdentity polynomialDefinesB commutes polynomial_implies_weak
      hasPolynomialIdentity hasPolynomialDefinesB =>
      exact ⟨polynomial_implies_weak hasPolynomialIdentity hasPolynomialDefinesB,
        commutes⟩

end PolynomialWeakDrazinCertificate

/-- Markov-chain weak-Drazin socket for Campbell--Meyer Theorem 8. -/
structure MarkovWeakDrazinReadout {R : Type u} [Ring R]
    (A B AD : Matrix (Fin n) (Fin n) R) (k : ℕ) where
  weak : IsWeakDrazinAt A B k
  groupInverseProjection : Matrix (Fin n) (Fin n) R
  weakProjection : Matrix (Fin n) (Fin n) R := 1 - B * A
  stationaryRowsAgree : Prop
  projection_eq_groupProjection : weakProjection = groupInverseProjection
  theorem8_readout : weakProjection = groupInverseProjection → stationaryRowsAgree

namespace MarkovWeakDrazinReadout

variable {R : Type u} [Ring R]
variable {A B AD : Matrix (Fin n) (Fin n) R} {k : ℕ}
variable (M : MarkovWeakDrazinReadout A B AD k)

/-- The weak-Drazin projection has the supplied stationary-row readout. -/
theorem stationary_rows_readout : M.stationaryRowsAgree :=
  M.theorem8_readout M.projection_eq_groupProjection

end MarkovWeakDrazinReadout

end

end InfoGeometry.Canonical.WeakDrazinInverse
