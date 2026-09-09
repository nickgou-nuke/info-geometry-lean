import Mathlib.Tactic

/-!
# Weak Drazin inverses

Theorem-safe scaffold for Stephen L. Campbell and Carl D. Meyer, Jr.,
"Weak Drazin Inverses", Linear Algebra Appl. 20, 167--178 (1978).

The paper defines a weak Drazin inverse `(d)` of a square matrix `A` of index
`k` by the relation

```text
  B A^(k+1) = A^k.
```

Additional adjectives are encoded by explicit matrix equations: projective,
commuting, and minimal-rank.  This file proves only the elementary algebraic
readouts present in those equations.  Jordan/Drazin decomposition,
characteristic-polynomial, and Markov-chain applications require separate
owner definitions before they can be promoted to theorem surfaces.
-/

namespace InfoGeometry.Canonical.WeakDrazinInverse

noncomputable section

universe u

variable {n : ℕ}

/-- Matrix-level weak Drazin `(d)` relation at a supplied index `k`. -/
def IsWeakDrazinAt {R : Type u} [Semiring R]
    (A B : Matrix (Fin n) (Fin n) R) (k : ℕ) : Prop :=
  B * A ^ (k + 1) = A ^ k

/-- Projective weak Drazin relation with an explicit idempotent projection. -/
structure ProjectiveWeakDrazin {R : Type u} [Semiring R]
    (A B AD : Matrix (Fin n) (Fin n) R) (k : ℕ) where
  weak : IsWeakDrazinAt A B k
  AD_eq : AD = A * B
  AD_idempotent : AD * AD = AD

/-- Commuting weak Drazin relation. -/
structure CommutingWeakDrazin {R : Type u} [Semiring R]
    (A B : Matrix (Fin n) (Fin n) R) (k : ℕ) where
  weak : IsWeakDrazinAt A B k
  commutes : A * B = B * A

/-- Minimal-rank weak Drazin relation; the compared ranks are explicit natural readouts. -/
structure MinimalRankWeakDrazin {R : Type u} [Semiring R]
    (A B AD : Matrix (Fin n) (Fin n) R) (k : ℕ) where
  weak : IsWeakDrazinAt A B k
  rankB : ℕ
  rankAD : ℕ
  minimalRank : rankB = rankAD

namespace CommutingWeakDrazin

variable {R : Type u} [Semiring R]
variable {A B : Matrix (Fin n) (Fin n) R} {k : ℕ}
/-- Commuting weak Drazin inverses satisfy the `(c,d)` relation. -/
theorem cd_readout (C : CommutingWeakDrazin A B k) :
    IsWeakDrazinAt A B k ∧ A * B = B * A := by
  cases C with
  | mk weak commutes => exact ⟨weak, commutes⟩

/-- A commuting weak Drazin structure exposes the weak relation directly. -/
theorem weak_readout (C : CommutingWeakDrazin A B k) :
    IsWeakDrazinAt A B k :=
  (cd_readout (A := A) (B := B) (k := k) C).1

/-- A commuting weak Drazin structure exposes the commutation relation directly. -/
theorem commutes_readout (C : CommutingWeakDrazin A B k) :
    A * B = B * A :=
  (cd_readout (A := A) (B := B) (k := k) C).2

end CommutingWeakDrazin

namespace MinimalRankWeakDrazin

variable {R : Type u} [Semiring R]
variable {A B AD : Matrix (Fin n) (Fin n) R} {k : ℕ}
variable (M : MinimalRankWeakDrazin A B AD k)

/-- Minimal-rank weak Drazin inverses satisfy the `(m,d)` readout. -/
theorem md_readout :
    IsWeakDrazinAt A B k ∧ M.rankB = M.rankAD :=
  ⟨M.weak, M.minimalRank⟩

/-- A minimal-rank weak Drazin structure exposes the weak relation directly. -/
theorem weak_readout (M : MinimalRankWeakDrazin A B AD k) :
    IsWeakDrazinAt A B k :=
  (md_readout (A := A) (B := B) (AD := AD) (k := k) M).1

/-- A minimal-rank weak Drazin structure exposes the rank equality directly. -/
theorem rank_readout (M : MinimalRankWeakDrazin A B AD k) :
    M.rankB = M.rankAD :=
  (md_readout (A := A) (B := B) (AD := AD) (k := k) M).2

end MinimalRankWeakDrazin

/-- Polynomial weak Drazin relation with the polynomial evaluator exposed. -/
structure PolynomialWeakDrazin {R : Type u} [CommSemiring R]
    (A B : Matrix (Fin n) (Fin n) R) (k : ℕ) where
  p : Polynomial R
  B_eq_eval :
    B = p.eval₂ (algebraMap R (Matrix (Fin n) (Fin n) R)) A
  weak : IsWeakDrazinAt A B k
  commutes : A * B = B * A

namespace ProjectiveWeakDrazin

variable {R : Type u} [Semiring R]
variable {A B AD : Matrix (Fin n) (Fin n) R} {k : ℕ}

/-- Projective weak Drazin readout: weak relation plus the explicit idempotent projection. -/
theorem projective_readout (P : ProjectiveWeakDrazin A B AD k) :
    IsWeakDrazinAt A B k ∧ AD = A * B ∧ AD * AD = AD := by
  cases P with
  | mk weak AD_eq AD_idempotent =>
      exact ⟨weak, AD_eq, AD_idempotent⟩

/-- A projective weak Drazin structure exposes the weak relation directly. -/
theorem weak_readout (P : ProjectiveWeakDrazin A B AD k) :
    IsWeakDrazinAt A B k :=
  (projective_readout (A := A) (B := B) (AD := AD) (k := k) P).1

/-- A projective weak Drazin structure exposes the idempotent projection equation directly. -/
theorem projection_eq_readout (P : ProjectiveWeakDrazin A B AD k) :
    AD = A * B :=
  (projective_readout (A := A) (B := B) (AD := AD) (k := k) P).2.1

/-- A projective weak Drazin structure exposes the idempotence equation directly. -/
theorem idempotent_readout (P : ProjectiveWeakDrazin A B AD k) :
    AD * AD = AD :=
  (projective_readout (A := A) (B := B) (AD := AD) (k := k) P).2.2

end ProjectiveWeakDrazin

namespace PolynomialWeakDrazin

variable {R : Type u} [CommSemiring R]
variable {A B : Matrix (Fin n) (Fin n) R} {k : ℕ}

/-- The polynomial weak Drazin relation yields a commuting weak Drazin inverse. -/
theorem commuting_weak_readout (P : PolynomialWeakDrazin A B k) :
    IsWeakDrazinAt A B k ∧ A * B = B * A := by
  cases P with
  | mk p B_eq_eval weak commutes =>
      exact ⟨weak, commutes⟩

/-- A polynomial weak Drazin structure exposes the weak relation directly. -/
theorem weak_readout (P : PolynomialWeakDrazin A B k) :
    IsWeakDrazinAt A B k :=
  (commuting_weak_readout (A := A) (B := B) (k := k) P).1

/-- A polynomial weak Drazin structure exposes the commutation relation directly. -/
theorem commutes_readout (P : PolynomialWeakDrazin A B k) :
    A * B = B * A :=
  (commuting_weak_readout (A := A) (B := B) (k := k) P).2

end PolynomialWeakDrazin

/-- Markov-chain weak-Drazin projection comparison as a concrete matrix equality. -/
structure MarkovWeakDrazinProjection {R : Type u} [Ring R]
    (A B groupInverseProjection : Matrix (Fin n) (Fin n) R) (k : ℕ) where
  weak : IsWeakDrazinAt A B k
  weakProjection : Matrix (Fin n) (Fin n) R
  weakProjection_eq_formula : weakProjection = 1 - B * A
  projection_eq_groupProjection : weakProjection = groupInverseProjection

namespace MarkovWeakDrazinProjection

variable {R : Type u} [Ring R]
variable {A B groupInverseProjection : Matrix (Fin n) (Fin n) R} {k : ℕ}
variable (M : MarkovWeakDrazinProjection A B groupInverseProjection k)

/-- The weak-Drazin projection agrees with the supplied group-inverse projection. -/
theorem projection_readout : M.weakProjection = groupInverseProjection :=
  M.projection_eq_groupProjection

/-- The stored weak projection is the explicit matrix formula `1 - B * A`. -/
theorem weakProjection_formula :
    M.weakProjection = 1 - B * A :=
  M.weakProjection_eq_formula

end MarkovWeakDrazinProjection

end

end InfoGeometry.Canonical.WeakDrazinInverse
