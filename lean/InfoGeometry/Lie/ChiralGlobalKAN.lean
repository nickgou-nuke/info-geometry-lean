/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib

namespace InfoGeometry.Lie.GlobalDecomposition

/-!
# A certificate interface for a chiral KAN factorisation

The existence and uniqueness of a global KAN decomposition require a specified
group and concrete sector data.  This owner records exactly the finite,
kernel-checkable certificate needed by downstream theorems; it does not claim
that every matrix admits such a decomposition.
-/

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

abbrev Carrier (R ι : Type*) := Matrix ι ι R

def isSpinAlgebra (X : Carrier R ι) : Prop := X + X.transpose = 0

def isWeylDilation (H : Carrier R ι) : Prop :=
  ∃ d : ι → R, H = Matrix.diagonal d

def isParabolicNilpotent (N : Carrier R ι) : Prop := N * N = 0

structure KANCertificate (R ι : Type*) [CommRing R] [Fintype ι]
    [DecidableEq ι] (g : Carrier R ι) where
  k : Carrier R ι
  a : Carrier R ι
  n : Carrier R ι
  k_condition : isSpinAlgebra (R := R) (ι := ι) k
  a_condition : isWeylDilation (R := R) (ι := ι) a
  n_condition : isParabolicNilpotent (R := R) (ι := ι) n
  factorization : g = k * a * n

structure UniqueKANCertificate (R ι : Type*) [CommRing R] [Fintype ι]
    [DecidableEq ι] (g : Carrier R ι) extends KANCertificate R ι g where
  unique : ∀ k' a' n' : Carrier R ι,
    isSpinAlgebra k' → isWeylDilation a' →
      isParabolicNilpotent n' → g = k' * a' * n' →
      k' = k ∧ a' = a ∧ n' = n

theorem factorization_of_certificate {g : Carrier R ι}
    (c : KANCertificate R ι g) :
    ∃ k a n : Carrier R ι,
      isSpinAlgebra k ∧ isWeylDilation a ∧
        isParabolicNilpotent n ∧ g = k * a * n := by
  exact ⟨c.k, c.a, c.n, c.k_condition, c.a_condition,
    c.n_condition, c.factorization⟩

theorem certificate_factorization {g : Carrier R ι}
    (c : KANCertificate R ι g) :
    g = c.k * c.a * c.n :=
  c.factorization

theorem unique_certificate_factorization {g : Carrier R ι}
    (c : UniqueKANCertificate R ι g) :
    ∃! t : Carrier R ι × Carrier R ι × Carrier R ι,
      isSpinAlgebra t.1 ∧ isWeylDilation t.2.1 ∧
        isParabolicNilpotent t.2.2 ∧ g = t.1 * t.2.1 * t.2.2 := by
  refine ⟨(c.k, c.a, c.n), ?_, ?_⟩
  · exact ⟨c.k_condition, c.a_condition, c.n_condition, c.factorization⟩
  · intro t ht
    rcases t with ⟨k', a', n'⟩
    rcases ht with ⟨hk', ha', hn', hfactor⟩
    rcases c.unique k' a' n' hk' ha' hn' hfactor with ⟨rfl, rfl, rfl⟩
    rfl

end InfoGeometry.Lie.GlobalDecomposition
