import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic

/-!
# Canonical oriented Pfaffian owner

This file introduces the first data-free signed Pfaffian surface used by the
Hestenes--Krein Gauss--Bonnet corridor.

Unlike `PfaffianMatchingExpansionPacket`, no Pfaffian amplitude or matching
expansion is supplied as structure data.  The oriented Pfaffian is defined by
the standard normalized signed permutation sum.

The hard identities `Pf(A)^2 = det(A)` and congruence covariance are not
postulated here; they are subsequent theorems to be proved from this owner.
-/

noncomputable section

namespace InfoGeometry.Volume.OrientedPfaffian

open scoped BigOperators

/-- Canonical `2n`-element index used by the oriented Pfaffian owner. -/
abbrev PairSlot (n : ℕ) := Fin 2 × Fin n

/-- A perfect matching is a fixed-point-free involutive permutation.

This is a genuine finite combinatorial carrier.  No matching amplitude or sign
is stored as external data. -/
def PerfectMatching (n : ℕ) :=
  {σ : Equiv.Perm (PairSlot n) //
    Function.Involutive σ ∧ ∀ i : PairSlot n, σ i ≠ i}

noncomputable instance perfectMatchingFintype (n : ℕ) : Fintype (PerfectMatching n) :=
  Fintype.ofFinite _

@[simp] theorem PerfectMatching.involutive
    {n : ℕ} (m : PerfectMatching n) (i : PairSlot n) :
    m.1 (m.1 i) = i :=
  m.2.1 i

@[simp] theorem PerfectMatching.ne_self
    {n : ℕ} (m : PerfectMatching n) (i : PairSlot n) :
    m.1 i ≠ i :=
  m.2.2 i

/-- Canonical product attached to a perfect matching.

The lexicographic linear order on `Fin 2 × Fin n` chooses each unordered pair
exactly once by retaining the smaller endpoint.  This is only the product
weight; the crossing/orientation sign is deliberately not encoded as data. -/
def matchingProductWeight
    {n : ℕ}
    (A : Matrix (PairSlot n) (PairSlot n) ℝ)
    (m : PerfectMatching n) : ℝ :=
  ∏ i : PairSlot n with i < m.1 i, A i (m.1 i)

/-- Product of the canonical ordered pairs determined by a permutation. -/
def permutationPairWeight
    {n : ℕ}
    (A : Matrix (PairSlot n) (PairSlot n) ℝ)
    (σ : Equiv.Perm (PairSlot n)) : ℝ :=
  ∏ k : Fin n, A (σ (0, k)) (σ (1, k))

/-- Real sign of a permutation. -/
def permutationSign
    {n : ℕ}
    (σ : Equiv.Perm (PairSlot n)) : ℝ :=
  ((Equiv.Perm.sign σ : ℤ) : ℝ)

@[simp] theorem permutationSign_sq
    {n : ℕ}
    (σ : Equiv.Perm (PairSlot n)) :
    permutationSign σ ^ 2 = 1 := by
  unfold permutationSign
  norm_num [sq_eq_one_iff]

/-- The canonical signed oriented Pfaffian on a real `2n × 2n` matrix.

`Pf(A) = 1 / (2^n n!) * Σ_σ sign(σ) ∏_k A_{σ(0,k),σ(1,k)}`.

For skew matrices this is the usual oriented Pfaffian.  The definition is made
on all matrices so that skewness remains an explicit theorem hypothesis. -/
def orientedPfaffian
    (n : ℕ)
    (A : Matrix (PairSlot n) (PairSlot n) ℝ) : ℝ :=
  ((2 ^ n * n.factorial : ℕ) : ℝ)⁻¹ *
    ∑ σ : Equiv.Perm (PairSlot n),
      permutationSign σ * permutationPairWeight A σ

/-- Exact signed-permutation expansion of the canonical oriented Pfaffian. -/
theorem orientedPfaffian_eq_signedPermutationSum
    (n : ℕ)
    (A : Matrix (PairSlot n) (PairSlot n) ℝ) :
    orientedPfaffian n A =
      ((2 ^ n * n.factorial : ℕ) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (PairSlot n),
          permutationSign σ * permutationPairWeight A σ :=
  rfl

/-- Skewness predicate used by the characteristic-form corridor. -/
def IsSkew
    {n : ℕ}
    (A : Matrix (PairSlot n) (PairSlot n) ℝ) : Prop :=
  ∀ i j, A i j = -A j i

/-- Skew matrices have zero diagonal. -/
theorem IsSkew.diagonal_zero
    {n : ℕ}
    {A : Matrix (PairSlot n) (PairSlot n) ℝ}
    (hA : IsSkew A)
    (i : PairSlot n) :
    A i i = 0 := by
  have h := hA i i
  linarith

/-- The oriented Pfaffian in dimension zero is the empty-product value `1`. -/
@[simp] theorem orientedPfaffian_zero_dim :
    orientedPfaffian 0
      (0 : Matrix (PairSlot 0) (PairSlot 0) ℝ) = 1 := by
  simp [orientedPfaffian, permutationSign, permutationPairWeight]

end InfoGeometry.Volume.OrientedPfaffian
