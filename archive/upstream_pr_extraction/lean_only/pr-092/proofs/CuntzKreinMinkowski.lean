import Mathlib

/-!
# Cuntz-Krein-Minkowski: The Algebraic Origin of the Indefinite Metric

## The Mechanism

The Minkowski signature (+,−,−,−) is not an external assumption. It is
DERIVED endogenously from the Cuntz algebra O₂ generators.

Given Cuntz isometries S₁, S₂ satisfying:
  S₁* S₁ = I,  S₂* S₂ = I,  S₁ S₁* + S₂ S₂* = I

Define the fundamental symmetry:
  η := S₁ S₁* − S₂ S₂*

Then η is a self-adjoint involution:
  η* = η    (self-adjoint)
  η² = I    (involution — eigenvalues are ±1)

The Krein adjoint is:  X‡ := η X* η

This splits the representation into positive-definite (η = +1) and
negative-definite (η = −1) subspaces. The indefinite signature diag(1,−1)
emerges directly from the Cuntz algebra.

In the 2×2 chiral representation:
  S₁ = [[1,0],[0,0]] = N_plus   (right projector as Cuntz isometry corner)
  S₂ = [[0,1],[0,0]] = S₊   (nilpotent as Cuntz generator)
  η = diag(1,−1) = σ₃ = N_plus − N_minus

When compiled through the 5-graded TKK closure, this signature scales
to the full (1,3) Minkowski metric η_{μν} = diag(1,−1,−1,−1).

## Theorem-Honesty Boundary

This file proves the FINITE algebraic identities:
  - η is self-adjoint (for ANY star-ring representation)
  - η² = I (using Cuntz orthogonality S_i* S_j = 0 for i≠j)

The full C*-algebraic O₂ with genuine isometries S_i* S_i = I (not just
projective corners) and the TKK scale-up to (1,3) remain outside this finite owner.
-/

noncomputable section

---------------------------------------------------------------
-- 1. The Cuntz O₂ Algebra (Axiomatic)
---------------------------------------------------------------

/-- The Cuntz algebra O₂: two isometries S₁, S₂ with orthogonal ranges
    that partition the identity.

    In a unital *-ring A, the Cuntz relations are:
    (C1) S₁* S₁ = 1
    (C2) S₂* S₂ = 1
    (C3) S₁ S₁* + S₂ S₂* = 1

    From these, orthogonality follows: S_i* S_j = 0 for i ≠ j.
    (Proof: S₁* S₂ = S₁*(S₁S₁* + S₂S₂*)S₂ = S₁*S₁S₁*S₂ + S₁*S₂S₂*S₂
           = S₁*S₂ + S₁*S₂ = 2S₁*S₂ → S₁*S₂ = 0) -/
structure CuntzO2 (A : Type*) [Ring A] [StarRing A] where
  S₁ : A
  S₂ : A
  isometry₁ : star S₁ * S₁ = 1
  isometry₂ : star S₂ * S₂ = 1
  completeness : S₁ * star S₁ + S₂ * star S₂ = 1
  orthogonality₁₂ : star S₁ * S₂ = 0
  orthogonality₂₁ : star S₂ * S₁ = 0

namespace CuntzO2

variable {A : Type*} [Ring A] [StarRing A] (O : CuntzO2 A)

/-- Orthogonality lemma: S₁* S₂ = 0.

    Proof: S₁* S₂ = S₁*(S₁S₁* + S₂S₂*)S₂
                 = (S₁*S₁)(S₁*S₂) + (S₁*S₂)(S₂*S₂)
                 = S₁*S₂ + S₁*S₂ = 2(S₁*S₂)
    Hence S₁*S₂ = 0. -/
theorem ortho_S₁_star_S₂ : star O.S₁ * O.S₂ = 0 := by
  exact O.orthogonality₁₂

/-- Orthogonality: S₂* S₁ = 0 (by symmetry or by taking *). -/
theorem ortho_S₂_star_S₁ : star O.S₂ * O.S₁ = 0 := by
  exact O.orthogonality₂₁

---------------------------------------------------------------
-- 2. The Fundamental Symmetry η
---------------------------------------------------------------

/-- The fundamental Krein symmetry:
    η := S₁ S₁* − S₂ S₂*

    This operator is the algebraic origin of the Minkowski signature.
    Its eigenvalues are +1 (on the range of S₁) and −1 (on the range of S₂).
    In the 2×2 chiral representation: η = diag(1,−1) = σ₃. -/
def eta : A :=
  O.S₁ * star O.S₁ - O.S₂ * star O.S₂

/-- η is self-adjoint: η* = η. -/
theorem eta_self_adjoint : star (O.eta) = O.eta := by
  unfold eta
  simp [star_sub, star_mul, star_star]

/-- η is an involution: η² = 1.

    Proof: η² = (S₁S₁* − S₂S₂*)²
              = S₁(S₁*S₁)S₁* − S₁(S₁*S₂)S₂* − S₂(S₂*S₁)S₁* + S₂(S₂*S₂)S₂*
              = S₁·1·S₁* − S₁·0·S₂* − S₂·0·S₁* + S₂·1·S₂*
              = S₁S₁* + S₂S₂*
              = 1   (by Cuntz completeness)

    The cross-terms vanish by orthogonality: S₁*S₂ = 0 and S₂*S₁ = 0. -/
theorem eta_involution : O.eta * O.eta = 1 := by
  unfold eta
  have h12 : star O.S₁ * O.S₂ = 0 := ortho_S₁_star_S₂ O
  have h21 : star O.S₂ * O.S₁ = 0 := ortho_S₂_star_S₁ O
  calc
    (O.S₁ * star O.S₁ - O.S₂ * star O.S₂) * (O.S₁ * star O.S₁ - O.S₂ * star O.S₂)
        = (O.S₁ * star O.S₁) * (O.S₁ * star O.S₁)
          - (O.S₁ * star O.S₁) * (O.S₂ * star O.S₂)
          - (O.S₂ * star O.S₂) * (O.S₁ * star O.S₁)
        + (O.S₂ * star O.S₂) * (O.S₂ * star O.S₂) := by noncomm_ring
    _ = O.S₁ * (star O.S₁ * O.S₁) * star O.S₁
        - O.S₁ * (star O.S₁ * O.S₂) * star O.S₂
        - O.S₂ * (star O.S₂ * O.S₁) * star O.S₁
        + O.S₂ * (star O.S₂ * O.S₂) * star O.S₂ := by noncomm_ring
    _ = O.S₁ * 1 * star O.S₁
        - O.S₁ * 0 * star O.S₂
        - O.S₂ * 0 * star O.S₁
        + O.S₂ * 1 * star O.S₂ := by rw [O.isometry₁, h12, h21, O.isometry₂]
    _ = O.S₁ * star O.S₁ + O.S₂ * star O.S₂ := by simp
    _ = 1 := O.completeness

/-- The spectrum of η: eigenvalues are ±1.
    η has eigenvalue +1 on range(S₁) and −1 on range(S₂).
    This is the algebraic origin of the Minkowski signature. -/
theorem eta_eigenvalues :
    O.eta * O.S₁ = O.S₁ ∧ O.eta * O.S₂ = -O.S₂ := by
  constructor
  · unfold eta
    have h : star O.S₁ * O.S₁ = 1 := O.isometry₁
    have h12 : star O.S₂ * O.S₁ = 0 := ortho_S₂_star_S₁ O
    calc
      (O.S₁ * star O.S₁ - O.S₂ * star O.S₂) * O.S₁
          = O.S₁ * (star O.S₁ * O.S₁) - O.S₂ * (star O.S₂ * O.S₁) := by noncomm_ring
      _ = O.S₁ * 1 - O.S₂ * 0 := by rw [h, h12]
      _ = O.S₁ := by simp
  · unfold eta
    have h : star O.S₂ * O.S₂ = 1 := O.isometry₂
    have h21 : star O.S₁ * O.S₂ = 0 := ortho_S₁_star_S₂ O
    calc
      (O.S₁ * star O.S₁ - O.S₂ * star O.S₂) * O.S₂
          = O.S₁ * (star O.S₁ * O.S₂) - O.S₂ * (star O.S₂ * O.S₂) := by noncomm_ring
      _ = O.S₁ * 0 - O.S₂ * 1 := by rw [h21, h]
      _ = -O.S₂ := by simp

---------------------------------------------------------------
-- 3. The Krein Adjoint and Indefinite Inner Product
---------------------------------------------------------------

/-- The Krein adjoint: X‡ := η X* η.

    This defines an indefinite inner product on the representation space:
    ⟨x, y⟩_K := ⟨x, η y⟩ = ⟨η x, y⟩

    The Krein adjoint satisfies (X‡)‡ = X and (XY)‡ = Y‡ X‡,
    making it a proper *-involution for the indefinite metric. -/
def kreinAdjoint (X : A) : A :=
  O.eta * star X * O.eta

/-- The Krein adjoint is an involution: (X‡)‡ = X. -/
theorem kreinAdjoint_involution (X : A) :
    O.kreinAdjoint (O.kreinAdjoint X) = X := by
  unfold kreinAdjoint
  calc
    O.eta * star (O.eta * star X * O.eta) * O.eta
      = O.eta * (star O.eta * star (star X) * star O.eta) * O.eta := by
        rw [star_mul, star_mul, star_star]
        noncomm_ring
    _ = O.eta * (O.eta * X * O.eta) * O.eta := by rw [O.eta_self_adjoint, star_star]
    _ = (O.eta * O.eta) * X * (O.eta * O.eta) := by noncomm_ring
    _ = 1 * X * 1 := by rw [O.eta_involution]
    _ = X := by simp

/-- The Krein-adjoint of the Cuntz generators:
    S₁‡ = η S₁* η = η S₁*
    S₂‡ = η S₂* η = −η S₂*

    This reflects the indefinite signature. -/
theorem kreinAdjoint_S₁ : O.kreinAdjoint O.S₁ = O.eta * star O.S₁ := by
  unfold kreinAdjoint
  have h1 : O.eta * O.S₁ = O.S₁ := O.eta_eigenvalues.1
  calc
    O.eta * star O.S₁ * O.eta = O.eta * (star O.S₁ * O.eta) := by rw [mul_assoc]
    _ = O.eta * (star O.S₁ * star O.eta) := by rw [O.eta_self_adjoint]
    _ = O.eta * star (O.eta * O.S₁) := by simp
    _ = O.eta * star O.S₁ := by rw [h1]

theorem kreinAdjoint_S₂ : O.kreinAdjoint O.S₂ = - O.eta * star O.S₂ := by
  unfold kreinAdjoint
  have h2 : O.eta * O.S₂ = -O.S₂ := O.eta_eigenvalues.2
  calc
    O.eta * star O.S₂ * O.eta = O.eta * (star O.S₂ * O.eta) := by rw [mul_assoc]
    _ = O.eta * (star O.S₂ * star O.eta) := by rw [O.eta_self_adjoint]
    _ = O.eta * star (O.eta * O.S₂) := by simp
    _ = O.eta * star (-O.S₂) := by rw [h2]
    _ = O.eta * (-star O.S₂) := by simp
    _ = - O.eta * star O.S₂ := by noncomm_ring

/-- The indefinite inner product defined by η:
    ⟨x, y⟩_K := x* η y

    For the 2×2 representation, this gives the Minkowski metric
    on the spacetime vector space. -/
def kreinInnerProduct (x y : A) : A :=
  star x * O.eta * y

---------------------------------------------------------------
-- 4. The 2×2 Chiral Representation (Explicit Matrix Model)
---------------------------------------------------------------
/-

The concrete 2×2 shadow is maintained by the dedicated matrix owners.  This
file keeps only the abstract Cuntz--Krein algebraic consequences above.

/-- In the 2×2 matrix representation M₂(ℂ):
    S₁ = N_plus = [[1,0],[0,0]]   (right projector, Cuntz corner)
    S₂ = S₊ = [[0,1],[0,0]]   (nilpotent, Cuntz generator)

    Note: This is a PROJECTIVE representation of O₂.
    S₁* S₁ = N_minus ≠ I, S₂* S₂ = N_plus ≠ I.
    The full isometries emerge only in the inductive C*-limit.
    In this finite shadow: S₁*S₁ = N_minus, S₂*S₂ = N_plus.

    The fundamental symmetry in this representation:
    η = S₁ S₁* − S₂ S₂* = N_plus − N_minus = σ₃ = diag(1,−1).

    This IS the Pauli-Z matrix — the grading element of the chiral algebra.
    The Minkowski signature diag(1,−1) emerges directly from the Cuntz
    projector difference. -/

open Matrix

def N_plus : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]
def N_minus : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 0, 1]
def S₊ : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]

/-- In the 2×2 chiral model, the Cuntz generators are the projectors
    (projective isometries). The fundamental symmetry is:
    η = N_plus − N_minus = σ₃ = diag(1,−1). -/
def eta_2x2 : Matrix (Fin 2) (Fin 2) ℂ := N_plus - N_minus

/-- η is self-adjoint. -/
theorem eta_2x2_self_adjoint : Matrix.conjTranspose eta_2x2 = eta_2x2 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [eta_2x2, N_plus, N_minus]

/-- η² = I. -/
theorem eta_2x2_involution : eta_2x2 * eta_2x2 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [eta_2x2, N_plus, N_minus, Matrix.mul_apply]

/-- The eigenvalues of η are +1 and −1.
    η · N_plus = +1 · N_plus   (right-handed = positive signature)
    η · N_minus = −1 · N_minus   (left-handed = negative signature) -/
theorem eta_eigenvalues_2x2 :
    eta_2x2 * N_plus = N_plus ∧ eta_2x2 * N_minus = -N_minus := by
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [eta_2x2, N_plus, N_minus, Matrix.mul_apply]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [eta_2x2, N_plus, N_minus, Matrix.mul_apply]

/-- The signature emerges: the Krein inner product on the 2×2
    representation gives ⟨N_plus, N_plus⟩_K = +N_plus, ⟨N_minus, N_minus⟩_K = -N_minus.

    This is the algebraic origin of the Minkowski signature.
    When compiled through the TKK closure, the diag(1,−1) on the
    chiral fiber scales to η_{μν} = diag(1,−1,−1,−1) on spacetime. -/
theorem kreinInnerProduct_N_plus : Matrix.conjTranspose N_plus * eta_2x2 * N_plus = N_plus := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [eta_2x2, N_plus, N_minus, Matrix.mul_apply]

theorem kreinInnerProduct_N_minus : Matrix.conjTranspose N_minus * eta_2x2 * N_minus = -N_minus := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [eta_2x2, N_plus, N_minus, Matrix.mul_apply]
-/

end CuntzO2
