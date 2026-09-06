/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib
import InfoGeometry.Algebra.NPotentAlgebraicSpectra
import InfoGeometry.Algebra.Zorn.ConformalNPotentRoots
import InfoGeometry.Physics.Algebra.ArtinSchreierF2

namespace InfoGeometry.Algebra.PrimePotentHierarchy

open InfoGeometry.Algebra.NPotentSpectra
open InfoGeometry.Algebra.Zorn.ConformalNPotent
open InfoGeometry.Physics.Algebra.ArtinSchreierF2

/-!
# The Prime-Potent Spectral Hierarchy

This module formalizes the hierarchy of $p$-potent operators ($X^p = X$) for prime numbers
$p \in \{2, 3, 5, 7, 13\}$.

Key Theorems:
1. $p=2$: Idempotents $X^2 = X \implies X \in \{0, 1\}$.
2. $p=3$: Tripotents / Chiral Grading $X^3 = X \implies X \in \{0, 1, -1\}$.
3. $p=5$: Conformal / Dirac Roots $X^5 = X \implies X \in \{0, 1, -1, i, -i\}$.
4. $p=7$: Fano Octonionic Rays $X^7 = X \wedge X \neq 0 \implies X^6 = 1$.
   Over $\mathbb{F}_8$, $X^7 = X$ isolates the base subfield $\mathbb{F}_2 = \{0, 1\}$.
5. $p=13$: Double Star $G_2$ Cyclotomic Factorization $X^{13} = X \wedge X \neq 0 \implies X^{12} = 1$,
   factoring through the 12th cyclotomic polynomial $\Phi_{12}(X) = X^4 - X^2 + 1$.
6. Linear Operator Lift: Resolution of identity, projector orthogonality, and state vector decomposition.
-/

/-- Definition of a $p$-potent element in a ring. -/
def IsPrimePotent {A : Type*} [Ring A] (X : A) (p : ℕ) : Prop :=
  X ^ p = X

section DomainSpectra

variable {A : Type*} [CommRing A] [IsDomain A]

/-- 🏆 THEOREM 1 ($p=2$): Idempotents in an integral domain satisfy $X \in \{0, 1\}$. -/
theorem spectrum_p2 (X : A) (h : IsPrimePotent X 2) :
    X = 0 ∨ X = 1 := by
  have h_eq : X * (X - 1) = 0 := by
    calc
      X * (X - 1) = X ^ 2 - X := by ring
      _ = X - X := by rw [h]
      _ = 0 := by ring
  rcases mul_eq_zero.mp h_eq with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

/-- 🏆 THEOREM 2 ($p=3$): Tripotents in an integral domain satisfy $X \in \{0, 1, -1\}$. -/
theorem spectrum_p3 (X : A) (h : IsPrimePotent X 3) :
    X = 0 ∨ X = 1 ∨ X = -1 := by
  have h_eq : X * (X - 1) * (X + 1) = 0 := by
    calc
      X * (X - 1) * (X + 1) = X ^ 3 - X := by ring
      _ = X - X := by rw [h]
      _ = 0 := by ring
  rcases mul_eq_zero.mp h_eq with h12 | h3
  · rcases mul_eq_zero.mp h12 with h1 | h2
    · exact Or.inl h1
    · exact Or.inr (Or.inl (sub_eq_zero.mp h2))
  · have h_neg : X + 1 = 0 := h3
    exact Or.inr (Or.inr (eq_neg_of_add_eq_zero_left h_neg))

end DomainSpectra

section ComplexSpectra

/-- 🏆 THEOREM 3 ($p=5$): 5-potent complex elements decompose into $\{0, 1, -1, i, -i\}$. -/
theorem spectrum_p5 (X : ℂ) (h : IsPrimePotent X 5) :
    X = 0 ∨ X = 1 ∨ X = -1 ∨ X = Complex.I ∨ X = -Complex.I :=
  roots_of_five_potent X h

/-- 🏆 THEOREM 4 ($p=7$): Nonzero 7-potent complex elements are 6th roots of unity. -/
theorem spectrum_p7_nonzero (X : ℂ) (h : IsPrimePotent X 7) (hnz : X ≠ 0) :
    X ^ 6 = 1 := by
  have h_fact : X * (X ^ 6 - 1) = 0 := by
    calc
      X * (X ^ 6 - 1) = X ^ 7 - X := by ring
      _ = X - X := by rw [h]
      _ = 0 := by ring
  rcases mul_eq_zero.mp h_fact with h0 | h6
  · exact (hnz h0).elim
  · exact sub_eq_zero.mp h6

/-- 🏆 THEOREM 5 ($p=13$): Nonzero 13-potent complex elements factor through $\Phi_{12}(X) = X^4 - X^2 + 1$. -/
theorem spectrum_p13_factors_phi12 (X : ℂ) (h : IsPrimePotent X 13) (hnz : X ≠ 0) :
    (X ^ 4 - X ^ 2 + 1) * (X ^ 8 + X ^ 6 - X ^ 2 - 1) = 0 := by
  have h12 : X ^ 12 = 1 := by
    have h_fact : X * (X ^ 12 - 1) = 0 := by
      calc
        X * (X ^ 12 - 1) = X ^ 13 - X := by ring
        _ = X - X := by rw [h]
        _ = 0 := by ring
    rcases mul_eq_zero.mp h_fact with h0 | h12'
    · exact (hnz h0).elim
    · exact sub_eq_zero.mp h12'
  have h_poly : (X ^ 4 - X ^ 2 + 1) * (X ^ 8 + X ^ 6 - X ^ 2 - 1) = X ^ 12 - 1 := by ring
  rw [h_poly, h12, sub_self]

end ComplexSpectra

section FiniteFieldF8

variable {K : Type*} [Field K] [Fintype K]

/-- 🏆 THEOREM 6: In $\mathbb{F}_8$, $X^7 = X$ isolates precisely the base subfield $\mathbb{F}_2 = \{0, 1\}$. -/
theorem spectrum_p7_in_f8_is_f2 (hK : Fintype.card K = 8) (X : K) (h : IsPrimePotent X 7) :
    X = 0 ∨ X = 1 :=
  f8_seven_potent_is_f2 hK X h

end FiniteFieldF8

section OperatorSpectra

variable {K M : Type*} [CommRing K] [AddCommGroup M] [Module K M]

/-- Definition of a $p$-potent linear operator $T : M \to M$. -/
def IsPrimePotentOp (T : Module.End K M) (p : ℕ) : Prop :=
  IsNPotentOperator T p

/-- 🏆 THEOREM 7: General $p$-potent linear operator spectral decomposition on state vectors. -/
theorem operator_spectral_state_decomposition
    (T : Module.End K M) (p : ℕ) (v : M) :
    v = opProjZero T p v + opProjNonzero T p v :=
  vector_spectral_decomposition T p v

/-- 🏆 THEOREM 8: Projector orthogonality for $p$-potent linear operators. -/
theorem operator_projector_orthogonality
    (T : Module.End K M) (p : ℕ) (hp : 2 ≤ p) (hT : IsPrimePotentOp T p) :
    opProjZero T p * opProjNonzero T p = 0 :=
  opProj_orthogonal T p hp hT

end OperatorSpectra

end InfoGeometry.Algebra.PrimePotentHierarchy
