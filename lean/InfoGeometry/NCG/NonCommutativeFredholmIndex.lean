/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.NoncommRing

set_option linter.unusedSectionVars false

namespace NonCommutativeFredholmIndex

open Matrix

variable {R : Type*} {n : Type*} [Fintype n] [DecidableEq n]

/-!
### Archetype α₀: Graded Matrix Substrate, Commutators & Anticommutators
-/

/-- The non-commutative inner derivation (commutator) [A, B] = A * B - B * A on M_n(R). -/
def commutator [Ring R] (A B : Matrix n n R) : Matrix n n R :=
  A * B - B * A

/-- The non-commutative anticommutator (graded bracket) {A, B} = A * B + B * A on M_n(R). -/
def anticommutator [Ring R] (A B : Matrix n n R) : Matrix n n R :=
  A * B + B * A

/-- The non-commutative Leibniz rule: [D, X * Y] = [D, X] * Y + X * [D, Y]. -/
theorem commutator_leibniz [Ring R] (D X Y : Matrix n n R) :
    commutator D (X * Y) = commutator D X * Y + X * commutator D Y := by
  dsimp [commutator]
  noncomm_ring

/-- Homological Trace Vanishing: tr([A, B]) = 0. -/
theorem trace_commutator_zero [CommRing R] (A B : Matrix n n R) :
    Matrix.trace (commutator A B) = 0 := by
  dsimp [commutator]
  rw [Matrix.trace_sub, Matrix.trace_mul_comm A B, sub_self]

/-- Graded Parity of First-Order Derivations:
If γ anticommutes with D ({γ, D} = 0) and commutes with X ([γ, X] = 0),
then γ strictly anticommutes with the evolutionary derivation [D, X]: {γ, [D, X]} = 0. -/
theorem anticommutator_commutator_of_even [Ring R] (γ D X : Matrix n n R)
    (hγD : anticommutator γ D = 0) (hγX : commutator γ X = 0) :
    anticommutator γ (commutator D X) = 0 := by
  have h_id :
      anticommutator γ (commutator D X) =
      anticommutator γ D * X - D * commutator γ X -
      commutator γ X * D - X * anticommutator γ D := by
    dsimp [anticommutator, commutator]
    noncomm_ring
  rw [h_id, hγD, hγX]
  noncomm_ring

/-- Graded Parity of Quadratic Operators:
If γ anticommutes with Y ({γ, Y} = 0), then γ commutes with Y² ([γ, Y²] = 0). -/
theorem commutator_sq_of_anticomm_zero [Ring R] (γ Y : Matrix n n R)
    (hγY : anticommutator γ Y = 0) :
    commutator γ (Y * Y) = 0 := by
  have h_id :
      commutator γ (Y * Y) = anticommutator γ Y * Y - Y * anticommutator γ Y := by
    dsimp [commutator, anticommutator]
    noncomm_ring
  rw [h_id, hγY]
  noncomm_ring

/-- Even Grading of Connes Curvature:
If {γ, D} = 0 and [γ, P] = 0, then the Connes curvature [D, P]² commutes with γ. -/
theorem commutator_grading_connes_curvature [Ring R] (γ D P : Matrix n n R)
    (hγD : anticommutator γ D = 0) (hγP : commutator γ P = 0) :
    commutator γ (commutator D P * commutator D P) = 0 :=
  commutator_sq_of_anticomm_zero γ (commutator D P)
    (anticommutator_commutator_of_even γ D P hγD hγP)

/-!
### Archetype α₁: Odd Fredholm Module (D² = 1) & Toeplitz Curvature Defect
Causal Dependency: α₀ ≺ α₁
-/

/-- An idempotent projection operator (taxonomic stratum) P² = P in M_n(R). -/
structure IsIdempotent [Ring R] (P : Matrix n n R) : Prop where
  idem : P * P = P

/-- Two operator strata P and Q are mutually orthogonal if P * Q = 0 and Q * P = 0. -/
structure IsOrthogonalPair [Ring R] (P Q : Matrix n n R) : Prop where
  mul_eq_zero : P * Q = 0
  rev_eq_zero : Q * P = 0

/-- An odd Fredholm module over M_n(R) equipped with an involutive Dirac phase D² = 1. -/
structure IsOddFredholmModule [Ring R] (D : Matrix n n R) : Prop where
  sq_one : D * D = 1

/-- The compressed Toeplitz operator T_P(D) = P * D * P on the stratum P. -/
def toeplitzCompression [Ring R] (P D : Matrix n n R) : Matrix n n R :=
  P * D * P

/-- The local even Chern–Connes 2-cocycle density C(D, P) = P * [D, P] * [D, P]. -/
def connesDensity [Ring R] (D P : Matrix n n R) : Matrix n n R :=
  P * (commutator D P * commutator D P)

/-- Phase-Flip Anticommutativity of Odd Fredholm Derivations:
When D² = 1, the inner derivation [D, X] anticommutes with D for every X ∈ M_n(R):
{D, [D, X]} = 0. -/
theorem oddFredholm_anticomm_commutator [Ring R] (D X : Matrix n n R)
    (hD : IsOddFredholmModule D) :
    anticommutator D (commutator D X) = 0 := by
  dsimp [anticommutator, commutator]
  calc
    D * (D * X - X * D) + (D * X - X * D) * D
      = (D * D) * X - X * (D * D) := by noncomm_ring
    _ = 1 * X - X * 1 := by rw [hD.sq_one]
    _ = 0 := by noncomm_ring

/-- Conjugating any inner derivation [D, X] by an involutive Dirac operator D² = 1
inverts its sign: D * [D, X] * D = -[D, X]. -/
theorem oddFredholm_conj_commutator [Ring R] (D X : Matrix n n R)
    (hD : IsOddFredholmModule D) :
    D * commutator D X * D = - commutator D X := by
  dsimp [commutator]
  calc
    D * (D * X - X * D) * D
      = (D * D) * X * D - D * X * (D * D) := by noncomm_ring
    _ = 1 * X * D - D * X * 1 := by rw [hD.sq_one]
    _ = - (D * X - X * D) := by noncomm_ring

/-- Left multiplication of [D, X] by D flips D to the right with a minus sign:
D * [D, X] = -([D, X] * D). -/
theorem oddFredholm_mul_commutator [Ring R] (D X : Matrix n n R)
    (hD : IsOddFredholmModule D) :
    D * commutator D X = - (commutator D X * D) := by
  dsimp [commutator]
  calc
    D * (D * X - X * D)
      = (D * D) * X - D * X * D := by noncomm_ring
    _ = 1 * X - D * X * D := by rw [hD.sq_one]
    _ = X * 1 - D * X * D := by noncomm_ring
    _ = X * (D * D) - D * X * D := by rw [hD.sq_one]
    _ = - ((D * X - X * D) * D) := by noncomm_ring

/-- Fundamental Toeplitz Curvature Defect Identity:
For an odd Fredholm module D² = 1 and any idempotent stratum P² = P, the local
Chern–Connes density C(D, P) = P * [D, P]² equals the quadratic Toeplitz defect
T_P(D)² - P = (P * D * P)² - P. -/
theorem connesDensity_eq_toeplitz_defect [Ring R] (D P : Matrix n n R)
    (hD : IsOddFredholmModule D) (hP : IsIdempotent P) :
    connesDensity D P = toeplitzCompression P D * toeplitzCompression P D - P := by
  dsimp [connesDensity, commutator, toeplitzCompression]
  have hPPL : ∀ X : Matrix n n R, (P * P) * X = P * X := by
    intro X; rw [hP.idem]
  have h1 :
      P * ((D * P - P * D) * (D * P - P * D)) =
      P * D * P * D * P - P * D * (P * P) * D -
      (P * P) * (D * D) * P + (P * P) * D * P * D := by noncomm_ring
  have e1 : P * D * (P * P) * D = P * D * P * D := by rw [hP.idem]
  have e2 : P * P * (D * D) * P = P := by
    rw [hPPL, hD.sq_one, mul_one, hP.idem]
  have e3 : P * P * D * P * D = P * D * P * D := by rw [hPPL]
  have eFin : (P * D * P) * (P * D * P) = P * D * (P * P) * D * P := by simp only [mul_assoc]
  rw [h1, e1, e2, e3, eFin, hP.idem]
  noncomm_ring

/-!
### Archetype α₂: Even Z₂-Graded & Chiral Fredholm Modules
Causal Dependency: α₀, α₁ ≺ α₂
-/

/-- An even Z₂-graded Fredholm module (D, γ) over M_n(R) satisfying
D² = 1, γ² = 1, and {γ, D} = γ * D + D * γ = 0. -/
structure IsEvenFredholmModule [Ring R] (D γ : Matrix n n R) : Prop where
  sq_D     : D * D = 1
  sq_γ     : γ * γ = 1
  anticomm : anticommutator γ D = 0

/-- Underlying odd Fredholm module of an even Z₂-graded Fredholm module. -/
lemma IsEvenFredholmModule.toOdd [Ring R] {D γ : Matrix n n R}
    (hE : IsEvenFredholmModule D γ) :
    IsOddFredholmModule D :=
  ⟨hE.sq_D⟩

/-- A division-free chiral Z₂-graded Fredholm module (D, E_pos, E_neg) over M_n(R),
where E_pos + E_neg = 1 are orthogonal chiral idempotents and D is purely off-diagonal
(E_pos * D * E_pos = 0 and E_neg * D * E_neg = 0). -/
structure IsChiralFredholmModule [Ring R] (D E_pos E_neg : Matrix n n R) : Prop where
  sq_D        : D * D = 1
  idem_pos    : IsIdempotent E_pos
  idem_neg    : IsIdempotent E_neg
  orth_chiral : IsOrthogonalPair E_pos E_neg
  sum_one     : E_pos + E_neg = 1
  odd_pos     : E_pos * D * E_pos = 0
  odd_neg     : E_neg * D * E_neg = 0

/-- Underlying odd Fredholm module of a chiral Fredholm module. -/
lemma IsChiralFredholmModule.toOdd [Ring R] {D E_pos E_neg : Matrix n n R}
    (hF : IsChiralFredholmModule D E_pos E_neg) :
    IsOddFredholmModule D :=
  ⟨hF.sq_D⟩

/-- Off-Diagonal Chiral Decomposition of the Dirac Operator:
In any chiral Fredholm module, D = E_pos * D * E_neg + E_neg * D * E_pos. -/
theorem chiral_off_diagonal_dirac [Ring R] {D E_pos E_neg : Matrix n n R}
    (hF : IsChiralFredholmModule D E_pos E_neg) :
    D = E_pos * D * E_neg + E_neg * D * E_pos := by
  calc
    D = 1 * D * 1 := by noncomm_ring
    _ = (E_pos + E_neg) * D * (E_pos + E_neg) := by rw [← hF.sum_one]
    _ = E_pos * D * E_pos + E_pos * D * E_neg +
        E_neg * D * E_pos + E_neg * D * E_neg := by noncomm_ring
    _ = 0 + E_pos * D * E_neg + E_neg * D * E_pos + 0 := by
        rw [hF.odd_pos, hF.odd_neg]
    _ = E_pos * D * E_neg + E_neg * D * E_pos := by noncomm_ring

/-- Every chiral Fredholm module (D, E_pos, E_neg) canonically induces an even
Z₂-graded Fredholm module with grading involution γ = E_pos - E_neg. -/
theorem chiral_induces_evenFredholmModule [Ring R] {D E_pos E_neg : Matrix n n R}
    (hF : IsChiralFredholmModule D E_pos E_neg) :
    IsEvenFredholmModule D (E_pos - E_neg) := by
  refine ⟨hF.sq_D, ?_, ?_⟩
  · calc
      (E_pos - E_neg) * (E_pos - E_neg)
        = E_pos * E_pos - E_pos * E_neg - E_neg * E_pos + E_neg * E_neg := by noncomm_ring
      _ = E_pos - 0 - 0 + E_neg := by
          rw [hF.idem_pos.idem, hF.orth_chiral.mul_eq_zero,
              hF.orth_chiral.rev_eq_zero, hF.idem_neg.idem]
      _ = E_pos + E_neg := by noncomm_ring
      _ = 1 := hF.sum_one
  · dsimp [anticommutator]
    have hD := chiral_off_diagonal_dirac hF
    calc
      (E_pos - E_neg) * D + D * (E_pos - E_neg)
        = (E_pos - E_neg) * (E_pos * D * E_neg + E_neg * D * E_pos) +
          (E_pos * D * E_neg + E_neg * D * E_pos) * (E_pos - E_neg) :=
          congr_arg₂ (· + ·) (congr_arg ((E_pos - E_neg) * ·) hD)
            (congr_arg (· * (E_pos - E_neg)) hD)
      _ = (E_pos * E_pos) * D * E_neg + (E_pos * E_neg) * D * E_pos -
          (E_neg * E_pos) * D * E_neg - (E_neg * E_neg) * D * E_pos +
          E_pos * D * (E_neg * E_pos) - E_pos * D * (E_neg * E_neg) +
          E_neg * D * (E_pos * E_pos) - E_neg * D * (E_pos * E_neg) := by noncomm_ring
      _ = E_pos * D * E_neg + 0 * D * E_pos -
          0 * D * E_neg - E_neg * D * E_pos +
          E_pos * D * 0 - E_pos * D * E_neg +
          E_neg * D * E_pos - E_neg * D * 0 := by
          rw [hF.idem_pos.idem, hF.idem_neg.idem,
              hF.orth_chiral.mul_eq_zero, hF.orth_chiral.rev_eq_zero]
      _ = 0 := by noncomm_ring

/-!
### Archetype α₃: Strict Cyclic Invariance of Fredholm Cochains under D² = 1
Causal Dependency: α₁, α₂ ≺ α₃
-/

/-- The normalized odd Fredholm 1-cochain ψ_D(A₀, A₁) = tr(D * [D, A₀] * [D, A₁]). -/
def oddFredholmCochain1 [CommRing R] (D A₀ A₁ : Matrix n n R) : R :=
  Matrix.trace (D * commutator D A₀ * commutator D A₁)

/-- The normalized even Z₂-graded Fredholm 2-cochain
Φ_{D,γ}(A₀, A₁, A₂) = tr(γ * D * [D, A₀] * [D, A₁] * [D, A₂]). -/
def evenFredholmCochain2 [CommRing R] (D γ A₀ A₁ A₂ : Matrix n n R) : R :=
  Matrix.trace (γ * D * commutator D A₀ * commutator D A₁ * commutator D A₂)

/-- Strict Cyclic Skew-Symmetry (λ₁ ψ_D = ψ_D) of the Odd Fredholm 1-Cochain:
When D² = 1, ψ_D(A₁, A₀) = -ψ_D(A₀, A₁) for all A₀, A₁ ∈ M_n(R). -/
theorem oddFredholmCochain1_cyclic [CommRing R] (D A₀ A₁ : Matrix n n R)
    (hD : IsOddFredholmModule D) :
    - oddFredholmCochain1 D A₁ A₀ = oddFredholmCochain1 D A₀ A₁ := by
  dsimp [oddFredholmCochain1]
  rw [oddFredholm_mul_commutator D A₁ hD]
  have h_alg :
      - (commutator D A₁ * D) * commutator D A₀ =
      - (commutator D A₁ * (D * commutator D A₀)) := by noncomm_ring
  rw [h_alg, Matrix.trace_neg, neg_neg]
  rw [Matrix.trace_mul_comm (commutator D A₁) (D * commutator D A₀)]

/-- Commutation of the Combined Chiral-Dirac Phase γ * D with Even Derivations [D, X]:
In an even Z₂-graded Fredholm module (D, γ), if [γ, X] = 0, then γ * D commutes
with [D, X]: (γ * D) * [D, X] = [D, X] * (γ * D). -/
theorem gamma_dirac_commutes_with_derivation [Ring R] (D γ X : Matrix n n R)
    (hE : IsEvenFredholmModule D γ) (hγX : commutator γ X = 0) :
    (γ * D) * commutator D X = commutator D X * (γ * D) := by
  have h_anti_D := oddFredholm_anticomm_commutator D X hE.toOdd
  have h_anti_γ := anticommutator_commutator_of_even γ D X hE.anticomm hγX
  have h_id :
      (γ * D) * commutator D X - commutator D X * (γ * D) =
      γ * anticommutator D (commutator D X) -
      anticommutator γ (commutator D X) * D := by
    dsimp [anticommutator]
    noncomm_ring
  rw [h_anti_D, h_anti_γ] at h_id
  have h_zero : (γ * D) * commutator D X - commutator D X * (γ * D) = 0 := by
    calc
      (γ * D) * commutator D X - commutator D X * (γ * D)
        = γ * 0 - 0 * D := h_id
      _ = 0 := by noncomm_ring
  exact sub_eq_zero.mp h_zero

/-- Strict Cyclic Invariance (λ₂ Φ_{D,γ} = Φ_{D,γ}) of the Graded Fredholm 2-Cochain:
In an even Z₂-graded Fredholm module (D, γ), for any even matrix A₂ ([γ, A₂] = 0),
Φ_{D,γ}(A₂, A₀, A₁) = Φ_{D,γ}(A₀, A₁, A₂). -/
theorem evenFredholmCochain2_cyclic [CommRing R] (D γ A₀ A₁ A₂ : Matrix n n R)
    (hE : IsEvenFredholmModule D γ) (hγA₂ : commutator γ A₂ = 0) :
    evenFredholmCochain2 D γ A₂ A₀ A₁ = evenFredholmCochain2 D γ A₀ A₁ A₂ := by
  dsimp [evenFredholmCochain2]
  have h_comm := gamma_dirac_commutes_with_derivation D γ A₂ hE hγA₂
  have h_shift :
      γ * D * commutator D A₂ * commutator D A₀ * commutator D A₁ =
      commutator D A₂ * (γ * D * commutator D A₀ * commutator D A₁) := by
    calc
      γ * D * commutator D A₂ * commutator D A₀ * commutator D A₁
        = ((γ * D) * commutator D A₂) * commutator D A₀ * commutator D A₁ := by noncomm_ring
      _ = (commutator D A₂ * (γ * D)) * commutator D A₀ * commutator D A₁ := by rw [h_comm]
      _ = commutator D A₂ * (γ * D * commutator D A₀ * commutator D A₁) := by noncomm_ring
  rw [h_shift]
  rw [Matrix.trace_mul_comm (commutator D A₂) (γ * D * commutator D A₀ * commutator D A₁)]

/-!
### Archetype α₄: Chiral Toeplitz Factorization & The Calderón–Fedosov Index Operator
Causal Dependency: α₁, α₂ ≺ α₄
-/

/-- An idempotent stratum P² = P that is even with respect to the chiral projections
(E_pos * P = P * E_pos and E_neg * P = P * E_neg). -/
structure IsEvenIdempotent [Ring R] (P E_pos E_neg : Matrix n n R) : Prop where
  idem     : IsIdempotent P
  comm_pos : E_pos * P = P * E_pos
  comm_neg : E_neg * P = P * E_neg

/-- Positive chiral subprojection P_+ = E_pos * P of an even idempotent stratum P. -/
def chiralProjPos [Ring R] (E_pos P : Matrix n n R) : Matrix n n R :=
  E_pos * P

/-- Negative chiral subprojection P_- = E_neg * P of an even idempotent stratum P. -/
def chiralProjNeg [Ring R] (E_neg P : Matrix n n R) : Matrix n n R :=
  E_neg * P

/-- Forward chiral Dirac–Toeplitz operator F_+ = P_- * D * P_+ : P_+ A → P_- A. -/
def chiralToeplitzPos [Ring R] (D E_pos E_neg P : Matrix n n R) : Matrix n n R :=
  chiralProjNeg E_neg P * D * chiralProjPos E_pos P

/-- Backward chiral Dirac–Toeplitz parametrix F_- = P_+ * D * P_- : P_- A → P_+ A. -/
def chiralToeplitzNeg [Ring R] (D E_pos E_neg P : Matrix n n R) : Matrix n n R :=
  chiralProjPos E_pos P * D * chiralProjNeg E_neg P

/-- The Calderón–Fedosov local index operator
I_FC(D, P) = (P_+ - F_- * F_+) - (P_- - F_+ * F_-). -/
def fedosovIndexOperator [Ring R] (D E_pos E_neg P : Matrix n n R) : Matrix n n R :=
  (chiralProjPos E_pos P -
    chiralToeplitzNeg D E_pos E_neg P * chiralToeplitzPos D E_pos E_neg P) -
  (chiralProjNeg E_neg P -
    chiralToeplitzPos D E_pos E_neg P * chiralToeplitzNeg D E_pos E_neg P)

/-- Chiral Resolution of an Even Idempotent Stratum: P_+ + P_- = P. -/
theorem chiralProjPos_add_neg [Ring R] {D E_pos E_neg P : Matrix n n R}
    (hF : IsChiralFredholmModule D E_pos E_neg) :
    chiralProjPos E_pos P + chiralProjNeg E_neg P = P := by
  dsimp [chiralProjPos, chiralProjNeg]
  calc
    E_pos * P + E_neg * P = (E_pos + E_neg) * P := by noncomm_ring
    _ = 1 * P := by rw [hF.sum_one]
    _ = P := one_mul P

/-- Graded Difference of Chiral Subprojections: (E_pos - E_neg) * P = P_+ - P_-. -/
theorem grading_mul_stratum_eq_chiral_diff [Ring R] (E_pos E_neg P : Matrix n n R) :
    (E_pos - E_neg) * P = chiralProjPos E_pos P - chiralProjNeg E_neg P := by
  dsimp [chiralProjPos, chiralProjNeg]
  noncomm_ring

/-- Idempotence of the positive chiral subprojection P_+. -/
theorem isIdempotent_chiralProjPos [Ring R] {D E_pos E_neg P : Matrix n n R}
    (hF : IsChiralFredholmModule D E_pos E_neg)
    (hP : IsEvenIdempotent P E_pos E_neg) :
    IsIdempotent (chiralProjPos E_pos P) := by
  refine ⟨?_⟩
  dsimp [chiralProjPos]
  calc
    (E_pos * P) * (E_pos * P)
      = E_pos * (P * E_pos) * P := by noncomm_ring
    _ = E_pos * (E_pos * P) * P := by rw [← hP.comm_pos]
    _ = (E_pos * E_pos) * (P * P) := by noncomm_ring
    _ = E_pos * P := by rw [hF.idem_pos.idem, hP.idem.idem]

/-- Idempotence of the negative chiral subprojection P_-. -/
theorem isIdempotent_chiralProjNeg [Ring R] {D E_pos E_neg P : Matrix n n R}
    (hF : IsChiralFredholmModule D E_pos E_neg)
    (hP : IsEvenIdempotent P E_pos E_neg) :
    IsIdempotent (chiralProjNeg E_neg P) := by
  refine ⟨?_⟩
  dsimp [chiralProjNeg]
  calc
    (E_neg * P) * (E_neg * P)
      = E_neg * (P * E_neg) * P := by noncomm_ring
    _ = E_neg * (E_neg * P) * P := by rw [← hP.comm_neg]
    _ = (E_neg * E_neg) * (P * P) := by noncomm_ring
    _ = E_neg * P := by rw [hF.idem_neg.idem, hP.idem.idem]

/-- Mutual orthogonality of the chiral subprojections P_+ and P_-. -/
theorem orthogonal_chiralProj [Ring R] {D E_pos E_neg P : Matrix n n R}
    (hF : IsChiralFredholmModule D E_pos E_neg)
    (hP : IsEvenIdempotent P E_pos E_neg) :
    IsOrthogonalPair (chiralProjPos E_pos P) (chiralProjNeg E_neg P) := by
  refine ⟨?_, ?_⟩
  · dsimp [chiralProjPos, chiralProjNeg]
    calc
      (E_pos * P) * (E_neg * P)
        = E_pos * (P * E_neg) * P := by noncomm_ring
      _ = E_pos * (E_neg * P) * P := by rw [← hP.comm_neg]
      _ = (E_pos * E_neg) * (P * P) := by noncomm_ring
      _ = 0 * P := by rw [hF.orth_chiral.mul_eq_zero, hP.idem.idem]
      _ = 0 := zero_mul P
  · dsimp [chiralProjPos, chiralProjNeg]
    calc
      (E_neg * P) * (E_pos * P)
        = E_neg * (P * E_pos) * P := by noncomm_ring
      _ = E_neg * (E_pos * P) * P := by rw [← hP.comm_pos]
      _ = (E_neg * E_pos) * (P * P) := by noncomm_ring
      _ = 0 * P := by rw [hF.orth_chiral.rev_eq_zero, hP.idem.idem]
      _ = 0 := zero_mul P

/-- Vanishing of the positive-chirality diagonal Dirac block: P_+ * D * P_+ = 0. -/
theorem chiralProjPos_dirac_zero [Ring R] {D E_pos E_neg P : Matrix n n R}
    (hF : IsChiralFredholmModule D E_pos E_neg)
    (hP : IsEvenIdempotent P E_pos E_neg) :
    chiralProjPos E_pos P * D * chiralProjPos E_pos P = 0 := by
  dsimp [chiralProjPos]
  calc
    (E_pos * P) * D * (E_pos * P)
      = (P * E_pos) * D * (E_pos * P) := by rw [hP.comm_pos]
    _ = P * (E_pos * D * E_pos) * P := by noncomm_ring
    _ = P * 0 * P := by rw [hF.odd_pos]
    _ = 0 := by noncomm_ring

/-- Vanishing of the negative-chirality diagonal Dirac block: P_- * D * P_- = 0. -/
theorem chiralProjNeg_dirac_zero [Ring R] {D E_pos E_neg P : Matrix n n R}
    (hF : IsChiralFredholmModule D E_pos E_neg)
    (hP : IsEvenIdempotent P E_pos E_neg) :
    chiralProjNeg E_neg P * D * chiralProjNeg E_neg P = 0 := by
  dsimp [chiralProjNeg]
  calc
    (E_neg * P) * D * (E_neg * P)
      = (P * E_neg) * D * (E_neg * P) := by rw [hP.comm_neg]
    _ = P * (E_neg * D * E_neg) * P := by noncomm_ring
    _ = P * 0 * P := by rw [hF.odd_neg]
    _ = 0 := by noncomm_ring

/-- Chiral Decomposition of the Compressed Toeplitz Operator:
P * D * P = F_- + F_+. -/
theorem toeplitzCompression_eq_chiral_sum [Ring R] {D E_pos E_neg P : Matrix n n R}
    (hF : IsChiralFredholmModule D E_pos E_neg)
    (hP : IsEvenIdempotent P E_pos E_neg) :
    toeplitzCompression P D =
    chiralToeplitzNeg D E_pos E_neg P + chiralToeplitzPos D E_pos E_neg P := by
  dsimp [toeplitzCompression, chiralToeplitzNeg, chiralToeplitzPos]
  have hSum := chiralProjPos_add_neg hF (P := P)
  calc
    P * D * P
      = (chiralProjPos E_pos P + chiralProjNeg E_neg P) * D *
        (chiralProjPos E_pos P + chiralProjNeg E_neg P) :=
        congr_arg₂ (· * ·) (congr_arg (· * D) hSum.symm) hSum.symm
    _ = chiralProjPos E_pos P * D * chiralProjPos E_pos P +
        chiralProjPos E_pos P * D * chiralProjNeg E_neg P +
        chiralProjNeg E_neg P * D * chiralProjPos E_pos P +
        chiralProjNeg E_neg P * D * chiralProjNeg E_neg P := by noncomm_ring
    _ = 0 + chiralProjPos E_pos P * D * chiralProjNeg E_neg P +
        chiralProjNeg E_neg P * D * chiralProjPos E_pos P + 0 := by
        rw [chiralProjPos_dirac_zero hF hP, chiralProjNeg_dirac_zero hF hP]
    _ = chiralProjPos E_pos P * D * chiralProjNeg E_neg P +
        chiralProjNeg E_neg P * D * chiralProjPos E_pos P := by abel

/-- Strict Index-2 Nilpotence of the Backward Chiral Toeplitz Operator: (F_-)² = 0. -/
theorem chiralToeplitzNeg_sq_zero [Ring R] {D E_pos E_neg P : Matrix n n R}
    (hF : IsChiralFredholmModule D E_pos E_neg)
    (hP : IsEvenIdempotent P E_pos E_neg) :
    chiralToeplitzNeg D E_pos E_neg P * chiralToeplitzNeg D E_pos E_neg P = 0 := by
  have hOrth := orthogonal_chiralProj hF hP
  dsimp [chiralToeplitzNeg]
  calc
    (chiralProjPos E_pos P * D * chiralProjNeg E_neg P) *
      (chiralProjPos E_pos P * D * chiralProjNeg E_neg P)
      = chiralProjPos E_pos P * D *
        (chiralProjNeg E_neg P * chiralProjPos E_pos P) *
        D * chiralProjNeg E_neg P := by noncomm_ring
    _ = chiralProjPos E_pos P * D * 0 * D * chiralProjNeg E_neg P := by
        rw [hOrth.rev_eq_zero]
    _ = 0 := by noncomm_ring

/-- Strict Index-2 Nilpotence of the Forward Chiral Toeplitz Operator: (F_+)² = 0. -/
theorem chiralToeplitzPos_sq_zero [Ring R] {D E_pos E_neg P : Matrix n n R}
    (hF : IsChiralFredholmModule D E_pos E_neg)
    (hP : IsEvenIdempotent P E_pos E_neg) :
    chiralToeplitzPos D E_pos E_neg P * chiralToeplitzPos D E_pos E_neg P = 0 := by
  have hOrth := orthogonal_chiralProj hF hP
  dsimp [chiralToeplitzPos]
  calc
    (chiralProjNeg E_neg P * D * chiralProjPos E_pos P) *
      (chiralProjNeg E_neg P * D * chiralProjPos E_pos P)
      = chiralProjNeg E_neg P * D *
        (chiralProjPos E_pos P * chiralProjNeg E_neg P) *
        D * chiralProjPos E_pos P := by noncomm_ring
    _ = chiralProjNeg E_neg P * D * 0 * D * chiralProjPos E_pos P := by
        rw [hOrth.mul_eq_zero]
    _ = 0 := by noncomm_ring

/-- Anticommutator Factorization of the Squared Toeplitz Compression:
(P * D * P)² = F_- * F_+ + F_+ * F_-. -/
theorem toeplitzCompression_sq_eq_anticomm [Ring R] {D E_pos E_neg P : Matrix n n R}
    (hF : IsChiralFredholmModule D E_pos E_neg)
    (hP : IsEvenIdempotent P E_pos E_neg) :
    toeplitzCompression P D * toeplitzCompression P D =
    chiralToeplitzNeg D E_pos E_neg P * chiralToeplitzPos D E_pos E_neg P +
    chiralToeplitzPos D E_pos E_neg P * chiralToeplitzNeg D E_pos E_neg P := by
  rw [toeplitzCompression_eq_chiral_sum hF hP]
  calc
    (chiralToeplitzNeg D E_pos E_neg P + chiralToeplitzPos D E_pos E_neg P) *
      (chiralToeplitzNeg D E_pos E_neg P + chiralToeplitzPos D E_pos E_neg P)
      = chiralToeplitzNeg D E_pos E_neg P * chiralToeplitzNeg D E_pos E_neg P +
        chiralToeplitzNeg D E_pos E_neg P * chiralToeplitzPos D E_pos E_neg P +
        chiralToeplitzPos D E_pos E_neg P * chiralToeplitzNeg D E_pos E_neg P +
        chiralToeplitzPos D E_pos E_neg P * chiralToeplitzPos D E_pos E_neg P := by noncomm_ring
    _ = 0 +
        chiralToeplitzNeg D E_pos E_neg P * chiralToeplitzPos D E_pos E_neg P +
        chiralToeplitzPos D E_pos E_neg P * chiralToeplitzNeg D E_pos E_neg P + 0 := by
        rw [chiralToeplitzNeg_sq_zero hF hP, chiralToeplitzPos_sq_zero hF hP]
    _ = chiralToeplitzNeg D E_pos E_neg P * chiralToeplitzPos D E_pos E_neg P +
        chiralToeplitzPos D E_pos E_neg P * chiralToeplitzNeg D E_pos E_neg P := by abel

/-- Positive-Chirality Eigenvalue of F_- under γ = E_pos - E_neg:
(E_pos - E_neg) * F_- = F_-. -/
lemma grading_mul_chiralToeplitzNeg [Ring R] {D E_pos E_neg P : Matrix n n R}
    (hF : IsChiralFredholmModule D E_pos E_neg) :
    (E_pos - E_neg) * chiralToeplitzNeg D E_pos E_neg P =
    chiralToeplitzNeg D E_pos E_neg P := by
  dsimp [chiralToeplitzNeg, chiralProjPos]
  calc
    (E_pos - E_neg) * (E_pos * P * D * chiralProjNeg E_neg P)
      = ((E_pos * E_pos) - (E_neg * E_pos)) * P * D * chiralProjNeg E_neg P := by noncomm_ring
    _ = (E_pos - 0) * P * D * chiralProjNeg E_neg P := by
        rw [hF.idem_pos.idem, hF.orth_chiral.rev_eq_zero]
    _ = E_pos * P * D * chiralProjNeg E_neg P := by noncomm_ring

/-- Negative-Chirality Eigenvalue of F_+ under γ = E_pos - E_neg:
(E_pos - E_neg) * F_+ = -F_+. -/
lemma grading_mul_chiralToeplitzPos [Ring R] {D E_pos E_neg P : Matrix n n R}
    (hF : IsChiralFredholmModule D E_pos E_neg) :
    (E_pos - E_neg) * chiralToeplitzPos D E_pos E_neg P =
    - chiralToeplitzPos D E_pos E_neg P := by
  dsimp [chiralToeplitzPos, chiralProjNeg]
  calc
    (E_pos - E_neg) * (E_neg * P * D * chiralProjPos E_pos P)
      = ((E_pos * E_neg) - (E_neg * E_neg)) * P * D * chiralProjPos E_pos P := by noncomm_ring
    _ = (0 - E_neg) * P * D * chiralProjPos E_pos P := by
        rw [hF.orth_chiral.mul_eq_zero, hF.idem_neg.idem]
    _ = - (E_neg * P * D * chiralProjPos E_pos P) := by noncomm_ring

/-- Commutator Factorization of the Graded Squared Toeplitz Operator:
(E_pos - E_neg) * (P * D * P)² = [F_-, F_+]. -/
theorem grading_mul_toeplitz_sq_eq_commutator [Ring R] {D E_pos E_neg P : Matrix n n R}
    (hF : IsChiralFredholmModule D E_pos E_neg)
    (hP : IsEvenIdempotent P E_pos E_neg) :
    (E_pos - E_neg) * (toeplitzCompression P D * toeplitzCompression P D) =
    commutator (chiralToeplitzNeg D E_pos E_neg P) (chiralToeplitzPos D E_pos E_neg P) := by
  rw [toeplitzCompression_sq_eq_anticomm hF hP]
  dsimp [commutator]
  calc
    (E_pos - E_neg) *
      (chiralToeplitzNeg D E_pos E_neg P * chiralToeplitzPos D E_pos E_neg P +
       chiralToeplitzPos D E_pos E_neg P * chiralToeplitzNeg D E_pos E_neg P)
      = ((E_pos - E_neg) * chiralToeplitzNeg D E_pos E_neg P) *
        chiralToeplitzPos D E_pos E_neg P +
        ((E_pos - E_neg) * chiralToeplitzPos D E_pos E_neg P) *
        chiralToeplitzNeg D E_pos E_neg P := by noncomm_ring
    _ = chiralToeplitzNeg D E_pos E_neg P * chiralToeplitzPos D E_pos E_neg P +
        (- chiralToeplitzPos D E_pos E_neg P) * chiralToeplitzNeg D E_pos E_neg P := by
        rw [grading_mul_chiralToeplitzNeg hF, grading_mul_chiralToeplitzPos hF]
    _ = chiralToeplitzNeg D E_pos E_neg P * chiralToeplitzPos D E_pos E_neg P -
        chiralToeplitzPos D E_pos E_neg P * chiralToeplitzNeg D E_pos E_neg P := by noncomm_ring

/-!
### Archetype α₅: The Connes–Chern Index Pairing Formula & Three-Level Flag Partition
Causal Dependency: α₂, α₄ ≺ α₅
-/

/-- The graded even Connes cyclic 2-cocycle pairing
τ₂^γ(D; P) = tr(γ * P * [D, P]²). -/
def gradedConnesCocycle [CommRing R] (γ D P : Matrix n n R) : R :=
  Matrix.trace (γ * connesDensity D P)

/-- The Calderón–Fedosov analytical index of the chiral Toeplitz pair (F_+, F_-):
ind_FC(D, P) = tr((P_+ - F_- * F_+) - (P_- - F_+ * F_-)). -/
def fedosovAnalyticalIndex [CommRing R] (D E_pos E_neg P : Matrix n n R) : R :=
  Matrix.trace (fedosovIndexOperator D E_pos E_neg P)

/-- The McKean–Singer chiral supertrace index:
ind_ST(P) = tr(P_+) - tr(P_-). -/
def chiralSupertraceIndex [CommRing R] (E_pos E_neg P : Matrix n n R) : R :=
  Matrix.trace (chiralProjPos E_pos P) - Matrix.trace (chiralProjNeg E_neg P)

/-- Master Theorem 1 (Operator-Level Connes–Chern–Fedosov Index Identity):
In any chiral Z₂-graded Fredholm module (D, E_pos, E_neg) and even idempotent stratum P,
the negative graded Chern–Connes curvature density -(E_pos - E_neg) * P * [D, P]² is
identically equal as a matrix in M_n(R) to the Calderón–Fedosov local index operator
(P_+ - F_- * F_+) - (P_- - F_+ * F_-). -/
theorem operator_connes_chern_fedosov_identity [Ring R] {D E_pos E_neg P : Matrix n n R}
    (hF : IsChiralFredholmModule D E_pos E_neg)
    (hP : IsEvenIdempotent P E_pos E_neg) :
    - ((E_pos - E_neg) * connesDensity D P) =
    fedosovIndexOperator D E_pos E_neg P := by
  rw [connesDensity_eq_toeplitz_defect D P hF.toOdd hP.idem]
  have h_sub :
      - ((E_pos - E_neg) * (toeplitzCompression P D * toeplitzCompression P D - P)) =
      (E_pos - E_neg) * P -
      (E_pos - E_neg) * (toeplitzCompression P D * toeplitzCompression P D) := by
    noncomm_ring
  rw [h_sub,
      grading_mul_stratum_eq_chiral_diff E_pos E_neg P,
      grading_mul_toeplitz_sq_eq_commutator hF hP]
  dsimp [fedosovIndexOperator, commutator]
  noncomm_ring

/-- Master Theorem 2 (Operator-Level McKean–Singer Commutator Decomposition):
-(E_pos - E_neg) * P * [D, P]² = (P_+ - P_-) - [F_-, F_+]. -/
theorem operator_connes_chern_commutator_decomp [Ring R] {D E_pos E_neg P : Matrix n n R}
    (hF : IsChiralFredholmModule D E_pos E_neg)
    (hP : IsEvenIdempotent P E_pos E_neg) :
    - ((E_pos - E_neg) * connesDensity D P) =
    (chiralProjPos E_pos P - chiralProjNeg E_neg P) -
    commutator (chiralToeplitzNeg D E_pos E_neg P) (chiralToeplitzPos D E_pos E_neg P) := by
  rw [operator_connes_chern_fedosov_identity hF hP]
  dsimp [fedosovIndexOperator, commutator]
  noncomm_ring

/-- Master Theorem 3 (Abstract Fredholm Functional Index Pairing Formula):
For ANY additive functional τ : M_n(R) →+ R (including non-cyclically-trivial infinite
Fredholm trace functionals), the pairing of τ with the negative graded Chern–Connes
density equals the Calderón–Fedosov index τ(P_+ - F_- F_+) - τ(P_- - F_+ F_-). -/
theorem abstract_connes_chern_index_pairing [Ring R] (τ : Matrix n n R →+ R)
    {D E_pos E_neg P : Matrix n n R}
    (hF : IsChiralFredholmModule D E_pos E_neg)
    (hP : IsEvenIdempotent P E_pos E_neg) :
    τ (- ((E_pos - E_neg) * connesDensity D P)) =
    τ (chiralProjPos E_pos P -
        chiralToeplitzNeg D E_pos E_neg P * chiralToeplitzPos D E_pos E_neg P) -
    τ (chiralProjNeg E_neg P -
        chiralToeplitzPos D E_pos E_neg P * chiralToeplitzNeg D E_pos E_neg P) := by
  rw [operator_connes_chern_fedosov_identity hF hP]
  dsimp [fedosovIndexOperator]
  exact map_sub τ _ _

/-- Master Theorem 4 (The Connes–Chern–Fedosov Index Pairing Formula):
Over any commutative base ring R, the negative graded Connes cyclic 2-cocycle
-τ₂^γ(D; P) = -tr((E_pos - E_neg) * P * [D, P]²) equals both the Calderón–Fedosov
analytical index ind_FC(D, P) and the chiral supertrace index tr(P_+) - tr(P_-). -/
theorem connes_chern_index_pairing_formula [CommRing R] {D E_pos E_neg P : Matrix n n R}
    (hF : IsChiralFredholmModule D E_pos E_neg)
    (hP : IsEvenIdempotent P E_pos E_neg) :
    - gradedConnesCocycle (E_pos - E_neg) D P =
    fedosovAnalyticalIndex D E_pos E_neg P ∧
    fedosovAnalyticalIndex D E_pos E_neg P =
    chiralSupertraceIndex E_pos E_neg P := by
  refine ⟨?_, ?_⟩
  · dsimp [gradedConnesCocycle, fedosovAnalyticalIndex]
    rw [← Matrix.trace_neg, operator_connes_chern_fedosov_identity hF hP]
  · dsimp [fedosovAnalyticalIndex, chiralSupertraceIndex]
    have h_decomp :
        fedosovIndexOperator D E_pos E_neg P =
        (chiralProjPos E_pos P - chiralProjNeg E_neg P) -
        commutator (chiralToeplitzNeg D E_pos E_neg P) (chiralToeplitzPos D E_pos E_neg P) := by
      dsimp [fedosovIndexOperator, commutator]
      noncomm_ring
    rw [h_decomp, Matrix.trace_sub,
        trace_commutator_zero (chiralToeplitzNeg D E_pos E_neg P)
          (chiralToeplitzPos D E_pos E_neg P),
        sub_zero, Matrix.trace_sub]

/-- Direct Supertrace Form of the Connes–Chern Index Pairing Formula:
-τ₂^γ(D; P) = tr((E_pos - E_neg) * P). -/
theorem gradedConnesCocycle_eq_supertrace [CommRing R] {D E_pos E_neg P : Matrix n n R}
    (hF : IsChiralFredholmModule D E_pos E_neg)
    (hP : IsEvenIdempotent P E_pos E_neg) :
    - gradedConnesCocycle (E_pos - E_neg) D P =
    Matrix.trace ((E_pos - E_neg) * P) := by
  have h_pair := connes_chern_index_pairing_formula hF hP
  rw [h_pair.1, h_pair.2]
  dsimp [chiralSupertraceIndex]
  rw [← Matrix.trace_sub, ← grading_mul_stratum_eq_chiral_diff]

/-- Master Theorem 5 (Unconditional Three-Level Flag Connes–Chern Index Partition):
For any 3-level flag of even idempotent strata (P, G - P, M - G) in a chiral Fredholm
module (D, E_pos, E_neg), the sum of the negative graded Connes cyclic 2-cocycles across
all three strata equals the macro-stratum chiral supertrace index tr((E_pos - E_neg) * M)
for EVERY chiral Dirac operator D (without requiring [D, G] = 0 or [D, M] = 0). -/
theorem three_stratum_graded_index_partition [CommRing R]
    {D E_pos E_neg P G M : Matrix n n R}
    (hF : IsChiralFredholmModule D E_pos E_neg)
    (hP : IsEvenIdempotent P E_pos E_neg)
    (hGP : IsEvenIdempotent (G - P) E_pos E_neg)
    (hMG : IsEvenIdempotent (M - G) E_pos E_neg) :
    (- gradedConnesCocycle (E_pos - E_neg) D P) +
    (- gradedConnesCocycle (E_pos - E_neg) D (G - P)) +
    (- gradedConnesCocycle (E_pos - E_neg) D (M - G)) =
    Matrix.trace ((E_pos - E_neg) * M) := by
  rw [gradedConnesCocycle_eq_supertrace hF hP,
      gradedConnesCocycle_eq_supertrace hF hGP,
      gradedConnesCocycle_eq_supertrace hF hMG]
  rw [← Matrix.trace_add, ← Matrix.trace_add]
  have h_flag_sum :
      (E_pos - E_neg) * P + (E_pos - E_neg) * (G - P) + (E_pos - E_neg) * (M - G) =
      (E_pos - E_neg) * M := by
    noncomm_ring
  rw [h_flag_sum]

end NonCommutativeFredholmIndex
