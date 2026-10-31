/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic

/-!
# Peirce spine A₁–A₁₁: the tetraktys `(Φ, J, V, Σ)` and its inner-derivation spectra

Causal order inside this file:

* A₁ Leibniz/Jacobi laws of `comm`, `anticomm` (no idempotent needed);
* A₂ grading by `S = P - (1 - P)` and `ad_P³ = ad_P`;
* A₃ the multiplication table of `N₊, N₋, Φ, J, V, Σ`;
* A₄ sandwiches and the double-derivation trinity;
* A₅, A₁₀, A₁₁ spectra of `ad_Φ², ad_J², ad_Σ²` with operator-valued eigenvalues
  `V`, `V²`;
* A₆ the mixed ladders `ad_Φ ad_J`, `ad_J ad_Φ`;
* A₇ `sl₂`-type brackets; A₈ same-corner annihilation; A₉ Peirce block splits.

All eigenvalues are left multiplications by the mass `V` or `V²`, never scalars.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-! ### Superoperators -/

def derivSqPhi (P A C X : B) : B := -comm (genPhi P A C) (comm (genPhi P A C) X)
def derivSqJ (P A C X : B) : B := comm (genJ P A C) (comm (genJ P A C) X)
def derivSqSig (P A C X : B) : B := -comm (genSig P A C) (comm (genSig P A C) X)
def derivCasimir (P A C X : B) : B :=
  derivSqPhi P A C X + derivSqJ P A C X + derivSqSig P A C X

def projV (P A C X : B) : B := (8 : ℤ) • X + derivCasimir P A C X
def projPhi (P A C X : B) : B := derivSqPhi P A C X - derivSqJ P A C X - derivSqSig P A C X
def projJ (P A C X : B) : B := derivSqJ P A C X - derivSqPhi P A C X - derivSqSig P A C X
def projSig (P A C X : B) : B := derivSqSig P A C X - derivSqPhi P A C X - derivSqJ P A C X

def sandwichCross (P A C X : B) : B :=
  conePlus P A * X * coneMinus P C + coneMinus P C * X * conePlus P A
def sandwichSame (P A C X : B) : B :=
  conePlus P A * X * conePlus P A + coneMinus P C * X * coneMinus P C

def ladderMinus (P A C X : B) : B := comm (genPhi P A C) (comm (genJ P A C) X)
def ladderPlus (P A C X : B) : B := comm (genJ P A C) (comm (genPhi P A C) X)
def ladderSum (P A C X : B) : B := ladderMinus P A C X + ladderPlus P A C X

/-! ### A₁ -/

theorem archetype_A1_dual_leibniz_and_jacobi (H U V : B) :
    comm H (U * V) = comm H U * V + U * comm H V ∧
    comm H (U * V) = anticomm H U * V - U * anticomm H V ∧
    comm H (comm U V) + comm U (comm V H) + comm V (comm H U) = 0 ∧
    comm H (anticomm U V) - anticomm U (comm H V) = anticomm (comm H U) V ∧
    comm H (anticomm H U) = comm (H * H) U ∧
    anticomm H (comm H U) = comm (H * H) U := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (simp only [comm, anticomm]; noncomm_ring)

variable {P : B} (hP : P * P = P)
include hP

/-! ### A₂ -/

theorem archetype_A2_peirce_cartan_grading_and_tangent_closure (A C : B) :
    invS P * invS P = 1 ∧
    comm P (comm P A) = oddGrade P A ∧
    A - comm P (comm P A) = evenGrade P A ∧
    comm P (comm P (comm P A)) = comm P A ∧
    anticomm P (comm P A) = comm P A ∧
    comm P (comm P A * comm P C) = 0 ∧
    invS P * A * invS P = evenGrade P A - oddGrade P A := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-! ### A₃ -/

theorem archetype_A3_nilpotent_cones_and_tetraktys_table (A C : B) :
    conePlus P A * conePlus P A = 0 ∧
    coneMinus P C * coneMinus P C = 0 ∧
    genPhi P A C * genPhi P A C = genV P A C ∧
    genJ P A C * genJ P A C = -genV P A C ∧
    genPhi P A C * genPhi P A C + genJ P A C * genJ P A C = 0 ∧
    genJ P A C * genPhi P A C = genSig P A C ∧
    genPhi P A C * genJ P A C = -genSig P A C ∧
    anticomm (genPhi P A C) (genJ P A C) = 0 ∧
    genSig P A C = invS P * genV P A C ∧
    genV P A C = invS P * genSig P A C ∧
    genSig P A C * genSig P A C = genV P A C * genV P A C ∧
    comm (conePlus P A) (genV P A C) = 0 ∧
    comm (coneMinus P C) (genV P A C) = 0 ∧
    anticomm (conePlus P A) (genSig P A C) = 0 ∧
    anticomm (coneMinus P C) (genSig P A C) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-! ### A₄ -/

theorem archetype_A4_sandwich_complementarity_and_trinity (A C X : B) :
    sandwichCross P A C X + sandwichSame P A C X = genPhi P A C * X * genPhi P A C ∧
    sandwichCross P A C X - sandwichSame P A C X = -(genJ P A C * X * genJ P A C) ∧
    -(comm (conePlus P A) (comm (coneMinus P C) X) +
        comm (coneMinus P C) (comm (conePlus P A) X)) =
      (2 : ℤ) • sandwichCross P A C X - anticomm (genV P A C) X ∧
    (2 : ℤ) • ((2 : ℤ) • sandwichCross P A C X - anticomm (genV P A C) X) =
      derivSqPhi P A C X + derivSqJ P A C X ∧
    derivSqPhi P A C X - derivSqJ P A C X = (4 : ℤ) • sandwichSame P A C X ∧
    sandwichCross P A C (genV P A C) = genV P A C * genV P A C ∧
    sandwichCross P A C (genSig P A C) = -(genV P A C * genSig P A C) ∧
    sandwichCross P A C (genPhi P A C) = 0 ∧
    sandwichCross P A C (genJ P A C) = 0 ∧
    sandwichSame P A C (genV P A C) = 0 ∧
    sandwichSame P A C (genSig P A C) = 0 ∧
    sandwichSame P A C (genPhi P A C) = genV P A C * genPhi P A C ∧
    sandwichSame P A C (genJ P A C) = -(genV P A C * genJ P A C) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    ((try simp only [sandwichCross, sandwichSame, derivSqPhi, derivSqJ]); peirce_nf hP)

/-! ### A₅ -/

theorem archetype_A5_klein_hadamard_spectra_and_partition (A C X : B) :
    projV P A C X + projPhi P A C X + projJ P A C X + projSig P A C X = (8 : ℤ) • X ∧
    derivSqPhi P A C (genPhi P A C) = 0 ∧
    derivSqPhi P A C (genV P A C) = 0 ∧
    derivSqPhi P A C (genJ P A C) = -((4 : ℤ) • (genV P A C * genJ P A C)) ∧
    derivSqPhi P A C (genSig P A C) = -((4 : ℤ) • (genV P A C * genSig P A C)) ∧
    derivSqJ P A C (genJ P A C) = 0 ∧
    derivSqJ P A C (genV P A C) = 0 ∧
    derivSqJ P A C (genPhi P A C) = -((4 : ℤ) • (genV P A C * genPhi P A C)) ∧
    derivSqJ P A C (genSig P A C) = -((4 : ℤ) • (genV P A C * genSig P A C)) ∧
    derivSqSig P A C (genSig P A C) = 0 ∧
    derivSqSig P A C (genV P A C) = 0 ∧
    derivSqSig P A C (genPhi P A C) =
      -((4 : ℤ) • ((genV P A C * genV P A C) * genPhi P A C)) ∧
    derivSqSig P A C (genJ P A C) =
      -((4 : ℤ) • ((genV P A C * genV P A C) * genJ P A C)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    ((try simp only [projV, projPhi, projJ, projSig, derivCasimir, derivSqPhi, derivSqJ,
      derivSqSig]); peirce_nf hP)

/-! ### A₆ -/

theorem archetype_A6_superoperator_ladder_recursion (A C X : B) :
    ladderMinus P A C (genPhi P A C) = -((4 : ℤ) • (genV P A C * genJ P A C)) ∧
    ladderMinus P A C (genJ P A C) = 0 ∧
    ladderPlus P A C (genJ P A C) = (4 : ℤ) • (genV P A C * genPhi P A C) ∧
    ladderPlus P A C (genPhi P A C) = 0 ∧
    ladderMinus P A C (ladderMinus P A C (genPhi P A C)) = 0 ∧
    ladderPlus P A C (ladderPlus P A C (genJ P A C)) = 0 ∧
    ladderMinus P A C X - ladderPlus P A C X = -((2 : ℤ) • comm (genSig P A C) X) ∧
    ladderSum P A C (genV P A C) = 0 ∧
    ladderSum P A C (genSig P A C) = 0 ∧
    ladderSum P A C (ladderSum P A C (genPhi P A C)) =
      -((16 : ℤ) • ((genV P A C * genV P A C) * genPhi P A C)) ∧
    ladderSum P A C (ladderSum P A C (genJ P A C)) =
      -((16 : ℤ) • ((genV P A C * genV P A C) * genJ P A C)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    ((try simp only [ladderSum, ladderMinus, ladderPlus]); peirce_nf hP)

/-! ### A₇ -/

theorem archetype_A7_so12_lie_brackets_and_cubic_inversions (A C : B) :
    comm (genPhi P A C) (genJ P A C) = -((2 : ℤ) • genSig P A C) ∧
    comm (genSig P A C) (genPhi P A C) = (2 : ℤ) • (genV P A C * genJ P A C) ∧
    comm (genSig P A C) (genJ P A C) = (2 : ℤ) • (genV P A C * genPhi P A C) ∧
    comm (genSig P A C) (conePlus P A) = (2 : ℤ) • (genV P A C * conePlus P A) ∧
    comm (genSig P A C) (coneMinus P C) = -((2 : ℤ) • (genV P A C * coneMinus P C)) ∧
    genPhi P A C * conePlus P A * genPhi P A C = genV P A C * coneMinus P C ∧
    genPhi P A C * coneMinus P C * genPhi P A C = conePlus P A * genV P A C ∧
    genPhi P A C * genPhi P A C * genPhi P A C = genV P A C * genPhi P A C ∧
    genJ P A C * genJ P A C * genJ P A C = -(genV P A C * genJ P A C) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-! ### A₈ -/

theorem archetype_A8_same_cone_annihilation_and_superposition (A₁ A₂ C₁ C₂ : B) :
    conePlus P A₁ * conePlus P A₂ = 0 ∧
    coneMinus P C₁ * coneMinus P C₂ = 0 ∧
    comm (conePlus P A₁) (conePlus P A₂) = 0 ∧
    comm (coneMinus P C₁) (coneMinus P C₂) = 0 ∧
    genV P (A₁ + A₂) (C₁ + C₂) =
      genV P A₁ C₁ + genV P A₂ C₂ +
        (anticomm (conePlus P A₁) (coneMinus P C₂) +
          anticomm (conePlus P A₂) (coneMinus P C₁)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-! ### A₉ -/

theorem archetype_A9_peirce_block_diagonal_splits (A C X : B) :
    peirce11 P X + peirce00 P X + conePlus P X + coneMinus P X = X ∧
    peirce11 P (genV P A C) = conePlus P A * coneMinus P C ∧
    peirce00 P (genV P A C) = coneMinus P C * conePlus P A ∧
    peirce11 P (genSig P A C) = conePlus P A * coneMinus P C ∧
    peirce00 P (genSig P A C) = -(coneMinus P C * conePlus P A) ∧
    genV P A C + genSig P A C = (2 : ℤ) • (conePlus P A * coneMinus P C) ∧
    genV P A C - genSig P A C = (2 : ℤ) • (coneMinus P C * conePlus P A) ∧
    evenGrade P (genV P A C) = genV P A C ∧
    oddGrade P (genV P A C) = 0 ∧
    evenGrade P (genSig P A C) = genSig P A C ∧
    oddGrade P (genSig P A C) = 0 ∧
    evenGrade P (genPhi P A C) = 0 ∧
    oddGrade P (genPhi P A C) = genPhi P A C ∧
    evenGrade P (genJ P A C) = 0 ∧
    oddGrade P (genJ P A C) = genJ P A C := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [peirce11, peirce00, conePlus, coneMinus]; noncomm_ring
  all_goals peirce_nf hP

/-! ### Two-connection composition

The mixed term in a square is a Jordan cross term.  It cannot in general be
replaced by the commutator (curvature) cross term: the two carry different
Peirce-corner information.
-/

/-- The anticommutator of two `Φ` operators is the sum of their mixed
upper/lower Peirce contractions. -/
theorem twoPhi_anticomm_expansion (A₁ C₁ A₂ C₂ : B) :
    anticomm (genPhi P A₁ C₁) (genPhi P A₂ C₂) =
      anticomm (conePlus P A₁) (coneMinus P C₂) +
        anticomm (conePlus P A₂) (coneMinus P C₁) := by
  peirce_nf hP

/-- Ordered product formula for two symmetric boundary operators. -/
theorem twoPhi_mul_expansion (A₁ C₁ A₂ C₂ : B) :
    genPhi P A₁ C₁ * genPhi P A₂ C₂ =
      conePlus P A₁ * coneMinus P C₂ +
        coneMinus P C₁ * conePlus P A₂ := by
  peirce_nf hP

/-- The commutator of two `Φ` operators is the corresponding mixed
commutator, with the second connection entering with reversed order. -/
theorem twoPhi_comm_expansion (A₁ C₁ A₂ C₂ : B) :
    comm (genPhi P A₁ C₁) (genPhi P A₂ C₂) =
      comm (conePlus P A₁) (coneMinus P C₂) -
        comm (conePlus P A₂) (coneMinus P C₁) := by
  peirce_nf hP

/-- Correct mixed square for a symmetric first boundary operator and a
skew-signed second one. Its cross term is a difference of anticommutators. -/
theorem phi_add_j_square (A₁ C₁ A₂ C₂ : B) :
    (genPhi P A₁ C₁ + genJ P A₂ C₂) *
        (genPhi P A₁ C₁ + genJ P A₂ C₂) =
      genV P A₁ C₁ - genV P A₂ C₂ -
        (anticomm (conePlus P A₁) (coneMinus P C₂) -
          anticomm (conePlus P A₂) (coneMinus P C₁)) := by
  peirce_nf hP

/-- Elliptic sum square, with its mixed term written as the symmetric
two-connection Jordan pairing. -/
theorem twoPhi_sum_square (A₁ C₁ A₂ C₂ : B) :
    (genPhi P A₁ C₁ + genPhi P A₂ C₂) *
        (genPhi P A₁ C₁ + genPhi P A₂ C₂) =
      genV P A₁ C₁ + genV P A₂ C₂ +
        anticomm (conePlus P A₁) (coneMinus P C₂) +
          anticomm (conePlus P A₂) (coneMinus P C₁) := by
  peirce_nf hP

/-- The ordered product of two odd Peirce operators is even and therefore
commutes with the cut idempotent. -/
theorem twoPhi_mul_commutes_cut (A₁ C₁ A₂ C₂ : B) :
    comm P (genPhi P A₁ C₁ * genPhi P A₂ C₂) = 0 := by
  peirce_nf hP

/-- The symmetric Jordan pairing of two odd Peirce operators lies in the even
subalgebra and commutes with the cut idempotent. -/
theorem twoPhi_anticomm_commutes_cut (A₁ C₁ A₂ C₂ : B) :
    comm P (anticomm (genPhi P A₁ C₁) (genPhi P A₂ C₂)) = 0 := by
  peirce_nf hP

/-- The antisymmetric Lie pairing of two odd Peirce operators also lies in
the even subalgebra and commutes with the cut idempotent. -/
theorem twoPhi_comm_commutes_cut (A₁ C₁ A₂ C₂ : B) :
    comm P (comm (genPhi P A₁ C₁) (genPhi P A₂ C₂)) = 0 := by
  peirce_nf hP

/-- The sign-flip sum isolates the difference of the two diagonal quadratic
terms, without imposing commutativity on the ambient ring. -/
theorem phi_j_sign_flip_sum (A₁ C₁ A₂ C₂ : B) :
    (genPhi P A₁ C₁ + genJ P A₂ C₂) *
        (genPhi P A₁ C₁ + genJ P A₂ C₂) +
      (genPhi P A₁ C₁ - genJ P A₂ C₂) *
        (genPhi P A₁ C₁ - genJ P A₂ C₂) =
      (2 : ℤ) • (genV P A₁ C₁ - genV P A₂ C₂) := by
  peirce_nf hP

/-- The sign-flip difference isolates twice the mixed Jordan cross term.
This is the correction to the proposed commutator-curvature formula. -/
theorem phi_j_sign_flip_difference (A₁ C₁ A₂ C₂ : B) :
    (genPhi P A₁ C₁ + genJ P A₂ C₂) *
        (genPhi P A₁ C₁ + genJ P A₂ C₂) -
      (genPhi P A₁ C₁ - genJ P A₂ C₂) *
        (genPhi P A₁ C₁ - genJ P A₂ C₂) =
      (2 : ℤ) •
        (anticomm (coneMinus P C₁) (conePlus P A₂) -
          anticomm (conePlus P A₁) (coneMinus P C₂)) := by
  peirce_nf hP

/-! ### A₁₀ -/

theorem archetype_A10_casimir_and_superoperator_commutators (A C : B) :
    derivCasimir P A C (genV P A C) = 0 ∧
    derivCasimir P A C (genSig P A C) = -((8 : ℤ) • (genV P A C * genSig P A C)) ∧
    derivCasimir P A C (genPhi P A C) =
      -((4 : ℤ) • (genV P A C * genPhi P A C + (genV P A C * genV P A C) * genPhi P A C)) ∧
    derivCasimir P A C (genJ P A C) =
      -((4 : ℤ) • (genV P A C * genJ P A C + (genV P A C * genV P A C) * genJ P A C)) ∧
    ladderPlus P A C (ladderMinus P A C (genPhi P A C)) =
      -((16 : ℤ) • ((genV P A C * genV P A C) * genPhi P A C)) ∧
    ladderMinus P A C (ladderPlus P A C (genJ P A C)) =
      -((16 : ℤ) • ((genV P A C * genV P A C) * genJ P A C)) ∧
    derivSqPhi P A C (derivSqJ P A C (genPhi P A C)) = 0 ∧
    derivSqJ P A C (derivSqPhi P A C (genJ P A C)) = 0 ∧
    derivSqPhi P A C (derivSqJ P A C (genSig P A C)) =
      (16 : ℤ) • ((genV P A C * genV P A C) * genSig P A C) ∧
    derivSqJ P A C (derivSqPhi P A C (genSig P A C)) =
      (16 : ℤ) • ((genV P A C * genV P A C) * genSig P A C) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    ((try simp only [derivCasimir, derivSqPhi, derivSqJ, derivSqSig, ladderMinus, ladderPlus]);
      peirce_nf hP)

/-! ### A₁₁ -/

theorem archetype_A11_klein_hadamard_character_selection (A C : B) :
    projV P A C (genV P A C) = (8 : ℤ) • genV P A C ∧
    projPhi P A C (genV P A C) = 0 ∧
    projPhi P A C (genSig P A C) = 0 ∧
    projJ P A C (genV P A C) = 0 ∧
    projJ P A C (genSig P A C) = 0 ∧
    projSig P A C (genV P A C) = 0 ∧
    projSig P A C (genSig P A C) = (8 : ℤ) • (genV P A C * genSig P A C) ∧
    projV P A C (genSig P A C) = (8 : ℤ) • (genSig P A C - genV P A C * genSig P A C) ∧
    projPhi P A C (genPhi P A C) =
      (4 : ℤ) • (genV P A C * genPhi P A C + (genV P A C * genV P A C) * genPhi P A C) ∧
    projJ P A C (genJ P A C) =
      (4 : ℤ) • (genV P A C * genJ P A C + (genV P A C * genV P A C) * genJ P A C) ∧
    projPhi P A C (genJ P A C) =
      (4 : ℤ) • ((genV P A C * genV P A C) * genJ P A C - genV P A C * genJ P A C) ∧
    projJ P A C (genPhi P A C) =
      (4 : ℤ) • ((genV P A C * genV P A C) * genPhi P A C - genV P A C * genPhi P A C) ∧
    projSig P A C (genPhi P A C) =
      (4 : ℤ) • (genV P A C * genPhi P A C - (genV P A C * genV P A C) * genPhi P A C) ∧
    projSig P A C (genJ P A C) =
      (4 : ℤ) • (genV P A C * genJ P A C - (genV P A C * genV P A C) * genJ P A C) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    ((try simp only [projV, projPhi, projJ, projSig, derivCasimir, derivSqPhi, derivSqJ,
      derivSqSig]); peirce_nf hP)

end InfoGeometry.OperatorAlgebra.PeirceSpine
