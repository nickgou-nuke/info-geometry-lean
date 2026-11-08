/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Algebra.Module.NatInt

/-!
# Peirce spine A₁–A₁₁: the tetraktys `(Φ, J, V, Σ)` and its inner-derivation spectra

## i. Overview

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

## ii. Key results

- `archetype_A1_dual_leibniz_and_jacobi` through `archetype_A11_klein_hadamard_character_selection`
- `dressedPeirceProjector_idempotent`, `dressedPeirceProjector_socratic_identity`
- `internal_globular_boundary_squared_zero`, `coherator_weak_vs_strict_socratic_defect`,
  `constructive_elementary_expansion_word_and_commutator_shift`,
  `constructive_elementary_expansion_retraction_isomorphism`

## iii. Table of contents

- Superoperators & Archetypes A₁–A₁₁
- Dressed Peirce–Bruhat Projectors & Conjugation
- Constructive Elementary Expansion & Internal Globular Boundary

## iv. References

- Charles Sanders Peirce, *Linear Associative Algebra* (1881).
- Alexander Grothendieck, *Pursuing Stacks* (1983).

#### BUCKET 1: CLOSED FINITE THEOREMS
- `archetype_A1_dual_leibniz_and_jacobi`, `orthogonal_idempotent_difference_is_tripotent`,
  `three_corner_difference_square`, `difference_commutator_sandwich`,
  `genV_add_genSig_is_twice_upper_lower`, `genV_sub_genSig_is_twice_lower_upper`,
  `internal_globular_boundary_squared_zero`, `coherator_weak_vs_strict_socratic_defect`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
- `archetype_A2_peirce_cartan_grading_and_tangent_closure` through
  `archetype_A11_klein_hadamard_character_selection`, `comm_P_tripotent` through
  `constructive_elementary_expansion_retraction_isomorphism`.

#### BUCKET 3: OPEN CLOSURE DEBT
- None within this module (`0 sorry`, `0 admit`, `0 custom axioms`).
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-! ### Superoperators -/

/-- Negative squared inner derivation `-ad_Φ²(X) = -[Φ, [Φ, X]]`. -/
def derivSqPhi (P A C X : B) : B := -comm (genPhi P A C) (comm (genPhi P A C) X)
/-- Squared inner derivation `ad_J²(X) = [J, [J, X]]`. -/
def derivSqJ (P A C X : B) : B := comm (genJ P A C) (comm (genJ P A C) X)
/-- Negative squared inner derivation `-ad_Σ²(X) = -[Σ, [Σ, X]]`. -/
def derivSqSig (P A C X : B) : B := -comm (genSig P A C) (comm (genSig P A C) X)
/-- Total Tetraktys Casimir derivation `(-ad_Φ² + ad_J² - ad_Σ²)(X)`. -/
def derivCasimir (P A C X : B) : B :=
  derivSqPhi P A C X + derivSqJ P A C X + derivSqSig P A C X

/-- Klein–Hadamard character superoperator selecting the `V`-channel (`8 • X + derivCasimir`). -/
def projV (P A C X : B) : B := (8 : ℤ) • X + derivCasimir P A C X
/-- Klein–Hadamard character superoperator selecting the `Φ`-channel (`derivSqPhi - derivSqJ - derivSqSig`). -/
def projPhi (P A C X : B) : B := derivSqPhi P A C X - derivSqJ P A C X - derivSqSig P A C X
/-- Klein–Hadamard character superoperator selecting the `J`-channel (`derivSqJ - derivSqPhi - derivSqSig`). -/
def projJ (P A C X : B) : B := derivSqJ P A C X - derivSqPhi P A C X - derivSqSig P A C X
/-- Klein–Hadamard character superoperator selecting the `Σ`-channel (`derivSqSig - derivSqPhi - derivSqJ`). -/
def projSig (P A C X : B) : B := derivSqSig P A C X - derivSqPhi P A C X - derivSqJ P A C X

/-- Symmetric cross-corner Peirce sandwich `N₊ X N₋ + N₋ X N₊`. -/
def sandwichCross (P A C X : B) : B :=
  conePlus P A * X * coneMinus P C + coneMinus P C * X * conePlus P A
/-- Skew cross-corner Peirce sandwich `N₊ X N₋ - N₋ X N₊`. -/
def sandwichSkew (P A C X : B) : B :=
  conePlus P A * X * coneMinus P C - coneMinus P C * X * conePlus P A
/-- Same-corner Peirce sandwich `N₊ X N₊ + N₋ X N₋`. -/
def sandwichSame (P A C X : B) : B :=
  conePlus P A * X * conePlus P A + coneMinus P C * X * coneMinus P C

/-- Lowering mixed derivation ladder `[Φ, [J, X]]`. -/
def ladderMinus (P A C X : B) : B := comm (genPhi P A C) (comm (genJ P A C) X)
/-- Raising mixed derivation ladder `[J, [Φ, X]]`. -/
def ladderPlus (P A C X : B) : B := comm (genJ P A C) (comm (genPhi P A C) X)
/-- Symmetric mixed derivation ladder `[Φ, [J, X]] + [J, [Φ, X]]`. -/
def ladderSum (P A C X : B) : B := ladderMinus P A C X + ladderPlus P A C X

/-! ### A₁ -/

/-- **Archetype `A₁` (`archetype_A1_dual_leibniz_and_jacobi`)**:
Universal Leibniz, graded Leibniz, Jacobi, Poisson-derivation, and square-commutator identities
for `comm` and `anticomm` in any associative ring `[Ring B]`. -/
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

/-- **Archetype `A₂` (`archetype_A2_peirce_cartan_grading_and_tangent_closure`)**:
Peirce–Cartan grading involution `invS P * invS P = 1`, double-commutator grade projections,
tripotency `comm P (comm P (comm P A)) = comm P A`, and tangent product parity closure. -/
theorem archetype_A2_peirce_cartan_grading_and_tangent_closure (A C : B) :
    invS P * invS P = 1 ∧
    comm P (comm P A) = oddGrade P A ∧
    A - comm P (comm P A) = evenGrade P A ∧
    comm P (comm P (comm P A)) = comm P A ∧
    anticomm P (comm P A) = comm P A ∧
    comm P (comm P A * comm P C) = 0 ∧
    invS P * A * invS P = evenGrade P A - oddGrade P A := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- The commutator of two tangent directions generated by the idempotent
cut is diagonal: its commutator with the cut vanishes. This is the
Grassmannian curvature parity law, stated in the associative ring itself. -/
theorem peirce_tangent_commutator_is_even (A C : B) :
    comm P (comm (comm P A) (comm P C)) = 0 := by
  peirce_nf hP

/-! ### Three-corner realization of the tripotent contact shell -/

omit hP in
/-- The difference of two orthogonal idempotents is tripotent.  The third
orthogonal corner is not needed for this cubic identity. -/
theorem orthogonal_idempotent_difference_is_tripotent
    {Pplus Pminus : B}
    (hplus : Pplus * Pplus = Pplus)
    (hminus : Pminus * Pminus = Pminus)
    (horth₁ : Pplus * Pminus = 0)
    (horth₂ : Pminus * Pplus = 0) :
    (Pplus - Pminus) * (Pplus - Pminus) * (Pplus - Pminus) =
      Pplus - Pminus := by
  have hSq : (Pplus - Pminus) * (Pplus - Pminus) = Pplus + Pminus := by
    calc
      (Pplus - Pminus) * (Pplus - Pminus) =
          Pplus * Pplus - Pplus * Pminus - Pminus * Pplus + Pminus * Pminus := by
        noncomm_ring
      _ = Pplus + Pminus := by
        rw [hplus, horth₁, horth₂, hminus]
        noncomm_ring
  calc
    (Pplus - Pminus) * (Pplus - Pminus) * (Pplus - Pminus) =
        (Pplus + Pminus) * (Pplus - Pminus) := by rw [hSq]
    _ = Pplus * Pplus - Pplus * Pminus + Pminus * Pplus - Pminus * Pminus := by
      noncomm_ring
    _ = Pplus - Pminus := by
      rw [hplus, horth₁, horth₂, hminus]
      noncomm_ring

omit hP in
/-- In a three-corner unit partition, the square of the difference of the
outer idempotents is the support complementary to the middle corner. -/
theorem three_corner_difference_square
    {Pplus Pzero Pminus : B}
    (hplus : Pplus * Pplus = Pplus)
    (hminus : Pminus * Pminus = Pminus)
    (horth₁ : Pplus * Pminus = 0)
    (horth₂ : Pminus * Pplus = 0)
    (hsum : Pplus + Pzero + Pminus = 1) :
    (Pplus - Pminus) * (Pplus - Pminus) = 1 - Pzero := by
  calc
    (Pplus - Pminus) * (Pplus - Pminus) = Pplus + Pminus := by
      noncomm_ring [hplus, hminus, horth₁, horth₂]
    _ = 1 - Pzero := by rw [← hsum]; noncomm_ring

omit hP in
/-- The bilateral commutator sandwich of a difference is supported on its
two cross terms, with their order and signs explicit. -/
theorem difference_commutator_sandwich
    {Pplus Pminus : B}
    (hplus : Pplus * Pplus = Pplus)
    (hminus : Pminus * Pminus = Pminus)
    (horth₁ : Pplus * Pminus = 0)
    (horth₂ : Pminus * Pplus = 0)
    (X : B) :
    (Pplus - Pminus) *
        comm (Pplus - Pminus) X * (Pplus - Pminus) =
      -(Pplus * X * Pminus - Pminus * X * Pplus) -
        (Pplus * X * Pminus - Pminus * X * Pplus) := by
  have hSq : (Pplus - Pminus) * (Pplus - Pminus) = Pplus + Pminus := by
    calc
      (Pplus - Pminus) * (Pplus - Pminus) =
          Pplus * Pplus - Pplus * Pminus - Pminus * Pplus + Pminus * Pminus := by
        noncomm_ring
      _ = Pplus + Pminus := by
        rw [hplus, horth₁, horth₂, hminus]
        noncomm_ring
  calc
    (Pplus - Pminus) * comm (Pplus - Pminus) X * (Pplus - Pminus) =
        ((Pplus - Pminus) * (Pplus - Pminus)) * X * (Pplus - Pminus) -
          (Pplus - Pminus) * X * ((Pplus - Pminus) * (Pplus - Pminus)) := by
      dsimp [comm]
      noncomm_ring
    _ = (Pplus + Pminus) * X * (Pplus - Pminus) -
          (Pplus - Pminus) * X * (Pplus + Pminus) := by
      rw [hSq]
    _ = -(Pplus * X * Pminus - Pminus * X * Pplus) -
          (Pplus * X * Pminus - Pminus * X * Pplus) := by
      noncomm_ring

/-! ### A₃ -/

/-- **Archetype `A₃` (`archetype_A3_nilpotent_cones_and_tetraktys_table`)**:
Nilpotent Peirce corners `N₊² = N₋² = 0` and the complete Tetraktys multiplication table
of `(Φ, J, V, Σ)` over any associative ring `[Ring B]` with idempotent `P * P = P`. -/
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

/-- The Peirce diagonal projection loses the odd solder operator `Φ`, but
projecting its square recovers the full mass `V`.  This is the exact failure
of the diagonal projection to preserve this product, stated directly in the
associative ring without introducing a projection-valued wrapper. -/
theorem peirce_diagonal_product_defect_is_genV (A C : B) :
    (P * (genPhi P A C * genPhi P A C) * P +
        (1 - P) * (genPhi P A C * genPhi P A C) * (1 - P)) -
      (P * genPhi P A C * P + (1 - P) * genPhi P A C * (1 - P)) *
        (P * genPhi P A C * P + (1 - P) * genPhi P A C * (1 - P)) =
      genV P A C := by
  peirce_nf hP

omit hP in
/-- The sum of the Jordan mass and the Peirce commutator isolates the
upper-then-lower transition, with its order retained. -/
theorem genV_add_genSig_is_twice_upper_lower (A C : B) :
    genV P A C + genSig P A C =
      (2 : ℤ) • (conePlus P A * coneMinus P C) := by
  simp only [genV, genSig, anticomm, comm]
  noncomm_ring

omit hP in
/-- The difference of the Jordan mass and the Peirce commutator isolates the
lower-then-upper transition, with its order retained. -/
theorem genV_sub_genSig_is_twice_lower_upper (A C : B) :
    genV P A C - genSig P A C =
      (2 : ℤ) • (coneMinus P C * conePlus P A) := by
  simp only [genV, genSig, anticomm, comm]
  noncomm_ring

/-- Left action of the Peirce grading on the odd sum exchanges the sum and
difference generators. -/
theorem invS_mul_genPhi_eq_genJ (A C : B) :
    invS P * genPhi P A C = genJ P A C := by
  peirce_nf hP

/-- Left action of the Peirce grading on the odd difference exchanges the
difference and sum generators. -/
theorem invS_mul_genJ_eq_genPhi (A C : B) :
    invS P * genJ P A C = genPhi P A C := by
  peirce_nf hP

/-- Right action of the Peirce grading reverses the sign of the odd sum's
graded partner. -/
theorem genPhi_mul_invS_eq_neg_genJ (A C : B) :
    genPhi P A C * invS P = -genJ P A C := by
  peirce_nf hP

/-- Right action of the Peirce grading reverses the sign of the odd
difference's graded partner. -/
theorem genJ_mul_invS_eq_neg_genPhi (A C : B) :
    genJ P A C * invS P = -genPhi P A C := by
  peirce_nf hP

/-- The Peirce mass commutes with the solder generator.  This is an
operator-valued centrality statement inside the generated tetraktys, with no
commutativity assumption on the ambient ring. -/
theorem comm_genV_genPhi (A C : B) :
    comm (genV P A C) (genPhi P A C) = 0 := by
  peirce_nf hP

/-- The Peirce mass commutes with the seam generator in the ambient ring. -/
theorem comm_genV_genJ (A C : B) :
    comm (genV P A C) (genJ P A C) = 0 := by
  peirce_nf hP

/-- The Peirce mass commutes with the sheet-skew generator, completing its
centrality on the four-generator tetraktys. -/
theorem comm_genV_genSig (A C : B) :
    comm (genV P A C) (genSig P A C) = 0 := by
  peirce_nf hP

/-- The inner differential of the ordered chord-phase product vanishes:
`[P, Φ · [P, Φ]] = 0`. This is a ring-valued degree-two closure law, without
assuming a separate scalar differential-form carrier. -/
theorem peirce_adjoint_chord_two_form_is_closed (A C : B) :
    comm P (genPhi P A C * comm P (genPhi P A C)) = 0 := by
  peirce_nf hP

/-- The nested anticommutator/commutator expression has a universal ordered
normal form. In particular it is right multiplication by `V`, not the
crossed-corner sandwich `N₊ X N₋ + N₋ X N₊` in general. -/
theorem tetraktys_nested_bulk_expression (A C X : B) :
    anticomm (genV P A C) X -
        comm (genPhi P A C) (anticomm (genPhi P A C) X) =
      (2 : ℤ) • (X * genV P A C) := by
  have hPhiSq : genPhi P A C * genPhi P A C = genV P A C :=
    (archetype_A3_nilpotent_cones_and_tetraktys_table hP A C).2.2.1
  rw [← hPhiSq]
  simp only [anticomm, comm]
  noncomm_ring

/-! ### A₄ -/

/-- **Archetype `A₄` (`archetype_A4_sandwich_complementarity_and_trinity`)**:
Cross-corner and same-corner Peirce sandwiches (`sandwichCross`, `sandwichSame`) and the
double-derivation trinity linking `derivSqPhi` and `derivSqJ`. -/
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

/-- Archetype LXVIII Aharonov sign inversion for the symmetric cross-sheet
readout. Inserting the Peirce grading into the observable reverses the sign
relative to acting by the grading after the readout. The three unit-observable
specializations recover the spin dipole and the negative mass. -/
theorem archetype_LXVIII_aharonov_sign_inversion (A C X : B) :
    sandwichCross P A C (invS P * X) =
      -(invS P * sandwichCross P A C X) ∧
    invS P * sandwichCross P A C 1 = genSig P A C ∧
    sandwichCross P A C (invS P) = -genSig P A C ∧
    invS P * sandwichCross P A C (invS P) = -genV P A C := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    ((try simp only [sandwichCross, invS, genSig, genV, comm, anticomm]); peirce_nf hP)

/-- Archetype LXIX vertex-level form of the same sign inversion. The Higgs
vertex reverses sign when the Peirce grading is inserted between its two
chiral factors. This is an algebraic identity for every observable. -/
theorem archetype_LXIX_higgs_vertex_sign_inversion (A C X : B) :
    genPhi P A C * (invS P * X) * genPhi P A C =
      -(invS P * (genPhi P A C * X * genPhi P A C)) := by
  peirce_nf hP

/-! ### A₅ -/

/-- **Archetype `A₅` (`archetype_A5_klein_hadamard_spectra_and_partition`)**:
Partition of `8 • X` by `(projV, projPhi, projJ, projSig)` and the operator-valued eigenvalue
table of `(derivSqPhi, derivSqJ, derivSqSig)` on `(Φ, J, V, Σ)`. -/
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

/-- **Archetype `A₆` (`archetype_A6_superoperator_ladder_recursion`)**:
Mixed derivation ladder superoperators `ladderMinus`, `ladderPlus`, and `ladderSum` on `(Φ, J, V, Σ)`. -/
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

/-- The positive square of the doubled spin derivation, the final
LXXXI readout. It follows from the `ad_Σ²` eigenvalue in A₅; its scalar order
is made explicit rather than inferred from the physical “boost” description. -/
theorem archetype_A81_doubled_spin_derivation_positive_square (A C : B) :
    (2 : ℤ) • comm (genSig P A C)
        ((2 : ℤ) • comm (genSig P A C) (genPhi P A C)) =
      (16 : ℤ) • ((genV P A C * genV P A C) * genPhi P A C) := by
  rcases archetype_A5_klein_hadamard_spectra_and_partition
      (P := P) hP A C (genPhi P A C) with
    ⟨_, _, _, _, _, _, _, _, _, _, _, hSpectrum, _⟩
  have hDouble :
      comm (genSig P A C) (comm (genSig P A C) (genPhi P A C)) =
        (4 : ℤ) • ((genV P A C * genV P A C) * genPhi P A C) := by
    have hNeg := congrArg (fun Y : B => -Y) hSpectrum
    simpa [derivSqSig] using hNeg
  let adSig : B →+ B :=
    { toFun := comm (genSig P A C)
      map_zero' := by simp [comm]
      map_add' := by
        intro X Y
        simp only [comm, mul_add, add_mul]
        abel }
  have hScale :
      comm (genSig P A C)
          ((2 : ℤ) • comm (genSig P A C) (genPhi P A C)) =
        (2 : ℤ) • comm (genSig P A C)
          (comm (genSig P A C) (genPhi P A C)) := by
    change adSig ((2 : ℤ) • comm (genSig P A C) (genPhi P A C)) = _
    rw [map_zsmul]
    rfl
  rw [hScale, hDouble]
  abel

/-! ### A₇ -/

/-- **Archetype `A₇` (`archetype_A7_so12_lie_brackets_and_cubic_inversions`)**:
`𝔰𝔬(1,2)`-type Lie brackets of `(Φ, J, Σ)`, corner weight equations, and cubic inversions
`Φ N₊ Φ = V N₋`, `Φ N₋ Φ = N₊ V`, `Φ³ = V Φ`, and `J³ = -V J`. -/
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

/-- The cubic tripotency defects are exactly the failure of the mass
operator to act as the identity on the corresponding odd mode. Thus
`V² = V` alone does not erase these defects; the range equations
`V * Φ = Φ` and `V * J = J` are what the cubic laws require. -/
theorem tetraktys_tripotency_defect_readout (A C : B) :
    genPhi P A C * genPhi P A C * genPhi P A C - genPhi P A C =
      genV P A C * genPhi P A C - genPhi P A C ∧
    genJ P A C * genJ P A C * genJ P A C + genJ P A C =
      -(genV P A C * genJ P A C - genJ P A C) := by
  rcases archetype_A7_so12_lie_brackets_and_cubic_inversions
      (P := P) hP A C with ⟨_, _, _, _, _, _, _, hPhiCube, hJCube⟩
  exact ⟨by rw [hPhiCube], by rw [hJCube]; noncomm_ring⟩

/-- The nested bracket of the even commutator with either odd Peirce cone is
the corresponding cubic round trip. It is not universally a scalar multiple
of the cone itself. -/
theorem sigma_bracket_cones_as_cubic_round_trips (A C : B) :
    comm (genSig P A C) (conePlus P A) =
      (2 : ℤ) • (conePlus P A * coneMinus P C * conePlus P A) ∧
    comm (genSig P A C) (coneMinus P C) =
      -((2 : ℤ) • (coneMinus P C * conePlus P A * coneMinus P C)) := by
  refine ⟨?_, ?_⟩
  · dsimp [comm, genSig, conePlus, coneMinus]
    peirce_nf hP
  · dsimp [comm, genSig, conePlus, coneMinus]
    peirce_nf hP

/-- The even element `Σ` generates an inner derivation that preserves the
Peirce parity decomposition. This is the exact grading statement: its action
does not, by itself, imply ascent through finer grades. -/
theorem sigma_inner_derivation_preserves_peirce_parity (A C X : B) :
    evenGrade P (comm (genSig P A C) X) =
      comm (genSig P A C) (evenGrade P X) ∧
    oddGrade P (comm (genSig P A C) X) =
      comm (genSig P A C) (oddGrade P X) := by
  constructor <;>
    (simp only [evenGrade, oddGrade, genSig, comm, conePlus, coneMinus]; peirce_nf hP)

/-- For the two opposite Peirce cones, the Jordan interaction and the Lie
commutator vanish together. Thus a nonzero interaction has a nonzero chiral
commutator, and conversely. This is an algebraic equivalence, not a claim that
an arbitrary obstruction creates new grades or models a logical incompleteness
theorem. -/
theorem tetraktys_interaction_iff_chiral_obstruction (A C : B) :
    genV P A C = 0 ↔ genSig P A C = 0 := by
  have hPplus : P * genV P A C = conePlus P A * coneMinus P C := by
    peirce_nf hP
  have hCompplus : P * genSig P A C = conePlus P A * coneMinus P C := by
    peirce_nf hP
  have hCompminus : (1 - P) * genSig P A C =
      -(coneMinus P C * conePlus P A) := by
    peirce_nf hP
  have hVminus : (1 - P) * genV P A C = coneMinus P C * conePlus P A := by
    peirce_nf hP
  constructor
  · intro hV
    have hPlus : conePlus P A * coneMinus P C = 0 := by
      have h := congrArg (fun Z : B => P * Z) hV
      rw [hPplus] at h
      simpa using h
    have hMinus : coneMinus P C * conePlus P A = 0 := by
      have h := congrArg (fun Z : B => (1 - P) * Z) hV
      rw [hVminus] at h
      simpa using h
    simp only [genSig, comm, hPlus, hMinus, sub_zero]
  · intro hSig
    have hPlus : conePlus P A * coneMinus P C = 0 := by
      have h := congrArg (fun Z : B => P * Z) hSig
      rw [hCompplus] at h
      simpa using h
    have hMinus : coneMinus P C * conePlus P A = 0 := by
      have h := congrArg (fun Z : B => (1 - P) * Z) hSig
      rw [hCompminus] at h
      simpa using h
    simp only [genV, anticomm, hPlus, hMinus, zero_add]

/-! ### A₈ -/

/-- **Archetype `A₈` (`archetype_A8_same_cone_annihilation_and_superposition`)**:
Same-cone product and commutator annihilation (`N₊(A₁) N₊(A₂) = 0`, `N₋(C₁) N₋(C₂) = 0`)
and bilinear superposition of `genV P (A₁ + A₂) (C₁ + C₂)`. -/
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

/-- **Archetype `A₉` (`archetype_A9_peirce_block_diagonal_splits`)**:
Four-block Peirce resolution of `X`, diagonal projections `peirce11`/`peirce00` of `(V, Σ)`,
and even/odd grading parities of `(V, Σ, Φ, J)`. -/
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

/-- Equivalent form of `phi_add_j_square` written directly in terms of the mixed
quadratic Peirce metrics `genV P A₁ C₂` and `genV P A₂ C₁`, contrasting
against the false commutator-curvature claim in A83. -/
theorem phi_add_j_square_genV_form (A₁ C₁ A₂ C₂ : B) :
    (genPhi P A₁ C₁ + genJ P A₂ C₂) *
        (genPhi P A₁ C₁ + genJ P A₂ C₂) =
      (genV P A₁ C₁ - genV P A₂ C₂) -
        (genV P A₁ C₂ - genV P A₂ C₁) := by
  peirce_nf hP

/-- The commutator of `Φ₁` and `J₂` is minus the sum of the two mixed
chiral curvatures `genSig P A₁ C₂` and `genSig P A₂ C₁`. -/
theorem phi_j_comm_expansion (A₁ C₁ A₂ C₂ : B) :
    comm (genPhi P A₁ C₁) (genJ P A₂ C₂) =
      -(genSig P A₁ C₂ + genSig P A₂ C₁) := by
  peirce_nf hP

/-- Multiplying `Φ₁ + J₂` by its sign-flipped companion `Φ₁ - J₂` produces
the sum of the diagonal Peirce metrics plus the mixed chiral curvatures
`genSig P A₁ C₂ + genSig P A₂ C₁`. -/
theorem phi_add_j_mul_phi_sub_j (A₁ C₁ A₂ C₂ : B) :
    (genPhi P A₁ C₁ + genJ P A₂ C₂) *
        (genPhi P A₁ C₁ - genJ P A₂ C₂) =
      genV P A₁ C₁ + genV P A₂ C₂ +
        (genSig P A₁ C₂ + genSig P A₂ C₁) := by
  peirce_nf hP

/-! ### A₁₀ -/

/-- **Archetype `A₁₀` (`archetype_A10_casimir_and_superoperator_commutators`)**:
Total Casimir derivation action on `(V, Σ, Φ, J)` and composed ladder/derivation identities. -/
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

/-- **Archetype `A₁₁` (`archetype_A11_klein_hadamard_character_selection`)**:
Klein–Hadamard character selection identities for `(projV, projPhi, projJ, projSig)` on `(V, Σ, Φ, J)`. -/
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

/-! ### Maurer–Cartan Double-Commutator Grading & Multiplicative Defect (`𝔎₁–𝔎₆`) -/

/-- The inner derivation `comm P` of an idempotent `P * P = P` is tripotent:
`[P, [P, [P, X]]] = [P, X]`. -/
theorem comm_P_tripotent (X : B) :
    comm P (comm P (comm P X)) = comm P X := by
  peirce_nf hP

/-- The even Peirce grade is `1 - (ad_P)²`: `evenGrade P X = X - [P, [P, X]]`. -/
theorem evenGrade_eq_sub_double_comm (X : B) :
    evenGrade P X = X - comm P (comm P X) := by
  peirce_nf hP

/-- The odd Peirce grade is `(ad_P)²`: `oddGrade P X = [P, [P, X]]`. -/
theorem oddGrade_eq_double_comm (X : B) :
    oddGrade P X = comm P (comm P X) := by
  peirce_nf hP

/-- Idempotence of the even Peirce grade `evenGrade P`. -/
theorem evenGrade_idem (X : B) :
    evenGrade P (evenGrade P X) = evenGrade P X := by
  peirce_nf hP

/-- Idempotence of the odd Peirce grade `oddGrade P`. -/
theorem oddGrade_idem (X : B) :
    oddGrade P (oddGrade P X) = oddGrade P X := by
  peirce_nf hP

/-- Mutual orthogonality `evenGrade P (oddGrade P X) = 0`. -/
theorem evenGrade_oddGrade (X : B) :
    evenGrade P (oddGrade P X) = 0 := by
  peirce_nf hP

/-- Mutual orthogonality `oddGrade P (evenGrade P X) = 0`. -/
theorem oddGrade_evenGrade (X : B) :
    oddGrade P (evenGrade P X) = 0 := by
  peirce_nf hP

/-- Linear annihilation of `comm P X` by `evenGrade P`. -/
theorem evenGrade_comm_P (X : B) :
    evenGrade P (comm P X) = 0 := by
  peirce_nf hP

/-- Fixed-point preservation of `comm P X` under `oddGrade P`. -/
theorem oddGrade_comm_P (X : B) :
    oddGrade P (comm P X) = comm P X := by
  peirce_nf hP

/-- Vanishing of `comm P` on `evenGrade P X`. -/
theorem comm_P_evenGrade (X : B) :
    comm P (evenGrade P X) = 0 := by
  peirce_nf hP

omit hP in
/-- Division-free chiral involution conjugation formula for `evenGrade P`:
`(2 : ℤ) • evenGrade P X = X + invS P * X * invS P`. -/
theorem two_zsmul_evenGrade_eq_invS_conj (X : B) :
    (2 : ℤ) • evenGrade P X = X + invS P * X * invS P := by
  unfold evenGrade invS
  noncomm_ring

omit hP in
/-- Division-free chiral involution conjugation formula for `oddGrade P`:
`(2 : ℤ) • oddGrade P X = X - invS P * X * invS P`. -/
theorem two_zsmul_oddGrade_eq_invS_conj (X : B) :
    (2 : ℤ) • oddGrade P X = X - invS P * X * invS P := by
  unfold oddGrade invS
  noncomm_ring

/-- Division-free double-commutator of `invS P` for `evenGrade P`:
`(4 : ℤ) • evenGrade P X = (4 : ℤ) • X - [invS P, [invS P, X]]`. -/
theorem four_zsmul_evenGrade_eq_sub_double_comm_invS (X : B) :
    (4 : ℤ) • evenGrade P X = (4 : ℤ) • X - comm (invS P) (comm (invS P) X) := by
  peirce_nf hP

/-- Division-free double-commutator of `invS P` for `oddGrade P`:
`(4 : ℤ) • oddGrade P X = [invS P, [invS P, X]]`. -/
theorem four_zsmul_oddGrade_eq_double_comm_invS (X : B) :
    (4 : ℤ) • oddGrade P X = comm (invS P) (comm (invS P) X) := by
  peirce_nf hP

/-- Exact multiplicative defect of `evenGrade P`:
`evenGrade P (X * Y) - evenGrade P X * evenGrade P Y = oddGrade P X * oddGrade P Y`. -/
theorem evenGrade_mul_defect_eq_oddGrade_mul (X Y : B) :
    evenGrade P (X * Y) - evenGrade P X * evenGrade P Y =
      oddGrade P X * oddGrade P Y := by
  peirce_nf hP

/-- Multiplicative defect of `evenGrade P` on `(conePlus P A, coneMinus P C)` equals
`conePlus P A * coneMinus P C`. -/
theorem evenGrade_mul_defect_conePlus_coneMinus (A C : B) :
    evenGrade P (conePlus P A * coneMinus P C) -
      evenGrade P (conePlus P A) * evenGrade P (coneMinus P C) =
      conePlus P A * coneMinus P C := by
  peirce_nf hP

/-- Multiplicative defect of `evenGrade P` on `(coneMinus P C, conePlus P A)` equals
`coneMinus P C * conePlus P A`. -/
theorem evenGrade_mul_defect_coneMinus_conePlus (A C : B) :
    evenGrade P (coneMinus P C * conePlus P A) -
      evenGrade P (coneMinus P C) * evenGrade P (conePlus P A) =
      coneMinus P C * conePlus P A := by
  peirce_nf hP

/-- Multiplicative defect of `evenGrade P` on `(genPhi P A C, genPhi P A C)` equals `genV P A C`. -/
theorem evenGrade_mul_defect_genPhi_sq (A C : B) :
    evenGrade P (genPhi P A C * genPhi P A C) -
      evenGrade P (genPhi P A C) * evenGrade P (genPhi P A C) =
      genV P A C := by
  peirce_nf hP

/-- Multiplicative defect of `evenGrade P` on `(-genJ P A C, genJ P A C)` equals `genV P A C`. -/
theorem evenGrade_mul_defect_neg_genJ_genJ (A C : B) :
    evenGrade P (-genJ P A C * genJ P A C) -
      evenGrade P (-genJ P A C) * evenGrade P (genJ P A C) =
      genV P A C := by
  peirce_nf hP

/-- Multiplicative defect of `evenGrade P` on `(genJ P A C, genPhi P A C)` equals `genSig P A C`. -/
theorem evenGrade_mul_defect_genJ_genPhi (A C : B) :
    evenGrade P (genJ P A C * genPhi P A C) -
      evenGrade P (genJ P A C) * evenGrade P (genPhi P A C) =
      genSig P A C := by
  peirce_nf hP

/-- Even-odd Lie brackets are purely odd: `evenGrade P [evenGrade P X, oddGrade P Y] = 0`. -/
theorem evenGrade_comm_evenGrade_oddGrade (X Y : B) :
    evenGrade P (comm (evenGrade P X) (oddGrade P Y)) = 0 := by
  peirce_nf hP

/-- Odd-even Lie brackets are purely odd: `evenGrade P [oddGrade P Y, evenGrade P X] = 0`. -/
theorem evenGrade_comm_oddGrade_evenGrade (X Y : B) :
    evenGrade P (comm (oddGrade P Y) (evenGrade P X)) = 0 := by
  peirce_nf hP

/-- Even-even Lie brackets are purely even: `oddGrade P [evenGrade P X, evenGrade P Y] = 0`. -/
theorem oddGrade_comm_evenGrade_evenGrade (X Y : B) :
    oddGrade P (comm (evenGrade P X) (evenGrade P Y)) = 0 := by
  peirce_nf hP

/-- Odd-odd Lie brackets are purely even: `oddGrade P [oddGrade P X, oddGrade P Y] = 0`. -/
theorem oddGrade_comm_oddGrade_oddGrade (X Y : B) :
    oddGrade P (comm (oddGrade P X) (oddGrade P Y)) = 0 := by
  peirce_nf hP

/-- Applying `evenGrade P` to the commutator of two Cartan-decomposed connections isolates the
pure gauge curvature plus the transvection curvature:
`evenGrade P [evenGrade P X₁ + oddGrade P Y₁, evenGrade P X₂ + oddGrade P Y₂] =
 [evenGrade P X₁, evenGrade P X₂] + [oddGrade P Y₁, oddGrade P Y₂]`. -/
theorem evenGrade_cartan_commutator_isolation (X₁ Y₁ X₂ Y₂ : B) :
    evenGrade P (comm (evenGrade P X₁ + oddGrade P Y₁) (evenGrade P X₂ + oddGrade P Y₂)) =
      comm (evenGrade P X₁) (evenGrade P X₂) + comm (oddGrade P Y₁) (oddGrade P Y₂) := by
  peirce_nf hP

/-- Applying `oddGrade P` to the commutator of two Cartan-decomposed connections isolates the
Élie Cartan covariant torsion cross-brackets:
`oddGrade P [evenGrade P X₁ + oddGrade P Y₁, evenGrade P X₂ + oddGrade P Y₂] =
 [evenGrade P X₁, oddGrade P Y₂] + [oddGrade P Y₁, evenGrade P X₂]`. -/
theorem oddGrade_cartan_torsion_isolation (X₁ Y₁ X₂ Y₂ : B) :
    oddGrade P (comm (evenGrade P X₁ + oddGrade P Y₁) (evenGrade P X₂ + oddGrade P Y₂)) =
      comm (evenGrade P X₁) (oddGrade P Y₂) + comm (oddGrade P Y₁) (evenGrade P X₂) := by
  peirce_nf hP

/-! ### Einstein–Cartan Chiral Anomaly, Spin Frame Dragging & Jordan Associator (`𝔈₁–𝔈₈`) -/

/-- Left multiplication of `comm (genPhi P A C) (genJ P A C)` by `invS P` yields `-2 • genV P A C`. -/
theorem invS_mul_comm_genPhi_genJ (A C : B) :
    invS P * comm (genPhi P A C) (genJ P A C) = -((2 : ℤ) • genV P A C) := by
  peirce_nf hP

/-- Right multiplication of `comm (genPhi P A C) (genJ P A C)` by `invS P` yields `-2 • genV P A C`. -/
theorem comm_genPhi_genJ_mul_invS (A C : B) :
    comm (genPhi P A C) (genJ P A C) * invS P = -((2 : ℤ) • genV P A C) := by
  peirce_nf hP

/-- Chiral duality `invS P * genSig P A C = genV P A C`. -/
theorem invS_mul_genSig_eq_genV (A C : B) :
    invS P * genSig P A C = genV P A C := by
  peirce_nf hP

/-- Chiral duality `genSig P A C * invS P = genV P A C`. -/
theorem genSig_mul_invS_eq_genV (A C : B) :
    genSig P A C * invS P = genV P A C := by
  peirce_nf hP

/-- Chiral duality `invS P * genV P A C = genSig P A C`. -/
theorem invS_mul_genV_eq_genSig (A C : B) :
    invS P * genV P A C = genSig P A C := by
  peirce_nf hP

/-- Chiral duality `genV P A C * invS P = genSig P A C`. -/
theorem genV_mul_invS_eq_genSig (A C : B) :
    genV P A C * invS P = genSig P A C := by
  peirce_nf hP

/-- Spin frame-dragging law for `genPhi P A C` under the Einstein–Cartan spin connection
`P + genSig P A C`:
`comm (P + genSig P A C) (genPhi P A C) = genJ P A C + (2 : ℤ) • (genV P A C * genJ P A C)`. -/
theorem comm_P_add_genSig_genPhi (A C : B) :
    comm (P + genSig P A C) (genPhi P A C) =
      genJ P A C + (2 : ℤ) • (genV P A C * genJ P A C) := by
  peirce_nf hP

/-- Spin frame-dragging law for `genJ P A C` under the Einstein–Cartan spin connection
`P + genSig P A C`:
`comm (P + genSig P A C) (genJ P A C) = genPhi P A C + (2 : ℤ) • (genV P A C * genPhi P A C)`. -/
theorem comm_P_add_genSig_genJ (A C : B) :
    comm (P + genSig P A C) (genJ P A C) =
      genPhi P A C + (2 : ℤ) • (genV P A C * genPhi P A C) := by
  peirce_nf hP

/-- Square of the dressed torsion `comm (P + genSig P A C) (genPhi P A C)`:
`T * T = -V - 4 • V² - 4 • V³`. -/
theorem comm_P_add_genSig_dressed_torsion_sq (A C : B) :
    comm (P + genSig P A C) (genPhi P A C) * comm (P + genSig P A C) (genPhi P A C) =
      -genV P A C - (4 : ℤ) • (genV P A C * genV P A C) -
        (4 : ℤ) • (genV P A C * genV P A C * genV P A C) := by
  peirce_nf hP

/-- Soldered Cartan–Ehresmann commutator split:
`[Σ + Φ, Σ + J] = -2 • Σ + 2 • (V * (Φ - J))`. -/
theorem comm_soldered_genSig_genPhi_genJ (A C : B) :
    comm (genSig P A C + genPhi P A C) (genSig P A C + genJ P A C) =
      -((2 : ℤ) • genSig P A C) +
        (2 : ℤ) • (genV P A C * (genPhi P A C - genJ P A C)) := by
  peirce_nf hP

/-- Even-grade component of the soldered Cartan–Ehresmann commutator:
`evenGrade P [Σ + Φ, Σ + J] = -2 • Σ`. -/
theorem evenGrade_comm_soldered_genSig_genPhi_genJ (A C : B) :
    evenGrade P (comm (genSig P A C + genPhi P A C) (genSig P A C + genJ P A C)) =
      -((2 : ℤ) • genSig P A C) := by
  peirce_nf hP

/-- Odd-grade component of the soldered Cartan–Ehresmann commutator:
`oddGrade P [Σ + Φ, Σ + J] = 2 • (V * (Φ - J))`. -/
theorem oddGrade_comm_soldered_genSig_genPhi_genJ (A C : B) :
    oddGrade P (comm (genSig P A C + genPhi P A C) (genSig P A C + genJ P A C)) =
      (2 : ℤ) • (genV P A C * (genPhi P A C - genJ P A C)) := by
  peirce_nf hP

omit hP in
/-- Universal identity over any `[Ring B]` expressing the anticommutator associator as a nested
commutator: `{{X, Y}, Z} - {X, {Y, Z}} = [Y, [X, Z]]`. -/
theorem anticomm_associator_eq_comm_comm (X Y Z : B) :
    anticomm (anticomm X Y) Z - anticomm X (anticomm Y Z) =
      comm Y (comm X Z) := by
  unfold anticomm comm
  noncomm_ring

/-- Jordan associator of `(coneMinus P C, conePlus P A, conePlus P A)`:
`{{N_-, N_+}, N_+} - {N_-, {N_+, N_+}} = (2 : ℤ) • (genV P A C * conePlus P A)`. -/
theorem jordan_associator_coneMinus_conePlus (A C : B) :
    anticomm (anticomm (coneMinus P C) (conePlus P A)) (conePlus P A) -
      anticomm (coneMinus P C) (anticomm (conePlus P A) (conePlus P A)) =
      (2 : ℤ) • (genV P A C * conePlus P A) := by
  peirce_nf hP

/-- Dual Jordan associator of `(conePlus P A, coneMinus P C, coneMinus P C)`:
`{{N_+, N_-}, N_-} - {N_+, {N_-, N_-}} = (2 : ℤ) • (genV P A C * coneMinus P C)`. -/
theorem jordan_associator_conePlus_coneMinus (A C : B) :
    anticomm (anticomm (conePlus P A) (coneMinus P C)) (coneMinus P C) -
      anticomm (conePlus P A) (anticomm (coneMinus P C) (coneMinus P C)) =
      (2 : ℤ) • (genV P A C * coneMinus P C) := by
  peirce_nf hP

/-! ### Orthogonal Clifford Triad, Lichnerowicz Square, Bruhat Cubic Defect & Modular Uncertainty (`𝔚𝔊₂₂–𝔚𝔊₂₉`) -/

/-- Exact Clifford orthogonality of `genPhi P A C` and `genSig P A C`:
`anticomm (genPhi P A C) (genSig P A C) = 0`. -/
theorem anticomm_genPhi_genSig (A C : B) :
    anticomm (genPhi P A C) (genSig P A C) = 0 := by
  peirce_nf hP

/-- Exact Clifford orthogonality of `genJ P A C` and `genSig P A C`:
`anticomm (genJ P A C) (genSig P A C) = 0`. -/
theorem anticomm_genJ_genSig (A C : B) :
    anticomm (genJ P A C) (genSig P A C) = 0 := by
  peirce_nf hP

/-- Exact Clifford orthogonality of `genPhi P A C` and `genJ P A C`:
`anticomm (genPhi P A C) (genJ P A C) = 0`. -/
theorem anticomm_genPhi_genJ (A C : B) :
    anticomm (genPhi P A C) (genJ P A C) = 0 := by
  peirce_nf hP

/-- Spacelike Cartan–Gödel Lichnerowicz square (`𝔚𝔊₂₂`):
`(genPhi P A C + genSig P A C)² = genV P A C + genV P A C * genV P A C`. -/
theorem genPhi_add_genSig_sq (A C : B) :
    (genPhi P A C + genSig P A C) * (genPhi P A C + genSig P A C) =
      genV P A C + genV P A C * genV P A C := by
  peirce_nf hP

/-- Timelike Cartan–Gödel Lichnerowicz square (`𝔚𝔊₂₂`):
`(genJ P A C + genSig P A C)² = -genV P A C + genV P A C * genV P A C`. -/
theorem genJ_add_genSig_sq (A C : B) :
    (genJ P A C + genSig P A C) * (genJ P A C + genSig P A C) =
      -genV P A C + genV P A C * genV P A C := by
  peirce_nf hP

/-- Outward Gödel lightlike horizon Lichnerowicz square (`𝔚𝔊₂₂` / `𝔚𝔊₂₅`):
`(genPhi P A C + genJ P A C + genSig P A C)² = genV P A C * genV P A C`. -/
theorem genPhi_add_genJ_add_genSig_sq (A C : B) :
    (genPhi P A C + genJ P A C + genSig P A C) *
      (genPhi P A C + genJ P A C + genSig P A C) =
      genV P A C * genV P A C := by
  peirce_nf hP

/-- Inward Gödel lightlike horizon Lichnerowicz square (`𝔚𝔊₂₂` / `𝔚𝔊₂₅`):
`(genPhi P A C - genJ P A C + genSig P A C)² = genV P A C * genV P A C`. -/
theorem genPhi_sub_genJ_add_genSig_sq (A C : B) :
    (genPhi P A C - genJ P A C + genSig P A C) *
      (genPhi P A C - genJ P A C + genSig P A C) =
      genV P A C * genV P A C := by
  peirce_nf hP

/-- Bichiral Bruhat midpoint cubic defect (`𝔚𝔊₁₄` / `𝔚𝔊₂₆`): for the two opposite-order Bruhat
dressed Peirce projectors
`P_+ = (1 - N_+) * (1 + N_-) * P * (1 - N_-) * (1 + N_+) = P + Φ - Σ - V * N_+` and
`P_- = (1 + N_-) * (1 - N_+) * P * (1 + N_+) * (1 - N_-) = P + Φ - Σ - V * N_-`,
the Jordan anticommutator minus their sum equals the cubic Casimir defect
`V³ = genV P A C * genV P A C * genV P A C`. -/
theorem bichiral_bruhat_midpoint_cubic_defect (A C : B) :
    anticomm
      ((1 - conePlus P A) * (1 + coneMinus P C) * P * (1 - coneMinus P C) * (1 + conePlus P A))
      ((1 + coneMinus P C) * (1 - conePlus P A) * P * (1 + conePlus P A) * (1 - coneMinus P C)) -
    (((1 - conePlus P A) * (1 + coneMinus P C) * P * (1 - coneMinus P C) * (1 + conePlus P A)) +
     ((1 + coneMinus P C) * (1 - conePlus P A) * P * (1 + conePlus P A) * (1 - coneMinus P C))) =
      genV P A C * genV P A C * genV P A C := by
  peirce_nf hP

/-- Modular uncertainty derivation proportionality on `genPhi P A C` (`𝔚𝔊₂₈`):
`comm (genSig P A C) (genPhi P A C) = genV P A C * comm (invS P) (genPhi P A C)`. -/
theorem comm_genSig_genPhi_eq_genV_mul_comm_invS_genPhi (A C : B) :
    comm (genSig P A C) (genPhi P A C) =
      genV P A C * comm (invS P) (genPhi P A C) := by
  peirce_nf hP

/-- Modular uncertainty derivation proportionality on `genJ P A C` (`𝔚𝔊₂₈`):
`comm (genSig P A C) (genJ P A C) = genV P A C * comm (invS P) (genJ P A C)`. -/
theorem comm_genSig_genJ_eq_genV_mul_comm_invS_genJ (A C : B) :
    comm (genSig P A C) (genJ P A C) =
      genV P A C * comm (invS P) (genJ P A C) := by
  peirce_nf hP

/-- Modular uncertainty derivation proportionality on `conePlus P A` (`𝔚𝔊₂₈`):
`comm (genSig P A C) (conePlus P A) = genV P A C * comm (invS P) (conePlus P A)`. -/
theorem comm_genSig_conePlus_eq_genV_mul_comm_invS_conePlus (A C : B) :
    comm (genSig P A C) (conePlus P A) =
      genV P A C * comm (invS P) (conePlus P A) := by
  peirce_nf hP

/-- Modular uncertainty derivation proportionality on `coneMinus P C` (`𝔚𝔊₂₈`):
`comm (genSig P A C) (coneMinus P C) = genV P A C * comm (invS P) (coneMinus P C)`. -/
theorem comm_genSig_coneMinus_eq_genV_mul_comm_invS_coneMinus (A C : B) :
    comm (genSig P A C) (coneMinus P C) =
      genV P A C * comm (invS P) (coneMinus P C) := by
  peirce_nf hP

/-! ### Double-Commutator Goldstone/Vortex Mass Spectrum & Operator GMOR Identities (`χ₃`, `χ₆`) -/

/-- Goldstone zero-mode identity for `genPhi P A C`:
`comm (genPhi P A C) (comm (genPhi P A C) (genPhi P A C)) = 0`. -/
theorem comm_genPhi_comm_genPhi_genPhi (A C : B) :
    comm (genPhi P A C) (comm (genPhi P A C) (genPhi P A C)) = 0 := by
  peirce_nf hP

/-- Radial metric commutativity under `ad_{genPhi}²`:
`comm (genPhi P A C) (comm (genPhi P A C) (genV P A C)) = 0`. -/
theorem comm_genPhi_comm_genPhi_genV (A C : B) :
    comm (genPhi P A C) (comm (genPhi P A C) (genV P A C)) = 0 := by
  peirce_nf hP

/-- Dynamical axial mass-squared eigenvalue `4 • genV P A C` on `genJ P A C`:
`comm (genPhi P A C) (comm (genPhi P A C) (genJ P A C)) = (4 : ℤ) • (genV P A C * genJ P A C)`. -/
theorem comm_genPhi_comm_genPhi_genJ (A C : B) :
    comm (genPhi P A C) (comm (genPhi P A C) (genJ P A C)) =
      (4 : ℤ) • (genV P A C * genJ P A C) := by
  peirce_nf hP

/-- Dynamical vortex mass-squared eigenvalue `4 • genV P A C` on `genSig P A C`:
`comm (genPhi P A C) (comm (genPhi P A C) (genSig P A C)) = (4 : ℤ) • (genV P A C * genSig P A C)`. -/
theorem comm_genPhi_comm_genPhi_genSig (A C : B) :
    comm (genPhi P A C) (comm (genPhi P A C) (genSig P A C)) =
      (4 : ℤ) • (genV P A C * genSig P A C) := by
  peirce_nf hP

/-- Dynamical mass-squared eigenvalue `4 • genV P A C` on the chiral involution `invS P`:
`comm (genPhi P A C) (comm (genPhi P A C) (invS P)) = (4 : ℤ) • (genV P A C * invS P)`. -/
theorem comm_genPhi_comm_genPhi_invS (A C : B) :
    comm (genPhi P A C) (comm (genPhi P A C) (invS P)) =
      (4 : ℤ) • (genV P A C * invS P) := by
  peirce_nf hP

/-- Operator GMOR double commutator of `invS P` on `genPhi P A C`:
`comm (invS P) (comm (invS P) (genPhi P A C)) = (4 : ℤ) • genPhi P A C`. -/
theorem comm_invS_comm_invS_genPhi (A C : B) :
    comm (invS P) (comm (invS P) (genPhi P A C)) = (4 : ℤ) • genPhi P A C := by
  peirce_nf hP

/-- Operator GMOR double commutator of `invS P` on `genJ P A C`:
`comm (invS P) (comm (invS P) (genJ P A C)) = (4 : ℤ) • genJ P A C`. -/
theorem comm_invS_comm_invS_genJ (A C : B) :
    comm (invS P) (comm (invS P) (genJ P A C)) = (4 : ℤ) • genJ P A C := by
  peirce_nf hP

/-- Chiral neutrality of `genV P A C` under the axial double commutator `ad_{invS P}²`:
`comm (invS P) (comm (invS P) (genV P A C)) = 0`. -/
theorem comm_invS_comm_invS_genV (A C : B) :
    comm (invS P) (comm (invS P) (genV P A C)) = 0 := by
  peirce_nf hP

/-- Chiral neutrality of `genSig P A C` under the axial double commutator `ad_{invS P}²`:
`comm (invS P) (comm (invS P) (genSig P A C)) = 0`. -/
theorem comm_invS_comm_invS_genSig (A C : B) :
    comm (invS P) (comm (invS P) (genSig P A C)) = 0 := by
  peirce_nf hP

/-- Second-order operator GMOR condensate contraction:
`genPhi P A C * comm (invS P) (comm (invS P) (genPhi P A C)) = (4 : ℤ) • genV P A C`. -/
theorem genPhi_mul_comm_invS_comm_invS_genPhi (A C : B) :
    genPhi P A C * comm (invS P) (comm (invS P) (genPhi P A C)) =
      (4 : ℤ) • genV P A C := by
  peirce_nf hP

/-- First-order chiral annihilation of the axial double commutator under `evenGrade P`:
`evenGrade P (comm (invS P) (comm (invS P) (genPhi P A C))) = 0`. -/
theorem evenGrade_comm_invS_comm_invS_genPhi (A C : B) :
    evenGrade P (comm (invS P) (comm (invS P) (genPhi P A C))) = 0 := by
  peirce_nf hP

/-- Second-order GMOR condensate survival under `evenGrade P`:
`evenGrade P (genPhi P A C * comm (invS P) (comm (invS P) (genPhi P A C))) = (4 : ℤ) • genV P A C`. -/
theorem evenGrade_genPhi_mul_comm_invS_comm_invS_genPhi (A C : B) :
    evenGrade P (genPhi P A C * comm (invS P) (comm (invS P) (genPhi P A C))) =
      (4 : ℤ) • genV P A C := by
  peirce_nf hP

/-! ### Constructive Polynomial Peirce–Dirac Resolvents Over `[Ring B]` (`χ₇`, `𝔎₇`) -/

/-- Exact factorization of the unit-mass Peirce–Dirac operator `genJ P A C + 1` and its conjugate
`-genJ P A C + 1`:
`(genJ P A C + 1) * (-genJ P A C + 1) = 1 + genV P A C`. -/
theorem genJ_add_one_mul_neg_genJ_add_one (A C : B) :
    (genJ P A C + 1) * (-genJ P A C + 1) = 1 + genV P A C := by
  peirce_nf hP

/-- Commuted factorization of the unit-mass Peirce–Dirac conjugate `-genJ P A C + 1` and
`genJ P A C + 1`:
`(-genJ P A C + 1) * (genJ P A C + 1) = 1 + genV P A C`. -/
theorem neg_genJ_add_one_mul_genJ_add_one (A C : B) :
    (-genJ P A C + 1) * (genJ P A C + 1) = 1 + genV P A C := by
  peirce_nf hP

/-- Constructive first-order Neumann resolvent identity (right multiplication):
`(genJ P A C + 1) * ((-genJ P A C + 1) * (1 - genV P A C)) = 1 - genV P A C * genV P A C`. -/
theorem genJ_add_one_mul_neumann_resolvent_deg1 (A C : B) :
    (genJ P A C + 1) * ((-genJ P A C + 1) * (1 - genV P A C)) =
      1 - genV P A C * genV P A C := by
  peirce_nf hP

/-- Constructive first-order Neumann resolvent identity (left multiplication):
`((-genJ P A C + 1) * (1 - genV P A C)) * (genJ P A C + 1) = 1 - genV P A C * genV P A C`. -/
theorem neumann_resolvent_deg1_mul_genJ_add_one (A C : B) :
    ((-genJ P A C + 1) * (1 - genV P A C)) * (genJ P A C + 1) =
      1 - genV P A C * genV P A C := by
  peirce_nf hP

/-- Constructive two-sided inverse of `genJ P A C + 1` whenever `genV P A C * genV P A C = 0`
(with no assumed external inverse element `R_η`):
`(-genJ P A C + 1) * (1 - genV P A C)` is a two-sided inverse of `genJ P A C + 1`. -/
theorem genJ_add_one_two_sided_inverse_of_genV_sq_zero (A C : B)
    (hV2 : genV P A C * genV P A C = 0) :
    (genJ P A C + 1) * ((-genJ P A C + 1) * (1 - genV P A C)) = 1 ∧
    ((-genJ P A C + 1) * (1 - genV P A C)) * (genJ P A C + 1) = 1 := by
  rw [genJ_add_one_mul_neumann_resolvent_deg1 hP A C,
      neumann_resolvent_deg1_mul_genJ_add_one hP A C, hV2, sub_zero]
  exact ⟨rfl, rfl⟩

/-- Even Peirce grade of the constructive first-order Neumann resolvent
`(-genJ P A C + 1) * (1 - genV P A C)` equals the purely even kernel `1 - genV P A C`. -/
theorem evenGrade_neumann_resolvent_deg1 (A C : B) :
    evenGrade P ((-genJ P A C + 1) * (1 - genV P A C)) = 1 - genV P A C := by
  peirce_nf hP

/-- Odd Peirce grade of the constructive first-order Neumann resolvent
`(-genJ P A C + 1) * (1 - genV P A C)` equals `-genJ P A C + genJ P A C * genV P A C`. -/
theorem oddGrade_neumann_resolvent_deg1 (A C : B) :
    oddGrade P ((-genJ P A C + 1) * (1 - genV P A C)) =
      -genJ P A C + genJ P A C * genV P A C := by
  peirce_nf hP

/-- Constructive second-order Neumann resolvent identity (right multiplication):
`(genJ P A C + 1) * ((-genJ P A C + 1) * (1 - genV P A C + genV P A C * genV P A C)) =
 1 + genV P A C * genV P A C * genV P A C`. -/
theorem genJ_add_one_mul_neumann_resolvent_deg2 (A C : B) :
    (genJ P A C + 1) *
      ((-genJ P A C + 1) * (1 - genV P A C + genV P A C * genV P A C)) =
      1 + genV P A C * genV P A C * genV P A C := by
  peirce_nf hP

/-- Constructive second-order Neumann resolvent identity (left multiplication):
`((-genJ P A C + 1) * (1 - genV P A C + genV P A C * genV P A C)) * (genJ P A C + 1) =
 1 + genV P A C * genV P A C * genV P A C`. -/
theorem neumann_resolvent_deg2_mul_genJ_add_one (A C : B) :
    ((-genJ P A C + 1) * (1 - genV P A C + genV P A C * genV P A C)) *
      (genJ P A C + 1) =
      1 + genV P A C * genV P A C * genV P A C := by
  peirce_nf hP

/-- Even Peirce grade of the constructive second-order Neumann resolvent equals
`1 - genV P A C + genV P A C * genV P A C`. -/
theorem evenGrade_neumann_resolvent_deg2 (A C : B) :
    evenGrade P ((-genJ P A C + 1) * (1 - genV P A C + genV P A C * genV P A C)) =
      1 - genV P A C + genV P A C * genV P A C := by
  peirce_nf hP

/-- Division-free constructive resolvent identity for idempotent metric defect
`genV P A C - genV P A C * genV P A C`:
`(genJ P A C + 1) * ((-genJ P A C + 1) * (1 + 1 - genV P A C)) - (1 + 1) =
 genV P A C - genV P A C * genV P A C`. -/
theorem genJ_add_one_mul_idempotent_resolvent_defect (A C : B) :
    (genJ P A C + 1) * ((-genJ P A C + 1) * (1 + 1 - genV P A C)) - (1 + 1) =
      genV P A C - genV P A C * genV P A C := by
  peirce_nf hP

/-- Even Peirce grade of the division-free idempotent-metric resolvent
`(-genJ P A C + 1) * (1 + 1 - genV P A C)` equals `1 + 1 - genV P A C`. -/
theorem evenGrade_idempotent_resolvent (A C : B) :
    evenGrade P ((-genJ P A C + 1) * (1 + 1 - genV P A C)) =
      1 + 1 - genV P A C := by
  rw [evenGrade_mul hP]
  have hEvenLeft : evenGrade P (-genJ P A C + 1) = 1 := by
    peirce_nf hP
  have hOddLeft : oddGrade P (-genJ P A C + 1) = -genJ P A C := by
    peirce_nf hP
  have hEvenRight : evenGrade P (1 + 1 - genV P A C) = 1 + 1 - genV P A C := by
    peirce_nf hP
  have hOddRight : oddGrade P (1 + 1 - genV P A C) = 0 := by
    peirce_nf hP
  rw [hEvenLeft, hOddLeft, hEvenRight, hOddRight]
  noncomm_ring

/-! ### Connes 1-Form Factorization, Bianchi Conservation & Centrifugal Dragging (`𝔈₈`, `𝔚𝔊₁₈–𝔚𝔊₂₀`) -/

/-- Connes differential factorization of the Heisenberg spin-vorticity `genSig P A C`:
`genPhi P A C * comm (genPhi P A C) P = genSig P A C`. -/
theorem genPhi_mul_comm_genPhi_P (A C : B) :
    genPhi P A C * comm (genPhi P A C) P = genSig P A C := by
  peirce_nf hP

/-- Reverse Connes differential factorization of the Heisenberg spin-vorticity `genSig P A C`:
`comm (genPhi P A C) P * genPhi P A C = -genSig P A C`. -/
theorem comm_genPhi_P_mul_genPhi (A C : B) :
    comm (genPhi P A C) P * genPhi P A C = -genSig P A C := by
  peirce_nf hP

/-- Positive-definite square of the Connes 1-form `comm (genPhi P A C) P`:
`-(comm (genPhi P A C) P * comm (genPhi P A C) P) = genV P A C`. -/
theorem neg_comm_genPhi_P_sq (A C : B) :
    -(comm (genPhi P A C) P * comm (genPhi P A C) P) = genV P A C := by
  peirce_nf hP

/-- Covariant constancy of the Fisher metric `genV P A C` under the deformed connection
`P + genPhi P A C`: `comm (P + genPhi P A C) (genV P A C) = 0`. -/
theorem comm_P_add_genPhi_genV (A C : B) :
    comm (P + genPhi P A C) (genV P A C) = 0 := by
  peirce_nf hP

/-- Exact commutator of the deformed operator `P + Φ` with the curvature
readout `[P, Φ] + Φ² = J + V`.  The result retains the rotor term rather than
asserting a spurious cancellation. -/
theorem comm_P_add_genPhi_maurer_cartan_curvature (A C : B) :
    comm (P + genPhi P A C) (comm P (genPhi P A C) + genPhi P A C * genPhi P A C) =
      genPhi P A C - (2 : ℤ) • genSig P A C := by
  peirce_nf hP

/-- 4th-order centrifugal spin frame dragging on `genPhi P A C`:
`comm (genSig P A C) (comm (genSig P A C) (genPhi P A C)) =
 (4 : ℤ) • (genV P A C * genV P A C * genPhi P A C)`. -/
theorem comm_genSig_comm_genSig_genPhi (A C : B) :
    comm (genSig P A C) (comm (genSig P A C) (genPhi P A C)) =
      (4 : ℤ) • (genV P A C * genV P A C * genPhi P A C) := by
  peirce_nf hP

/-- 4th-order centrifugal spin frame dragging on `genJ P A C`:
`comm (genSig P A C) (comm (genSig P A C) (genJ P A C)) =
 (4 : ℤ) • (genV P A C * genV P A C * genJ P A C)`. -/
theorem comm_genSig_comm_genSig_genJ (A C : B) :
    comm (genSig P A C) (comm (genSig P A C) (genJ P A C)) =
      (4 : ℤ) • (genV P A C * genV P A C * genJ P A C) := by
  peirce_nf hP

/-- Fisher–Riemann double-commutator sectional curvature equals twice the spin frame-dragging
rate:
`comm (genPhi P A C) (comm (genPhi P A C) (genJ P A C)) =
 (2 : ℤ) • comm (genSig P A C) (genPhi P A C)`. -/
theorem comm_genPhi_comm_genPhi_genJ_eq_two_comm_genSig_genPhi (A C : B) :
    comm (genPhi P A C) (comm (genPhi P A C) (genJ P A C)) =
      (2 : ℤ) • comm (genSig P A C) (genPhi P A C) := by
  peirce_nf hP

/-! ### Master 12-Stage Coagulation Quadrants (`Ω₁–Ω₇` & `Ω₉–Ω₁₂`) Over `[Ring B]` -/

omit hP in
/-- `Ω₂` Clifford–Krein QGT split on the upper Peirce corner product:
`(2 : ℤ) • (conePlus P A * coneMinus P C) = genV P A C + genSig P A C`. -/
theorem two_zsmul_conePlus_mul_coneMinus_eq_genV_add_genSig (A C : B) :
    (2 : ℤ) • (conePlus P A * coneMinus P C) = genV P A C + genSig P A C := by
  dsimp [genV, genSig, anticomm, comm]
  noncomm_ring

omit hP in
/-- `Ω₂` Clifford–Krein QGT split on the lower Peirce corner product:
`(2 : ℤ) • (coneMinus P C * conePlus P A) = genV P A C - genSig P A C`. -/
theorem two_zsmul_coneMinus_mul_conePlus_eq_genV_sub_genSig (A C : B) :
    (2 : ℤ) • (coneMinus P C * conePlus P A) = genV P A C - genSig P A C := by
  dsimp [genV, genSig, anticomm, comm]
  noncomm_ring

/-- `Ω₃` `V₄` Klein-bottle sum-difference commutator/anticommutator crossover:
`comm (invS P * evenGrade P W) (genPhi P A C) = anticomm (evenGrade P W) (genJ P A C)`. -/
theorem klein_bottle_diff_comm_genPhi_eq_evenGrade_anticomm_genJ (A C W : B) :
    comm (invS P * evenGrade P W) (genPhi P A C) =
      anticomm (evenGrade P W) (genJ P A C) := by
  peirce_nf hP

/-- `Ω₃` Dual `V₄` Klein-bottle sum-difference anticommutator/commutator crossover:
`anticomm (invS P * evenGrade P W) (genPhi P A C) = comm (evenGrade P W) (genJ P A C)`. -/
theorem klein_bottle_diff_anticomm_genPhi_eq_evenGrade_comm_genJ (A C W : B) :
    anticomm (invS P * evenGrade P W) (genPhi P A C) =
      comm (evenGrade P W) (genJ P A C) := by
  peirce_nf hP

/-- `Ω₄` Gauss–Bonnet supertrace commutator cancellation:
`(2 : ℤ) • (invS P * genV P A C) = comm (genJ P A C) (genPhi P A C)`. -/
theorem gauss_bonnet_supertrace_commutator_cancellation (A C : B) :
    (2 : ℤ) • (invS P * genV P A C) = comm (genJ P A C) (genPhi P A C) := by
  peirce_nf hP

/-- **Quadrant I (`Ω₁–Ω₄`, `omega1_to_omega4_peirce_cartan_gauss_bonnet`)**:
Peirce tripotency `ad_P³ = ad_P`, corner nilpotency `N_±² = 0`, Clifford–Krein QGT split
`2 N_+ N_- = V + Σ`, para-Kähler lock `S_P Σ = V` and `S_P V = Σ`, `V₄` Klein-bottle sum-difference
crossover `[S_P evenGrade W, Φ] = {evenGrade W, J}` and `{S_P evenGrade W, Φ} = [evenGrade W, J]`,
modular-dissipative clocking `-[Φ, [Φ, J]] = -2[Σ, Φ]`, conditional expectation multiplicative
defect `evenGrade(XY) - evenGrade(X)evenGrade(Y) = oddGrade(X)oddGrade(Y)`, and Gauss–Bonnet
commutator identity `2 S_P V = [J, Φ]`. -/
theorem omega1_to_omega4_peirce_cartan_gauss_bonnet (A C W X Y : B) :
    comm P (comm P (comm P A)) = comm P A ∧
    conePlus P A * conePlus P C = 0 ∧
    coneMinus P A * coneMinus P C = 0 ∧
    (2 : ℤ) • (conePlus P A * coneMinus P C) = genV P A C + genSig P A C ∧
    invS P * genSig P A C = genV P A C ∧
    invS P * genV P A C = genSig P A C ∧
    comm (invS P * evenGrade P W) (genPhi P A C) =
      anticomm (evenGrade P W) (genJ P A C) ∧
    anticomm (invS P * evenGrade P W) (genPhi P A C) =
      comm (evenGrade P W) (genJ P A C) ∧
    -comm (genPhi P A C) (comm (genPhi P A C) (genJ P A C)) =
      -((2 : ℤ) • comm (genSig P A C) (genPhi P A C)) ∧
    evenGrade P (X * Y) - evenGrade P X * evenGrade P Y =
      oddGrade P X * oddGrade P Y ∧
    (2 : ℤ) • (invS P * genV P A C) = comm (genJ P A C) (genPhi P A C) := by
  refine ⟨by peirce_nf hP, by peirce_nf hP, by peirce_nf hP, by peirce_nf hP,
          by peirce_nf hP, by peirce_nf hP, by peirce_nf hP, by peirce_nf hP,
          by peirce_nf hP, by peirce_nf hP, by peirce_nf hP⟩

/-- `Ω₅` Amari `e`-flat abelian addition on the upper Peirce unipotent chart:
`(1 + conePlus P A₁) * (1 + conePlus P A₂) = 1 + (conePlus P A₁ + conePlus P A₂)`. -/
theorem amari_conePlus_unipotent_mul (A₁ A₂ : B) :
    (1 + conePlus P A₁) * (1 + conePlus P A₂) =
      1 + (conePlus P A₁ + conePlus P A₂) := by
  peirce_nf hP

/-- `Ω₅` Amari `m`-flat abelian addition on the lower Peirce unipotent chart:
`(1 + coneMinus P C₁) * (1 + coneMinus P C₂) = 1 + (coneMinus P C₁ + coneMinus P C₂)`. -/
theorem amari_coneMinus_unipotent_mul (C₁ C₂ : B) :
    (1 + coneMinus P C₁) * (1 + coneMinus P C₂) =
      1 + (coneMinus P C₁ + coneMinus P C₂) := by
  peirce_nf hP

/-- `Ω₅` Connes–Fusion balancing monodromy:
`(1 + N_+) * (1 + N_-) * (1 - N_+) * (1 - N_-) = 1 + Σ - V * J + (N_+ * N_-)²`. -/
theorem connes_fusion_balancing_monodromy (A C : B) :
    (1 + conePlus P A) * (1 + coneMinus P C) *
      (1 - conePlus P A) * (1 - coneMinus P C) =
      1 + genSig P A C - genV P A C * genJ P A C +
        (conePlus P A * coneMinus P C) * (conePlus P A * coneMinus P C) := by
  peirce_nf hP

/-- `Ω₆` Upper Bruhat conjugation `G_+ * P * G_+⁻¹ = P + Φ - Σ - V * N_+`. -/
theorem bruhat_upper_conjugation_eq (A C : B) :
    (1 - conePlus P A) * (1 + coneMinus P C) * P *
      ((1 - coneMinus P C) * (1 + conePlus P A)) =
      P + genPhi P A C - genSig P A C - genV P A C * conePlus P A := by
  peirce_nf hP

/-- `Ω₆` Lower Bruhat conjugation `G_- * P * G_-⁻¹ = P + Φ - Σ - V * N_-`. -/
theorem bruhat_lower_conjugation_eq (A C : B) :
    (1 + coneMinus P C) * (1 - conePlus P A) * P *
      ((1 + conePlus P A) * (1 - coneMinus P C)) =
      P + genPhi P A C - genSig P A C - genV P A C * coneMinus P C := by
  peirce_nf hP

/-- `Ω₇` Push–Pull corner shift `(N_+ * N_-) * N_+ = N_+ * (N_- * N_+) = V * N_+`. -/
theorem push_pull_corner_shift_conePlus (A C : B) :
    (conePlus P A * coneMinus P C) * conePlus P A =
      conePlus P A * (coneMinus P C * conePlus P A) ∧
    (conePlus P A * coneMinus P C) * conePlus P A =
      genV P A C * conePlus P A := by
  refine ⟨by peirce_nf hP, by peirce_nf hP⟩

/-- `Ω₇` Zero-memory Maurer–Cartan backpropagation identity:
`(dN_+ * (1 + N_-) + (1 + N_+) * dN_-) * ((1 - N_-) * (1 - N_+)) =
 dN_+ + (1 + N_+) * dN_- * (1 - N_+)`. -/
theorem maurer_cartan_zero_memory_backprop (A C dA dC : B) :
    (conePlus P dA * (1 + coneMinus P C) + (1 + conePlus P A) * coneMinus P dC) *
      ((1 - coneMinus P C) * (1 - conePlus P A)) =
      conePlus P dA + (1 + conePlus P A) * coneMinus P dC * (1 - conePlus P A) := by
  peirce_nf hP

/-- **Quadrant II (`Ω₅–Ω₇`, `omega5_to_omega7_amari_bruhat_push_pull_and_backprop`)**:
Amari `e`-flat abelian addition, Connes–Fusion balancing monodromy, unimodular Bruhat conjugation
`P̂_± = G_± P G_±⁻¹`, idempotency `P̂_±² = P̂_±`, bichiral anticommutator `{P̂_+, P̂_-} = P̂_+ + P̂_- + V³`,
Push–Pull corner shift, and zero-memory Maurer–Cartan backpropagation. -/
theorem omega5_to_omega7_amari_bruhat_push_pull_and_backprop (A C dA dC : B) :
    let np := conePlus P A
    let nm := coneMinus P C
    let dnp := conePlus P dA
    let dnm := coneMinus P dC
    let qp := np * nm
    let qm := nm * np
    let v := genV P A C
    let s := genSig P A C
    let j := genJ P A C
    let Pp := P + genPhi P A C - s - v * np
    let Pm := P + genPhi P A C - s - v * nm
    (1 + np) * (1 + dnp) = 1 + (np + dnp) ∧
    (1 + np) * (1 + nm) * (1 - np) * (1 - nm) = 1 + s - v * j + qp * qp ∧
    (1 - np) * (1 + nm) * P * ((1 - nm) * (1 + np)) = Pp ∧
    (1 + nm) * (1 - np) * P * ((1 + np) * (1 - nm)) = Pm ∧
    Pp * Pp = Pp ∧
    Pm * Pm = Pm ∧
    anticomm Pp Pm = Pp + Pm + v * v * v ∧
    qp * np = np * qm ∧
    qp * np = v * np ∧
    (dnp * (1 + nm) + (1 + np) * dnm) * ((1 - nm) * (1 - np)) =
      dnp + (1 + np) * dnm * (1 - np) := by
  refine ⟨by peirce_nf hP, by peirce_nf hP, by peirce_nf hP, by peirce_nf hP,
          by peirce_nf hP, by peirce_nf hP, by peirce_nf hP, by peirce_nf hP,
          by peirce_nf hP, by peirce_nf hP⟩

omit hP in
/-- `Ω₉-1` Tripotent cubic defect (`H * (H * H) = H`):
`comm H (comm H (comm H X)) - comm H X = -((3 : ℤ) • (H * comm H X * H))`. -/
theorem tripotent_comm_cubic_defect {H : B} (hH : H * (H * H) = H) (X : B) :
    comm H (comm H (comm H X)) - comm H X =
      -((3 : ℤ) • (H * comm H X * H)) := by
  have hH' : H * H * H = H := by rw [mul_assoc, hH]
  dsimp only [comm]
  calc
    H * (H * (H * X - X * H) - (H * X - X * H) * H) -
        (H * (H * X - X * H) - (H * X - X * H) * H) * H - (H * X - X * H) =
      (H * H * H) * X - X * (H * H * H) - (H * X - X * H) -
        (3 : ℤ) • (H * (H * X - X * H) * H) := by noncomm_ring
    _ = H * X - X * H - (H * X - X * H) -
        (3 : ℤ) • (H * (H * X - X * H) * H) := by rw [hH']
    _ = -((3 : ℤ) • (H * (H * X - X * H) * H)) := by noncomm_ring

omit hP in
/-- `Ω₉-2` Eigenvalue `+4` of `ad_H²` on the sandwich `H * comm H X * H` when `H * (H * H) = H`:
`comm H (comm H (H * comm H X * H)) = (4 : ℤ) • (H * comm H X * H)`. -/
theorem tripotent_comm_sq_sandwich {H : B} (hH : H * (H * H) = H) (X : B) :
    comm H (comm H (H * comm H X * H)) =
      (4 : ℤ) • (H * comm H X * H) := by
  have hH' : H * H * H = H := by rw [mul_assoc, hH]
  dsimp only [comm]
  calc
    H * (H * (H * (H * X - X * H) * H) - (H * (H * X - X * H) * H) * H) -
        (H * (H * (H * X - X * H) * H) - (H * (H * X - X * H) * H) * H) * H =
      (H * H * H) * (H * X - X * H) * H + H * (H * X - X * H) * (H * H * H) -
        (2 : ℤ) • ((H * H * H) * X * H * H - H * H * X * (H * H * H)) := by noncomm_ring
    _ = H * (H * X - X * H) * H + H * (H * X - X * H) * H -
        (2 : ℤ) • (H * X * H * H - H * H * X * H) := by rw [hH']
    _ = (4 : ℤ) • (H * (H * X - X * H) * H) := by noncomm_ring

omit hP in
/-- `Ω₉-2` Exact 5-graded Kantor–Tanaka quintic closure (`H * (H * H) = H`):
`(ad_H⁵ - 5 ad_H³ + 4 ad_H)(X) = 0`. -/
theorem tripotent_comm_quintic_closure {H : B} (hH : H * (H * H) = H) (X : B) :
    comm H (comm H (comm H (comm H (comm H X)))) -
      (5 : ℤ) • comm H (comm H (comm H X)) +
        (4 : ℤ) • comm H X = 0 := by
  have hH' : H * H * H = H := by rw [mul_assoc, hH]
  have hCub2 := tripotent_comm_cubic_defect hH (comm H (comm H X))
  have hCub1 := tripotent_comm_cubic_defect hH X
  have hH2 :
      H * (H * comm H X * H) * H = - (H * comm H X * H) := by
    dsimp only [comm]
    calc
      H * (H * (H * X - X * H) * H) * H =
          (H * H * H) * X * H * H - H * H * X * (H * H * H) := by noncomm_ring
      _ = H * X * H * H - H * H * X * H := by rw [hH']
      _ = - (H * (H * X - X * H) * H) := by noncomm_ring
  have hSub4 :
      H * comm H (comm H (comm H X)) * H =
        (4 : ℤ) • (H * comm H X * H) := by
    calc
      H * comm H (comm H (comm H X)) * H =
          H * (comm H (comm H (comm H X)) - comm H X) * H +
            H * comm H X * H := by noncomm_ring
      _ = H * (-((3 : ℤ) • (H * comm H X * H))) * H +
            H * comm H X * H := by rw [hCub1]
      _ = -((3 : ℤ) • (H * (H * comm H X * H) * H)) +
            H * comm H X * H := by
            have h3 : ∀ Z : B, (3 : ℤ) • Z = Z + Z + Z := fun _ => by abel
            rw [h3 (H * comm H X * H), h3 (H * (H * comm H X * H) * H)]
            simp only [neg_add, mul_add, add_mul]
            noncomm_ring
      _ = -((3 : ℤ) • (-(H * comm H X * H))) +
            H * comm H X * H := by rw [hH2]
      _ = (4 : ℤ) • (H * comm H X * H) := by abel
  calc
    comm H (comm H (comm H (comm H (comm H X)))) -
      (5 : ℤ) • comm H (comm H (comm H X)) +
        (4 : ℤ) • comm H X =
      (comm H (comm H (comm H (comm H (comm H X)))) -
        comm H (comm H (comm H X))) -
      (4 : ℤ) • (comm H (comm H (comm H X)) - comm H X) := by abel
    _ = -((3 : ℤ) • (H * comm H (comm H (comm H X)) * H)) -
        (4 : ℤ) • (-((3 : ℤ) • (H * comm H X * H))) := by rw [hCub2, hCub1]
    _ = -((3 : ℤ) • ((4 : ℤ) • (H * comm H X * H))) -
        (4 : ℤ) • (-((3 : ℤ) • (H * comm H X * H))) := by rw [hSub4]
    _ = 0 := by abel

omit hP in
/-- `Ω₉-3` Case-free super-adjoint square `sad_Q²(X) = [Q², X]` for any involution `S * S = 1`
and `S`-odd supercharge `S * Q * S = -Q`:
`Q * (Q * X - S * X * S * Q) - S * (Q * X - S * X * S * Q) * S * Q = comm (Q * Q) X`. -/
theorem super_adjoint_sq_eq_comm_sq {S Q : B}
    (hS : S * S = 1) (hQ : S * Q * S = -Q) (X : B) :
    Q * (Q * X - S * X * S * Q) -
      S * (Q * X - S * X * S * Q) * S * Q =
      comm (Q * Q) X := by
  have hQS : Q * S = -(S * Q) := by
    calc
      Q * S = (S * S) * Q * S := by rw [hS, one_mul]
      _ = S * (S * Q * S) := by noncomm_ring
      _ = -(S * Q) := by rw [hQ, mul_neg]
  have hT1 : Q * (S * X * S * Q) = -(S * (Q * X * S * Q)) := by
    calc
      Q * (S * X * S * Q) = (Q * S) * X * S * Q := by noncomm_ring
      _ = -(S * Q) * X * S * Q := by rw [hQS]
      _ = -(S * (Q * X * S * Q)) := by noncomm_ring
  have hT2 : S * (S * X * S * Q) * S * Q = -(X * (Q * Q)) := by
    calc
      S * (S * X * S * Q) * S * Q = (S * S) * X * (S * Q * S) * Q := by noncomm_ring
      _ = 1 * X * (-Q) * Q := by rw [hS, hQ]
      _ = -(X * (Q * Q)) := by noncomm_ring
  dsimp only [comm]
  calc
    Q * (Q * X - S * X * S * Q) - S * (Q * X - S * X * S * Q) * S * Q =
      (Q * Q) * X - Q * (S * X * S * Q) - S * (Q * X * S * Q) +
        S * (S * X * S * Q) * S * Q := by noncomm_ring
    _ = (Q * Q) * X - (-(S * (Q * X * S * Q))) - S * (Q * X * S * Q) +
        (-(X * (Q * Q))) := by rw [hT1, hT2]
    _ = (Q * Q) * X - X * (Q * Q) := by noncomm_ring

omit hP in
/-- `Ω₉-3` Asymmetric defect between the ungraded double commutator `ad_Q²(X)` and the
super-adjoint square `sad_Q²(X)`:
`comm Q (comm Q X) - sad_Q²(X) = -((2 : ℤ) • (comm Q X * Q))`. -/
theorem comm_sq_sub_super_adjoint_sq {S Q : B}
    (hS : S * S = 1) (hQ : S * Q * S = -Q) (X : B) :
    comm Q (comm Q X) -
      (Q * (Q * X - S * X * S * Q) -
        S * (Q * X - S * X * S * Q) * S * Q) =
      -((2 : ℤ) • (comm Q X * Q)) := by
  rw [super_adjoint_sq_eq_comm_sq hS hQ X]
  dsimp only [comm]
  noncomm_ring

omit hP in
/-- `Ω₁₀` Division-free `24 = 4!` integer Lagrange projector partition in `B`:
`6(D₄ - 5D₂ + 4X) - 4(D₄ + D₃ - 4D₂ - 4D₁) - 4(D₄ - D₃ - 4D₂ + 4D₁) + (D₄ + 2D₃ - D₂ - 2D₁) + (D₄ - 2D₃ - D₂ + 2D₁) = 24 • X`. -/
theorem five_graded_lagrange_24_partition (D₄ D₃ D₂ D₁ X : B) :
    (6 : ℤ) • (D₄ - (5 : ℤ) • D₂ + (4 : ℤ) • X) -
      (4 : ℤ) • (D₄ + D₃ - (4 : ℤ) • D₂ - (4 : ℤ) • D₁) -
      (4 : ℤ) • (D₄ - D₃ - (4 : ℤ) • D₂ + (4 : ℤ) • D₁) +
      (D₄ + (2 : ℤ) • D₃ - D₂ - (2 : ℤ) • D₁) +
      (D₄ - (2 : ℤ) • D₃ - D₂ + (2 : ℤ) • D₁) = (24 : ℤ) • X := by
  simp only [zsmul_eq_mul]
  norm_num
  noncomm_ring

omit hP in
/-- **Quadrant III-A (`Ω₉–Ω₁₀`, `omega9_to_omega10_kantor_quintic_super_adjoint_and_24_isogeny`)**:
Tripotent cubic defect, `+4` sandwich eigenvalue, 5-graded Kantor–Tanaka quintic closure,
case-free super-adjoint square `sad_Q²(X) = [Q², X]`, asymmetric defect `-2[Q, X]Q`, and
division-free `24 = 4!` Lagrange projector partition. -/
theorem omega9_to_omega10_kantor_quintic_super_adjoint_and_24_isogeny
    {H Q S : B} (X : B)
    (hH : H * (H * H) = H) (hS : S * S = 1) (hQ : S * Q * S = -Q) :
    let W := H * comm H X * H
    let sadQ2 := Q * (Q * X - S * X * S * Q) - S * (Q * X - S * X * S * Q) * S * Q
    let D₁ := comm H X
    let D₂ := comm H D₁
    let D₃ := comm H D₂
    let D₄ := comm H D₃
    comm H (comm H (comm H X)) - comm H X = -((3 : ℤ) • W) ∧
    comm H (comm H W) = (4 : ℤ) • W ∧
    comm H (comm H (comm H (comm H (comm H X)))) -
      (5 : ℤ) • comm H (comm H (comm H X)) + (4 : ℤ) • comm H X = 0 ∧
    sadQ2 = comm (Q * Q) X ∧
    comm Q (comm Q X) - sadQ2 = -((2 : ℤ) • (comm Q X * Q)) ∧
    (6 : ℤ) • (D₄ - (5 : ℤ) • D₂ + (4 : ℤ) • X) -
      (4 : ℤ) • (D₄ + D₃ - (4 : ℤ) • D₂ - (4 : ℤ) • D₁) -
      (4 : ℤ) • (D₄ - D₃ - (4 : ℤ) • D₂ + (4 : ℤ) • D₁) +
      (D₄ + (2 : ℤ) • D₃ - D₂ - (2 : ℤ) • D₁) +
      (D₄ - (2 : ℤ) • D₃ - D₂ + (2 : ℤ) • D₁) = (24 : ℤ) • X := by
  refine ⟨tripotent_comm_cubic_defect hH X,
   tripotent_comm_sq_sandwich hH X,
   tripotent_comm_quintic_closure hH X,
   super_adjoint_sq_eq_comm_sq hS hQ X,
   comm_sq_sub_super_adjoint_sq hS hQ X,
   ?_⟩
  abel

/-- `Ω₁₁` Universal bulk–boundary anticommutation: for any involution `C * C = 1` and idempotent
`P * P = P`, the even diagonal bulk operator `evenGrade P C` anticommutes with the odd boundary
transfer operator `oddGrade P C = genPhi P C C`. -/
theorem bulk_boundary_evenGrade_anticomm_oddGrade_of_sq_one
    {C : B} (hC : C * C = 1) :
    anticomm (evenGrade P C) (oddGrade P C) = 0 := by
  have hC_assoc : ∀ Z : B, C * (C * Z) = Z := by
    intro Z; rw [← mul_assoc, hC, one_mul]
  dsimp only [evenGrade, oddGrade, anticomm]
  simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
             mul_assoc, hP, P_mul_P' hP, hC, hC_assoc]
  abel

/-- `Ω₁₁` Universal bulk–boundary gap-transfer conservation law: for any involution `C * C = 1`
and idempotent `P * P = P`, `(evenGrade P C)² + (oddGrade P C)² = (evenGrade P C)² + genV P C C = 1`. -/
theorem bulk_boundary_evenGrade_sq_add_genV_eq_one_of_sq_one
    {C : B} (hC : C * C = 1) :
    evenGrade P C * evenGrade P C + genV P C C = 1 := by
  have hC_assoc : ∀ Z : B, C * (C * Z) = Z := by
    intro Z; rw [← mul_assoc, hC, one_mul]
  dsimp only [evenGrade, genV, anticomm, conePlus, coneMinus]
  simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
             mul_assoc, hP, P_mul_P' hP, hC, hC_assoc]
  abel

/-- **Quadrant IV (`Ω₁₁–Ω₁₂`, `omega11_to_omega12_bulk_boundary_and_logcft_balance`)**:
Universal bulk–boundary anticommutation `{evenGrade P C, oddGrade P C} = 0`, gap transfer
`(evenGrade P C)² + (oddGrade P C)² = (evenGrade P C)² + genV P C C = 1`, and LogCFT unipotent
balance `(1 - N_nil) * (1 + N_nil) = 1`. -/
theorem omega11_to_omega12_bulk_boundary_and_logcft_balance
    {C N_nil : B} (hC : C * C = 1) (hN : N_nil * N_nil = 0) :
    anticomm (evenGrade P C) (oddGrade P C) = 0 ∧
    evenGrade P C * evenGrade P C + oddGrade P C * oddGrade P C = 1 ∧
    evenGrade P C * evenGrade P C + genV P C C = 1 ∧
    (1 - N_nil) * (1 + N_nil) = 1 := by
  have hOddSq : oddGrade P C * oddGrade P C = genV P C C := by
    dsimp only [oddGrade, genV, anticomm, conePlus, coneMinus]
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
               mul_assoc, P_mul_P' hP]
    abel
  have hGap := bulk_boundary_evenGrade_sq_add_genV_eq_one_of_sq_one hP hC
  refine ⟨bulk_boundary_evenGrade_anticomm_oddGrade_of_sq_one hP hC, ?_, hGap, ?_⟩
  · rw [hOddSq]; exact hGap
  · calc (1 - N_nil) * (1 + N_nil) = 1 - N_nil * N_nil := by noncomm_ring
      _ = 1 := by rw [hN, sub_zero]

/-! ### Outer-identity Peirce extension -/

/-- Subtracting the identity from an operator that acts as `P * F * P` on
the `P` corner, as the identity on its complement, and carries both Peirce
cross terms leaves the inner deviation and those cross terms. -/
theorem peirce_outer_identity_extension_sub_one (F : B) :
    (P * F * P + (1 - P) + genPhi P F F) - 1 =
      P * (F - 1) * P + genPhi P F F := by
  dsimp [genPhi, conePlus, coneMinus]
  peirce_nf hP

/-- Squaring the outer-identity Peirce extension retains both cross-corner
Gramians and the linear cross terms. This is an associative-ring identity;
it makes no claim about order-embedding maximality or proof-theoretic strength. -/
theorem peirce_outer_identity_extension_square (F : B) :
    (P * F * P + (1 - P) + genPhi P F F) *
        (P * F * P + (1 - P) + genPhi P F F) =
      (P * F * P * (P * F * P) + (1 - P) + genV P F F) +
        (P * F * P * conePlus P F + conePlus P F) +
        (coneMinus P F * (P * F * P) + coneMinus P F) := by
  dsimp [genPhi, genV, conePlus, coneMinus, comm, anticomm]
  peirce_nf hP

/-- Compressing the square of the outer-identity Peirce extension to the `P`
corner differs from squaring its compressed operator by exactly the excursion
through the complementary corner. -/
theorem peirce_outer_identity_inner_square_defect (F : B) :
    P * ((P * F * P + (1 - P) + genPhi P F F) *
      (P * F * P + (1 - P) + genPhi P F F)) * P -
      (P * (P * F * P + (1 - P) + genPhi P F F) * P) *
        (P * (P * F * P + (1 - P) + genPhi P F F) * P) =
      conePlus P F * coneMinus P F := by
  dsimp [genPhi, conePlus, coneMinus]
  peirce_nf hP

/-- If the cross-corner excursion is nonzero, compression to the `P` corner
does not preserve the square of the outer-identity extension. -/
theorem peirce_outer_identity_inner_compression_not_preserve_square
    (F : B) (hExcursion : conePlus P F * coneMinus P F ≠ 0) :
    P * ((P * F * P + (1 - P) + genPhi P F F) *
      (P * F * P + (1 - P) + genPhi P F F)) * P ≠
      (P * (P * F * P + (1 - P) + genPhi P F F) * P) *
        (P * (P * F * P + (1 - P) + genPhi P F F) * P) := by
  intro hCompressedSquare
  have hDefect := peirce_outer_identity_inner_square_defect hP F
  rw [hCompressedSquare, sub_self] at hDefect
  exact hExcursion hDefect.symm

/-- Compression to the `P` corner preserves the square of the outer-identity
extension exactly when the ordered excursion through the complementary corner
vanishes. This equivalence identifies the obstruction, not merely a
sufficient nonvanishing condition. -/
theorem peirce_outer_identity_inner_square_preserved_iff_return_vanishes
    (F : B) :
    P * ((P * F * P + (1 - P) + genPhi P F F) *
      (P * F * P + (1 - P) + genPhi P F F)) * P =
      (P * (P * F * P + (1 - P) + genPhi P F F) * P) *
        (P * (P * F * P + (1 - P) + genPhi P F F) * P) ↔
      conePlus P F * coneMinus P F = 0 := by
  constructor
  · intro hCompressedSquare
    have hDefect := peirce_outer_identity_inner_square_defect hP F
    rw [hCompressedSquare, sub_self] at hDefect
    exact hDefect.symm
  · intro hReturn
    have hDefect := peirce_outer_identity_inner_square_defect hP F
    have hZero :
        P * ((P * F * P + (1 - P) + genPhi P F F) *
          (P * F * P + (1 - P) + genPhi P F F)) * P -
          (P * (P * F * P + (1 - P) + genPhi P F F) * P) *
            (P * (P * F * P + (1 - P) + genPhi P F F) * P) = 0 := by
      rw [hDefect, hReturn]
    exact sub_eq_zero.mp hZero

/-- The complementary corner has the corresponding square-compression defect.
The baseline term is the square of the compressed outer identity. -/
theorem peirce_outer_identity_outer_square_defect (F : B) :
    (1 - P) * ((P * F * P + (1 - P) + genPhi P F F) *
      (P * F * P + (1 - P) + genPhi P F F)) * (1 - P) - (1 - P) =
      coneMinus P F * conePlus P F := by
  dsimp [genPhi, conePlus, coneMinus]
  peirce_nf hP

/-- A nonzero return excursion through the `P` corner prevents the outer
corner of the squared extension from remaining the identity. -/
theorem peirce_outer_identity_outer_compression_not_preserve_identity
    (F : B) (hExcursion : coneMinus P F * conePlus P F ≠ 0) :
    (1 - P) * ((P * F * P + (1 - P) + genPhi P F F) *
      (P * F * P + (1 - P) + genPhi P F F)) * (1 - P) ≠ 1 - P := by
  intro hCompressedIdentity
  have hDefect := peirce_outer_identity_outer_square_defect hP F
  rw [hCompressedIdentity, sub_self] at hDefect
  exact hExcursion hDefect.symm

/-- The complementary corner of the outer-identity extension remains the
identity after squaring exactly when the ordered return through the `P`
corner vanishes. -/
theorem peirce_outer_identity_outer_square_preserved_iff_return_vanishes
    (F : B) :
    (1 - P) * ((P * F * P + (1 - P) + genPhi P F F) *
      (P * F * P + (1 - P) + genPhi P F F)) * (1 - P) = 1 - P ↔
      coneMinus P F * conePlus P F = 0 := by
  constructor
  · intro hOuterSquare
    have hDefect := peirce_outer_identity_outer_square_defect hP F
    rw [hOuterSquare, sub_self] at hDefect
    exact hDefect.symm
  · intro hReturn
    have hDefect := peirce_outer_identity_outer_square_defect hP F
    have hZero :
        (1 - P) * ((P * F * P + (1 - P) + genPhi P F F) *
          (P * F * P + (1 - P) + genPhi P F F)) * (1 - P) - (1 - P) = 0 := by
      rw [hDefect, hReturn]
    exact sub_eq_zero.mp hZero

/-- Adding the two diagonal square-compression defects of the outer-identity
extension recovers its Peirce mass `genV`, with the upper-then-lower and
lower-then-upper excursions retained in their respective corners. -/
theorem peirce_outer_identity_total_square_defect_eq_genV (F : B) :
    (P * ((P * F * P + (1 - P) + genPhi P F F) *
      (P * F * P + (1 - P) + genPhi P F F)) * P -
      (P * (P * F * P + (1 - P) + genPhi P F F) * P) *
        (P * (P * F * P + (1 - P) + genPhi P F F) * P)) +
      ((1 - P) * ((P * F * P + (1 - P) + genPhi P F F) *
        (P * F * P + (1 - P) + genPhi P F F)) * (1 - P) - (1 - P)) =
      genV P F F := by
  rw [peirce_outer_identity_inner_square_defect hP F,
    peirce_outer_identity_outer_square_defect hP F]
  rfl

/-- The solder term is the commutator with the cut, rotated by the Peirce
involution. This fixes the order of multiplication in the noncommutative ring. -/
theorem peirce_boundary_transition_eq_invS_comm (F : B) :
    genPhi P F F = invS P * comm P F := by
  dsimp [genPhi, conePlus, coneMinus, invS, comm]
  peirce_nf hP

/-- The outer extension has no off-diagonal boundary term exactly when `F`
commutes with the Peirce cut. -/
theorem peirce_boundary_transition_vanishes_iff_commutes (F : B) :
    genPhi P F F = 0 ↔ comm P F = 0 := by
  have hS : invS P * invS P = 1 := by peirce_nf hP
  rw [peirce_boundary_transition_eq_invS_comm hP]
  constructor
  · intro h
    have h' := congrArg (fun X : B => invS P * X) h
    calc
      comm P F = 1 * comm P F := by simp
      _ = (invS P * invS P) * comm P F := by rw [hS]
      _ = invS P * (invS P * comm P F) := by rw [mul_assoc]
      _ = 0 := by rw [h', mul_zero]
  · intro h
    simp [h]

/-! ### Cross-Quadrant Welds `𝓜₃` & `𝓜₄`: Three-Idempotent Tripotent Contact Shell & Bruhat-to-Circle Reduction -/

omit hP in
/-- **Seam `𝓜₃` (`seam_M3_three_idempotent_tripotent_charge_and_contact_shell`)**:
Welds the 3-graded Peirce cut (`Ω₁`) directly into the 5-graded Kantor–Tanaka contact tower (`Ω₉`):
Under the assumptions that `Pplus` and `Pminus` are idempotent, the listed cross-products vanish, and `Pplus + Pzero + Pminus = 1`, the internal
charge `H := Pplus - Pminus` satisfies:
1. `H * H = Pplus + Pminus = 1 - Pzero` and `H * (H * H) = H`,
2. The bilateral contact sandwich `W := H * comm H X * H` evaluates explicitly to `-2` times the
   Grade-`±2` two-step corner jump: `W = -((2 : ℤ) • (Pplus * X * Pminus - Pminus * X * Pplus))`,
3. `comm H (comm H W) = (4 : ℤ) • W`,
4. The cubic-minus-linear contact filter isolates `+6` times the extreme corner jump:
   `comm H (comm H (comm H X)) - comm H X = (6 : ℤ) • (Pplus * X * Pminus - Pminus * X * Pplus)`,
5. On the Grade-`±1` inner core (`Pplus * X * Pzero` and `Pzero * X * Pminus`), `ad_H³ - ad_H`
   vanishes identically. -/
theorem seam_M3_three_idempotent_tripotent_charge_and_contact_shell
    {Pplus Pzero Pminus : B}
    (hplus : Pplus * Pplus = Pplus)
    (hminus : Pminus * Pminus = Pminus)
    (horth_pm : Pplus * Pminus = 0)
    (horth_mp : Pminus * Pplus = 0)
    (horth_pz : Pplus * Pzero = 0)
    (horth_zm : Pzero * Pminus = 0)
    (horth_mz : Pminus * Pzero = 0)
    (hsum : Pplus + Pzero + Pminus = 1) (X : B) :
    let H := Pplus - Pminus
    let W := H * comm H X * H
    H * H = Pplus + Pminus ∧
    H * H = 1 - Pzero ∧
    H * (H * H) = H ∧
    W = -((2 : ℤ) • (Pplus * X * Pminus - Pminus * X * Pplus)) ∧
    comm H (comm H W) = (4 : ℤ) • W ∧
    comm H (comm H (comm H X)) - comm H X =
      (6 : ℤ) • (Pplus * X * Pminus - Pminus * X * Pplus) ∧
    comm H (comm H (comm H (Pplus * X * Pzero))) - comm H (Pplus * X * Pzero) = 0 ∧
    comm H (comm H (comm H (Pzero * X * Pminus))) - comm H (Pzero * X * Pminus) = 0 := by
  intro H W
  have hSq : H * H = Pplus + Pminus := by
    dsimp only [H]
    calc
      (Pplus - Pminus) * (Pplus - Pminus) =
          Pplus * Pplus - Pplus * Pminus - Pminus * Pplus + Pminus * Pminus := by
        noncomm_ring
      _ = Pplus + Pminus := by
        rw [hplus, horth_pm, horth_mp, hminus]
        noncomm_ring
  have hSqSub : H * H = 1 - Pzero := by
    rw [hSq, ← hsum]
    abel
  have hH3 : H * (H * H) = H := by
    rw [← mul_assoc]
    exact orthogonal_idempotent_difference_is_tripotent hplus hminus horth_pm horth_mp
  have hW_General : ∀ Y : B,
      H * comm H Y * H = -((2 : ℤ) • (Pplus * Y * Pminus - Pminus * Y * Pplus)) := by
    intro Y
    have hSand := difference_commutator_sandwich hplus hminus horth_pm horth_mp Y
    have h2 : ∀ Z : B, -Z - Z = -((2 : ℤ) • Z) := fun _ => by abel
    dsimp only [H]
    rw [hSand, h2]
  have hW : W = -((2 : ℤ) • (Pplus * X * Pminus - Pminus * X * Pplus)) :=
    hW_General X
  have hCubic_General : ∀ Y : B,
      comm H (comm H (comm H Y)) - comm H Y =
        (6 : ℤ) • (Pplus * Y * Pminus - Pminus * Y * Pplus) := by
    intro Y
    rw [tripotent_comm_cubic_defect hH3 Y, hW_General Y]
    abel
  refine ⟨hSq, hSqSub, hH3, hW,
          tripotent_comm_sq_sandwich hH3 X,
          hCubic_General X, ?_, ?_⟩
  · rw [hCubic_General (Pplus * X * Pzero)]
    have h1 : Pplus * (Pplus * X * Pzero) * Pminus = 0 := by
      calc Pplus * (Pplus * X * Pzero) * Pminus = Pplus * Pplus * X * (Pzero * Pminus) := by noncomm_ring
        _ = Pplus * Pplus * X * 0 := by rw [horth_zm]
        _ = 0 := by noncomm_ring
    have h2 : Pminus * (Pplus * X * Pzero) * Pplus = 0 := by
      calc Pminus * (Pplus * X * Pzero) * Pplus =
          (Pminus * Pplus) * X * Pzero * Pplus := by noncomm_ring
        _ = 0 := by rw [horth_mp]; noncomm_ring
    rw [h1, h2, sub_self, smul_zero]
  · rw [hCubic_General (Pzero * X * Pminus)]
    have h1 : Pplus * (Pzero * X * Pminus) * Pminus = 0 := by
      calc Pplus * (Pzero * X * Pminus) * Pminus =
          (Pplus * Pzero) * X * Pminus * Pminus := by noncomm_ring
        _ = 0 := by rw [horth_pz]; noncomm_ring
    have h2 : Pminus * (Pzero * X * Pminus) * Pplus = 0 := by
      calc
        Pminus * (Pzero * X * Pminus) * Pplus =
            (Pminus * Pzero) * X * (Pminus * Pplus) := by noncomm_ring
        _ = 0 := by rw [horth_mz, horth_mp]; simp
    rw [h1, h2, sub_self, smul_zero]

/-- **Seam `𝓜₄` (`seam_M4_homogeneous_bruhat_to_projective_circle_reduction`)**:
Welds the polynomial Bruhat projector `P_hat = P + Φ - Σ - V N_+` (`Ω₆`) directly to the
homogeneous projective circle operator `Π̃(u,v) = u² P + uv Φ + v²(1 - P)` (`Ω₁₁`):
1. The four Peirce blocks `P * P_hat * P`, `P * P_hat * (1 - P)`, `(1 - P) * P_hat * P`, and
   `(1 - P) * P_hat * (1 - P)` evaluate explicitly to `P * (1 - V)`, `(1 - V) * N_+`, `N_-`, and
   `(1 - P) * V`,
2. Reconstructing `P_hat` from its four Peirce blocks recovers `P_hat` identically:
   `P * (1 - V) + (1 - V) * N_+ + N_- + (1 - P) * V = P_hat`,
3. Under the homogeneous specialization `1 - genV P A C = (u ^ 2) • 1`, `genV P A C = (v ^ 2) • 1`,
   `(u ^ 2) • conePlus P A = (u * v) • conePlus P U`, and `coneMinus P C = (u * v) • coneMinus P U`,
   the Bruhat projector `P_hat` reduces identically to the homogeneous projective circle
   `(u ^ 2) • P + (u * v) • genPhi P U U + (v ^ 2) • (1 - P)`. -/
theorem seam_M4_homogeneous_bruhat_to_projective_circle_reduction
    (A C U : B) (u v : ℤ) :
    let P_hat := P + genPhi P A C - genSig P A C - genV P A C * conePlus P A
    let Pi_uv := (u ^ 2) • P + (u * v) • genPhi P U U + (v ^ 2) • (1 - P)
    P * P_hat * P = P * (1 - genV P A C) ∧
    P * P_hat * (1 - P) = (1 - genV P A C) * conePlus P A ∧
    (1 - P) * P_hat * P = coneMinus P C ∧
    (1 - P) * P_hat * (1 - P) = (1 - P) * genV P A C ∧
    P * (1 - genV P A C) + (1 - genV P A C) * conePlus P A +
      coneMinus P C + (1 - P) * genV P A C = P_hat ∧
    (1 - genV P A C = (u ^ 2) • (1 : B) →
      genV P A C = (v ^ 2) • (1 : B) →
      (u ^ 2) • conePlus P A = (u * v) • conePlus P U →
      coneMinus P C = (u * v) • coneMinus P U →
      P_hat = Pi_uv) := by
  intro P_hat Pi_uv
  have hSum :
      P * (1 - genV P A C) + (1 - genV P A C) * conePlus P A +
        coneMinus P C + (1 - P) * genV P A C = P_hat := by
    dsimp only [P_hat]
    peirce_nf hP
  refine ⟨by dsimp only [P_hat]; peirce_nf hP,
          by dsimp only [P_hat]; peirce_nf hP,
          by dsimp only [P_hat]; peirce_nf hP,
          by dsimp only [P_hat]; peirce_nf hP,
          hSum, ?_⟩
  intro hU hV hCornerPlus hCornerMinus
  rw [← hSum, hU, hV]
  have h1 : P * ((u ^ 2) • (1 : B)) = (u ^ 2) • P := by
    rw [mul_smul_comm, mul_one]
  have h2 : ((u ^ 2) • (1 : B)) * conePlus P A = (u * v) • conePlus P U := by
    rw [smul_mul_assoc, one_mul, hCornerPlus]
  have h3 : (1 - P) * ((v ^ 2) • (1 : B)) = (v ^ 2) • (1 - P) := by
    rw [mul_smul_comm, mul_one]
  rw [h1, h2, hCornerMinus, h3]
  dsimp only [Pi_uv, genPhi]
  rw [smul_add]
  abel

/-- **The Inner Gödel vs. Outer Friedman Bruhat Mirror (`inner_godel_outer_friedman_bruhat_mirror`)**:
Over any associative ring `[Ring B]` with idempotent `hP : P * P = P`, compares Gödel's Inner State
`Ψ₀ = P + Φ` (active on the interior `P`) with Friedman's Outer-Identity State `W₀ = (1 - P) + Φ`
(active on the exterior `1 - P`):
1. Opposite chiral action on `Σ`: `anticomm P Σ - Σ = +V` whereas `anticomm (1 - P) Σ - Σ = -V`,
2. Both `Ψ₀` and `W₀` share the exact same Stage-0 Socratic defect `+V`:
   `Ψ₀ * Ψ₀ - Ψ₀ = V` and `W₀ * W₀ - W₀ = V`,
3. Subtracting `-Σ` from `Ψ₀` (`Ψ₁ = P + Φ - Σ`) and ADDING `+Σ` to `W₀` (`W₁ = (1 - P) + Φ + Σ`)
   reduces both defects to `+V²`: `Ψ₁ * Ψ₁ - Ψ₁ = V * V` and `W₁ * W₁ - W₁ = V * V`,
4. Subtracting `-V * N_+` produces the exact Stage-2 Bruhat idempotents `P̂_+` (`P_hat * P_hat = P_hat`),
   `P̂_+(-Φ)` (`P_hat_m * P_hat_m = P_hat_m`), and `Ŵ_+` (`W_hat * W_hat = W_hat`),
5. The unimodular Bruhat gauge rotor `G_m = (1 + N_+) * (1 - N_-)` with inverse
   `G_m_inv = (1 + N_-) * (1 - N_+)` conjugates `P` to `P̂_+(-Φ)` and `1 - P` to `Ŵ_+(+Φ)`,
6. `P̂_+(-Φ)` and `Ŵ_+(+Φ)` form an exact orthogonal partition of unity:
   `P_hat_m + W_hat = 1`, `P_hat_m * W_hat = 0`, and `W_hat * P_hat_m = 0`. -/
theorem inner_godel_outer_friedman_bruhat_mirror (A C : B) :
    let Psi0 := P + genPhi P A C
    let W0 := (1 - P) + genPhi P A C
    let Psi1 := P + genPhi P A C - genSig P A C
    let W1 := (1 - P) + genPhi P A C + genSig P A C
    let P_hat := P + genPhi P A C - genSig P A C - genV P A C * conePlus P A
    let P_hat_m := P - genPhi P A C - genSig P A C + genV P A C * conePlus P A
    let W_hat := (1 - P) + genPhi P A C + genSig P A C - genV P A C * conePlus P A
    let G_m := (1 + conePlus P A) * (1 - coneMinus P C)
    let G_m_inv := (1 + coneMinus P C) * (1 - conePlus P A)
    anticomm P (genSig P A C) - genSig P A C = genV P A C ∧
    anticomm (1 - P) (genSig P A C) - genSig P A C = -genV P A C ∧
    Psi0 * Psi0 - Psi0 = genV P A C ∧
    W0 * W0 - W0 = genV P A C ∧
    Psi1 * Psi1 - Psi1 = genV P A C * genV P A C ∧
    W1 * W1 - W1 = genV P A C * genV P A C ∧
    P_hat * P_hat = P_hat ∧
    P_hat_m * P_hat_m = P_hat_m ∧
    W_hat * W_hat = W_hat ∧
    G_m * G_m_inv = 1 ∧
    G_m_inv * G_m = 1 ∧
    G_m * P * G_m_inv = P_hat_m ∧
    G_m * (1 - P) * G_m_inv = W_hat ∧
    P_hat_m + W_hat = 1 ∧
    P_hat_m * W_hat = 0 ∧
    W_hat * P_hat_m = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- The negative inner Bruhat projector and positive outer Bruhat projector
sum to the unit in the associative Peirce ring. -/
theorem peirce_inner_outer_bruhat_projectors_sum (A C : B) :
    (P - genPhi P A C - genSig P A C + genV P A C * conePlus P A) +
      ((1 - P) + genPhi P A C + genSig P A C - genV P A C * conePlus P A) = 1 := by
  peirce_nf hP

/-- The negative inner Bruhat projector annihilates the positive outer
Bruhat projector in the stated multiplication order. -/
theorem peirce_inner_outer_bruhat_projectors_mul_eq_zero (A C : B) :
    (P - genPhi P A C - genSig P A C + genV P A C * conePlus P A) *
      ((1 - P) + genPhi P A C + genSig P A C - genV P A C * conePlus P A) = 0 := by
  peirce_nf hP

/-- Orthogonality also holds in the reverse multiplication order. -/
theorem peirce_outer_inner_bruhat_projectors_mul_eq_zero (A C : B) :
    ((1 - P) + genPhi P A C + genSig P A C - genV P A C * conePlus P A) *
      (P - genPhi P A C - genSig P A C + genV P A C * conePlus P A) = 0 := by
  peirce_nf hP

/-! ### A₁₇ Wheeler–Gödel Two-Projector Heisenberg–Undecidability Bridge (`JW₅–JW₇`) -/

/-- **Theorem `JW₅` (The Heisenberg–Gödel Commutator–Undecidability Bridge)**:
For any two idempotent projectors `P, Q : B` (`hP : P * P = P`, `hQ : Q * Q = Q`) in an arbitrary
associative ring `[Ring B]`:
1. The Heisenberg commutator `comm P Q` equals the chiral Peirce difference
   `conePlus P Q - coneMinus P Q = genJ P Q Q`,
2. Its square is the negative Jordan/Fisher mass: `comm P Q * comm P Q + genV P Q Q = 0`,
3. The interior (`P`-sheet) idempotence defect of `peirce11 P Q = P * Q * P` equals the clockwise
   cross-boundary round-trip `conePlus P Q * coneMinus P Q`,
4. The exterior (`(1 - P)`-sheet) idempotence defect of `peirce00 P Q = (1 - P) * Q * (1 - P)`
   equals the counterclockwise cross-boundary round-trip `coneMinus P Q * conePlus P Q`,
5. The total two-sheet idempotence defect equals the Jordan/Fisher mass `genV P Q Q`.

The Heisenberg–Gödel terminology is a label for these associative-ring identities only: this
theorem does not formalize physical uncertainty or Gödel incompleteness. -/
theorem heisenberg_godel_commutator_undecidability_bridge
    {Q : B} (hQ : Q * Q = Q) :
    comm P Q = conePlus P Q - coneMinus P Q ∧
    comm P Q * comm P Q + genV P Q Q = 0 ∧
    peirce11 P Q - peirce11 P Q * peirce11 P Q = conePlus P Q * coneMinus P Q ∧
    peirce00 P Q - peirce00 P Q * peirce00 P Q = coneMinus P Q * conePlus P Q ∧
    (peirce11 P Q - peirce11 P Q * peirce11 P Q) +
      (peirce00 P Q - peirce00 P Q * peirce00 P Q) = genV P Q Q := by
  have hP_idem : ∀ Z : B, P * (P * Z) = P * Z := fun Z => by rw [← mul_assoc, hP]
  have hQ_idem : ∀ Z : B, Q * (Q * Z) = Q * Z := fun Z => by rw [← mul_assoc, hQ]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals
    dsimp only [comm, anticomm, genV, conePlus, coneMinus, peirce11, peirce00]
    simp only [sub_mul, mul_sub, one_mul, mul_one, mul_assoc, hP_idem, hQ, hQ_idem]
    abel

/-- **Theorem `JW₂ ∧ JW₆` (The Glass-Door Quarantine & Einstein Brainwashing Tragedy)**:
When both cross-boundary Peirce round-trips between idempotents `P` and `Q` vanish
(`conePlus P Q * coneMinus P Q = 0` and `coneMinus P Q * conePlus P Q = 0`), the Jordan/Fisher
mass `genV P Q Q` vanishes, the square of the Heisenberg commutator `comm P Q * comm P Q` vanishes,
and both restricted diagonal blocks `peirce11 P Q` and `peirce00 P Q` collapse to classical
idempotents. This is an algebraic implication under the two stated zero-product hypotheses; it
does not formalize the historical or physical interpretation in the theorem name. -/
theorem einstein_brainwashing_quarantine_tragedy
    {Q : B} (hQ : Q * Q = Q)
    (h_pm : conePlus P Q * coneMinus P Q = 0)
    (h_mp : coneMinus P Q * conePlus P Q = 0) :
    genV P Q Q = 0 ∧
    comm P Q * comm P Q = 0 ∧
    peirce11 P Q * peirce11 P Q = peirce11 P Q ∧
    peirce00 P Q * peirce00 P Q = peirce00 P Q := by
  have hB := heisenberg_godel_commutator_undecidability_bridge hP hQ
  have hV : genV P Q Q = 0 := by
    simp only [genV, anticomm, h_pm, h_mp, add_zero]
  have hCommSq : comm P Q * comm P Q = 0 := by
    have h2 := hB.2.1
    rw [hV, add_zero] at h2
    exact h2
  have h11 : peirce11 P Q * peirce11 P Q = peirce11 P Q :=
    (sub_eq_zero.mp (hB.2.2.1.trans h_pm)).symm
  have h00 : peirce00 P Q * peirce00 P Q = peirce00 P Q :=
    (sub_eq_zero.mp (hB.2.2.2.1.trans h_mp)).symm
  exact ⟨hV, hCommSq, h11, h00⟩

/-- **Theorem `JW₇` (Wheeler's "How Come the Quantum?" ↔ "How Come Existence?" Equivalence)**:
For any two idempotent projectors `P, Q : B` (`hP : P * P = P`, `hQ : Q * Q = Q`) in an arbitrary
associative ring `[Ring B]`, non-vanishing cross-boundary Peirce transport (`conePlus P Q * coneMinus P Q ≠ 0`
or `coneMinus P Q * conePlus P Q ≠ 0`) is logically equivalent to non-vanishing diagonal idempotence
defect (`peirce11 P Q - peirce11 P Q * peirce11 P Q ≠ 0` or
`peirce00 P Q - peirce00 P Q * peirce00 P Q ≠ 0`).
The “quantum” and “existence” labels here denote only these two ring propositions. In particular,
the theorem does not identify physical quantum uncertainty with ontological existence, nor does it
assert that a nonzero commutator alone implies a nonzero round-trip product. -/
theorem wheeler_how_come_quantum_iff_how_come_existence
    {Q : B} (hQ : Q * Q = Q) :
    (conePlus P Q * coneMinus P Q ≠ 0 ∨ coneMinus P Q * conePlus P Q ≠ 0) ↔
      (peirce11 P Q - peirce11 P Q * peirce11 P Q ≠ 0 ∨
        peirce00 P Q - peirce00 P Q * peirce00 P Q ≠ 0) := by
  have hB := heisenberg_godel_commutator_undecidability_bridge hP hQ
  rw [hB.2.2.1, hB.2.2.2.1]

/-! ### A₁₈ Doubled Plabic Twisted Amplituhedron & Unified Operator Spine (`PA₃–PA₇`, `Ω₁–Ω₁₂`) -/

/-- **Node `PA₃` (`single_plabic_sheet_nilpotent_vs_doubled_handle`)**:
For any boundary projector `P * P = P` and operator `g : B`:
1. A single upper corner `conePlus P g` is strictly nilpotent (`conePlus P g * conePlus P g = 0`)
   and has zero `P`-corner projection (`peirce11 P (conePlus P g) = 0`),
2. A single lower corner `coneMinus P g` is strictly nilpotent (`coneMinus P g * coneMinus P g = 0`)
   and has zero `P`-corner projection (`peirce11 P (coneMinus P g) = 0`),
3. Doubling the two sheets into `genPhi P g g = conePlus P g + coneMinus P g` produces the
   two-sided Jordan/foam square `genPhi P g g * genPhi P g g = genV P g g`. -/
theorem single_plabic_sheet_nilpotent_vs_doubled_handle (g : B) :
    conePlus P g * conePlus P g = 0 ∧
    coneMinus P g * coneMinus P g = 0 ∧
    peirce11 P (conePlus P g) = 0 ∧
    peirce11 P (coneMinus P g) = 0 ∧
    genPhi P g g * genPhi P g g = genV P g g := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- **Node `PA₄` (`peirce_grading_twist_identities`)**:
For any projector `P * P = P` and operator `g : B`:
1. The Peirce grading twist `invS P = P - (1 - P)` is an involution (`invS P * invS P = 1`),
2. Twisting the symmetric odd sum `genPhi P g g` by `invS P` produces the boundary commutator
   `invS P * genPhi P g g = comm P g`,
3. `comm P g = conePlus P g - coneMinus P g`,
4. `invS P` and `genPhi P g g` anti-commute (`invS P * genPhi P g g + genPhi P g g * invS P = 0`),
5. The square of the twisted wave equals `-genV P g g`:
   `(invS P * genPhi P g g) * (invS P * genPhi P g g) + genV P g g = 0`. -/
theorem peirce_grading_twist_identities (g : B) :
    invS P * invS P = 1 ∧
    invS P * genPhi P g g = comm P g ∧
    comm P g = conePlus P g - coneMinus P g ∧
    invS P * genPhi P g g + genPhi P g g * invS P = 0 ∧
    (invS P * genPhi P g g) * (invS P * genPhi P g g) + genV P g g = 0 := by
  have h3 : comm P g = conePlus P g - coneMinus P g := by
    simp only [comm, conePlus, coneMinus]
    noncomm_ring
  have h2 : invS P * genPhi P g g = comm P g := by
    rw [h3]
    peirce_nf hP
  refine ⟨by peirce_nf hP, h2, h3, by peirce_nf hP, by peirce_nf hP⟩

/-- **Node `PA₄` (`klt_twisted_double_copy_foam_defect`)**:
For any twist operator `Theta : B` commuting with the projector `P` (`P * Theta = Theta * P`),
the `Theta`-twisted diagonal quadratic defects on the `P` and `1 - P` sectors factor as the
braided double-copy products across `Theta`:
- `peirce11 P (g * Theta * g) - peirce11 P g * Theta * peirce11 P g = conePlus P g * Theta * coneMinus P g`,
- `peirce00 P (g * Theta * g) - peirce00 P g * Theta * peirce00 P g = coneMinus P g * Theta * conePlus P g`. -/
theorem klt_twisted_double_copy_foam_defect
    (g Theta : B) (hTheta : P * Theta = Theta * P) :
    peirce11 P (g * Theta * g) - peirce11 P g * Theta * peirce11 P g =
      conePlus P g * Theta * coneMinus P g ∧
    peirce00 P (g * Theta * g) - peirce00 P g * Theta * peirce00 P g =
      coneMinus P g * Theta * conePlus P g := by
  have hPTP : P * Theta * P = P * Theta := by
    calc P * Theta * P = P * (P * Theta) := by rw [mul_assoc, hTheta]
    _ = (P * P) * Theta := by noncomm_ring
    _ = P * Theta := by rw [hP]
  have h1T1 : (1 - P) * Theta * (1 - P) = Theta - P * Theta := by
    calc (1 - P) * Theta * (1 - P)
      _ = Theta - P * Theta - Theta * P + P * Theta * P := by noncomm_ring
      _ = Theta - P * Theta - P * Theta + P * Theta := by rw [← hTheta, hPTP]
      _ = Theta - P * Theta := by noncomm_ring
  have h11 :
      peirce11 P (g * Theta * g) - peirce11 P g * Theta * peirce11 P g =
        conePlus P g * Theta * coneMinus P g := by
    calc peirce11 P (g * Theta * g) - peirce11 P g * Theta * peirce11 P g
      _ = P * g * Theta * g * P - P * g * (P * Theta * P) * g * P := by
        simp only [peirce11]
        noncomm_ring
      _ = P * g * Theta * g * P - P * g * (P * Theta) * g * P := by rw [hPTP]
      _ = P * g * (Theta - P * Theta) * g * P := by noncomm_ring
      _ = P * g * ((1 - P) * Theta * (1 - P)) * g * P := by rw [← h1T1]
      _ = conePlus P g * Theta * coneMinus P g := by
        simp only [conePlus, coneMinus]
        noncomm_ring
  have h00 :
      peirce00 P (g * Theta * g) - peirce00 P g * Theta * peirce00 P g =
        coneMinus P g * Theta * conePlus P g := by
    calc peirce00 P (g * Theta * g) - peirce00 P g * Theta * peirce00 P g
      _ = (1 - P) * g * Theta * g * (1 - P) -
            (1 - P) * g * ((1 - P) * Theta * (1 - P)) * g * (1 - P) := by
        simp only [peirce00]
        noncomm_ring
      _ = (1 - P) * g * Theta * g * (1 - P) -
            (1 - P) * g * (Theta - P * Theta) * g * (1 - P) := by rw [h1T1]
      _ = (1 - P) * g * (P * Theta) * g * (1 - P) := by noncomm_ring
      _ = (1 - P) * g * (P * Theta * P) * g * (1 - P) := by rw [hPTP]
      _ = coneMinus P g * Theta * conePlus P g := by
        simp only [coneMinus, conePlus]
        noncomm_ring
  exact ⟨h11, h00⟩

/-- The inner and outer unweighted diagonal compression defects sum to `genV`. -/
theorem unweighted_compression_defects_sum_eq_genV (g : B) :
    (peirce11 P (g * g) - peirce11 P g * peirce11 P g) +
      (peirce00 P (g * g) - peirce00 P g * peirce00 P g) =
        genV P g g := by
  have hTheta : P * (1 : B) = (1 : B) * P := by simp
  have hKLT := klt_twisted_double_copy_foam_defect hP g 1 hTheta
  have hKLT' := hKLT
  simp only [mul_one] at hKLT'
  rw [hKLT'.1, hKLT'.2]
  simp [genV, anticomm]

/-- **Node `PA₅` (`amplituhedron_boundary_leibniz_and_unitarity_cut`)**:
1. The boundary commutator `comm P` satisfies the Leibniz derivation rule
   `comm P (X * Y) = comm P X * Y + X * comm P Y`,
2. Projecting `comm P g * comm P g` onto the `P` and `1 - P` sectors extracts the negative
   cross-boundary round-trip products:
   `peirce11 P (comm P g * comm P g) + conePlus P g * coneMinus P g = 0` and
   `peirce00 P (comm P g * comm P g) + coneMinus P g * conePlus P g = 0`. -/
theorem amplituhedron_boundary_leibniz_and_unitarity_cut (X Y g : B) :
    comm P (X * Y) = comm P X * Y + X * comm P Y ∧
    peirce11 P (comm P g * comm P g) + conePlus P g * coneMinus P g = 0 ∧
    peirce00 P (comm P g * comm P g) + coneMinus P g * conePlus P g = 0 := by
  have hLeib : comm P (X * Y) = comm P X * Y + X * comm P Y := by
    simp only [comm]
    noncomm_ring
  have hComm : comm P g = conePlus P g - coneMinus P g :=
    (peirce_grading_twist_identities hP g).2.2.1
  have h11 : peirce11 P (comm P g * comm P g) + conePlus P g * coneMinus P g = 0 := by
    rw [hComm]
    peirce_nf hP
  have h00 : peirce00 P (comm P g * comm P g) + coneMinus P g * conePlus P g = 0 := by
    rw [hComm]
    peirce_nf hP
  exact ⟨hLeib, h11, h00⟩

/-- **Node `PA₆` (`popper_surprise_and_survival_of_twisted_klt_foam`)**:
For any twist operator `Theta : B` commuting with `P` (`P * Theta = Theta * P`), non-vanishing
of the twisted diagonal defect `peirce11 P (g * Theta * g) - peirce11 P g * Theta * peirce11 P g ≠ 0`
implies that all three factors `conePlus P g`, `Theta`, and `coneMinus P g` are non-zero. -/
theorem popper_surprise_and_survival_of_twisted_klt_foam
    (g Theta : B) (hTheta : P * Theta = Theta * P)
    (h_surv : peirce11 P (g * Theta * g) - peirce11 P g * Theta * peirce11 P g ≠ 0) :
    conePlus P g ≠ 0 ∧ Theta ≠ 0 ∧ coneMinus P g ≠ 0 := by
  rw [(klt_twisted_double_copy_foam_defect hP g Theta hTheta).1] at h_surv
  refine ⟨?_, ?_, ?_⟩
  · intro hL
    rw [hL, zero_mul, zero_mul] at h_surv
    exact h_surv rfl
  · intro hT
    rw [hT, mul_zero, zero_mul] at h_surv
    exact h_surv rfl
  · intro hR
    rw [hR, mul_zero] at h_surv
    exact h_surv rfl

/-- **Node `PA₇` (`doubled_plabic_twisted_amplituhedron_master_synthesis`)**:
Unites in one theorem over `[Ring B]` for `hP : P * P = P` and `hTheta : P * Theta = Theta * P`:
1. Linear `P`-corner vanishing `peirce11 P (genPhi P g g) = 0`,
2. Doubled wave square `genPhi P g g * genPhi P g g = genV P g g`,
3. Grading twist identity `invS P * genPhi P g g = comm P g`,
4. Twisted double-copy factorization
   `peirce11 P (g * Theta * g) - peirce11 P g * Theta * peirce11 P g = conePlus P g * Theta * coneMinus P g`,
5. Quadratic boundary cut factorization
   `peirce11 P (comm P g * comm P g) = - (conePlus P g * coneMinus P g)`. -/
theorem doubled_plabic_twisted_amplituhedron_master_synthesis
    (g Theta : B) (hTheta : P * Theta = Theta * P) :
    peirce11 P (genPhi P g g) = 0 ∧
    genPhi P g g * genPhi P g g = genV P g g ∧
    invS P * genPhi P g g = comm P g ∧
    peirce11 P (g * Theta * g) - peirce11 P g * Theta * peirce11 P g =
      conePlus P g * Theta * coneMinus P g ∧
    peirce11 P (comm P g * comm P g) = - (conePlus P g * coneMinus P g) := by
  have hTwist := peirce_grading_twist_identities hP g
  have hKLT := (klt_twisted_double_copy_foam_defect hP g Theta hTheta).1
  have hCut : peirce11 P (comm P g * comm P g) = - (conePlus P g * coneMinus P g) := by
    rw [hTwist.2.2.1]
    peirce_nf hP
  exact ⟨by peirce_nf hP, by peirce_nf hP, hTwist.2.1, hKLT, hCut⟩

/-- **Unified `Ω₁–Ω₁₂ ⋈ HF₅` Master Operator Synthesis (`master_omega1_to_omega12_operator_synthesis`)**:
Over any associative ring `[Ring B]` with idempotent `hP : P * P = P`, tripotent `hH : H * (H * H) = H`,
involution `hS : S * S = 1`, `S`-odd operator `hQ : S * Q * S = -Q`, and involution `hC : C * C = 1`:
1. 3-Graded Peirce tripotency `comm P (comm P (comm P X)) = comm P X` and `invS P * genSig P X Y = genV P X Y`,
2. Inner Gödel (`P_hat`) and Outer Friedman (`W_hat`) Bruhat idempotency and partition of unity
   `P_hat_m + W_hat = 1`, `P_hat_m * W_hat = 0`,
3. Maurer–Cartan backpropagation identity
   `(conePlus P dX * (1 + coneMinus P Y) + (1 + conePlus P X) * coneMinus P dY) * ((1 - coneMinus P Y) * (1 - conePlus P X)) = conePlus P dX + (1 + conePlus P X) * coneMinus P dY * (1 - conePlus P X)`,
4. 5-Graded Kantor–Tanaka quintic `ad_H⁵(X) - 5 ad_H³(X) + 4 ad_H(X) = 0` and super-adjoint square
   `sad_Q(sad_Q(X)) = (Q * Q) * X - X * (Q * Q)`,
5. Bulk–Boundary decomposition `anticomm (evenGrade P C) (oddGrade P C) = 0` and
   `evenGrade P C * evenGrade P C + oddGrade P C * oddGrade P C = 1`. -/
theorem master_omega1_to_omega12_operator_synthesis
    (X Y dX dY H Q S C : B)
    (hH : H * (H * H) = H) (hS : S * S = 1) (hQ : S * Q * S = -Q) (hC : C * C = 1) :
    let P_hat := P + genPhi P X Y - genSig P X Y - genV P X Y * conePlus P X
    let P_hat_m := P - genPhi P X Y - genSig P X Y + genV P X Y * conePlus P X
    let W_hat := (1 - P) + genPhi P X Y + genSig P X Y - genV P X Y * conePlus P X
    let sadQ := fun Z : B => Q * Z - S * Z * S * Q
    comm P (comm P (comm P X)) = comm P X ∧
    invS P * genSig P X Y = genV P X Y ∧
    P_hat * P_hat = P_hat ∧
    W_hat * W_hat = W_hat ∧
    P_hat_m + W_hat = 1 ∧
    P_hat_m * W_hat = 0 ∧
    (conePlus P dX * (1 + coneMinus P Y) + (1 + conePlus P X) * coneMinus P dY) *
        ((1 - coneMinus P Y) * (1 - conePlus P X)) =
      conePlus P dX + (1 + conePlus P X) * coneMinus P dY * (1 - conePlus P X) ∧
    comm H (comm H (comm H (comm H (comm H X)))) -
      (comm H (comm H (comm H X)) + comm H (comm H (comm H X)) +
       comm H (comm H (comm H X)) + comm H (comm H (comm H X)) +
       comm H (comm H (comm H X))) +
      (comm H X + comm H X + comm H X + comm H X) = 0 ∧
    sadQ (sadQ X) = (Q * Q) * X - X * (Q * Q) ∧
    anticomm (evenGrade P C) (oddGrade P C) = 0 ∧
    evenGrade P C * evenGrade P C + oddGrade P C * oddGrade P C = 1 := by
  have hQS : Q * S = - (S * Q) := by
    calc Q * S = (S * S) * Q * S := by rw [hS, one_mul]
    _ = S * (S * Q * S) := by noncomm_ring
    _ = S * (-Q) := by rw [hQ]
    _ = - (S * Q) := by noncomm_ring
  have hSad :
      Q * (Q * X - S * X * S * Q) - S * (Q * X - S * X * S * Q) * S * Q =
        (Q * Q) * X - X * (Q * Q) := by
    calc Q * (Q * X - S * X * S * Q) - S * (Q * X - S * X * S * Q) * S * Q
      _ = (Q * Q) * X - (Q * S) * X * S * Q - S * Q * X * S * Q +
            (S * S) * X * (S * Q * S) * Q := by noncomm_ring
      _ = (Q * Q) * X - (-(S * Q)) * X * S * Q - S * Q * X * S * Q +
            1 * X * (-Q) * Q := by rw [hQS, hS, hQ]
      _ = (Q * Q) * X - X * (Q * Q) := by noncomm_ring
  have hH_trip : ∀ Z : B, H * (H * (H * Z)) = H * Z := fun Z => by
    calc H * (H * (H * Z)) = (H * (H * H)) * Z := by simp only [mul_assoc]
    _ = H * Z := by rw [hH]
  have hQuintic :
      comm H (comm H (comm H (comm H (comm H X)))) -
        (comm H (comm H (comm H X)) + comm H (comm H (comm H X)) +
         comm H (comm H (comm H X)) + comm H (comm H (comm H X)) +
         comm H (comm H (comm H X))) +
        (comm H X + comm H X + comm H X + comm H X) = 0 := by
    dsimp only [comm]
    simp only [sub_mul, mul_sub, mul_assoc, hH, hH_trip]
    abel
  have hP_idem : ∀ Z : B, P * (P * Z) = P * Z := fun Z => by rw [← mul_assoc, hP]
  have hC_idem : ∀ Z : B, C * (C * Z) = Z := fun Z => by rw [← mul_assoc, hC, one_mul]
  have hAnti : anticomm (evenGrade P C) (oddGrade P C) = 0 := by
    dsimp only [evenGrade, oddGrade, anticomm]
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
               mul_assoc, hP, hP_idem, hC, hC_idem]
    abel
  have hSq : evenGrade P C * evenGrade P C + oddGrade P C * oddGrade P C = 1 := by
    dsimp only [evenGrade, oddGrade]
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
               mul_assoc, hP, hP_idem, hC, hC_idem]
    abel
  exact ⟨by peirce_nf hP, by peirce_nf hP, by peirce_nf hP, by peirce_nf hP,
         by peirce_nf hP, by peirce_nf hP, by peirce_nf hP,
         hQuintic, hSad, hAnti, hSq⟩

/-- **Macroscopic Causal Rectification of Acausal Foam (`macroscopic_causal_rectification_of_acausal_foam`)**:
Projecting the symmetric foam anticommutator `genV P g g = conePlus P g * coneMinus P g + coneMinus P g * conePlus P g`
onto `P` preserves `conePlus P g * coneMinus P g` and annihilates `coneMinus P g * conePlus P g`,
while projecting onto `1 - P` preserves `coneMinus P g * conePlus P g` and annihilates `conePlus P g * coneMinus P g`. -/
theorem macroscopic_causal_rectification_of_acausal_foam
    (g : B) :
    peirce11 P (conePlus P g * coneMinus P g) = conePlus P g * coneMinus P g ∧
    peirce11 P (coneMinus P g * conePlus P g) = 0 ∧
    peirce11 P (genV P g g) = conePlus P g * coneMinus P g ∧
    peirce00 P (coneMinus P g * conePlus P g) = coneMinus P g * conePlus P g ∧
    peirce00 P (conePlus P g * coneMinus P g) = 0 ∧
    peirce00 P (genV P g g) = coneMinus P g * conePlus P g := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- **Degree-3 Bruhat Observer Self-Closure (`degree_three_bruhat_observer_self_closure`)**:
1. Naive linear wave addition `P + genPhi P g g` has quadratic idempotence defect `genV P g g`,
2. Quadratic commutator subtraction `P + genPhi P g g - genSig P g g` has quartic defect `genV P g g * genV P g g`,
3. The unimodular Bruhat rotor `(1 - conePlus P g) * (1 + coneMinus P g)` has two-sided inverse
   `(1 - coneMinus P g) * (1 + conePlus P g)`,
4. Conjugating `P` by the Bruhat rotor yields `dressedPeirceProjector P g g = P + genPhi P g g - genSig P g g - genV P g g * conePlus P g`,
   which is strictly idempotent (`dressedPeirceProjector P g g * dressedPeirceProjector P g g = dressedPeirceProjector P g g`). -/
theorem degree_three_bruhat_observer_self_closure
    (g : B) :
    (P + genPhi P g g) * (P + genPhi P g g) - (P + genPhi P g g) = genV P g g ∧
    (P + genPhi P g g - genSig P g g) * (P + genPhi P g g - genSig P g g) -
      (P + genPhi P g g - genSig P g g) = genV P g g * genV P g g ∧
    ((1 - conePlus P g) * (1 + coneMinus P g)) *
      ((1 - coneMinus P g) * (1 + conePlus P g)) = 1 ∧
    ((1 - coneMinus P g) * (1 + conePlus P g)) *
      ((1 - conePlus P g) * (1 + coneMinus P g)) = 1 ∧
    ((1 - conePlus P g) * (1 + coneMinus P g)) * P *
      ((1 - coneMinus P g) * (1 + conePlus P g)) =
      P + genPhi P g g - genSig P g g - genV P g g * conePlus P g ∧
    (P + genPhi P g g - genSig P g g - genV P g g * conePlus P g) *
      (P + genPhi P g g - genSig P g g - genV P g g * conePlus P g) =
      P + genPhi P g g - genSig P g g - genV P g g * conePlus P g := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-! ### Constructive Globular Boundary & Elementary Expansion Over `[Ring B]` (`𝔊ℌ₁`, `𝔊ℌ₃`, `𝔊ℌ₅`) -/

omit hP in
/-- Constructive globular target operator `t(X) := conePlus P g * X` inside `[Ring B]`. -/
def globTarget (P g X : B) : B := conePlus P g * X

omit hP in
/-- Constructive globular source operator `s(X) := invS P * X * invS P * conePlus P g` inside `[Ring B]`. -/
def globSource (P g X : B) : B := invS P * X * invS P * conePlus P g

omit hP in
/-- Constructive globular boundary super-derivation `∂_{N_+}(X) := globTarget P g X - globSource P g X`. -/
def globBoundary (P g X : B) : B := globTarget P g X - globSource P g X

omit hP in
/-- Constructive elementary expansion `i_exp P g X := G_+ * X * G_+⁻¹` by the unimodular
Bruhat cylinder rotor `G_+ = (1 - conePlus P g) * (1 + coneMinus P g)`. -/
def i_exp (P g X : B) : B :=
  ((1 - conePlus P g) * (1 + coneMinus P g)) * X * ((1 - coneMinus P g) * (1 + conePlus P g))

omit hP in
/-- Constructive coherator retraction `r_ret P g Y := P * G_+⁻¹ * Y * G_+ * P` back onto the
`peirce11 P` base algebra. -/
def r_ret (P g Y : B) : B :=
  P * ((1 - coneMinus P g) * (1 + conePlus P g)) * Y * ((1 - conePlus P g) * (1 + coneMinus P g)) * P

/-- **Internal Globular Boundary Nilpotence (`internal_globular_boundary_squared_zero`, `𝔊ℌ₁`)**:
Over any associative ring `[Ring B]` with idempotent `hP : P * P = P`, the constructive
globular target `globTarget P g`, source `globSource P g`, and super-derivation boundary
`globBoundary P g` satisfy `globTarget² = 0`, `globSource² = 0`, anticommutation
`globTarget ∘ globSource = - globSource ∘ globTarget`, and `globBoundary² = 0`. -/
theorem internal_globular_boundary_squared_zero
    (g X : B) :
    globTarget P g (globTarget P g X) = 0 ∧
    globSource P g (globSource P g X) = 0 ∧
    globTarget P g (globSource P g X) = - globSource P g (globTarget P g X) ∧
    globBoundary P g (globBoundary P g X) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (dsimp only [globBoundary, globTarget, globSource]; peirce_nf hP)

/-- **Weak Coherator Defect Witness (`coherator_weak_vs_strict_socratic_defect`, `𝔊ℌ₃`)**:
In any non-commutative ring `[Ring B]` with `hP : P * P = P`, the compressed multiplicative
defect `P * (F * F) * P - (P * F * P) * (P * F * P)` equals the upper-lower Peirce corner
product `conePlus P F * coneMinus P F`, and non-vanishing of this defect forces both
`conePlus P F ≠ 0` and `coneMinus P F ≠ 0`. -/
theorem coherator_weak_vs_strict_socratic_defect
    (F : B)
    (h_non : P * (F * F) * P - (P * F * P) * (P * F * P) ≠ 0) :
    P * (F * F) * P - (P * F * P) * (P * F * P) = conePlus P F * coneMinus P F ∧
    (conePlus P F ≠ 0 ∧ coneMinus P F ≠ 0) := by
  have h_def : P * (F * F) * P - (P * F * P) * (P * F * P) = conePlus P F * coneMinus P F := by
    dsimp only [conePlus, coneMinus]
    peirce_nf hP
  refine ⟨h_def, ?_, ?_⟩
  · intro h_np
    apply h_non
    rw [h_def, h_np, zero_mul]
  · intro h_nm
    apply h_non
    rw [h_def, h_nm, mul_zero]

/-- **Constructive Elementary Expansion 4-Term Word & Commutator Shift (`constructive_elementary_expansion_word_and_commutator_shift`, `𝔊ℌ₅-A`)**:
For any base cell `x := P * X * P` in the `peirce11 P` subalgebra:
1. The constructive elementary expansion `i_exp P g x` expands into the exact 4-term coherator word
   `x + (x * conePlus P g + coneMinus P g * x) + (coneMinus P g * x * conePlus P g - (conePlus P g * coneMinus P g) * x) - (conePlus P g * coneMinus P g) * x * conePlus P g`,
2. Its even Peirce grade shift `evenGrade P (i_exp P g x - x)` equals the exact negative commutator
   `- comm (conePlus P g) (coneMinus P g * x)`. -/
theorem constructive_elementary_expansion_word_and_commutator_shift
    (g X : B) :
    let x := P * X * P
    let np := conePlus P g
    let nm := coneMinus P g
    let qp := np * nm
    i_exp P g x = x + (x * np + nm * x) + (nm * x * np - qp * x) - qp * x * np ∧
    evenGrade P (i_exp P g x - x) = - comm np (nm * x) := by
  refine ⟨?_, ?_⟩ <;>
    (dsimp only [i_exp]; peirce_nf hP)

/-- **Constructive Two-Sided Retraction Isomorphism (`constructive_elementary_expansion_retraction_isomorphism`, `𝔊ℌ₅-B`)**:
For any base cell `x := P * X * P` and dressed cell
`yh := dressedPeirceProjector P g g * Y * dressedPeirceProjector P g g`, the constructive
elementary expansion `i_exp P g` and retraction `r_ret P g` satisfy:
1. Left inverse on the base algebra: `r_ret P g (i_exp P g x) = x`,
2. Right inverse on the dressed algebra: `i_exp P g (r_ret P g yh) = yh`,
3. Exact ring homomorphism law: `i_exp P g (X1 * X2) = i_exp P g X1 * i_exp P g X2`. -/
theorem constructive_elementary_expansion_retraction_isomorphism
    (g X Y X1 X2 : B) :
    let x := P * X * P
    let yh := dressedPeirceProjector P g g * Y * dressedPeirceProjector P g g
    r_ret P g (i_exp P g x) = x ∧
    i_exp P g (r_ret P g yh) = yh ∧
    i_exp P g (X1 * X2) = i_exp P g X1 * i_exp P g X2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (dsimp only [i_exp, r_ret, dressedPeirceProjector]; peirce_nf hP)

end InfoGeometry.OperatorAlgebra.PeirceSpine
