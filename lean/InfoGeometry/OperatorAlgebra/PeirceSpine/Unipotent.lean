/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Homogenized

/-!
# Peirce spine A₁₂–A₂₂: unipotent conjugation, Steinberg braid, operator projective line

* A₁₂ `Ad(1 ± N₊)`, `Ad(1 ± N₋)` form two additive one-parameter groups;
* A₁₄ their action on the tetraktys; `V` is invariant;
* A₁₆ the Cayley–Weyl element `W = J + 1 - V` and the Steinberg braid;
* A₁₇/A₁₉ corner absorption and A₁₈ shear action on the homogenized channels;
* A₂₁ the affine charts `P - N₊(X)`, `(1 - P) - N₋(Y)` of the operator projective line;
* A₂₂ Hua's distance identity and the operator cross-ratio.

**Corrections to the intake.** A random `6 × 6` numerical model with a
non-orthogonal idempotent refutes four candidate conjuncts. They are stated here in
corrected form:

* A₁₄.10: `Ad₊ Ad₋ P - Ad₋ Ad₊ P = -(V Φ)`, not `2 Σ - V J`;
* A₁₆.8: `(1 + N₊)(1 - N₋)(1 + N₊) = W + (1 - V) N₊`, not `W + N₊ + V N₊`;
* A₁₆.9 and A₂₁.7: the Steinberg image of `P` is
  `P - 2N₊ - N₋ - 2Σ + 3VN₊ + VN₋ + VΣ - V²N₊` (`steinberg_image_idem`).
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

def conjPlus (P A X : B) : B := (1 + conePlus P A) * X * (1 - conePlus P A)
def conjPlusInv (P A X : B) : B := (1 - conePlus P A) * X * (1 + conePlus P A)
def conjMinus (P C X : B) : B := (1 + coneMinus P C) * X * (1 - coneMinus P C)
def conjMinusInv (P C X : B) : B := (1 - coneMinus P C) * X * (1 + coneMinus P C)

/-- The Cayley–Weyl element `W = J + (1 - V)`. -/
def weylJ (P A C : B) : B := genJ P A C + (1 - genV P A C)
def weylJInv (P A C : B) : B := -genJ P A C + (1 - genV P A C)

/-- The Steinberg braid `(1 + N₊)(1 - N₋)(1 + N₊)` and its inverse. -/
def steinbergBraid (P A C : B) : B :=
  (1 + conePlus P A) * (1 - coneMinus P C) * (1 + conePlus P A)
def steinbergBraidInv (P A C : B) : B :=
  (1 - conePlus P A) * (1 + coneMinus P C) * (1 - conePlus P A)

/-- The dual Steinberg braid `(1 - N₋)(1 + N₊)(1 - N₋)` and its inverse. -/
def steinbergBraidDual (P A C : B) : B :=
  (1 - coneMinus P C) * (1 + conePlus P A) * (1 - coneMinus P C)
def steinbergBraidDualInv (P A C : B) : B :=
  (1 + coneMinus P C) * (1 - conePlus P A) * (1 + coneMinus P C)

/-- Upper chart of the operator projective line, centred at `P`. -/
def projChartPlus (P X : B) : B := P - conePlus P X
/-- Lower chart of the operator projective line, centred at `1 - P`. -/
def projChartMinus (P Y : B) : B := (1 - P) - coneMinus P Y

/-- The operator cross-ratio `{P(X₁) - P(X₂), Q(Y₁) - Q(Y₂)}`. -/
def operatorCrossRatio (P X₁ X₂ Y₁ Y₂ : B) : B :=
  anticomm (projChartPlus P X₁ - projChartPlus P X₂) (projChartMinus P Y₁ - projChartMinus P Y₂)

/-- Multiscale unipotent idempotent tower: at each step `k`, the idempotent `P_k`
is conjugated by the upper Peirce shear `1 + conePlus P_k (A k)` along the
step generator `A k`. -/
def unipotentIdempotentTower (A : ℕ → B) : ℕ → B → B
  | 0, P => P
  | k + 1, P =>
      let P_k := unipotentIdempotentTower A k P
      conjPlus P_k (A k) P_k

variable {P : B} (hP : P * P = P)
include hP

/-! ### A₁₂ -/

theorem archetype_A12_nilpotent_conjugation_group (A₁ A₂ C₁ C₂ X : B) :
    conjPlus P A₁ X = X + comm (conePlus P A₁) X - conePlus P A₁ * X * conePlus P A₁ ∧
    conjMinus P C₁ X = X + comm (coneMinus P C₁) X - coneMinus P C₁ * X * coneMinus P C₁ ∧
    conjPlus P A₁ (conjPlusInv P A₁ X) = X ∧
    conjPlusInv P A₁ (conjPlus P A₁ X) = X ∧
    conjMinus P C₁ (conjMinusInv P C₁ X) = X ∧
    conjMinusInv P C₁ (conjMinus P C₁ X) = X ∧
    conjPlus P A₁ (conjPlus P A₂ X) = conjPlus P (A₁ + A₂) X ∧
    conjMinus P C₁ (conjMinus P C₂ X) = conjMinus P (C₁ + C₂) X ∧
    conjPlus P A₁ P = P - conePlus P A₁ ∧
    conjMinus P C₁ P = P + coneMinus P C₁ ∧
    conjPlus P A₁ (invS P) = invS P - (2 : ℤ) • conePlus P A₁ ∧
    conjMinus P C₁ (invS P) = invS P + (2 : ℤ) • coneMinus P C₁ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    ((try simp only [conjPlus, conjPlusInv, conjMinus, conjMinusInv]); peirce_nf hP)

/-! ### A₁₄ -/

theorem archetype_A14_unipotent_tetraktys_action (A C : B) :
    conjPlus P A (genV P A C) = genV P A C ∧
    conjPlusInv P A (genV P A C) = genV P A C ∧
    conjMinus P C (genV P A C) = genV P A C ∧
    conjMinusInv P C (genV P A C) = genV P A C ∧
    conjPlus P A (conjMinus P C (genV P A C)) = genV P A C ∧
    conjPlus P A (genSig P A C) = genSig P A C - (2 : ℤ) • (genV P A C * conePlus P A) ∧
    conjMinus P C (genSig P A C) = genSig P A C + (2 : ℤ) • (genV P A C * coneMinus P C) ∧
    conjPlus P A (genPhi P A C) = genPhi P A C + genSig P A C - genV P A C * conePlus P A ∧
    conjMinus P C (genPhi P A C) =
      genPhi P A C - genSig P A C - genV P A C * coneMinus P C ∧
    conjPlus P A (conjMinus P C P) - conjMinus P C (conjPlus P A P) =
      -(genV P A C * genPhi P A C) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    ((try simp only [conjPlus, conjPlusInv, conjMinus, conjMinusInv]); peirce_nf hP)

/-! ### A₁₆ -/

/-- The Steinberg image of `P`, as an explicit polynomial in the tetraktys. -/
theorem steinberg_image_idem (A C : B) :
    conjPlus P A (conjMinusInv P C (conjPlus P A P)) =
      P - (2 : ℤ) • conePlus P A - coneMinus P C - (2 : ℤ) • genSig P A C +
        (3 : ℤ) • (genV P A C * conePlus P A) + genV P A C * coneMinus P C +
        genV P A C * genSig P A C - genV P A C * genV P A C * conePlus P A := by
  simp only [conjPlus, conjMinusInv]; peirce_nf hP

theorem steinbergBraid_mul_inv (A C : B) :
    steinbergBraid P A C * steinbergBraidInv P A C = 1 ∧
    steinbergBraidInv P A C * steinbergBraid P A C = 1 := by
  refine ⟨?_, ?_⟩ <;> ((try simp only [steinbergBraid, steinbergBraidInv]); peirce_nf hP)

theorem steinbergBraidDual_mul_inv (A C : B) :
    steinbergBraidDual P A C * steinbergBraidDualInv P A C = 1 ∧
    steinbergBraidDualInv P A C * steinbergBraidDual P A C = 1 := by
  refine ⟨?_, ?_⟩ <;> ((try simp only [steinbergBraidDual, steinbergBraidDualInv]); peirce_nf hP)

/-- An expansion of the dual Steinberg word, its difference from the upper
word, and the two palindromic element sums (`A18` of `1E6iR`, `A73` of
`1ofa`). These are ring identities; no Yang–Baxter or trace structure is
asserted here. -/
theorem steinbergBraid_dual_expansion_and_difference (A C : B) :
    steinbergBraidDual P A C =
      weylJ P A C - (1 - genV P A C) * coneMinus P C ∧
    steinbergBraid P A C - steinbergBraidDual P A C =
      (1 - genV P A C) * genPhi P A C ∧
    steinbergBraid P A C + steinbergBraidInv P A C =
      (2 : ℤ) • (1 - genV P A C) ∧
    steinbergBraidDual P A C + steinbergBraidDualInv P A C =
      (2 : ℤ) • (1 - genV P A C) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    ((try simp only [steinbergBraid, steinbergBraidInv,
      steinbergBraidDual, steinbergBraidDualInv, weylJ]); peirce_nf hP)

/-- The two Steinberg words both collapse to the Weyl element exactly when
the two oriented mass-weighted corner shears vanish. The criterion keeps the
two corner equations separate, so no cancellation between Peirce corners is
assumed. -/
theorem steinberg_braids_collapse_iff_corner_absorption (A C : B) :
    (steinbergBraid P A C = weylJ P A C ∧
      steinbergBraidDual P A C = weylJ P A C) ↔
    ((1 - genV P A C) * conePlus P A = 0 ∧
      (1 - genV P A C) * coneMinus P C = 0) := by
  rcases steinbergBraid_dual_expansion_and_difference hP A C with
    ⟨hMinus, hDiff, _, _⟩
  have hPlus : steinbergBraid P A C =
      weylJ P A C + (1 - genV P A C) * conePlus P A := by
    calc
      steinbergBraid P A C =
          (steinbergBraid P A C - steinbergBraidDual P A C) +
            steinbergBraidDual P A C := by noncomm_ring
      _ = (1 - genV P A C) * genPhi P A C +
            (weylJ P A C - (1 - genV P A C) * coneMinus P C) := by
              rw [hDiff, hMinus]
      _ = weylJ P A C + (1 - genV P A C) * conePlus P A := by
              dsimp [genPhi]
              noncomm_ring
  constructor
  · rintro ⟨hPlusEq, hMinusEq⟩
    constructor
    · calc
        (1 - genV P A C) * conePlus P A =
            (weylJ P A C + (1 - genV P A C) * conePlus P A) - weylJ P A C := by
              noncomm_ring
        _ = steinbergBraid P A C - weylJ P A C := by rw [hPlus]
        _ = 0 := by rw [hPlusEq]; simp
    · calc
        (1 - genV P A C) * coneMinus P C =
            weylJ P A C - (weylJ P A C - (1 - genV P A C) * coneMinus P C) := by
              noncomm_ring
        _ = weylJ P A C - steinbergBraidDual P A C := by rw [hMinus]
        _ = 0 := by rw [hMinusEq]; simp
  · rintro ⟨hPlusZero, hMinusZero⟩
    constructor
    · rw [hPlus]
      simp [hPlusZero]
    · rw [hMinus]
      simp [hMinusZero]

omit hP in
/-- Conjugation by the braid is the composite of the three unipotent conjugations. -/
theorem steinbergBraid_conj (A C X : B) :
    steinbergBraid P A C * X * steinbergBraidInv P A C =
      conjPlus P A (conjMinusInv P C (conjPlus P A X)) := by
  simp only [steinbergBraid, steinbergBraidInv, conjPlus, conjMinusInv]; noncomm_ring

theorem archetype_A16_cayley_weyl_steinberg_reflection (A C : B) :
    weylJ P A C * weylJInv P A C - 1 = genV P A C * genV P A C - genV P A C ∧
    weylJInv P A C * weylJ P A C - 1 = genV P A C * genV P A C - genV P A C ∧
    comm (weylJ P A C) (genV P A C) = 0 ∧
    genJ P A C * peirce11 P (genV P A C) * (-genJ P A C) =
      peirce00 P (genV P A C * genV P A C) ∧
    genJ P A C * peirce00 P (genV P A C) * (-genJ P A C) =
      peirce11 P (genV P A C * genV P A C) ∧
    genPhi P A C * peirce11 P (genV P A C) * genPhi P A C =
      peirce00 P (genV P A C * genV P A C) ∧
    genPhi P A C * peirce00 P (genV P A C) * genPhi P A C =
      peirce11 P (genV P A C * genV P A C) ∧
    steinbergBraid P A C = weylJ P A C + (1 - genV P A C) * conePlus P A := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    ((try simp only [weylJ, weylJInv, steinbergBraid]); peirce_nf hP)

/-- The Peirce grading separates the even Weyl-scale component of the
Steinberg braid from its odd component.  The odd component retains both the
phase generator and the scale-weighted upper-cone shear; this statement makes
no assumption that the shear or the defect vanishes. -/
theorem steinberg_braid_peirce_scale_and_shear (A C : B) :
    evenGrade P (steinbergBraid P A C) = 1 - genV P A C ∧
    oddGrade P (steinbergBraid P A C) =
      genJ P A C + (1 - genV P A C) * conePlus P A := by
  have hExpansion : steinbergBraid P A C =
      weylJ P A C + (1 - genV P A C) * conePlus P A := by
    exact (archetype_A16_cayley_weyl_steinberg_reflection hP A C).2.2.2.2.2.2.2
  rw [hExpansion]
  constructor <;> simp only [evenGrade_add, oddGrade_add] <;>
    simp only [evenGrade, oddGrade, weylJ, genJ, genV, anticomm,
      conePlus, coneMinus, add_mul, mul_add, sub_mul, mul_sub,
      one_mul, mul_one, mul_assoc] <;> peirce_nf hP

/-! ### A₁₇–A₁₉ -/

theorem archetype_A17_A19_right_corner_absorption (A C : B) :
    conePlus P A * P = 0 ∧
    coneMinus P C * (1 - P) = 0 ∧
    genV P A C * P = conePlus P A * coneMinus P C * P ∧
    genV P A C * (1 - P) = (1 - P) * coneMinus P C * conePlus P A ∧
    genSig P A C * P = conePlus P A * coneMinus P C * P ∧
    genSig P A C * (1 - P) = -(1 - P) * coneMinus P C * conePlus P A := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-! ### A₁₈: action of the unipotent shears on the homogenized channels -/

theorem archetype_A18_unipotent_shear_tomography (A C : B) :
    hProjV P A C (conjPlus P A (genSig P A C)) = 0 ∧
    hProjV P A C (conjPlus P A (genPhi P A C)) = 0 ∧
    hProjV P A C (conjPlus P A (genJ P A C)) = 0 ∧
    hProjV P A C (conjMinus P C (genSig P A C)) = 0 ∧
    hProjSig P A C (conjPlus P A (genSig P A C)) =
      (8 : ℤ) • ((genV P A C * genV P A C) * genSig P A C) ∧
    hProjPhi P A C (conjPlus P A (genSig P A C)) =
      -((8 : ℤ) • ((genV P A C * genV P A C * genV P A C) * genPhi P A C)) ∧
    hProjJ P A C (conjPlus P A (genSig P A C)) =
      -((8 : ℤ) • ((genV P A C * genV P A C * genV P A C) * genJ P A C)) ∧
    hProjSig P A C (conjPlus P A (genPhi P A C)) =
      (8 : ℤ) • ((genV P A C * genV P A C) * genSig P A C) ∧
    hProjJ P A C (conjPlus P A (genPhi P A C)) =
      -((4 : ℤ) • ((genV P A C * genV P A C * genV P A C) * genJ P A C)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [conjPlus, conjMinus, hProjV, hProjPhi, hProjJ, hProjSig,
      derivSqPhi, derivSqJ, derivSqSig]; peirce_nf hP)

/-! ### A₂₁ -/

/-- Ordered Möbius–Bruhat factor and inverse expansions from the A21 source.
The factors are kept in their noncommutative order; the two Peirce diagonal
terms in the expansions are generally distinct. -/
theorem moebius_bruhat_factor_expansions (A C : B) :
    (1 + conePlus P A) * (1 - coneMinus P C) =
      1 + genJ P A C - peirce11 P (genV P A C) ∧
    (1 + coneMinus P C) * (1 - conePlus P A) =
      1 - genJ P A C - peirce00 P (genV P A C) ∧
    ((1 + conePlus P A) * (1 - coneMinus P C)) *
        ((1 + coneMinus P C) * (1 - conePlus P A)) = 1 ∧
    ((1 + coneMinus P C) * (1 - conePlus P A)) *
        ((1 + conePlus P A) * (1 - coneMinus P C)) = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- The ordered Möbius–Bruhat unit acts on the cut by conjugation. Its orbit
point remains idempotent, the tetraktys metric is fixed, and the point has
the exact Peirce expansion from the A21 source. This is a ring identity for
the displayed unit and inverse; it does not assert a group action or a
Grassmannian structure on the carrier. -/
theorem moebius_bruhat_idempotent_orbit_and_metric_invariance (A C : B) :
    let g := (1 + conePlus P A) * (1 - coneMinus P C)
    let gInv := (1 + coneMinus P C) * (1 - conePlus P A)
    (g * P * gInv) * (g * P * gInv) = g * P * gInv ∧
    g * genV P A C * gInv = genV P A C ∧
    g * P * gInv =
      P - genJ P A C - genSig P A C + genV P A C * conePlus P A -
        (2 : ℤ) • coneMinus P C := by
  dsimp
  peirce_nf hP; trivial

theorem archetype_A21_operator_projective_line (A C X : B) :
    projChartPlus P X * projChartPlus P X = projChartPlus P X ∧
    projChartMinus P C * projChartMinus P C = projChartMinus P C ∧
    conjPlus P A (projChartPlus P X) = projChartPlus P (X + A) ∧
    conjMinus P C (projChartMinus P X) = projChartMinus P (X + C) ∧
    P - genSig P A C = (1 - P) * genV P A C + P * (1 - genV P A C) ∧
    (1 - P) + genSig P A C = P * genV P A C + (1 - P) * (1 - genV P A C) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    ((try simp only [projChartPlus, projChartMinus, conjPlus, conjMinus]); peirce_nf hP)

/-- Corrected A₂₁.7: the braid moves the north pole `P` to the Steinberg polynomial. -/
theorem archetype_A21_steinberg_north_to_south (A C : B) :
    steinbergBraid P A C * P * steinbergBraidInv P A C =
      P - (2 : ℤ) • conePlus P A - coneMinus P C - (2 : ℤ) • genSig P A C +
        (3 : ℤ) • (genV P A C * conePlus P A) + genV P A C * coneMinus P C +
        genV P A C * genSig P A C - genV P A C * genV P A C * conePlus P A := by
  rw [steinbergBraid_conj, steinberg_image_idem hP]

/-! ### A₂₂ -/

theorem archetype_A22_hua_distance_and_cross_ratio (A C X Y X₁ X₂ Y₁ Y₂ : B) :
    (projChartPlus P X - projChartMinus P Y) * (projChartPlus P X - projChartMinus P Y) =
      1 - genV P X Y ∧
    operatorCrossRatio P X₁ X₂ Y₁ Y₂ = genV P (X₁ - X₂) (Y₁ - Y₂) ∧
    operatorCrossRatio P A 0 C 0 = genV P A C ∧
    operatorCrossRatio P (X₁ + A) (X₂ + A) (Y₁ + C) (Y₂ + C) =
      operatorCrossRatio P X₁ X₂ Y₁ Y₂ ∧
    conjPlus P (X₁ - X₂) (operatorCrossRatio P X₁ X₂ Y₁ Y₂) =
      operatorCrossRatio P X₁ X₂ Y₁ Y₂ ∧
    conjMinus P (Y₁ - Y₂) (operatorCrossRatio P X₁ X₂ Y₁ Y₂) =
      operatorCrossRatio P X₁ X₂ Y₁ Y₂ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    ((try simp only [operatorCrossRatio, projChartPlus, projChartMinus, conjPlus, conjMinus]);
      peirce_nf hP)

/-- The A22 source's displacement brackets of the two translated cut points.
For these exact arguments the Jordan and Lie brackets are `-V` and `-Σ`.
This definition-level calculation is kept separate from
`operatorCrossRatio`, whose owner convention gives `+V`. -/
theorem translated_idempotent_displacement_brackets (A C : B) :
    anticomm (P - conjPlus P A P) (P - conjMinus P C P) = -genV P A C ∧
    comm (P - conjPlus P A P) (P - conjMinus P C P) = -genSig P A C := by
  refine ⟨?_, ?_⟩ <;>
    (simp only [conjPlus, conjMinus]; peirce_nf hP)

/-- The A22 displacement Jordan bracket is invariant under the three
source-listed conjugations when each conjugation is applied to all four
arguments. The statement uses the source's explicit displacement formula,
not the separately defined `operatorCrossRatio`. -/
theorem translated_idempotent_displacement_jordan_invariance (A C : B) :
    let g := (1 + conePlus P A) * (1 - coneMinus P C)
    let gInv := (1 + coneMinus P C) * (1 - conePlus P A)
    anticomm
        (conjPlus P A P - conjPlus P A (conjPlus P A P))
        (conjPlus P A P - conjPlus P A (conjMinus P C P)) = -genV P A C ∧
    anticomm
        (conjMinus P C P - conjMinus P C (conjPlus P A P))
        (conjMinus P C P - conjMinus P C (conjMinus P C P)) = -genV P A C ∧
    anticomm
        (g * P * gInv - g * (conjPlus P A P) * gInv)
        (g * P * gInv - g * (conjMinus P C P) * gInv) = -genV P A C := by
  dsimp
  simp only [conjPlus, conjMinus]
  refine ⟨?_, ?_, ?_⟩ <;> peirce_nf hP

/-- The ordered A22 Hua products isolate the two diagonal Peirce corners
of the metric `V`; adding and subtracting them recovers `V` and `Σ`. The
conjugation order matters: `conjPlus P A P = P - conePlus P A`. -/
theorem translated_idempotent_hua_cross_ratio_products (A C : B) :
    P * (1 - conjPlus P A P) * (1 - P) * conjMinus P C P * P =
      peirce11 P (genV P A C) ∧
    (1 - P) * conjMinus P C P * P * (1 - conjPlus P A P) * (1 - P) =
      peirce00 P (genV P A C) ∧
    P * (1 - conjPlus P A P) * (1 - P) * conjMinus P C P * P +
      (1 - P) * conjMinus P C P * P * (1 - conjPlus P A P) * (1 - P) =
        genV P A C ∧
    P * (1 - conjPlus P A P) * (1 - P) * conjMinus P C P * P -
      (1 - P) * conjMinus P C P * P * (1 - conjPlus P A P) * (1 - P) =
        genSig P A C := by
  have hPlus : conjPlus P A P = P - conePlus P A := by
    unfold conjPlus
    peirce_nf hP
  have hMinus : conjMinus P C P = P + coneMinus P C := by
    unfold conjMinus
    peirce_nf hP
  rw [hPlus, hMinus]
  peirce_nf hP; trivial

/-! ### A₂₃: translated idempotent chords -/

/-- Ordered chord reconstruction for the two unipotently translated copies
of an idempotent. The statement is only a ring identity: it makes no claim
about a positive Grassmannian or a geometric embedding. -/
theorem translated_idempotent_chord_readout (A A₁ A₂ C C₁ C₂ : B) :
    (P - conePlus P A₁) * (P - conePlus P A₂) = P - conePlus P A₂ ∧
    (P + coneMinus P C₁) * (P + coneMinus P C₂) = P + coneMinus P C₁ ∧
    P * (P - conePlus P A) = P - conePlus P A ∧
    (P - conePlus P A) * P = P ∧
    (P + coneMinus P C) * P = P + coneMinus P C ∧
    P * (P + coneMinus P C) = P ∧
    (P + coneMinus P C) - (P - conePlus P A) = genPhi P A C ∧
    (P - (P - conePlus P A)) - ((P + coneMinus P C) - P) = genJ P A C ∧
    ((P + coneMinus P C) - (P - conePlus P A)) *
        ((P + coneMinus P C) - (P - conePlus P A)) = genV P A C ∧
    comm (P - (P - conePlus P A)) ((P + coneMinus P C) - P) =
      genSig P A C ∧
    comm (P - conePlus P A) (P + coneMinus P C) =
      genJ P A C - genSig P A C := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    peirce_nf hP

/-! ### Multiscale Unipotent Idempotent Tower -/

theorem conjPlus_idempotent_point_form (A : B) :
    conjPlus P A P = projChartPlus P A := by
  simp only [conjPlus, projChartPlus]
  peirce_nf hP

theorem conjPlus_idempotent_point (A : B) :
    conjPlus P A P * conjPlus P A P = conjPlus P A P := by
  simp only [conjPlus]
  peirce_nf hP

/-- Every finite stage of the unipotent idempotent tower is idempotent. -/
theorem unipotentIdempotentTower_idempotent (A : ℕ → B) :
    ∀ k : ℕ,
      unipotentIdempotentTower A k P * unipotentIdempotentTower A k P =
        unipotentIdempotentTower A k P
  | 0 => hP
  | k + 1 => by
      have hk := unipotentIdempotentTower_idempotent A k
      simpa [unipotentIdempotentTower] using
        (conjPlus_idempotent_point
          (P := unipotentIdempotentTower A k P) hk (A k))

theorem unipotentIdempotentTower_parent_mul_child (A : ℕ → B) (k : ℕ) :
    unipotentIdempotentTower A k P * unipotentIdempotentTower A (k + 1) P =
      unipotentIdempotentTower A (k + 1) P := by
  have hk := unipotentIdempotentTower_idempotent hP A k
  dsimp [unipotentIdempotentTower]
  simp only [conjPlus]
  peirce_nf hk

theorem unipotentIdempotentTower_child_mul_parent (A : ℕ → B) (k : ℕ) :
    unipotentIdempotentTower A (k + 1) P * unipotentIdempotentTower A k P =
      unipotentIdempotentTower A k P := by
  have hk := unipotentIdempotentTower_idempotent hP A k
  dsimp [unipotentIdempotentTower]
  simp only [conjPlus]
  peirce_nf hk

theorem unipotentIdempotentTower_parent_sub_child (A : ℕ → B) (k : ℕ) :
    unipotentIdempotentTower A k P - unipotentIdempotentTower A (k + 1) P =
      conePlus (unipotentIdempotentTower A k P) (A k) := by
  have hk := unipotentIdempotentTower_idempotent hP A k
  dsimp [unipotentIdempotentTower]
  simp only [conjPlus]
  peirce_nf hk

theorem unipotentIdempotentTower_edge_commutator (A : ℕ → B) (k : ℕ) :
    comm (unipotentIdempotentTower A k P) (unipotentIdempotentTower A (k + 1) P) =
      -conePlus (unipotentIdempotentTower A k P) (A k) := by
  have hk := unipotentIdempotentTower_idempotent hP A k
  dsimp [unipotentIdempotentTower]
  simp only [conjPlus]
  peirce_nf hk

end InfoGeometry.OperatorAlgebra.PeirceSpine
