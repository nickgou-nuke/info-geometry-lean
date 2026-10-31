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
