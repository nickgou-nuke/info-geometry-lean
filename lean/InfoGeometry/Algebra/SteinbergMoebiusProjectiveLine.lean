/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.SteinbergBraidDefectSpine

/-!
# Pure non-commutative operator Möbius projective line (A21-A22)

Owner module for the "drunken professor" deconfabulation of the Erlangen-2.0 stream
archetypes `A21`-`A22` (the operator Möbius projective line and its cross ratio /
Hua distance).  Everything extends
`PureNonCommutativeOperatorSpine` (cones, tetraktys, braids) over an arbitrary
associative unital ring `B`, still with the single hypothesis `hP : P * P = P`:
no commutativity, no division, no scalar carrier beyond `ℤ`-multiples.

* the two charts `P(X) = P - conePlus P X` and `Q(Y) = (1 - P) - coneMinus P Y`
  are exactly idempotent, and conjugation by `1 ± cones` shifts them (A21.1-A21.4);
* the Peirce mass splitting `P - Σ = (1-P)V + P(1-V)` (and its mirrored form)
  is exact (A21.5, A21.6);
* the braid action on the base point `P` is the verified one-parameter chain
  `B₊ P B₊'` (A21.7, A21.8);
* the operator cross ratio is `V` of the differences, invariant under both
  chart shifts and both cone conjugations (A22.1-A22.5), and the corrected Hua
  distance `(P(X) - Q(Y))² = 1 - V(X, Y)` is additive-only, closed from `hP`
  alone (A22.6).

Every statement was first arbitrated by the exact reduced-word model in
`proofs/steinberg_braid_defect_spine.py` before transcription.  Refuted drafts
(documented, *not* formalized): the factored A21.7 form
`B₊ P B₊' = QV + P(1-V) - J - (1-2V)N₊` and the wrong-sign draft
`(P(X) - Q(Y))² = 1 + V(X, Y)` (A22.7).
-/

namespace PureNonCommutativeOperatorSpine

variable {B : Type*} [Ring B]

/-! ### Operator Möbius charts and the operator cross ratio -/

/-- Upper Möbius chart: `P(X) = P - conePlus P X`. -/
def projChartPlus (P X : B) : B := P - conePlus P X

/-- Lower Möbius chart: `Q(Y) = (1 - P) - coneMinus P Y`. -/
def projChartMinus (P Y : B) : B := (1 - P) - coneMinus P Y

/-- Operator cross ratio: the anticommutator of the two chart differences. -/
def operatorCrossRatio (P X₁ X₂ Y₁ Y₂ : B) : B :=
  anticomm (projChartPlus P X₁ - projChartPlus P X₂)
    (projChartMinus P Y₁ - projChartMinus P Y₂)

/-- Chart differences are reversed cones (distributivity at the word level). -/
theorem projChartPlus_sub {P : B} (hP : P * P = P) (X₁ X₂ : B) :
    projChartPlus P X₁ - projChartPlus P X₂ = conePlus P (X₂ - X₁) := by
  simp only [projChartPlus, conePlus]
  noncomm_ring [hP, P_assoc hP]

/-- Lower chart differences are reversed lower cones. -/
theorem projChartMinus_sub {P : B} (hP : P * P = P) (Y₁ Y₂ : B) :
    projChartMinus P Y₁ - projChartMinus P Y₂ = coneMinus P (Y₂ - Y₁) := by
  simp only [projChartMinus, coneMinus]
  noncomm_ring [hP, P_assoc hP]

/-! ### A21: charts, shifts, mass splitting, braid action -/

/-- **A21.1**: the upper chart is exactly idempotent. -/
theorem projChartPlus_idem {P : B} (hP : P * P = P) (X : B) :
    projChartPlus P X * projChartPlus P X = projChartPlus P X := by
  simp only [projChartPlus, conePlus]
  noncomm_ring [hP, P_assoc hP]

/-- **A21.2**: the lower chart is exactly idempotent. -/
theorem projChartMinus_idem {P : B} (hP : P * P = P) (Y : B) :
    projChartMinus P Y * projChartMinus P Y = projChartMinus P Y := by
  simp only [projChartMinus, coneMinus]
  noncomm_ring [hP, P_assoc hP]

/-- **A21.3**: upper conjugation shifts the upper chart, `conjPlus(A) P(X) = P(X + A)`. -/
theorem conjPlus_chartPlus {P : B} (hP : P * P = P) (A X : B) :
    conjPlus P A (projChartPlus P X) = projChartPlus P (X + A) := by
  simp only [conjPlus, projChartPlus, conePlus]
  noncomm_ring [hP, P_assoc hP]

/-- **A21.4**: lower conjugation shifts the lower chart, `conjMinus(C) Q(Y) = Q(Y + C)`. -/
theorem conjMinus_chartMinus {P : B} (hP : P * P = P) (C Y : B) :
    conjMinus P C (projChartMinus P Y) = projChartMinus P (Y + C) := by
  simp only [conjMinus, projChartMinus, coneMinus]
  noncomm_ring [hP, P_assoc hP]

/-- **A21.5**: exact Peirce mass splitting `P - Sigma = (1-P)V + P(1-V)`. -/
theorem mass_split_upper {P : B} (hP : P * P = P) (A C : B) :
    P - genSig P A C = (1 - P) * genV P A C + P * (1 - genV P A C) := by
  simp only [genSig, genV, comm, anticomm, conePlus, coneMinus]
  noncomm_ring [hP, P_assoc hP]

/-- **A21.6**: the mirrored Peirce mass splitting `(1-P) + Sigma = PV + (1-P)(1-V)`. -/
theorem mass_split_lower {P : B} (hP : P * P = P) (A C : B) :
    (1 - P) + genSig P A C = P * genV P A C + (1 - P) * (1 - genV P A C) := by
  simp only [genSig, genV, comm, anticomm, conePlus, coneMinus]
  noncomm_ring [hP, P_assoc hP]

/-- **A21.7**: the braid action on the base point,
`B₊ P = P - N₋ - N₊N₋` (the stream's factored draft form was refuted). -/
theorem braid_action_base {P : B} (hP : P * P = P) (A C : B) :
    steinbergBraid P A C * P = P - coneMinus P C - conePlus P A * coneMinus P C := by
  simp only [steinbergBraid, conePlus, coneMinus]
  noncomm_ring [hP, P_assoc hP]

/-- **A21.8**: the verified 10-term chain action
`B₊ P B₊' = P - 2u - v - 2uv + 2vu + 3uvu + vuv + uvuv - vuvu - uvuvu`
with `u = conePlus P X` and `v = coneMinus P Y`.  (The stream's factored draft
`QV + P(1-V) - J - (1-2V)N₊` was refuted by the exact word model.) -/
theorem braid_action_chain {P : B} (hP : P * P = P) (X Y : B) :
    steinbergBraid P X Y * P * steinbergBraidInv P X Y
      = P
        - (2 : ℤ) • (conePlus P X)
        - (1 : ℤ) • (coneMinus P Y)
        - (2 : ℤ) • (conePlus P X * coneMinus P Y)
        + (2 : ℤ) • (coneMinus P Y * conePlus P X)
        + (3 : ℤ) • (conePlus P X * coneMinus P Y * conePlus P X)
        + (1 : ℤ) • (coneMinus P Y * conePlus P X * coneMinus P Y)
        + (1 : ℤ) • (conePlus P X * coneMinus P Y * conePlus P X * coneMinus P Y)
        - (1 : ℤ) • (coneMinus P Y * conePlus P X * coneMinus P Y * conePlus P X)
        - (1 : ℤ) • (conePlus P X * coneMinus P Y * conePlus P X * coneMinus P Y
            * conePlus P X) := by
  simp only [steinbergBraid, steinbergBraidInv, conePlus, coneMinus]
  noncomm_ring [hP, P_assoc hP]

/-! ### A22: cross ratio structure and the corrected Hua distance -/

/-- **A22.1**: the operator cross ratio is the mass of the differences,
`CR(X₁, X₂, Y₁, Y₂) = V(X₁ - X₂, Y₁ - Y₂)`. -/
theorem crossRatio_eq_genV {P : B} (hP : P * P = P) (X₁ X₂ Y₁ Y₂ : B) :
    operatorCrossRatio P X₁ X₂ Y₁ Y₂ = genV P (X₁ - X₂) (Y₁ - Y₂) := by
  simp only [operatorCrossRatio, genV, anticomm, projChartPlus, projChartMinus,
    conePlus, coneMinus]
  noncomm_ring [hP, P_assoc hP]

/-- **A22.2**: base cross ratio `CR(A, 0, C, 0) = V(A, C)`. -/
theorem crossRatio_base {P : B} (hP : P * P = P) (A C : B) :
    operatorCrossRatio P A 0 C 0 = genV P A C := by
  rw [crossRatio_eq_genV hP]
  simp only [sub_zero]

/-- **A22.3**: shift invariance, `(X+A, Z+A, Y+C, 0+C)` does not change the cross ratio. -/
theorem crossRatio_shift {P : B} (hP : P * P = P) (X Z Y C A : B) :
    operatorCrossRatio P (X + A) (Z + A) (Y + C) (0 + C)
      = operatorCrossRatio P X Z Y 0 := by
  simp only [operatorCrossRatio, projChartPlus, projChartMinus, conePlus, coneMinus]
  noncomm_ring [hP, P_assoc hP]

/-- **A22.4**: upper conjugation invariance, `conjPlus(X - Z)` fixes the base cross ratio. -/
theorem conjPlus_crossRatio {P : B} (hP : P * P = P) (X Z Y : B) :
    conjPlus P (X - Z) (operatorCrossRatio P X Z Y 0) = operatorCrossRatio P X Z Y 0 := by
  rw [crossRatio_eq_genV hP]
  simp only [sub_zero]
  unfold conjPlus
  have hu : conePlus P (X - Z) * conePlus P (X - Z) = 0 :=
    conePlus_sq_zero hP (X - Z)
  have huv : conePlus P (X - Z) * genV P (X - Z) Y =
      genV P (X - Z) Y * conePlus P (X - Z) := by
    exact sub_eq_zero.mp (genV_commute_conePlus hP (X - Z) Y)
  have hvu : genV P (X - Z) Y * conePlus P (X - Z) * conePlus P (X - Z) = 0 := by
    rw [mul_assoc, hu]
    simp
  calc
    (1 + conePlus P (X - Z)) * genV P (X - Z) Y *
        (1 - conePlus P (X - Z)) =
        genV P (X - Z) Y +
          (conePlus P (X - Z) * genV P (X - Z) Y -
            genV P (X - Z) Y * conePlus P (X - Z)) -
          conePlus P (X - Z) * genV P (X - Z) Y * conePlus P (X - Z) := by
      noncomm_ring
    _ = genV P (X - Z) Y := by rw [huv, hvu]; noncomm_ring

/-- **A22.5**: lower conjugation invariance, `conjMinus(Y - 0)` fixes the base cross ratio. -/
theorem conjMinus_crossRatio {P : B} (hP : P * P = P) (X Z Y : B) :
    conjMinus P (Y - 0) (operatorCrossRatio P X Z Y 0) = operatorCrossRatio P X Z Y 0 := by
  simp only [sub_zero]
  rw [crossRatio_eq_genV hP]
  simp only [sub_zero]
  unfold conjMinus
  have hw : coneMinus P Y * coneMinus P Y = 0 := coneMinus_sq_zero hP Y
  have hwv : coneMinus P Y * genV P (X - Z) Y =
      genV P (X - Z) Y * coneMinus P Y := by
    exact sub_eq_zero.mp (genV_commute_coneMinus hP (X - Z) Y)
  have hvw : genV P (X - Z) Y * coneMinus P Y * coneMinus P Y = 0 := by
    rw [mul_assoc, hw]
    simp
  calc
    (1 + coneMinus P Y) * genV P (X - Z) Y * (1 - coneMinus P Y) =
        genV P (X - Z) Y +
          (coneMinus P Y * genV P (X - Z) Y -
            genV P (X - Z) Y * coneMinus P Y) -
          coneMinus P Y * genV P (X - Z) Y * coneMinus P Y := by
      noncomm_ring
    _ = genV P (X - Z) Y := by rw [hwv, hvw]; noncomm_ring

/-- **A22.6** (corrected Hua distance, additive-only, closed from `hP` alone):
`(P(X) - Q(Y))² = 1 - V(X, Y)`.  The stream's wrong-sign draft `1 + V(X, Y)`
(A22.7) was refuted by the model. -/
theorem hua_distance_sq {P : B} (hP : P * P = P) (X Y : B) :
    (projChartPlus P X - projChartMinus P Y)
      * (projChartPlus P X - projChartMinus P Y)
      = 1 - genV P X Y := by
  simp only [projChartPlus, projChartMinus, genV, anticomm, conePlus, coneMinus]
  noncomm_ring [hP, P_assoc hP]
