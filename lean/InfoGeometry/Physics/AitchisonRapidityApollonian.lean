/-
Copyright (c) 2026 nickgou-nuke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: nickgou-nuke contributors
-/
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

open scoped BigOperators
open Real

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-!
# Section 5.85: Aitchison Simplex Geometry, Rapidity-Logit Duality, and Apollonian Metric

This module formalizes:
1. Binary simplex state space `BinarySimplexPoint`: `p ∈ (0, 1)`.
2. Normalized relativistic velocity: `v = 2p - 1 ∈ (-1, 1)`.
3. Logit and Relativistic Rapidity:
   `logit(p) = ln(p / (1 - p))` and `rapidity(p) = (1/2) * logit(p)`.
4. The Jaynesian reference state `p = 1/2` as the algebraic origin:
   `logit(1/2) = 0` and `rapidity(1/2) = 0`.
5. Aitchison Centered Log-Ratio (clr) trace cancellation:
   `clr₁(p) + clr₂(p) = 0`.
6. Aitchison perturbation group operation `P ⊕ Q`:
   Exact homomorphism to additive relativistic rapidity:
   `rapidity(P ⊕ Q) = rapidity(P) + rapidity(Q)`.
7. Apollonian / Hilbert projective cross-ratio metric:
   `d_Apol(P, Q) = |logit(P) - logit(Q)| = 2 * |rapidity(P) - rapidity(Q)|`.
8. Master Synthesis Theorem uniting all isomorphisms.

Zero debt, 0 sorry, 0 admit, kernel-checked in Lean 4.
-/

namespace InfoGeometry.Physics.AitchisonRapidityApollonian

/-! ### Part I: Binary Simplex State Space and Rapidity -/

/-- A point in the open 1-dimensional probability simplex Δ¹: `p ∈ (0, 1)`. -/
structure BinarySimplexPoint where
  p : ℝ
  hp0 : 0 < p
  hp1 : p < 1

namespace BinarySimplexPoint

variable (P : BinarySimplexPoint)

/-- Complementary probability: `1 - p > 0`. -/
lemma one_sub_p_pos : 0 < 1 - P.p := by
  linarith [P.hp1]

/-- The odds ratio: `p / (1 - p)`. -/
def odds : ℝ :=
  P.p / (1 - P.p)

lemma odds_pos : 0 < P.odds :=
  div_pos P.hp0 P.one_sub_p_pos

/-- Normalized relativistic velocity coordinate: `v = 2p - 1 ∈ (-1, 1)`. -/
def normalizedVelocity : ℝ :=
  2 * P.p - 1

lemma velocity_gt_neg_one : -1 < P.normalizedVelocity := by
  dsimp [normalizedVelocity]
  linarith [P.hp0]

lemma velocity_lt_one : P.normalizedVelocity < 1 := by
  dsimp [normalizedVelocity]
  linarith [P.hp1]

/-- The logit function (log-odds): `logit(p) = ln(p / (1 - p))`. -/
noncomputable def logit : ℝ :=
  Real.log P.odds

/-- Relativistic rapidity parameter: `θ = (1/2) * logit(p)`. -/
noncomputable def rapidity : ℝ :=
  (1 / 2 : ℝ) * P.logit

/-- **Theorem 1 (Logit-Rapidity Scaling)**:
    `logit(p) = 2 * rapidity(p)`. -/
theorem logit_eq_two_rapidity :
    P.logit = 2 * P.rapidity := by
  dsimp [rapidity]
  ring

end BinarySimplexPoint

/-! ### Part II: The Jaynesian Prior as the Algebraic Origin -/

/-- The Jaynesian maximum entropy reference state: `p = 1/2`. -/
def jaynesPoint : BinarySimplexPoint :=
  ⟨1 / 2, by norm_num, by norm_num⟩

lemma jaynes_odds : jaynesPoint.odds = 1 := by
  dsimp [BinarySimplexPoint.odds, jaynesPoint]
  norm_num

/-- **Theorem 2 (Jaynesian Logit Origin)**:
    The logit of the Jaynesian prior vanishes identically: `logit(1/2) = 0`. -/
theorem jaynes_logit_zero : jaynesPoint.logit = 0 := by
  dsimp [BinarySimplexPoint.logit]
  rw [jaynes_odds, Real.log_one]

/-- **Theorem 3 (Jaynesian Prior is the Relativistic Rest Frame)**:
    The rapidity of the Jaynesian prior vanishes identically: `θ(1/2) = 0`. -/
theorem jaynes_rapidity_zero : jaynesPoint.rapidity = 0 := by
  dsimp [BinarySimplexPoint.rapidity]
  rw [jaynes_logit_zero, mul_zero]

/-- **Theorem 4 (Jaynesian Normalized Velocity Vanishes)**:
    The normalized relativistic velocity of the Jaynesian state is strictly 0: `v = 0`. -/
theorem jaynes_velocity_zero : jaynesPoint.normalizedVelocity = 0 := by
  dsimp [BinarySimplexPoint.normalizedVelocity, jaynesPoint]
  ring

/-! ### Part III: Aitchison CLR Coordinates and Trace Cancellation -/

/-- First centered log-ratio coordinate: `clr₁(p) = (1/2) ln(p / (1 - p)) = θ`. -/
noncomputable def clr1 (P : BinarySimplexPoint) : ℝ :=
  P.rapidity

/-- Second centered log-ratio coordinate: `clr₂(p) = - clr₁(p) = -θ`. -/
noncomputable def clr2 (P : BinarySimplexPoint) : ℝ :=
  - P.rapidity

/-- **Theorem 5 (Aitchison Trace Cancellation)**:
    The sum of the centered log-ratio components vanishes identically:
    `clr₁(p) + clr₂(p) = 0`.
    This proves projection onto the traceless Cartan subalgebra `𝔞 ⊂ 𝔰𝔩(2, ℝ)`. -/
theorem aitchison_trace_cancellation (P : BinarySimplexPoint) :
    clr1 P + clr2 P = 0 := by
  dsimp [clr1, clr2]
  ring

/-! ### Part IV: Aitchison Perturbation as Rapidity Addition -/

lemma perturbation_denom_pos (P Q : BinarySimplexPoint) :
    0 < P.p * Q.p + (1 - P.p) * (1 - Q.p) := by
  have h1 : 0 < P.p * Q.p := mul_pos P.hp0 Q.hp0
  have h2 : 0 < (1 - P.p) * (1 - Q.p) := mul_pos P.one_sub_p_pos Q.one_sub_p_pos
  exact add_pos h1 h2

lemma perturbation_p_pos (P Q : BinarySimplexPoint) :
    0 < (P.p * Q.p) / (P.p * Q.p + (1 - P.p) * (1 - Q.p)) :=
  div_pos (mul_pos P.hp0 Q.hp0) (perturbation_denom_pos P Q)

lemma perturbation_p_lt_one (P Q : BinarySimplexPoint) :
    (P.p * Q.p) / (P.p * Q.p + (1 - P.p) * (1 - Q.p)) < 1 := by
  have hden := perturbation_denom_pos P Q
  rw [div_lt_one hden]
  have h2 : 0 < (1 - P.p) * (1 - Q.p) := mul_pos P.one_sub_p_pos Q.one_sub_p_pos
  linarith

/-- Aitchison perturbation group operation on the 1-simplex:
    `P ⊕ Q = [p q : (1 - p)(1 - q)]`. -/
noncomputable def perturb (P Q : BinarySimplexPoint) : BinarySimplexPoint :=
  ⟨(P.p * Q.p) / (P.p * Q.p + (1 - P.p) * (1 - Q.p)),
   perturbation_p_pos P Q,
   perturbation_p_lt_one P Q⟩

lemma perturb_odds (P Q : BinarySimplexPoint) :
    (perturb P Q).odds = P.odds * Q.odds := by
  dsimp [perturb, BinarySimplexPoint.odds]
  have hp1 := P.one_sub_p_pos
  have hq1 := Q.one_sub_p_pos
  have hden := perturbation_denom_pos P Q
  have hp1_ne : 1 - P.p ≠ 0 := ne_of_gt hp1
  have hq1_ne : 1 - Q.p ≠ 0 := ne_of_gt hq1
  have hden_ne : P.p * Q.p + (1 - P.p) * (1 - Q.p) ≠ 0 := ne_of_gt hden
  field_simp [hp1_ne, hq1_ne, hden_ne]
  ring

/-- **Theorem 6 (Logit Additivity under Aitchison Perturbation)**:
    `logit(P ⊕ Q) = logit(P) + logit(Q)`. -/
theorem perturb_logit_additive (P Q : BinarySimplexPoint) :
    (perturb P Q).logit = P.logit + Q.logit := by
  dsimp [BinarySimplexPoint.logit]
  rw [perturb_odds P Q]
  have hP_pos : P.odds ≠ 0 := ne_of_gt P.odds_pos
  have hQ_pos : Q.odds ≠ 0 := ne_of_gt Q.odds_pos
  exact Real.log_mul hP_pos hQ_pos

/-- **Theorem 7 (Aitchison Perturbation is Rapidity Addition)**:
    The Aitchison group operation corresponds to addition of relativistic rapidities:
    `rapidity(P ⊕ Q) = rapidity(P) + rapidity(Q)`. -/
theorem perturb_rapidity_additive (P Q : BinarySimplexPoint) :
    (perturb P Q).rapidity = P.rapidity + Q.rapidity := by
  dsimp [BinarySimplexPoint.rapidity]
  rw [perturb_logit_additive P Q]
  ring

/-! ### Part V: Apollonian / Hilbert Cross-Ratio Information Metric -/

/-- The Apollonian (Hilbert projective) metric on the simplex:
    `d_Apol(P, Q) = |logit(P) - logit(Q)|`. -/
noncomputable def apollonianDistance (P Q : BinarySimplexPoint) : ℝ :=
  |P.logit - Q.logit|

/-- **Theorem 8 (Apollonian Metric is Hyperbolic Rapidity Distance)**:
    The Apollonian cross-ratio information distance is strictly equal to
    twice the hyperbolic distance in relativistic rapidity space:
    `d_Apol(P, Q) = 2 * |rapidity(P) - rapidity(Q)|`. -/
theorem apollonian_rapidity_relation (P Q : BinarySimplexPoint) :
    apollonianDistance P Q = 2 * |P.rapidity - Q.rapidity| := by
  dsimp [apollonianDistance, BinarySimplexPoint.rapidity]
  have h : (1 / 2 : ℝ) * P.logit - (1 / 2 : ℝ) * Q.logit =
           (1 / 2 : ℝ) * (P.logit - Q.logit) := by ring
  rw [h, abs_mul]
  have h_half_abs : |(1 / 2 : ℝ)| = (1 / 2 : ℝ) := by norm_num
  rw [h_half_abs]
  ring

/-- The Aitchison Euclidean distance on CLR coordinates:
    `d_A(P, Q)² = (clr₁(P) - clr₁(Q))² + (clr₂(P) - clr₂(Q))²`. -/
noncomputable def aitchisonDistanceSq (P Q : BinarySimplexPoint) : ℝ :=
  (clr1 P - clr1 Q) ^ 2 + (clr2 P - clr2 Q) ^ 2

/-- **Theorem 9 (Aitchison Distance is Proportional to Rapidity Gap)**:
    `d_A(P, Q)² = 2 * (rapidity(P) - rapidity(Q))²`. -/
theorem aitchison_distance_rapidity_sq (P Q : BinarySimplexPoint) :
    aitchisonDistanceSq P Q = 2 * (P.rapidity - Q.rapidity) ^ 2 := by
  dsimp [aitchisonDistanceSq, clr1, clr2]
  ring

/-! ### Part VI: Master Synthesis Theorem -/

/-- Master Synthesis: Unifies Aitchison trace cancellation, the Jaynesian prior origin,
    the perturbation-rapidity isomorphism, and the Apollonian hyperbolic metric equivalence. -/
theorem aitchison_rapidity_apollonian_synthesis (P Q : BinarySimplexPoint) :
    (clr1 P + clr2 P = 0) ∧
    (jaynesPoint.rapidity = 0) ∧
    (jaynesPoint.normalizedVelocity = 0) ∧
    ((perturb P Q).rapidity = P.rapidity + Q.rapidity) ∧
    (apollonianDistance P Q = 2 * |P.rapidity - Q.rapidity|) ∧
    (aitchisonDistanceSq P Q = 2 * (P.rapidity - Q.rapidity) ^ 2) := by
  exact ⟨aitchison_trace_cancellation P,
         jaynes_rapidity_zero,
         jaynes_velocity_zero,
         perturb_rapidity_additive P Q,
         apollonian_rapidity_relation P Q,
         aitchison_distance_rapidity_sq P Q⟩

/-- Certified wrapper for Section 5.85 Aitchison-Rapidity synthesis. -/
structure CertifiedAitchisonRapidityApollonianSynthesis where
  certified_synthesis :
    ∀ (P Q : BinarySimplexPoint),
      (clr1 P + clr2 P = 0) ∧
      (jaynesPoint.rapidity = 0) ∧
      (jaynesPoint.normalizedVelocity = 0) ∧
      ((perturb P Q).rapidity = P.rapidity + Q.rapidity) ∧
      (apollonianDistance P Q = 2 * |P.rapidity - Q.rapidity|) ∧
      (aitchisonDistanceSq P Q = 2 * (P.rapidity - Q.rapidity) ^ 2)

def makeCertifiedAitchisonRapidityApollonianSynthesis :
    CertifiedAitchisonRapidityApollonianSynthesis where
  certified_synthesis := aitchison_rapidity_apollonian_synthesis

end InfoGeometry.Physics.AitchisonRapidityApollonian
