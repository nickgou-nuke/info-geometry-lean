/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceLogisticBitwordBridge

/-!
# D₄₄: Operator-side projective ensemble normalization and score transport

This module uses the Peirce logistic operators already owned by
`PeirceLogisticBitwordBridge`. The finite Gibbs ray and its real-valued
partition function remain in `Canonical.GrandCanonicalProjectiveRayBridge`;
no identification between that scalar carrier and this operator ring is made.

The gauge action here is left multiplication. The Massieu score law is stated
for a left Leibniz derivative and preserves the noncommutative factor order.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

/-! ## Causal dependency order -/

inductive GrandCanonicalOperatorStage where
  | homogeneousWeights
  | normalizedSection
  | massieuScoreTransport
  | scoreFluctuation
  | cumulantVariance
  deriving DecidableEq, Repr

def grandCanonicalOperatorRank : GrandCanonicalOperatorStage → ℕ
  | .homogeneousWeights => 0
  | .normalizedSection => 1
  | .massieuScoreTransport => 2
  | .scoreFluctuation => 3
  | .cumulantVariance => 4

theorem grandCanonicalOperatorRank_injective :
    Function.Injective grandCanonicalOperatorRank := by
  intro a b h
  cases a <;> cases b <;> cases h <;> rfl

instance : PartialOrder GrandCanonicalOperatorStage :=
  PartialOrder.lift grandCanonicalOperatorRank grandCanonicalOperatorRank_injective

theorem grandCanonicalOperator_causal_chain :
    GrandCanonicalOperatorStage.homogeneousWeights <
        GrandCanonicalOperatorStage.normalizedSection ∧
    GrandCanonicalOperatorStage.normalizedSection <
        GrandCanonicalOperatorStage.massieuScoreTransport ∧
    GrandCanonicalOperatorStage.massieuScoreTransport <
        GrandCanonicalOperatorStage.scoreFluctuation ∧
    GrandCanonicalOperatorStage.scoreFluctuation <
        GrandCanonicalOperatorStage.cumulantVariance := by
  change grandCanonicalOperatorRank .homogeneousWeights <
      grandCanonicalOperatorRank .normalizedSection ∧
    grandCanonicalOperatorRank .normalizedSection <
      grandCanonicalOperatorRank .massieuScoreTransport ∧
    grandCanonicalOperatorRank .massieuScoreTransport <
      grandCanonicalOperatorRank .scoreFluctuation ∧
    grandCanonicalOperatorRank .scoreFluctuation <
      grandCanonicalOperatorRank .cumulantVariance
  norm_num [grandCanonicalOperatorRank]

variable {B : Type*} [Ring B]

/-! ## GC₁–GC₂: homogeneous weights and left-gauge section -/

/-- A left inverse of the total weight remains a left inverse after
left-rescaling both weights by an invertible gauge element. -/
theorem leftGauge_partition_inverse
    {Wp Wm Zinv G Ginv : B}
    (hNorm : Zinv * (Wp + Wm) = 1) (hG : Ginv * G = 1) :
    (Zinv * Ginv) * ((G * Wp) + (G * Wm)) = 1 := by
  calc
    (Zinv * Ginv) * ((G * Wp) + (G * Wm))
        = Zinv * (Ginv * G) * (Wp + Wm) := by noncomm_ring
    _ = 1 := by rw [hG, mul_one, hNorm]

/-- Left-normalizing a partition-of-unity pair gives a partition of unity;
the same normalized operators are invariant under a common left gauge scale. -/
theorem leftGauge_normalized_section
    {Wp Wm Zinv G Ginv : B}
    (hNorm : Zinv * (Wp + Wm) = 1) (hG : Ginv * G = 1) :
    Zinv * Wp + Zinv * Wm = 1 ∧
    1 - Zinv * Wp = Zinv * Wm ∧
    (Zinv * Ginv) * (G * Wp) = Zinv * Wp ∧
    (Zinv * Ginv) * (G * Wm) = Zinv * Wm := by
  have hSum : Zinv * Wp + Zinv * Wm = 1 := by
    rw [← mul_add]
    exact hNorm
  have hGauge : ∀ W : B, (Zinv * Ginv) * (G * W) = Zinv * W := by
    intro W
    calc
      (Zinv * Ginv) * (G * W) = Zinv * (Ginv * G) * W := by
        noncomm_ring
      _ = Zinv * W := by rw [hG, mul_one]
  refine ⟨hSum, ?_, hGauge Wp, hGauge Wm⟩
  rw [← hSum, add_sub_cancel_left]

/-! ## GC₃: left logarithmic score cocycle -/

/-- The ordered left logarithmic derivative transforms by the conjugated
Maurer–Cartan term under left gauge rescaling. The inverse hypotheses are
explicit: `Zinv` is a left inverse of `Z`, and `Ginv` is a left inverse of `G`.
-/
theorem leftMassieuScore_gauge_cocycle
    (d : B → B) {Z Zinv G Ginv : B}
    (hZ : Zinv * Z = 1) (hG : Ginv * G = 1)
    (hLeib : d (G * Z) = d G * Z + G * d Z) :
    (Zinv * Ginv) * (G * Z) = 1 ∧
    (Zinv * Ginv) * d (G * Z) =
      Zinv * (Ginv * d G) * Z + Zinv * d Z := by
  constructor
  · calc
      (Zinv * Ginv) * (G * Z) = Zinv * (Ginv * G) * Z := by noncomm_ring
      _ = 1 := by rw [hG, mul_one, hZ]
  · calc
      (Zinv * Ginv) * d (G * Z) =
          (Zinv * Ginv) * (d G * Z + G * d Z) := by rw [hLeib]
      _ = Zinv * (Ginv * d G) * Z + Zinv * (Ginv * G) * d Z := by
          noncomm_ring
      _ = Zinv * (Ginv * d G) * Z + Zinv * d Z := by
          rw [hG, mul_one]

/-! ## GC₄: zero-mean score and unipotent score ray -/

/-- An additive derivative sends a normalized two-branch partition to
zero total score when it annihilates the unit. -/
theorem normalized_score_fluctuation_sum
    (d : B → B) {Lp Lm : B}
    (hAdd : ∀ X Y : B, d (X + Y) = d X + d Y)
    (hUnit : d 1 = 0) (hPartition : Lp + Lm = 1) :
    d Lp + d Lm = 0 := by
  rw [← hAdd, hPartition, hUnit]

/-- The left logarithmic score of the unipotent Peirce shear is its upper
corner. Its anticommutator with the lower corner is the existing Peirce metric.
-/
theorem unipotentScoreRay_eq_corner
    {P : B} (hP : P * P = P) (A C : B) :
    (1 - conePlus P A) * comm P (1 + conePlus P A) = conePlus P A ∧
    anticomm ((1 - conePlus P A) * comm P (1 + conePlus P A))
        (coneMinus P C) = genV P A C := by
  have hComm : comm P (1 + conePlus P A) = conePlus P A := by
    dsimp [comm]
    peirce_nf hP
  have hSquare : conePlus P A * conePlus P A = 0 :=
    conePlus_mul_conePlus hP A A
  have hScore : (1 - conePlus P A) * conePlus P A = conePlus P A := by
    calc
      (1 - conePlus P A) * conePlus P A =
          1 * conePlus P A - conePlus P A * conePlus P A := by noncomm_ring
      _ = conePlus P A := by rw [hSquare]; simp
  constructor
  · rw [hComm, hScore]
  · rw [hComm, hScore]
    rfl

/-! ## GC₅: gauge-invariant operator cumulant variance -/

/-- The variance polynomial of the normalized Peirce logistic operator is
gauge invariant and equals the negative idempotency defect of `genV`.
-/
theorem leftGauge_logistic_cumulant_variance
    {P G Ginv : B} [StarRing B] (hP : P * P = P) (hG : Ginv * G = 1) (A C : B) :
    Ginv * (G * peirceLogisticPlus P A C) = peirceLogisticPlus P A C ∧
    (Ginv * (G * peirceLogisticPlus P A C)) *
        (1 - Ginv * (G * peirceLogisticPlus P A C)) =
      -(genV P A C * genV P A C - genV P A C) := by
  have hSection : Ginv * (G * peirceLogisticPlus P A C) =
      peirceLogisticPlus P A C := by
    calc
      Ginv * (G * peirceLogisticPlus P A C) =
          (Ginv * G) * peirceLogisticPlus P A C := by noncomm_ring
      _ = peirceLogisticPlus P A C := by rw [hG, one_mul]
  have hLog := peirceLogistic_operator_identities hP A C
  refine ⟨hSection, ?_⟩
  rw [hSection, hLog.2.1]
  exact hLog.2.2.1

end InfoGeometry.OperatorAlgebra.PeirceSpine

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-! ## D₄₅: bilateral gauge transport and higher logistic cumulants -/

def gaugeSection (Zinv W : B) : B := Zinv * W

def massieuScore (d : B → B) (Z Zinv : B) : B := Zinv * d Z

def unipotentScoreRay (P U Uinv : B) : B := Uinv * comm P U

def refl (X : B) : B := 1 - X - X

def cumulantVariance (X : B) : B := X * (1 - X)

def cumulantSkewness (X : B) : B := cumulantVariance X * refl X

/-! ### GC₆: left and right Weyl gauge actions -/

/-- Left gauge normalization is invariant, whereas right gauge normalization is
covariant by conjugation. Both score formulas retain the indicated factor order. -/
theorem bilateral_weyl_massieu_cocycle
    (d : B → B) {Z Zinv G Ginv W : B}
    (hLeibL : d (G * Z) = d G * Z + G * d Z)
    (hLeibR : d (Z * G) = d Z * G + Z * d G)
    (hZ : Zinv * Z = 1) (hG : Ginv * G = 1) :
    gaugeSection (Zinv * Ginv) (G * W) = gaugeSection Zinv W ∧
    massieuScore d (G * Z) (Zinv * Ginv) =
      Zinv * massieuScore d G Ginv * Z + massieuScore d Z Zinv ∧
    gaugeSection (Ginv * Zinv) (W * G) =
      Ginv * gaugeSection Zinv W * G ∧
    massieuScore d (Z * G) (Ginv * Zinv) =
      Ginv * massieuScore d Z Zinv * G + massieuScore d G Ginv := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (Zinv * Ginv) * (G * W) = Zinv * W
    calc
      (Zinv * Ginv) * (G * W) = Zinv * (Ginv * G) * W := by noncomm_ring
      _ = Zinv * W := by rw [hG, mul_one]
  · change (Zinv * Ginv) * d (G * Z) =
      Zinv * (Ginv * d G) * Z + Zinv * d Z
    rw [hLeibL]
    calc
      (Zinv * Ginv) * (d G * Z + G * d Z) =
          Zinv * (Ginv * d G) * Z + Zinv * (Ginv * G) * d Z := by noncomm_ring
      _ = Zinv * (Ginv * d G) * Z + Zinv * d Z := by rw [hG, mul_one]
  · change (Ginv * Zinv) * (W * G) = Ginv * (Zinv * W) * G
    noncomm_ring
  · change (Ginv * Zinv) * d (Z * G) =
      Ginv * (Zinv * d Z) * G + Ginv * d G
    rw [hLeibR]
    calc
      (Ginv * Zinv) * (d Z * G + Z * d G) =
          Ginv * (Zinv * d Z) * G + Ginv * (Zinv * Z) * d G := by noncomm_ring
      _ = Ginv * (Zinv * d Z) * G + Ginv * d G := by rw [hZ, mul_one]

/-! ### GC₇: variance plus vacuum displacement recovers the metric -/

/-- The logistic displacement from the reference idempotent has square `V²`;
adding the second cumulant cancels that quadratic term and returns `V`. -/
theorem logistic_metric_variance_conservation
    {P : B} (hP : P * P = P) (A C : B) :
    peirceLogisticPlus P A C - P = -comm (conePlus P A) (coneMinus P C) ∧
    (peirceLogisticPlus P A C - P) * (peirceLogisticPlus P A C - P) =
      genV P A C * genV P A C ∧
    cumulantVariance (peirceLogisticPlus P A C) +
      (peirceLogisticPlus P A C - P) * (peirceLogisticPlus P A C - P) =
      genV P A C := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (simp only [peirceLogisticPlus, qgtPlus, qgtMinus, genV,
      comm, anticomm, conePlus, coneMinus, cumulantVariance]; peirce_nf hP)

/-! ### GC₈: the two unipotent score rays -/

/-- The upper and lower unipotent score rays are opposite Peirce corners;
their negative Jordan and Lie products recover the metric and curvature. -/
theorem dual_unipotent_score_rays
    {P : B} (hP : P * P = P) (A C : B) :
    unipotentScoreRay P (1 + conePlus P A) (1 - conePlus P A) = conePlus P A ∧
    unipotentScoreRay P (1 + coneMinus P C) (1 - coneMinus P C) = -coneMinus P C ∧
    -anticomm (unipotentScoreRay P (1 + conePlus P A) (1 - conePlus P A))
      (unipotentScoreRay P (1 + coneMinus P C) (1 - coneMinus P C)) = genV P A C ∧
    -comm (unipotentScoreRay P (1 + conePlus P A) (1 - conePlus P A))
      (unipotentScoreRay P (1 + coneMinus P C) (1 - coneMinus P C)) =
      comm (conePlus P A) (coneMinus P C) := by
  have hSource : unipotentScoreRay P (1 + conePlus P A) (1 - conePlus P A) =
      conePlus P A := by
    unfold unipotentScoreRay
    have hComm : comm P (1 + conePlus P A) = conePlus P A := by
      dsimp [comm]; peirce_nf hP
    have hSq : conePlus P A * conePlus P A = 0 := conePlus_mul_conePlus hP A A
    rw [hComm]
    calc
      (1 - conePlus P A) * conePlus P A =
          conePlus P A - conePlus P A * conePlus P A := by noncomm_ring
      _ = conePlus P A := by rw [hSq]; simp
  have hSink : unipotentScoreRay P (1 + coneMinus P C) (1 - coneMinus P C) =
      -coneMinus P C := by
    unfold unipotentScoreRay
    have hComm : comm P (1 + coneMinus P C) = -coneMinus P C := by
      dsimp [comm]; peirce_nf hP
    have hSq : coneMinus P C * coneMinus P C = 0 := coneMinus_mul_coneMinus hP C C
    rw [hComm]
    calc
      (1 - coneMinus P C) * -coneMinus P C =
          -coneMinus P C + coneMinus P C * coneMinus P C := by noncomm_ring
      _ = -coneMinus P C := by rw [hSq]; simp
  refine ⟨hSource, hSink, ?_, ?_⟩
  · rw [hSource, hSink]
    dsimp [genV, anticomm]
    noncomm_ring
  · rw [hSource, hSink]
    dsimp [comm]
    noncomm_ring

/-! ### GC₉: Leibniz flow of the second cumulant -/

theorem cumulant_variance_leibniz
    (d : B → B) (p : B)
    (hLeib : d (p * (1 - p)) = d p * (1 - p) + p * d (1 - p))
    (hComp : d (1 - p) = -d p) :
    d (cumulantVariance p) = d p * (1 - p) - p * d p := by
  unfold cumulantVariance
  rw [hLeib, hComp, mul_neg, ← sub_eq_add_neg]

/-! ### GC₁₀: polarization and third cumulant -/

/-- The logistic polarization factors into the reference and metric reflections;
the third cumulant inherits this factorization. -/
theorem logistic_third_cumulant_factorization
    {P G Ginv : B} [StarRing B]
    (hP : P * P = P) (hG : Ginv * G = 1) (A C : B) :
    refl P * refl P = 1 ∧
    peirceLogisticMinus P A C - peirceLogisticPlus P A C =
      refl (peirceLogisticPlus P A C) ∧
    refl (peirceLogisticPlus P A C) = refl P * refl (genV P A C) ∧
    cumulantSkewness (gaugeSection Ginv (G * peirceLogisticPlus P A C)) =
      -(genV P A C * genV P A C - genV P A C) *
        (refl P * refl (genV P A C)) := by
  have hSection : gaugeSection Ginv (G * peirceLogisticPlus P A C) =
      peirceLogisticPlus P A C := by
    change Ginv * (G * peirceLogisticPlus P A C) = _
    calc
      Ginv * (G * peirceLogisticPlus P A C) =
          (Ginv * G) * peirceLogisticPlus P A C := by noncomm_ring
      _ = peirceLogisticPlus P A C := by rw [hG, one_mul]
  have hLog := peirceLogistic_operator_identities hP A C
  have hPolar : refl (peirceLogisticPlus P A C) =
      refl P * refl (genV P A C) := by
    dsimp [refl, peirceLogisticPlus, peirceLogisticMinus,
      qgtPlus, qgtMinus, genV, anticomm, conePlus, coneMinus]
    peirce_nf hP
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp [refl]; peirce_nf hP
  · change peirceLogisticMinus P A C - peirceLogisticPlus P A C =
      1 - peirceLogisticPlus P A C - peirceLogisticPlus P A C
    rw [← hLog.1]
    abel
  · exact hPolar
  · rw [hSection]
    change (peirceLogisticPlus P A C *
        (1 - peirceLogisticPlus P A C)) *
        refl (peirceLogisticPlus P A C) = _
    rw [hLog.2.1, hLog.2.2.1]
    rw [hPolar]

/-! ## D₄₅ causal order and synthesis -/

inductive HigherCumulantStage where
  | bilateralGauge
  | metricVariance
  | dualScoreRays
  | varianceFlow
  | thirdCumulant
  deriving DecidableEq, Repr

def higherCumulantLe (a b : HigherCumulantStage) : Prop :=
  a = b ∨ (a = .metricVariance ∧ b = .thirdCumulant)

instance : PartialOrder HigherCumulantStage where
  le := higherCumulantLe
  le_refl a := Or.inl rfl
  le_trans := by
    intro a b c hab hbc
    cases hab with
    | inl hab => subst b; exact hbc
    | inr hab =>
      rcases hab with ⟨rfl, rfl⟩
      cases hbc with
      | inl hbc => subst c; exact Or.inr ⟨rfl, rfl⟩
      | inr hbc => rcases hbc with ⟨h, _⟩; cases h
  le_antisymm := by
    intro a b hab hba
    cases hab with
    | inl hab => exact hab
    | inr hab => rcases hab with ⟨rfl, rfl⟩; cases hba with
      | inl hba => cases hba
      | inr hba => rcases hba with ⟨h, _⟩; cases h

instance : DecidableLE HigherCumulantStage := fun a b =>
  if h : a = b then isTrue (Or.inl h)
  else if h' : a = .metricVariance ∧ b = .thirdCumulant then isTrue (Or.inr h')
  else isFalse (by
    intro hab
    rcases hab with hab | hab
    · exact h hab
    · exact h' hab)

/-- The variance identity is a premise in the third-cumulant factorization;
the gauge, score-ray, and general derivative-flow results are independent. -/
theorem higherCumulant_causal_dependencies :
    HigherCumulantStage.metricVariance < HigherCumulantStage.thirdCumulant ∧
    ¬ HigherCumulantStage.bilateralGauge ≤ HigherCumulantStage.metricVariance ∧
    ¬ HigherCumulantStage.metricVariance ≤ HigherCumulantStage.bilateralGauge ∧
    ¬ HigherCumulantStage.dualScoreRays ≤ HigherCumulantStage.varianceFlow ∧
    ¬ HigherCumulantStage.varianceFlow ≤ HigherCumulantStage.dualScoreRays := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change higherCumulantLe .metricVariance .thirdCumulant ∧
      ¬ higherCumulantLe .thirdCumulant .metricVariance
    constructor
    · exact Or.inr ⟨rfl, rfl⟩
    · intro h
      rcases h with h | h
      · cases h
      · cases h.1
  · intro h
    change higherCumulantLe .bilateralGauge .metricVariance at h
    rcases h with h | h
    · cases h
    · cases h.1
  · intro h
    change higherCumulantLe .metricVariance .bilateralGauge at h
    rcases h with h | h
    · cases h
    · cases h.2
  · intro h
    change higherCumulantLe .dualScoreRays .varianceFlow at h
    rcases h with h | h
    · cases h
    · cases h.1
  · intro h
    change higherCumulantLe .varianceFlow .dualScoreRays at h
    rcases h with h | h
    · cases h
    · cases h.2

/-- D₄₅ synthesis: bilateral gauge transport, metric/variance conservation,
dual Peirce score rays, second-cumulant Leibniz flow, and the gauge-normalized
third-cumulant factorization. The derivation laws are explicit hypotheses. -/
theorem stageD45_higher_cumulant_and_bilateral_weyl_synthesis
    (d : B → B) {P Z Zinv G Ginv W p : B} [StarRing B]
    (hP : P * P = P)
    (hLeibL : d (G * Z) = d G * Z + G * d Z)
    (hLeibR : d (Z * G) = d Z * G + Z * d G)
    (hZ : Zinv * Z = 1) (hG : Ginv * G = 1)
    (hVarLeib : d (p * (1 - p)) = d p * (1 - p) + p * d (1 - p))
    (hVarComp : d (1 - p) = -d p) (A C : B) :
    gaugeSection (Zinv * Ginv) (G * W) = gaugeSection Zinv W ∧
    massieuScore d (G * Z) (Zinv * Ginv) =
      Zinv * massieuScore d G Ginv * Z + massieuScore d Z Zinv ∧
    gaugeSection (Ginv * Zinv) (W * G) =
      Ginv * gaugeSection Zinv W * G ∧
    massieuScore d (Z * G) (Ginv * Zinv) =
      Ginv * massieuScore d Z Zinv * G + massieuScore d G Ginv ∧
    cumulantVariance (peirceLogisticPlus P A C) +
      (peirceLogisticPlus P A C - P) * (peirceLogisticPlus P A C - P) =
      genV P A C ∧
    -anticomm (unipotentScoreRay P (1 + conePlus P A) (1 - conePlus P A))
      (unipotentScoreRay P (1 + coneMinus P C) (1 - coneMinus P C)) = genV P A C ∧
    -comm (unipotentScoreRay P (1 + conePlus P A) (1 - conePlus P A))
      (unipotentScoreRay P (1 + coneMinus P C) (1 - coneMinus P C)) =
      comm (conePlus P A) (coneMinus P C) ∧
    d (cumulantVariance p) = d p * (1 - p) - p * d p ∧
    refl (peirceLogisticPlus P A C) = refl P * refl (genV P A C) ∧
    cumulantSkewness (gaugeSection Ginv (G * peirceLogisticPlus P A C)) =
      -(genV P A C * genV P A C - genV P A C) *
        (refl P * refl (genV P A C)) := by
  rcases bilateral_weyl_massieu_cocycle d (Z := Z) (Zinv := Zinv)
      (G := G) (Ginv := Ginv) (W := W) hLeibL hLeibR hZ hG with
    ⟨hLeftSection, hLeftScore, hRightSection, hRightScore⟩
  rcases logistic_metric_variance_conservation hP A C with
    ⟨_, _, hMetric⟩
  rcases dual_unipotent_score_rays hP A C with
    ⟨_, _, hMetricRay, hCurvatureRay⟩
  have hFlow := cumulant_variance_leibniz d p hVarLeib hVarComp
  rcases logistic_third_cumulant_factorization hP hG A C with
    ⟨_, _, hPolar, hThird⟩
  exact ⟨hLeftSection, hLeftScore, hRightSection, hRightScore, hMetric,
    hMetricRay, hCurvatureRay, hFlow, hPolar, hThird⟩

end InfoGeometry.OperatorAlgebra.PeirceSpine
