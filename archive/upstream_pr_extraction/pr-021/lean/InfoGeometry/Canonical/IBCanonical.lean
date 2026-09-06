import InfoGeometry.Canonical.IBCore

/-!
# InfoGeometry.Canonical.IBCanonical

Canonical theorem surface for the Information Bottleneck core:
- projective/gauge form of BA updates
- frozen free-energy decomposition/descent
- iteration-level frozen-target/current-target descent
- normalize-Lipschitz contraction packaging
-/

open scoped BigOperators ENNReal NNReal

namespace InfoGeometry.Canonical.IB

section CanonicalAPI

variable {X Y T : Type} [Fintype X] [Fintype Y] [Fintype T]
variable [MeasurableSpace X] [MeasurableSingletonClass X]
variable [MeasurableSpace Y] [MeasurableSingletonClass Y]
variable [MeasurableSpace T] [MeasurableSingletonClass T]

/-- Canonical package for normalize-Lipschitz BA contraction data. -/
structure BANormalizeLipschitzData
    (prob : IBProblem (X := X) (Y := Y)) where
  m : ℝ
  Kscore : ℝ
  Kinv : ℝ
  Kc : ℝ≥0
  hm : 0 < m
  hKscore_nonneg : 0 ≤ Kscore
  hKinv_nonneg : 0 ≤ Kinv
  hKc : (Kc : ℝ) = Kscore / m + Kinv
  hMassLower :
    ∀ p : X → FinProb T, ∀ x : X,
      m ≤ ((∑' t, baScore prob p x t).toReal)
  hScoreLip :
    ∀ p q : X → FinProb T, ∀ x : X, ∀ t : T,
      |(baScore prob p x t).toReal - (baScore prob q x t).toReal|
        ≤ Kscore * ((finProbMassNndist (T := T) (p x) (q x) : ℝ))
  hMassInvLip :
    ∀ p q : X → FinProb T, ∀ x : X,
      |((∑' t, baScore prob p x t).toReal)⁻¹
          - ((∑' t, baScore prob q x t).toReal)⁻¹|
        ≤ Kinv * ((finProbMassNndist (T := T) (p x) (q x) : ℝ))

/-- Canonical pointwise BA bound induced by normalize-Lipschitz control. -/
theorem baStep_pointwise_massNndist_le
    (prob : IBProblem (X := X) (Y := Y))
    (h : BANormalizeLipschitzData (X := X) (Y := Y) (T := T) prob) :
    ∀ p q : X → FinProb T, ∀ x : X,
      finProbMassNndist (T := T)
        ((ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p) x)
        ((ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q) x)
      ≤ h.Kc * finProbMassNndist (T := T) (p x) (q x) :=
  ibBlahutArimotoStep_pointwise_massNndist_le_of_massRecipLipschitz_intrinsicUpper
    (X := X) (Y := Y) (T := T)
    (prob := prob)
    (Kc := h.Kc)
    (hm := h.hm)
    (hKscore_nonneg := h.hKscore_nonneg)
    (hKinv_nonneg := h.hKinv_nonneg)
    (hKc := h.hKc)
    (hMassLower := h.hMassLower)
    (hScoreLip := h.hScoreLip)
    (hMassInvLip := h.hMassInvLip)

/-- Canonical global BA contraction in the encoder mass metric. -/
theorem baStep_encoderMassNndist_le
    (prob : IBProblem (X := X) (Y := Y))
    (h : BANormalizeLipschitzData (X := X) (Y := Y) (T := T) prob) :
    ∀ p q : X → FinProb T,
      encoderMassNndist (X := X) (T := T)
        (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p)
        (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q)
      ≤ h.Kc * encoderMassNndist (X := X) (T := T) p q :=
  ibBlahutArimotoStep_encoderMassNndist_le_of_massRecipLipschitz_intrinsicUpper
    (X := X) (Y := Y) (T := T)
    (prob := prob)
    (Kc := h.Kc)
    (hm := h.hm)
    (hKscore_nonneg := h.hKscore_nonneg)
    (hKinv_nonneg := h.hKinv_nonneg)
    (hKc := h.hKc)
    (hMassLower := h.hMassLower)
    (hScoreLip := h.hScoreLip)
    (hMassInvLip := h.hMassInvLip)

/-- Canonical BA update: gauge section of the score projective ray. -/
theorem baStep_eq_scoreRay_gaugeSection
    (prob : IBProblem (X := X) (Y := Y))
    (p : X → FinProb T) (x : X) :
    ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p x
      = ScoreRay.gaugeSection (T := T) (ibBlahutArimotoScoreRay prob p x) :=
  ibBlahutArimotoStep_eq_scoreRayGaugeSection
    (X := X) (Y := Y) (T := T) prob p x

/-- Canonical projective invariance of BA update from score-ray equality. -/
theorem baStep_eq_of_scoreRay_eq
    (prob : IBProblem (X := X) (Y := Y))
    {p q : X → FinProb T}
    (hRay :
      ibBlahutArimotoScoreRay (X := X) (Y := Y) (T := T) prob p
      = ibBlahutArimotoScoreRay (X := X) (Y := Y) (T := T) prob q) :
    ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p
      = ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q :=
  ibBlahutArimotoStep_eq_of_scoreRay_eq
    (X := X) (Y := Y) (T := T) prob p q hRay

/-- Canonical BA radial/projective factorization (slice-wise). -/
theorem baStep_radial_projective_split
    (prob : IBProblem (X := X) (Y := Y))
    (p : X → FinProb T) (x : X) (t : T) :
    ibBlahutArimotoStepUnnormalized (X := X) (Y := Y) (T := T) prob p x t
      =
    ibBlahutArimotoStepDegree (X := X) (Y := Y) (T := T) prob p x *
      (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p x t) := by
  symm
  simpa using
    ibBlahutArimotoStep_radial_projective_split
      (X := X) (Y := Y) (T := T) prob p x t

/-- Canonical frozen free-energy decomposition (internal Jaynes form). -/
theorem frozenFreeEnergy_eq_gap_minus_logPartition
    [DecidableEq T]
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (hq : ∀ t : T, 0 < (qT t).toReal)
    (p : X → FinProb T) :
    ibFrozenFreeEnergy prob qT mY_givenT p
      =
    baFrozenTargetGapWithGibbs
      (X := X) (Y := Y) (T := T) prob qT mY_givenT hq p
      - frozenLogPartitionOffset prob qT mY_givenT :=
  ibFrozenFreeEnergy_eq_gap_minus_logPartition
    (X := X) (Y := Y) (T := T) prob qT mY_givenT hq p

/-- Canonical frozen variational descent theorem. -/
theorem frozenVariational_descent
    [DecidableEq T]
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (hq : ∀ t : T, 0 < (qT t).toReal)
    (p : X → FinProb T) :
    ibVariationalFunctionalFrozen prob qT mY_givenT
      (ibBlahutArimotoStepFrozen (X := X) (Y := Y) (T := T) prob qT mY_givenT)
    ≤ ibVariationalFunctionalFrozen prob qT mY_givenT p :=
  ibVariationalFunctional_frozen_descent
    (X := X) (Y := Y) (T := T) prob qT mY_givenT hq p

end CanonicalAPI

end InfoGeometry.Canonical.IB
