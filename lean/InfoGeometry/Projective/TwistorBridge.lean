import InfoGeometry.Projective.Normalize
import InfoGeometry.Twistor.NullProjective

/-!
# Positive-Measure Projective/Twistor Bridge

Bridge from legacy positive-measure projective classes to twistor-space
null projective points on `EuclideanSpace ℝ α`.
-/

open scoped Projectivization

namespace InfoGeometry.Projective

open InfoGeometry.Twistor

section EuclideanTwistorBridge

variable {α : Type*} [Fintype α] [Nonempty α]

/-- Underlying Euclidean projective ray associated to a positive-measure projective class. -/
noncomputable def projectiveClassToEuclideanProjectivization :
    PositiveMeasure.Proj (α := α) → Projectivization ℝ (EuclideanSpace ℝ α) :=
  Quotient.lift
    (fun μ =>
      Projectivization.mk ℝ
        (positiveMeasureToEuclidean (α := α) μ)
        (positiveMeasureToEuclidean_ne_zero (α := α) μ))
    (by
      intro μ ν h
      exact congrArg Subtype.val
        (positiveMeasureToConeInteriorRay_sameRay (α := α) h))

@[simp] lemma projectiveClassToEuclideanProjectivization_mk (μ : PositiveMeasure α ℝ) :
    projectiveClassToEuclideanProjectivization (α := α) (Quotient.mk _ μ) =
      Projectivization.mk ℝ
        (positiveMeasureToEuclidean (α := α) μ)
        (positiveMeasureToEuclidean_ne_zero (α := α) μ) := rfl

/--
Map positive-measure projective classes into twistor space, assuming
every positive-measure Euclidean representative is `Q`-null.
-/
noncomputable def projectiveClassToTwistor
    (Q : QuadraticForm ℝ (EuclideanSpace ℝ α))
    (hNull : ∀ μ : PositiveMeasure α ℝ, Q (positiveMeasureToEuclidean (α := α) μ) = 0) :
    PositiveMeasure.Proj (α := α) → TwistorSpace Q :=
  Quotient.lift
    (fun μ =>
      twistorMk Q
        (positiveMeasureToEuclidean (α := α) μ)
        (positiveMeasureToEuclidean_ne_zero (α := α) μ)
        (hNull μ))
    (by
      intro μ ν h
      apply Subtype.ext
      have hq : (Quotient.mk _ μ : PositiveMeasure.Proj (α := α)) = Quotient.mk _ ν :=
        Quotient.sound h
      have hproj :=
        congrArg (projectiveClassToEuclideanProjectivization (α := α)) hq
      simpa [projectiveClassToEuclideanProjectivization_mk] using hproj)

@[simp] lemma projectiveClassToTwistor_mk
    (Q : QuadraticForm ℝ (EuclideanSpace ℝ α))
    (hNull : ∀ μ : PositiveMeasure α ℝ, Q (positiveMeasureToEuclidean (α := α) μ) = 0)
    (μ : PositiveMeasure α ℝ) :
    projectiveClassToTwistor (α := α) Q hNull (Quotient.mk _ μ)
      =
    twistorMk Q
      (positiveMeasureToEuclidean (α := α) μ)
      (positiveMeasureToEuclidean_ne_zero (α := α) μ)
      (hNull μ) := rfl

@[simp] lemma projectiveClassToTwistor_val
    (Q : QuadraticForm ℝ (EuclideanSpace ℝ α))
    (hNull : ∀ μ : PositiveMeasure α ℝ, Q (positiveMeasureToEuclidean (α := α) μ) = 0)
    (q : PositiveMeasure.Proj (α := α)) :
    (projectiveClassToTwistor (α := α) Q hNull q).1
      = projectiveClassToEuclideanProjectivization (α := α) q := by
  refine Quotient.inductionOn q ?_
  intro μ
  rfl

/--
Canonical degenerate null quadratic form on `EuclideanSpace ℝ α`.
Useful as a constructive twistor target when no nontrivial null form is fixed yet.
-/
noncomputable def zeroNullQuadraticForm :
    QuadraticForm ℝ (EuclideanSpace ℝ α) := 0

@[simp] lemma zeroNullQuadraticForm_apply (v : EuclideanSpace ℝ α) :
    zeroNullQuadraticForm (α := α) v = 0 := rfl

/-- Every positive-measure Euclidean representative is null for `zeroNullQuadraticForm`. -/
@[simp] lemma positiveMeasureToEuclidean_zeroNullQuadraticForm_null
    (μ : PositiveMeasure α ℝ) :
    zeroNullQuadraticForm (α := α) (positiveMeasureToEuclidean (α := α) μ) = 0 := by
  simp [zeroNullQuadraticForm]

/--
Anomaly-weighted null quadratic form parameterized by a scalar amplitude.
Since it scales the zero form, `hNull` is discharged constructively.
-/
noncomputable def anomalyWeightedNullQuadraticForm
    (A : ℝ) : QuadraticForm ℝ (EuclideanSpace ℝ α) :=
  A • zeroNullQuadraticForm (α := α)

@[simp] lemma anomalyWeightedNullQuadraticForm_apply
    (A : ℝ) (v : EuclideanSpace ℝ α) :
    anomalyWeightedNullQuadraticForm (α := α) A v = 0 := by
  simp [anomalyWeightedNullQuadraticForm, zeroNullQuadraticForm]

/-- Every positive-measure Euclidean representative is null for `anomalyWeightedNullQuadraticForm`. -/
@[simp] lemma positiveMeasureToEuclidean_anomalyWeightedNullQuadraticForm_null
    (A : ℝ) (μ : PositiveMeasure α ℝ) :
    anomalyWeightedNullQuadraticForm (α := α) A
      (positiveMeasureToEuclidean (α := α) μ) = 0 := by
  simp [anomalyWeightedNullQuadraticForm, zeroNullQuadraticForm]

/-- Twistor bridge using the canonical degenerate null quadratic form. -/
noncomputable def projectiveClassToTwistorZero :
    PositiveMeasure.Proj (α := α) →
      TwistorSpace (zeroNullQuadraticForm (α := α)) :=
  projectiveClassToTwistor (α := α)
    (Q := zeroNullQuadraticForm (α := α))
    (hNull := positiveMeasureToEuclidean_zeroNullQuadraticForm_null (α := α))

/-- Twistor bridge using an anomaly-weighted null quadratic form. -/
noncomputable def projectiveClassToTwistorAnomaly
    (A : ℝ) :
    PositiveMeasure.Proj (α := α) →
      TwistorSpace (anomalyWeightedNullQuadraticForm (α := α) A) :=
  projectiveClassToTwistor (α := α)
    (Q := anomalyWeightedNullQuadraticForm (α := α) A)
    (hNull := positiveMeasureToEuclidean_anomalyWeightedNullQuadraticForm_null (α := α) A)

@[simp] lemma projectiveClassToTwistorZero_val
    (q : PositiveMeasure.Proj (α := α)) :
    (projectiveClassToTwistorZero (α := α) q).1
      = projectiveClassToEuclideanProjectivization (α := α) q := by
  simpa [projectiveClassToTwistorZero] using
    (projectiveClassToTwistor_val (α := α)
      (Q := zeroNullQuadraticForm (α := α))
      (hNull := positiveMeasureToEuclidean_zeroNullQuadraticForm_null (α := α))
      q)

@[simp] lemma projectiveClassToTwistorAnomaly_val
    (A : ℝ) (q : PositiveMeasure.Proj (α := α)) :
    (projectiveClassToTwistorAnomaly (α := α) A q).1
      = projectiveClassToEuclideanProjectivization (α := α) q := by
  simpa [projectiveClassToTwistorAnomaly] using
    (projectiveClassToTwistor_val (α := α)
      (Q := anomalyWeightedNullQuadraticForm (α := α) A)
      (hNull := positiveMeasureToEuclidean_anomalyWeightedNullQuadraticForm_null (α := α) A)
      q)

/-- Twistor bridge is invariant under replacing a representative by its normalized gauge fix. -/
lemma projectiveClassToTwistor_mk_normalize
    (Q : QuadraticForm ℝ (EuclideanSpace ℝ α))
    (hNull : ∀ μ : PositiveMeasure α ℝ, Q (positiveMeasureToEuclidean (α := α) μ) = 0)
    (μ : PositiveMeasure α ℝ) :
    projectiveClassToTwistor (α := α) Q hNull
      (Quotient.mk _ (PositiveMeasure.normalize (α := α) (R := ℝ) μ))
    =
    projectiveClassToTwistor (α := α) Q hNull
      (Quotient.mk _ μ) := by
  have hsame : PositiveMeasure.SameRay μ (PositiveMeasure.normalize (α := α) (R := ℝ) μ) := by
    refine ⟨(PositiveMeasure.Z (α := α) (R := ℝ) μ)⁻¹,
      inv_pos.mpr (PositiveMeasure.Z_pos (α := α) (R := ℝ) μ), ?_⟩
    ext a
    rw [PositiveMeasure.scale_apply, PositiveMeasure.normalize_apply]
    field_simp [PositiveMeasure.Z_ne_zero (α := α) (R := ℝ) μ]
  exact (congrArg (projectiveClassToTwistor (α := α) Q hNull) (Quotient.sound hsame)).symm

/-- Twistor bridge is invariant under `normalizeOnProj`. -/
lemma projectiveClassToTwistor_normalizeOnProj
    (Q : QuadraticForm ℝ (EuclideanSpace ℝ α))
    (hNull : ∀ μ : PositiveMeasure α ℝ, Q (positiveMeasureToEuclidean (α := α) μ) = 0)
    (q : PositiveMeasure.Proj (α := α)) :
    projectiveClassToTwistor (α := α) Q hNull
      (Quotient.mk _ (PositiveMeasure.normalizeOnProj (α := α) q))
    =
    projectiveClassToTwistor (α := α) Q hNull q := by
  refine Quotient.inductionOn q ?_
  intro μ
  simpa [PositiveMeasure.normalizeOnProj_mk] using
    projectiveClassToTwistor_mk_normalize (α := α) (Q := Q) (hNull := hNull) μ

/-- Cone-interior-state-space view of the twistor bridge. -/
noncomputable def coneInteriorStateSpaceToTwistor
    (Q : QuadraticForm ℝ (EuclideanSpace ℝ α))
    (hNull : ∀ μ : PositiveMeasure α ℝ, Q (positiveMeasureToEuclidean (α := α) μ) = 0) :
    ConeInteriorStateSpace ((positiveOrthant (α := α)).cone) → TwistorSpace Q :=
  projectiveClassToTwistor (α := α) Q hNull ∘
    coneInteriorStateSpaceToProjectiveClass (α := α)

/-- Cone-state-space twistor bridge using the canonical degenerate null form. -/
noncomputable def coneInteriorStateSpaceToTwistorZero :
    ConeInteriorStateSpace ((positiveOrthant (α := α)).cone) →
      TwistorSpace (zeroNullQuadraticForm (α := α)) :=
  coneInteriorStateSpaceToTwistor (α := α)
    (Q := zeroNullQuadraticForm (α := α))
    (hNull := positiveMeasureToEuclidean_zeroNullQuadraticForm_null (α := α))

/-- Cone-state-space twistor bridge using an anomaly-weighted null form. -/
noncomputable def coneInteriorStateSpaceToTwistorAnomaly
    (A : ℝ) :
    ConeInteriorStateSpace ((positiveOrthant (α := α)).cone) →
      TwistorSpace (anomalyWeightedNullQuadraticForm (α := α) A) :=
  coneInteriorStateSpaceToTwistor (α := α)
    (Q := anomalyWeightedNullQuadraticForm (α := α) A)
    (hNull := positiveMeasureToEuclidean_anomalyWeightedNullQuadraticForm_null (α := α) A)

@[simp] lemma coneInteriorStateSpaceToTwistor_projectiveClass
    (Q : QuadraticForm ℝ (EuclideanSpace ℝ α))
    (hNull : ∀ μ : PositiveMeasure α ℝ, Q (positiveMeasureToEuclidean (α := α) μ) = 0)
    (q : PositiveMeasure.Proj (α := α)) :
    coneInteriorStateSpaceToTwistor (α := α) Q hNull
      (projectiveClassToConeInteriorStateSpace (α := α) q)
    =
    projectiveClassToTwistor (α := α) Q hNull q := by
  simp [coneInteriorStateSpaceToTwistor]

end EuclideanTwistorBridge

end InfoGeometry.Projective
