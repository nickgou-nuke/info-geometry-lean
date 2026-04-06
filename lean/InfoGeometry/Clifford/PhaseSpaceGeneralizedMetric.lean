import InfoGeometry.Cartan.Involution
import InfoGeometry.Clifford.NeutralPhaseSpaceCore
import InfoGeometry.Clifford.NeutralPhaseSpaceDoubledBridge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Clifford.PhaseSpaceGeneralizedMetric

Generalized-metric data on the corrected neutral phase-space owner `E × E*`.

This file stays algebraic and owner-level:

- a metric datum is a linear duality equivalence `gFlat : E ≃ₗ[ℝ] E*`,
- a `B`-field datum is a skew linear map `B : E →ₗ[ℝ] E*`,
- the base symmetric form is `gForm x y := gFlat x y`,
- the base antisymmetric form is `bForm x y := B x y`,
- the untwisted phase-space polarization swaps `E` and `E*` using `gFlat`,
- the owner-side generalized metric is the bilinear form
  `ℋ_G(X, Y) := canonicalNeutralBilin X (S_G Y)`,
- the full generalized-metric involution is the `B`-conjugate of that
  untwisted polarization,
- the induced plus/minus projectors are defined directly on the corrected owner.

No polarized, recomposition, or KKT capstones are attached here.
-/

namespace InfoGeometry.Clifford.PhaseSpaceGeneralizedMetric

open InfoGeometry.Cartan
open InfoGeometry.Clifford.NeutralPhaseSpaceCore
open InfoGeometry.Clifford.NeutralPhaseSpaceDoubledBridge
open InfoGeometry.Krein

noncomputable section

local instance phaseSpaceGeneralizedMetricInvertibleTwoReal : Invertible (2 : ℝ) :=
  invertibleOfNonzero (by norm_num)

section Core

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Metric data on `E`: an exact linear duality equivalence. -/
structure MetricDatum (E : Type*) [AddCommGroup E] [Module ℝ E] where
  gFlat : E ≃ₗ[ℝ] Module.Dual ℝ E
  symmetric : ∀ x y : E, gFlat x y = gFlat y x

namespace MetricDatum

/-- The raised-index inverse `g♯ : E* ≃ₗ[ℝ] E`. -/
@[rep_depth krein]
noncomputable abbrev gSharp (G : MetricDatum E) : Module.Dual ℝ E ≃ₗ[ℝ] E :=
  G.gFlat.symm

end MetricDatum

/-- Algebraic `B`-field data on phase space. -/
structure BFieldDatum (E : Type*) [AddCommGroup E] [Module ℝ E] where
  twist : E →ₗ[ℝ] Module.Dual ℝ E
  skew : ∀ x y : E, twist x y = -(twist y x)

namespace BFieldDatum

/-- The zero `B`-field. -/
@[rep_depth krein]
noncomputable def zero (E : Type*) [AddCommGroup E] [Module ℝ E] : BFieldDatum E where
  twist := 0
  skew := by
    intro x y
    simp

@[rep_depth krein, simp] theorem zero_twist (E : Type*) [AddCommGroup E] [Module ℝ E] :
    (zero E).twist = 0 := rfl

end BFieldDatum

/-- Generalized-metric data on the corrected phase-space owner. -/
structure GeneralizedMetricDatum (E : Type*) [AddCommGroup E] [Module ℝ E] where
  metric : MetricDatum E
  bField : BFieldDatum E

namespace GeneralizedMetricDatum

/-- The base symmetric metric form `g(x, y)`. -/
@[rep_depth krein]
noncomputable abbrev gForm (G : GeneralizedMetricDatum E) : LinearMap.BilinForm ℝ E :=
  G.metric.gFlat

/-- The base antisymmetric `B`-field form `B(x, y)`. -/
@[rep_depth krein]
noncomputable abbrev bForm (G : GeneralizedMetricDatum E) : LinearMap.BilinForm ℝ E :=
  G.bField.twist

/-- The untwisted phase-space polarization determined by the metric datum. -/
@[rep_depth krein]
noncomputable def basePolarization (G : GeneralizedMetricDatum E) :
    Module.End ℝ (PhaseSpaceCarrier E) where
  toFun := fun X => (G.metric.gFlat.symm X.2, G.metric.gFlat X.1)
  map_add' := by
    intro X Y
    refine Prod.ext ?_ ?_
    · simp
    · simp
  map_smul' := by
    intro r X
    refine Prod.ext ?_ ?_
    · simp
    · simp

/-- Phase-space `B`-transform `(x, φ) ↦ (x, Bx + φ)`. -/
@[rep_depth krein]
noncomputable def bTransform (G : GeneralizedMetricDatum E) :
    Module.End ℝ (PhaseSpaceCarrier E) where
  toFun := fun X => (X.1, G.bField.twist X.1 + X.2)
  map_add' := by
    intro X Y
    refine Prod.ext ?_ ?_
    · simp
    · simp [add_assoc, add_left_comm, add_comm]
  map_smul' := by
    intro r X
    refine Prod.ext ?_ ?_
    · simp
    · simp [smul_add]

/-- Inverse phase-space `B`-transform `(x, φ) ↦ (x, φ - Bx)`. -/
@[rep_depth krein]
noncomputable def bTransformInv (G : GeneralizedMetricDatum E) :
    Module.End ℝ (PhaseSpaceCarrier E) where
  toFun := fun X => (X.1, X.2 - G.bField.twist X.1)
  map_add' := by
    intro X Y
    refine Prod.ext ?_ ?_
    · simp
    · simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  map_smul' := by
    intro r X
    refine Prod.ext ?_ ?_
    · simp
    · simp [sub_eq_add_neg, smul_add]

/-- The phase-space generalized-metric involution, obtained by `B`-conjugating
the untwisted metric polarization. -/
@[rep_depth krein]
noncomputable def polarization (G : GeneralizedMetricDatum E) :
    Module.End ℝ (PhaseSpaceCarrier E) :=
  G.bTransform * G.basePolarization * G.bTransformInv

/-- The owner-side generalized metric `ℋ_G(X, Y) := η(X, S_G Y)`, where `η` is
the canonical neutral bilinear form and `S_G` is the phase-space polarization. -/
@[rep_depth krein]
noncomputable def generalizedMetricForm (G : GeneralizedMetricDatum E) :
    LinearMap.BilinForm ℝ (PhaseSpaceCarrier E) :=
  (canonicalNeutralBilin (E := E)).compl₂ G.polarization

/-- The quadratic form associated to the owner-side generalized metric. -/
@[rep_depth krein]
noncomputable def generalizedMetricQuadraticForm (G : GeneralizedMetricDatum E) :
    QuadraticForm ℝ (PhaseSpaceCarrier E) :=
  G.generalizedMetricForm.toQuadraticMap

/-- The `+1` projector attached to the phase-space generalized-metric involution. -/
@[rep_depth krein]
noncomputable def plusProjector (G : GeneralizedMetricDatum E) :
    Module.End ℝ (PhaseSpaceCarrier E) :=
  Pplus G.polarization

/-- The `-1` projector attached to the phase-space generalized-metric involution. -/
@[rep_depth krein]
noncomputable def minusProjector (G : GeneralizedMetricDatum E) :
    Module.End ℝ (PhaseSpaceCarrier E) :=
  Pminus G.polarization

@[rep_depth krein, simp] theorem gForm_apply
    (G : GeneralizedMetricDatum E) (x y : E) :
    G.gForm x y = G.metric.gFlat x y := rfl

@[rep_depth krein] theorem gForm_isSymm
    (G : GeneralizedMetricDatum E) :
    LinearMap.IsSymm G.gForm :=
  ⟨G.metric.symmetric⟩

@[rep_depth krein, simp] theorem bForm_apply
    (G : GeneralizedMetricDatum E) (x y : E) :
    G.bForm x y = G.bField.twist x y := rfl

@[rep_depth krein] theorem bForm_isSkew
    (G : GeneralizedMetricDatum E) (x y : E) :
    G.bForm x y = -(G.bForm y x) :=
  G.bField.skew x y

@[rep_depth krein, simp] theorem basePolarization_apply
    (G : GeneralizedMetricDatum E) (X : PhaseSpaceCarrier E) :
    G.basePolarization X = (G.metric.gFlat.symm X.2, G.metric.gFlat X.1) := rfl

@[rep_depth krein, simp] theorem bTransform_apply
    (G : GeneralizedMetricDatum E) (X : PhaseSpaceCarrier E) :
    G.bTransform X = (X.1, G.bField.twist X.1 + X.2) := rfl

@[rep_depth krein, simp] theorem bTransformInv_apply
    (G : GeneralizedMetricDatum E) (X : PhaseSpaceCarrier E) :
    G.bTransformInv X = (X.1, X.2 - G.bField.twist X.1) := rfl

@[rep_depth krein] theorem basePolarization_sq
    (G : GeneralizedMetricDatum E) :
    G.basePolarization * G.basePolarization = 1 := by
  apply LinearMap.ext
  intro X
  rcases X with ⟨x, φ⟩
  refine Prod.ext ?_ ?_
  · simp [basePolarization]
  · simp [basePolarization]

@[rep_depth krein] theorem bTransform_mul_bTransformInv
    (G : GeneralizedMetricDatum E) :
    G.bTransform * G.bTransformInv = 1 := by
  apply LinearMap.ext
  intro X
  rcases X with ⟨x, φ⟩
  refine Prod.ext ?_ ?_
  · simp [bTransform, bTransformInv]
  · simp [bTransform, bTransformInv, sub_eq_add_neg, add_comm, add_left_comm]

@[rep_depth krein] theorem bTransformInv_mul_bTransform
    (G : GeneralizedMetricDatum E) :
    G.bTransformInv * G.bTransform = 1 := by
  apply LinearMap.ext
  intro X
  rcases X with ⟨x, φ⟩
  refine Prod.ext ?_ ?_
  · simp [bTransform, bTransformInv]
  · simp [bTransform, bTransformInv, sub_eq_add_neg, add_comm]

@[rep_depth krein, simp] theorem polarization_apply
    (G : GeneralizedMetricDatum E) (x : E) (φ : Module.Dual ℝ E) :
    G.polarization (x, φ)
      =
        (G.metric.gFlat.symm (φ - G.bField.twist x),
          G.metric.gFlat x
            + G.bField.twist (G.metric.gFlat.symm (φ - G.bField.twist x))) := by
  refine Prod.ext ?_ ?_
  · simp [polarization, bTransform, bTransformInv, basePolarization]
  · simp [polarization, bTransform, bTransformInv, basePolarization, sub_eq_add_neg, add_comm]

@[rep_depth krein, simp] theorem generalizedMetricForm_apply
    (G : GeneralizedMetricDatum E) (X Y : PhaseSpaceCarrier E) :
    G.generalizedMetricForm X Y = canonicalNeutralBilin (E := E) X (G.polarization Y) := by
  simp [generalizedMetricForm, LinearMap.compl₂_apply]

@[rep_depth krein, simp] theorem generalizedMetricQuadraticForm_apply
    (G : GeneralizedMetricDatum E) (X : PhaseSpaceCarrier E) :
    G.generalizedMetricQuadraticForm X = canonicalNeutralBilin (E := E) X (G.polarization X) := by
  simp [generalizedMetricQuadraticForm, generalizedMetricForm_apply]

@[rep_depth krein, simp] theorem canonicalNeutralBilin_symm
    (X Y : PhaseSpaceCarrier E) :
    canonicalNeutralBilin (E := E) X Y = canonicalNeutralBilin (E := E) Y X := by
  rcases X with ⟨x, φ⟩
  rcases Y with ⟨y, ψ⟩
  simp [canonicalNeutralBilin_apply, add_comm]

@[rep_depth krein] theorem polarization_sq
    (G : GeneralizedMetricDatum E) :
    G.polarization * G.polarization = 1 := by
  apply LinearMap.ext
  intro X
  rcases X with ⟨x, φ⟩
  refine Prod.ext ?_ ?_
  · simp [polarization_apply]
  · simp [polarization_apply, sub_eq_add_neg, add_comm, add_left_comm]

@[rep_depth krein] theorem polarization_is_cartan
    (G : GeneralizedMetricDatum E) :
    IsCartanInvolution G.polarization :=
  G.polarization_sq

@[rep_depth krein] theorem plusProjector_idempotent
    (G : GeneralizedMetricDatum E) :
    G.plusProjector * G.plusProjector = G.plusProjector :=
  Pplus_idempotent G.polarization G.polarization_is_cartan

@[rep_depth krein] theorem minusProjector_idempotent
    (G : GeneralizedMetricDatum E) :
    G.minusProjector * G.minusProjector = G.minusProjector :=
  Pminus_idempotent G.polarization G.polarization_is_cartan

@[rep_depth krein] theorem plusProjector_add_minusProjector
    (G : GeneralizedMetricDatum E) :
    G.plusProjector + G.minusProjector = 1 :=
  Pplus_add_Pminus_eq_id G.polarization

@[rep_depth krein] theorem plusProjector_mul_minusProjector
    (G : GeneralizedMetricDatum E) :
    G.plusProjector * G.minusProjector = 0 :=
  Pplus_comp_Pminus G.polarization G.polarization_is_cartan

@[rep_depth krein] theorem polarization_eq_plusProjector_sub_minusProjector
    (G : GeneralizedMetricDatum E) :
    G.polarization = G.plusProjector - G.minusProjector := by
  apply LinearMap.ext
  intro X
  change G.polarization X = G.plusProjector X - G.minusProjector X
  have hplus : G.plusProjector X = (⅟ (2 : ℝ)) • (X + G.polarization X) := by
    rw [plusProjector, Pplus_apply]
  have hminus : G.minusProjector X = (⅟ (2 : ℝ)) • (X - G.polarization X) := by
    rw [minusProjector, Pminus_apply]
  rw [hplus, hminus]
  symm
  calc
    (⅟ (2 : ℝ)) • (X + G.polarization X) - (⅟ (2 : ℝ)) • (X - G.polarization X)
        = (⅟ (2 : ℝ)) • X + (⅟ (2 : ℝ)) • (G.polarization X)
            - ((⅟ (2 : ℝ)) • X - (⅟ (2 : ℝ)) • (G.polarization X)) := by
              rw [smul_add, smul_sub]
    _ = (⅟ (2 : ℝ)) • (G.polarization X) + (⅟ (2 : ℝ)) • (G.polarization X) := by
          abel_nf
    _ = ((⅟ (2 : ℝ)) + (⅟ (2 : ℝ))) • (G.polarization X) := by
          rw [add_smul]
    _ = G.polarization X := by
          norm_num

@[rep_depth krein] theorem decompose
    (G : GeneralizedMetricDatum E) (X : PhaseSpaceCarrier E) :
    X = G.plusProjector X + G.minusProjector X := by
  exact InfoGeometry.Cartan.decompose G.polarization G.polarization_is_cartan X

/-- The untwisted generalized metric determined only by the metric datum. -/
@[rep_depth krein]
noncomputable def ofMetric (metric : MetricDatum E) : GeneralizedMetricDatum E where
  metric := metric
  bField := BFieldDatum.zero E

@[rep_depth krein, simp] theorem ofMetric_polarization
    (metric : MetricDatum E) :
    (ofMetric metric).polarization = (ofMetric metric).basePolarization := by
  apply LinearMap.ext
  intro X
  rcases X with ⟨x, φ⟩
  refine Prod.ext ?_ ?_
  · simp [polarization, ofMetric, bTransform, bTransformInv, basePolarization, BFieldDatum.zero]
  · simp [polarization, ofMetric, bTransform, bTransformInv, basePolarization, BFieldDatum.zero]

@[rep_depth krein, simp] theorem generalizedMetricForm_ofMetric_apply
    (metric : MetricDatum E) (x y : E) (φ ψ : Module.Dual ℝ E) :
    (ofMetric metric).generalizedMetricForm (x, φ) (y, ψ)
      = metric.gFlat x y + φ (metric.gFlat.symm ψ) := by
  rw [generalizedMetricForm_apply, ofMetric_polarization]
  have hg : metric.gFlat y x = metric.gFlat x y := by
    simpa using metric.symmetric y x
  simp [canonicalNeutralBilin_apply, basePolarization, ofMetric, hg, add_comm]

@[rep_depth krein, simp] theorem generalizedMetricForm_apply_explicit
    (G : GeneralizedMetricDatum E) (x y : E) (φ ψ : Module.Dual ℝ E) :
    G.generalizedMetricForm (x, φ) (y, ψ)
      =
        φ (G.metric.gFlat.symm (ψ - G.bField.twist y))
          + G.metric.gFlat x y
          + G.bField.twist (G.metric.gFlat.symm (ψ - G.bField.twist y)) x := by
  rw [generalizedMetricForm_apply, polarization_apply]
  have hg : G.metric.gFlat y x = G.metric.gFlat x y := by
    simpa using G.metric.symmetric y x
  simp [canonicalNeutralBilin_apply, hg, add_assoc, add_left_comm]

@[rep_depth krein] theorem canonicalNeutralBilin_polarization_invariant
    (G : GeneralizedMetricDatum E) (X Y : PhaseSpaceCarrier E) :
    canonicalNeutralBilin (E := E) (G.polarization X) (G.polarization Y)
      = canonicalNeutralBilin (E := E) X Y := by
  rcases X with ⟨x, φ⟩
  rcases Y with ⟨y, ψ⟩
  let u : E := G.metric.gFlat.symm (φ - G.bField.twist x)
  let v : E := G.metric.gFlat.symm (ψ - G.bField.twist y)
  have hu : G.metric.gFlat u = φ - G.bField.twist x := by
    simp [u]
  have hv : G.metric.gFlat v = ψ - G.bField.twist y := by
    simp [v]
  have hxv : G.metric.gFlat x v = ψ x - G.bField.twist y x := by
    calc
      G.metric.gFlat x v = G.metric.gFlat v x := by
        simpa using G.metric.symmetric x v
      _ = (G.metric.gFlat v) x := rfl
      _ = (ψ - G.bField.twist y) x := by rw [hv]
      _ = ψ x - G.bField.twist y x := by simp
  have hyu : G.metric.gFlat y u = φ y - G.bField.twist x y := by
    calc
      G.metric.gFlat y u = G.metric.gFlat u y := by
        simpa using G.metric.symmetric y u
      _ = (G.metric.gFlat u) y := rfl
      _ = (φ - G.bField.twist x) y := by rw [hu]
      _ = φ y - G.bField.twist x y := by simp
  rw [polarization_apply, polarization_apply, canonicalNeutralBilin_apply]
  calc
    (G.metric.gFlat x + G.bField.twist u) v + (G.metric.gFlat y + G.bField.twist v) u
        = (G.metric.gFlat x v + G.bField.twist u v)
            + (G.metric.gFlat y u + G.bField.twist v u) := by
              simp [add_assoc]
    _ = (ψ x - G.bField.twist y x + G.bField.twist u v)
          + (φ y - G.bField.twist x y + G.bField.twist v u) := by
            rw [hxv, hyu]
    _ = (ψ x - G.bField.twist y x + G.bField.twist u v)
          + (φ y + G.bField.twist y x - G.bField.twist u v) := by
            rw [G.bField.skew x y, G.bField.skew u v]
            ring
    _ = φ y + ψ x := by ring
    _ = canonicalNeutralBilin (E := E) (x, φ) (y, ψ) := by
          simp [canonicalNeutralBilin_apply]

@[rep_depth krein] theorem canonicalNeutralBilin_polarization_left
    (G : GeneralizedMetricDatum E) (X Y : PhaseSpaceCarrier E) :
    canonicalNeutralBilin (E := E) (G.polarization X) Y
      = canonicalNeutralBilin (E := E) X (G.polarization Y) := by
  have h := G.canonicalNeutralBilin_polarization_invariant X (G.polarization Y)
  have hsq : G.polarization (G.polarization Y) = Y := by
    have hsq' :=
      congrArg (fun F : Module.End ℝ (PhaseSpaceCarrier E) => F Y) G.polarization_sq
    simpa using hsq'
  simpa [hsq] using h

@[rep_depth krein] theorem generalizedMetricForm_symm
    (G : GeneralizedMetricDatum E) (X Y : PhaseSpaceCarrier E) :
    G.generalizedMetricForm X Y = G.generalizedMetricForm Y X := by
  rw [generalizedMetricForm_apply, generalizedMetricForm_apply]
  calc
    canonicalNeutralBilin (E := E) X (G.polarization Y)
        = canonicalNeutralBilin (E := E) (G.polarization Y) X := by
            simpa using canonicalNeutralBilin_symm (E := E) X (G.polarization Y)
    _ = canonicalNeutralBilin (E := E) Y (G.polarization X) := by
          simpa using canonicalNeutralBilin_polarization_left (G := G) (X := Y) (Y := X)

@[rep_depth krein] theorem generalizedMetricForm_isSymm
    (G : GeneralizedMetricDatum E) :
    LinearMap.IsSymm G.generalizedMetricForm :=
  ⟨G.generalizedMetricForm_symm⟩

end GeneralizedMetricDatum

section Realization

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
@[rep_depth krein] theorem basePolarization_eq_phaseJ
    (G : GeneralizedMetricDatum E) :
    G.basePolarization = phaseJ G.metric.gFlat := by
  apply LinearMap.ext
  intro X
  rcases X with ⟨x, φ⟩
  rfl

omit [CompleteSpace E] in
@[rep_depth krein] theorem polarization_eq_b_conj_phaseJ
    (G : GeneralizedMetricDatum E) :
    G.polarization = G.bTransform * phaseJ G.metric.gFlat * G.bTransformInv := by
  rw [GeneralizedMetricDatum.polarization, basePolarization_eq_phaseJ]

omit [CompleteSpace E] in
@[rep_depth krein] theorem metric_phaseJ_sq
    (G : GeneralizedMetricDatum E) :
    phaseJ G.metric.gFlat * phaseJ G.metric.gFlat = 1 := by
  rw [← basePolarization_eq_phaseJ (G := G)]
  exact G.basePolarization_sq

omit [CompleteSpace E] in
@[rep_depth krein] theorem toDoubledCopyRho_comp_ofMetricPolarization
    (metric : MetricDatum E) :
    (toDoubledCopyRho metric.gFlat).comp ((GeneralizedMetricDatum.ofMetric metric).polarization)
      = (modular_j (E := E)).toLinearMap.comp (toDoubledCopyRho metric.gFlat) := by
  rw [GeneralizedMetricDatum.ofMetric_polarization]
  simpa [GeneralizedMetricDatum.basePolarization, GeneralizedMetricDatum.ofMetric] using
    (toDoubledCopyRho_comp_phaseJ (E := E) metric.gFlat)

end Realization

end Core

end

end InfoGeometry.Clifford.PhaseSpaceGeneralizedMetric
