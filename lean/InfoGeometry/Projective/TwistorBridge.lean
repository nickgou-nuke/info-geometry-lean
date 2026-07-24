import InfoGeometry.PositiveMeasure
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Projective.Bridge
import InfoGeometry.Projective.Normalize
import InfoGeometry.Twistor.NullProjective

/-!
# Projective.TwistorBridge

Bridge between Euclidean projectivization and twistor spaces.
This module defines the mapping from positive-measure rays to twistor points
under a fixed null quadratic form.

Vacuous zero-quadratic-form scaffolds have been removed in favor of
nontrivial constructive witnesses.

Repository policy boundary:
this file does not identify twistor space with split-octonions. Any
split-octonion/twistor relation is a carried-structure theorem target, not a
definitional equality.
It also does not claim a quantized twistor CCR realization by itself.
The intended target is Penrose's carried-structure statement:
the quantized twistor algebra carries split-octonion and `G2*` structure.
-/

namespace InfoGeometry.Projective.TwistorBridge

open InfoGeometry.Krein
open InfoGeometry.Projective
open InfoGeometry.Twistor
open scoped Projectivization

section EuclideanTwistorBridge

variable {α : Type*} [Fintype α] [Nonempty α]

/--
Map from a positive-measure ray to a twistor point under a null quadratic form.
-/
noncomputable def projectiveClassToTwistor
    (Q : QuadraticForm ℝ (EuclideanSpace ℝ α))
    (hNull : ∀ μ : PositiveMeasure α ℝ, Q (positiveMeasureToEuclidean (α := α) μ) = 0) :
    PositiveMeasure.Proj (α := α) → TwistorSpace Q :=
  Quotient.lift
    (fun μ => twistorMk Q (positiveMeasureToEuclidean (α := α) μ)
      (positiveMeasureToEuclidean_ne_zero (α := α) μ) (hNull μ))
    (by
      intro μ₁ μ₂ hray
      rcases hray with ⟨c, rfl⟩
      let v : EuclideanSpace ℝ α := positiveMeasureToEuclidean (α := α) μ₁
      have hv0 : v ≠ 0 := positiveMeasureToEuclidean_ne_zero (α := α) μ₁
      have hcv0 : c.1 • v ≠ 0 := smul_ne_zero (ne_of_gt c.2) hv0
      have hscaled :
          positiveMeasureToEuclidean (α := α) (PositiveMeasure.scale c.1 c.2 μ₁) = c.1 • v := by
        simpa [v] using positiveMeasureToEuclidean_scale (α := α) c.1 c.2 μ₁
      have hmkScaled :
          Projectivization.mk ℝ
              (positiveMeasureToEuclidean (α := α) (PositiveMeasure.scale c.1 c.2 μ₁))
              (positiveMeasureToEuclidean_ne_zero (α := α) (PositiveMeasure.scale c.1 c.2 μ₁))
            =
          Projectivization.mk ℝ (c.1 • v) hcv0 := by
        apply (Projectivization.mk_eq_mk_iff ℝ
          (positiveMeasureToEuclidean (α := α) (PositiveMeasure.scale c.1 c.2 μ₁))
          (c.1 • v)
          (positiveMeasureToEuclidean_ne_zero (α := α) (PositiveMeasure.scale c.1 c.2 μ₁))
          hcv0).2
        refine ⟨1, ?_⟩
        simpa [one_smul] using hscaled.symm
      have hmkRay :
          Projectivization.mk ℝ (c.1 • v) hcv0 = Projectivization.mk ℝ v hv0 := by
        apply (Projectivization.mk_eq_mk_iff ℝ (c.1 • v) v hcv0 hv0).2
        refine ⟨Units.mk0 c.1 (ne_of_gt c.2), ?_⟩
        simp
      have hmkGoal :
          Projectivization.mk ℝ v hv0
            =
          Projectivization.mk ℝ
              (positiveMeasureToEuclidean (α := α) (PositiveMeasure.scale c.1 c.2 μ₁))
              (positiveMeasureToEuclidean_ne_zero (α := α) (PositiveMeasure.scale c.1 c.2 μ₁)) := by
        exact hmkRay.symm.trans hmkScaled.symm
      apply Subtype.ext
      simpa [twistorMk, v] using hmkGoal
    )

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

/--
Theorem: Projection to a twistor space is equivalent to the cone-interior
projective representative at the level of value representatives.
-/
theorem projectiveClassToTwistor_val
    (Q : QuadraticForm ℝ (EuclideanSpace ℝ α))
    (hNull : ∀ μ : PositiveMeasure α ℝ, Q (positiveMeasureToEuclidean (α := α) μ) = 0)
    (q : PositiveMeasure.Proj (α := α)) :
    (projectiveClassToTwistor (α := α) Q hNull q).1
      = (projectiveClassToConeInteriorStateSpace (α := α) q).1 := by
  refine Quotient.inductionOn q ?_
  intro μ
  rfl

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
    refine ⟨(⟨(PositiveMeasure.Z (α := α) (R := ℝ) μ)⁻¹,
      inv_pos.mpr (PositiveMeasure.Z_pos (α := α) (R := ℝ) μ)⟩ : InfoGeometry.Stratum.PosGauge), ?_⟩
    ext a
    change (PositiveMeasure.Z (α := α) (R := ℝ) μ)⁻¹ * μ a = μ a * (PositiveMeasure.Z (α := α) (R := ℝ) μ)⁻¹
    simpa [mul_comm] using (rfl : (PositiveMeasure.Z (α := α) (R := ℝ) μ)⁻¹ * μ a =
      (PositiveMeasure.Z (α := α) (R := ℝ) μ)⁻¹ * μ a)
  exact (congrArg (projectiveClassToTwistor (α := α) Q hNull) (Quotient.sound hsame)).symm

/-- Twistor bridge is invariant under `normalizeOnProj`. -/
lemma projectiveClassToTwistor_normalizeOnProj
    (Q : QuadraticForm ℝ (EuclideanSpace ℝ α))
    (hNull : ∀ μ : PositiveMeasure α ℝ, Q (positiveMeasureToEuclidean (α := α) μ) = 0)
    (q : PositiveMeasure.Proj (α := α)) :
    projectiveClassToTwistor (α := α) Q hNull
      (Quotient.mk _ (InfoGeometry.Projective.Normalize.normalizeOnProj (α := α) q))
    =
    projectiveClassToTwistor (α := α) Q hNull q := by
  refine Quotient.inductionOn q ?_
  intro μ
  simpa [InfoGeometry.Projective.Normalize.normalizeOnProj_mk] using
    projectiveClassToTwistor_mk_normalize (α := α) (Q := Q) (hNull := hNull) μ

/-- Cone-interior-state-space view of the twistor bridge. -/
noncomputable def coneInteriorStateSpaceToTwistor
    (Q : QuadraticForm ℝ (EuclideanSpace ℝ α))
    (hNull : ∀ μ : PositiveMeasure α ℝ, Q (positiveMeasureToEuclidean (α := α) μ) = 0) :
    ConeInteriorStateSpace ((positiveOrthant (α := α)).cone) → TwistorSpace Q :=
  projectiveClassToTwistor (α := α) Q hNull ∘
    coneInteriorStateSpaceToProjectiveClass (α := α)

end EuclideanTwistorBridge

end InfoGeometry.Projective.TwistorBridge
