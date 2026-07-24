/-
InfoGeometry/Arithmetic/ProjectiveWeylGauge.lean

Weyl-gauge decomposition sockets for projective arithmetic KL readouts.

This module reuses the finite shape/scale KL machinery from
`PrimitiveProjectiveRays` and the compact temperature coordinate from
`ProjectiveTemperature`.

It does not prove a global KL decomposition theorem, Itakura-Saito theorem,
Jensen inequality, or zeta estimate.  The Weyl factorization laws are supplied
as explicit witness data.
-/

import InfoGeometry.Arithmetic.PrimitiveProjectiveRays
import InfoGeometry.Arithmetic.ProjectiveRelativeEntropy
import InfoGeometry.Thermodynamics.ProjectiveTemperature

noncomputable section

namespace InfoGeometry.Arithmetic.ProjectiveWeylGauge

open InfoGeometry.Arithmetic.PrimitiveProjectiveRays
open InfoGeometry.Arithmetic.ProjectiveRelativeEntropy
open InfoGeometry.Thermodynamics.ProjectiveTemperature

/-! ## 1. Scale and shape readouts in projective temperature -/

/-- Projective Weyl thermal mass, evaluated at `β = u⁻¹`. -/
def projectiveWeylThermalMass
    (counts : CountProfile) (support : Finset ℕ) (u : ℝ) : ℝ :=
  finiteArithmeticPartition counts support (betaInvert u)

/-- Projective scale-invariant arithmetic shape, evaluated at `β = u⁻¹`. -/
def projectiveArithmeticShape
    (counts : CountProfile) (support : Finset ℕ) (u : ℝ) : CountProfile :=
  finiteArithmeticNormalizedRay counts support (betaInvert u)

/-- The projective Weyl mass is the finite partition at inverted temperature. -/
theorem projectiveWeylThermalMass_eq
    (counts : CountProfile) (support : Finset ℕ) (u : ℝ) :
    projectiveWeylThermalMass counts support u =
      finiteArithmeticPartition counts support (betaInvert u) := by
  rfl

/-- The projective arithmetic shape is the normalized finite ray at inverted temperature. -/
theorem projectiveArithmeticShape_eq
    (counts : CountProfile) (support : Finset ℕ) (u : ℝ) :
    projectiveArithmeticShape counts support u =
      finiteArithmeticNormalizedRay counts support (betaInvert u) := by
  rfl

/-- Projective arithmetic shape is invariant under nonzero global rescaling of counts. -/
theorem projectiveArithmeticShape_scale_counts
    (counts : CountProfile) (support : Finset ℕ) (u c : ℝ)
    (hc : c ≠ 0) :
    projectiveArithmeticShape (fun n => c * counts n) support u =
      projectiveArithmeticShape counts support u := by
  simpa [projectiveArithmeticShape] using
    finiteArithmeticNormalizedRay_scale_counts counts support (betaInvert u) c hc

/-! ## 2. Abstract scale-invariant readouts -/

/--
A readout of arithmetic shapes which is invariant under Weyl rescaling of the
count profile.
-/
structure ScaleInvariantReadout where
  /-- Shape/core readout. -/
  readout : CountProfile → Finset ℕ → ℝ → ℝ

  /-- Weyl-scale invariance under nonzero global rescaling of counts. -/
  scale_invariant :
    ∀ (counts : CountProfile) (support : Finset ℕ) (u c : ℝ),
      c ≠ 0 →
        readout (fun n => c * counts n) support u =
          readout counts support u

namespace ScaleInvariantReadout

variable (R : ScaleInvariantReadout)

/-- Re-export scale invariance for a supplied shape/core readout. -/
theorem readout_scale_invariant
    (counts : CountProfile) (support : Finset ℕ) (u c : ℝ)
    (hc : c ≠ 0) :
    R.readout (fun n => c * counts n) support u =
      R.readout counts support u :=
  R.scale_invariant counts support u c hc

end ScaleInvariantReadout

/-! ## 2A. Pairwise scale-invariant Itakura-Saito shape readout -/

/--
A pairwise readout of arithmetic shapes which is invariant under independent
nonzero Weyl rescaling of either count profile.
-/
structure PairScaleInvariantReadout where
  /-- Pairwise shape/core readout. -/
  readout : CountProfile → CountProfile → Finset ℕ → ℝ → ℝ

  /-- Left profile Weyl-scale invariance. -/
  scale_invariant_left :
    ∀ (counts₁ counts₂ : CountProfile) (support : Finset ℕ) (u c : ℝ),
      c ≠ 0 →
        readout (fun n => c * counts₁ n) counts₂ support u =
          readout counts₁ counts₂ support u

  /-- Right profile Weyl-scale invariance. -/
  scale_invariant_right :
    ∀ (counts₁ counts₂ : CountProfile) (support : Finset ℕ) (u c : ℝ),
      c ≠ 0 →
        readout counts₁ (fun n => c * counts₂ n) support u =
          readout counts₁ counts₂ support u

namespace PairScaleInvariantReadout

variable (R : PairScaleInvariantReadout)

/-- Re-export left scale invariance. -/
theorem readout_scale_invariant_left
    (counts₁ counts₂ : CountProfile) (support : Finset ℕ) (u c : ℝ)
    (hc : c ≠ 0) :
    R.readout (fun n => c * counts₁ n) counts₂ support u =
      R.readout counts₁ counts₂ support u :=
  R.scale_invariant_left counts₁ counts₂ support u c hc

/-- Re-export right scale invariance. -/
theorem readout_scale_invariant_right
    (counts₁ counts₂ : CountProfile) (support : Finset ℕ) (u c : ℝ)
    (hc : c ≠ 0) :
    R.readout counts₁ (fun n => c * counts₂ n) support u =
      R.readout counts₁ counts₂ support u :=
  R.scale_invariant_right counts₁ counts₂ support u c hc

end PairScaleInvariantReadout

/--
Projective Itakura-Saito distance between two normalized arithmetic shapes.

The inputs to `scalarItakuraSaitoDivergence` are the projective shapes, not the
raw count profiles, so the readout is insensitive to Weyl rescaling of either
profile.
-/
def projectiveItakuraSaitoDistance
    (counts₁ counts₂ : CountProfile) (support : Finset ℕ) (u : ℝ) : ℝ :=
  Finset.sum support (fun n =>
    scalarItakuraSaitoDivergence
      (projectiveArithmeticShape counts₁ support u n)
      (projectiveArithmeticShape counts₂ support u n))

/-- The projective Itakura-Saito distance is invariant under left Weyl rescaling. -/
theorem projectiveItakuraSaitoDistance_scale_left
    (counts₁ counts₂ : CountProfile) (support : Finset ℕ) (u c : ℝ)
    (hc : c ≠ 0) :
    projectiveItakuraSaitoDistance (fun n => c * counts₁ n) counts₂ support u =
      projectiveItakuraSaitoDistance counts₁ counts₂ support u := by
  unfold projectiveItakuraSaitoDistance
  rw [projectiveArithmeticShape_scale_counts counts₁ support u c hc]

/-- The projective Itakura-Saito distance is invariant under right Weyl rescaling. -/
theorem projectiveItakuraSaitoDistance_scale_right
    (counts₁ counts₂ : CountProfile) (support : Finset ℕ) (u c : ℝ)
    (hc : c ≠ 0) :
    projectiveItakuraSaitoDistance counts₁ (fun n => c * counts₂ n) support u =
      projectiveItakuraSaitoDistance counts₁ counts₂ support u := by
  unfold projectiveItakuraSaitoDistance
  rw [projectiveArithmeticShape_scale_counts counts₂ support u c hc]

/-- Itakura-Saito distance as a pairwise scale-invariant shape readout. -/
def itakuraSaitoDistanceReadout : PairScaleInvariantReadout where
  readout := projectiveItakuraSaitoDistance
  scale_invariant_left := by
    intro counts₁ counts₂ support u c hc
    exact projectiveItakuraSaitoDistance_scale_left counts₁ counts₂ support u c hc
  scale_invariant_right := by
    intro counts₁ counts₂ support u c hc
    exact projectiveItakuraSaitoDistance_scale_right counts₁ counts₂ support u c hc

/-! ## 3. Weyl-gauge KL decomposition witness -/

/--
Proof-carrying Weyl-gauge decomposition of a finite arithmetic KL readout.

The existing `FiniteShapeScaleKLDecomposition` supplies the additive
shape-plus-scale split.  This structure additionally records a model-specific
factorization into a Weyl thermal scale and a scale-invariant shape core.
-/
structure ProjectiveWeylGaugeDecomposition
    (counts₁ counts₂ : CountProfile) (support : Finset ℕ) (u : ℝ) where
  /-- Total KL-style readout in the compact projective coordinate. -/
  totalKL : ℝ

  /-- Weyl thermal scale factor. -/
  weylScaleFactor : ℝ

  /-- Scale-invariant spectral/shape core. -/
  shapeCore : ℝ

  /-- Optional scalar/scale KL contribution from the finite shape-scale packet. -/
  scalarCore : ℝ

  /-- Additive finite shape/scale KL packet at `β = u⁻¹`. -/
  shapeScale :
    FiniteShapeScaleKLDecomposition counts₁ counts₂ support (betaInvert u)

  /-- The total readout is the finite unnormalized KL expression. -/
  totalKL_eq_finiteKL :
    totalKL =
      finiteUnnormalizedKLDivergence counts₁ counts₂ support (betaInvert u)

  /-- The supplied shape core agrees with the finite shape packet. -/
  shapeCore_eq_shapeKL :
    shapeCore = shapeScale.shapeKL

  /-- The supplied scalar core agrees with the finite scalar packet. -/
  scalarCore_eq_scalarKL :
    scalarCore = shapeScale.scalarKL

  /--
  Weyl gauge factorization law.

  This is supplied as data; it is not derived here from logarithm-splitting or
  positivity hypotheses.
  -/
  totalKL_eq_weylScale_mul_shapeCore :
    totalKL = weylScaleFactor * shapeCore

namespace ProjectiveWeylGaugeDecomposition

variable {counts₁ counts₂ : CountProfile} {support : Finset ℕ} {u : ℝ}
variable (D : ProjectiveWeylGaugeDecomposition counts₁ counts₂ support u)

/-- Re-export total KL as the finite unnormalized arithmetic KL expression. -/
theorem total_eq_finiteKL :
    D.totalKL =
      finiteUnnormalizedKLDivergence counts₁ counts₂ support (betaInvert u) :=
  D.totalKL_eq_finiteKL

/-- Re-export the additive shape-plus-scale decomposition. -/
theorem finiteKL_eq_shape_plus_scalar :
    finiteUnnormalizedKLDivergence counts₁ counts₂ support (betaInvert u) =
      D.shapeCore + D.scalarCore := by
  have h :=
    D.shapeScale.finiteUnnormalizedKL_eq_shape_plus_scalar
  rw [← D.shapeCore_eq_shapeKL, ← D.scalarCore_eq_scalarKL] at h
  exact h

/-- Re-export the Weyl factorization law. -/
theorem total_eq_weyl_mul_shape :
    D.totalKL = D.weylScaleFactor * D.shapeCore :=
  D.totalKL_eq_weylScale_mul_shapeCore

/-- The finite KL expression equals the supplied Weyl factorization. -/
theorem finiteKL_eq_weyl_mul_shape :
    finiteUnnormalizedKLDivergence counts₁ counts₂ support (betaInvert u) =
      D.weylScaleFactor * D.shapeCore := by
  calc
    finiteUnnormalizedKLDivergence counts₁ counts₂ support (betaInvert u)
        = D.totalKL := by
            rw [D.totalKL_eq_finiteKL]
    _ = D.weylScaleFactor * D.shapeCore :=
            D.total_eq_weyl_mul_shape

end ProjectiveWeylGaugeDecomposition

/-! ## 4. State-space calibration -/

/--
State-space calibration for projective Weyl-gauge KL decompositions.
-/
structure ProjectiveWeylGaugeCalibration
    (State : Type*) where
  /-- Encode a pair of arithmetic count profiles and finite support as a model state. -/
  stateOfProfiles :
    CountProfile → CountProfile → Finset ℕ → State

  /-- Model-specific total KL readout. -/
  totalReadout : State → ℝ → ℝ

  /-- Model-specific Weyl scale readout. -/
  weylScaleReadout : State → ℝ → ℝ

  /-- Model-specific scale-invariant shape-core readout. -/
  shapeCoreReadout : State → ℝ → ℝ

  /-- Supplied Weyl decomposition witness for every finite profile pair. -/
  decompositionOf :
    ∀ counts₁ counts₂ : CountProfile, ∀ support : Finset ℕ, ∀ u : ℝ,
      ProjectiveWeylGaugeDecomposition counts₁ counts₂ support u

  /-- Total readout agrees with the supplied finite decomposition. -/
  total_eq_decomposition :
    ∀ counts₁ counts₂ support u,
      totalReadout (stateOfProfiles counts₁ counts₂ support) u =
        (decompositionOf counts₁ counts₂ support u).totalKL

  /-- Weyl-scale readout agrees with the supplied finite decomposition. -/
  scale_eq_decomposition :
    ∀ counts₁ counts₂ support u,
      weylScaleReadout (stateOfProfiles counts₁ counts₂ support) u =
        (decompositionOf counts₁ counts₂ support u).weylScaleFactor

  /-- Shape-core readout agrees with the supplied finite decomposition. -/
  shape_eq_decomposition :
    ∀ counts₁ counts₂ support u,
      shapeCoreReadout (stateOfProfiles counts₁ counts₂ support) u =
        (decompositionOf counts₁ counts₂ support u).shapeCore

namespace ProjectiveWeylGaugeCalibration

variable {State : Type*}
variable (C : ProjectiveWeylGaugeCalibration State)

/-- Calibrated total readout equals the finite arithmetic KL expression. -/
theorem total_eq_finiteKL
    (counts₁ counts₂ : CountProfile) (support : Finset ℕ) (u : ℝ) :
    C.totalReadout (C.stateOfProfiles counts₁ counts₂ support) u =
      finiteUnnormalizedKLDivergence counts₁ counts₂ support (betaInvert u) := by
  let D := C.decompositionOf counts₁ counts₂ support u
  calc
    C.totalReadout (C.stateOfProfiles counts₁ counts₂ support) u
        = D.totalKL := by
            exact C.total_eq_decomposition counts₁ counts₂ support u
    _ = finiteUnnormalizedKLDivergence counts₁ counts₂ support (betaInvert u) :=
            D.total_eq_finiteKL

/-- Calibrated total readout factors into Weyl scale times shape core. -/
theorem total_eq_scale_mul_shape
    (counts₁ counts₂ : CountProfile) (support : Finset ℕ) (u : ℝ) :
    C.totalReadout (C.stateOfProfiles counts₁ counts₂ support) u =
      C.weylScaleReadout (C.stateOfProfiles counts₁ counts₂ support) u *
        C.shapeCoreReadout (C.stateOfProfiles counts₁ counts₂ support) u := by
  let D := C.decompositionOf counts₁ counts₂ support u
  calc
    C.totalReadout (C.stateOfProfiles counts₁ counts₂ support) u
        = D.totalKL := by
            exact C.total_eq_decomposition counts₁ counts₂ support u
    _ = D.weylScaleFactor * D.shapeCore :=
            D.total_eq_weyl_mul_shape
    _ =
      C.weylScaleReadout (C.stateOfProfiles counts₁ counts₂ support) u *
        C.shapeCoreReadout (C.stateOfProfiles counts₁ counts₂ support) u := by
          rw [C.scale_eq_decomposition counts₁ counts₂ support u,
              C.shape_eq_decomposition counts₁ counts₂ support u]

end ProjectiveWeylGaugeCalibration

end InfoGeometry.Arithmetic.ProjectiveWeylGauge
