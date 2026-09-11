import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.LLM.TransformerArchitecture
import InfoGeometry.MassSpectrometry.GPUExecutionContracts

/-!
# Mellin mass encoding as a Transformer rotary layer

This module connects the mass-spectrometry Mellin/Givens primitive directly to
the repository-owned `InfoGeometry.LLM.RotaryPositionalLayer` interface.

The position is a dimensionless relative-mass phase datum.  The same exact 2D
rotation is applied to query and key lanes.  The bridge proves common-scale
invariance and quadratic-norm preservation; it does not make claims about
training stability, gradients, or empirical attention quality.
-/

noncomputable section

namespace InfoGeometry.MassSpectrometry

open InfoGeometry.LLM

/-- Relative-mass position used by the Mellin rotary adapter. -/
structure MellinRotaryPosition where
  omega : ℝ
  mass : ℝ
  referenceMass : ℝ

namespace MellinRotaryPosition

/-- Phase angle `ω log(m/m₀)` associated with a Mellin position. -/
def angle (p : MellinRotaryPosition) : ℝ :=
  mellinAngle p.omega p.mass p.referenceMass

/-- Common nonzero mass scaling does not change the relative Mellin phase. -/
theorem angle_common_scale (p : MellinRotaryPosition) {scale : ℝ}
    (hscale : scale ≠ 0) (hm₀ : p.referenceMass ≠ 0) :
    (MellinRotaryPosition.mk p.omega (scale * p.mass) (scale * p.referenceMass)).angle =
      p.angle := by
  exact mellinAngle_common_scale hscale hm₀

end MellinRotaryPosition

/-- Repository-native Transformer RoPE interface instantiated by the exact
Mellin/Givens pair rotation. -/
def mellinRotaryLayer :
    RotaryPositionalLayer MellinRotaryPosition (ℝ × ℝ) where
  rotateQ p q := givensRotate p.angle q
  rotateK p k := givensRotate p.angle k

@[simp] theorem mellinRotaryLayer_rotateQ
    (p : MellinRotaryPosition) (q : ℝ × ℝ) :
    mellinRotaryLayer.rotateQ p q = givensRotate p.angle q :=
  rfl

@[simp] theorem mellinRotaryLayer_rotateK
    (p : MellinRotaryPosition) (k : ℝ × ℝ) :
    mellinRotaryLayer.rotateK p k = givensRotate p.angle k :=
  rfl

/-- Query-lane Mellin rotation preserves squared Euclidean norm. -/
theorem mellinRotaryLayer_query_normSq
    (p : MellinRotaryPosition) (q : ℝ × ℝ) :
    pairNormSq (mellinRotaryLayer.rotateQ p q) = pairNormSq q := by
  exact pairNormSq_givensRotate p.angle q

/-- Key-lane Mellin rotation preserves squared Euclidean norm. -/
theorem mellinRotaryLayer_key_normSq
    (p : MellinRotaryPosition) (k : ℝ × ℝ) :
    pairNormSq (mellinRotaryLayer.rotateK p k) = pairNormSq k := by
  exact pairNormSq_givensRotate p.angle k

/-- Common nonzero calibration scaling leaves the query rotation unchanged. -/
theorem mellinRotaryLayer_query_common_scale
    (p : MellinRotaryPosition) {scale : ℝ}
    (hscale : scale ≠ 0) (hm₀ : p.referenceMass ≠ 0) (q : ℝ × ℝ) :
    mellinRotaryLayer.rotateQ
        ⟨p.omega, scale * p.mass, scale * p.referenceMass⟩ q =
      mellinRotaryLayer.rotateQ p q := by
  simp only [mellinRotaryLayer_rotateQ]
  rw [MellinRotaryPosition.angle_common_scale p hscale hm₀]

/-- Common nonzero calibration scaling leaves the key rotation unchanged. -/
theorem mellinRotaryLayer_key_common_scale
    (p : MellinRotaryPosition) {scale : ℝ}
    (hscale : scale ≠ 0) (hm₀ : p.referenceMass ≠ 0) (k : ℝ × ℝ) :
    mellinRotaryLayer.rotateK
        ⟨p.omega, scale * p.mass, scale * p.referenceMass⟩ k =
      mellinRotaryLayer.rotateK p k := by
  simp only [mellinRotaryLayer_rotateK]
  rw [MellinRotaryPosition.angle_common_scale p hscale hm₀]

/-- The repository-owned query/key pair operation specializes to the two exact
Mellin rotations. -/
theorem mellin_rotatePair_eq
    (p : MellinRotaryPosition) (q k : ℝ × ℝ) :
    mellinRotaryLayer.rotatePair p q k =
      (givensRotate p.angle q, givensRotate p.angle k) := by
  rfl

end InfoGeometry.MassSpectrometry
