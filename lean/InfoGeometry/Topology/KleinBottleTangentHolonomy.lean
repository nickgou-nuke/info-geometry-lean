import InfoGeometry.Topology.KleinBrillouinBase
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Matrix.Basic
import InfoGeometry.Topology.KleinBottleExteriorOrientationBridge
import InfoGeometry.Canonical.MasterSplitCayleyDicksonKleinDiracBridge

/-!
# Genuine Tangent Holonomy of the Klein Bottle

This module replaces the standalone "toy" affine wrapper with a fully integrated
differential topology theorem directly asserting over `KleinBrillouinBase.glide`.

We prove that the canonical affine cover map `glide` for the Klein bottle
orbit quotient is smooth (`ContDiff`), formally compute its exact Fréchet
derivative, and compute the induced action on the top exterior generator.
This establishes orientation reversal on the covering tangent space without
asserting a smooth quotient-manifold structure.
-/

open KleinBrillouinBase
open InfoGeometry.Topology.KleinBottleExteriorOrientationBridge
open InfoGeometry.Canonical.MasterSplitCayleyDicksonKleinDirac

noncomputable section
namespace InfoGeometry.Topology.KleinBottleTangentHolonomy

/-- The continuous linear part of the genuine affine glide map. -/
def glideLinearPart : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  ContinuousLinearMap.prod (ContinuousLinearMap.fst ℝ ℝ ℝ) (-ContinuousLinearMap.snd ℝ ℝ ℝ)

/-- The genuine affine glide map is smooth on the universal cover. -/
theorem contDiff_glide : ContDiff ℝ ⊤ glide := by
  unfold glide
  fun_prop

/-- The Fréchet derivative of the affine glide map is exactly `glideLinearPart`. -/
theorem hasFDerivAt_glide (k : Cover) :
    HasFDerivAt glide glideLinearPart k := by
  unfold glide glideLinearPart
  fun_prop

/-- Extracted `fderiv` identity for the universal cover map. -/
theorem fderiv_glide (k : Cover) :
    fderiv ℝ glide k = glideLinearPart :=
  (hasFDerivAt_glide k).fderiv

/-- Canonical linear equivalence between `Fin 2 → ℝ` and `ℝ × ℝ`. -/
def finTwoProdEquiv : (Fin 2 → ℝ) ≃ₗ[ℝ] (ℝ × ℝ) where
  toFun f := (f 0, f 1)
  invFun p := fun i => if i = 0 then p.1 else p.2
  left_inv f := by ext i; fin_cases i <;> simp
  right_inv p := by ext <;> simp
  map_add' f g := by simp
  map_smul' c f := by simp

/-- The geometric Fréchet derivative is represented by the canonical Klein
reflection matrix from the algebraic master bridge. -/
theorem glideLinearPart_equiv_matrix (f : Fin 2 → ℝ) :
    finTwoProdEquiv.symm (glideLinearPart (finTwoProdEquiv f)) =
      Matrix.toLin' linearTa f := by
  ext i
  fin_cases i
  · simp [finTwoProdEquiv, glideLinearPart, Matrix.toLin'_apply, linearTa,
      Matrix.mulVec, dotProduct]
  · simp [finTwoProdEquiv, glideLinearPart, Matrix.toLin'_apply, linearTa,
      Matrix.mulVec, dotProduct]

/-- The derivative acts involutively on tangent vectors, even though the
affine glide itself squares to a nontrivial translation. -/
theorem glideLinearPart_involutive (v : ℝ × ℝ) :
    glideLinearPart (glideLinearPart v) = v := by
  ext <;> simp [glideLinearPart]

/-- The action induced by the derivative on the exterior algebra of the
covering tangent space. -/
def glideTangentExterior : ExteriorAlgebra ℝ (ℝ × ℝ) →ₐ[ℝ]
    ExteriorAlgebra ℝ (ℝ × ℝ) :=
  ExteriorAlgebra.map glideLinearPart.toLinearMap

@[simp] theorem glideTangentExterior_generator (v : ℝ × ℝ) :
    glideTangentExterior (ExteriorAlgebra.ι ℝ v) =
      ExteriorAlgebra.ι ℝ (glideLinearPart v) := by
  exact ExteriorAlgebra.map_apply_ι glideLinearPart.toLinearMap v

/-- The derivative-induced exterior action squares to the identity. -/
theorem glideTangentExterior_involutive :
    AlgHom.comp glideTangentExterior glideTangentExterior =
      AlgHom.id ℝ (ExteriorAlgebra ℝ (ℝ × ℝ)) := by
  change AlgHom.comp (ExteriorAlgebra.map glideLinearPart.toLinearMap)
      (ExteriorAlgebra.map glideLinearPart.toLinearMap) = _
  rw [ExteriorAlgebra.map_comp_map]
  have hlinear :
      glideLinearPart.toLinearMap.comp glideLinearPart.toLinearMap =
        LinearMap.id := by
    apply LinearMap.ext
    intro v
    exact glideLinearPart_involutive v
  rw [hlinear, ExteriorAlgebra.map_id]

/-- The derivative of the affine glide acts by `-1` on the top exterior
generator of the covering tangent plane. -/
theorem glideTangentExterior_topForm :
    glideTangentExterior
        (ExteriorAlgebra.ι ℝ (1, 0) * ExteriorAlgebra.ι ℝ (0, 1)) =
      -(ExteriorAlgebra.ι ℝ (1, 0) * ExteriorAlgebra.ι ℝ (0, 1)) := by
  rw [map_mul, glideTangentExterior_generator, glideTangentExterior_generator]
  have h₁ : glideLinearPart (1, 0) = (1, 0) := by
    ext <;> simp [glideLinearPart]
  have h₂ : glideLinearPart (0, 1) = (0, -1) := by
    ext <;> simp [glideLinearPart]
  rw [h₁, h₂]
  rw [show ((0 : ℝ), (-1 : ℝ)) = -((0 : ℝ), (1 : ℝ)) by ext <;> norm_num,
    map_neg, mul_neg]

/-- Exchanging the two covering coordinates identifies the reciprocal-space
orientation action with the exterior-orientation bridge's deck linear map.
The two named glide conventions therefore have conjugate tangent actions. -/
def swapCoordinates (f : Fin 2 → ℝ) : Fin 2 → ℝ := fun i =>
  if i = 0 then f 1 else f 0

theorem glideTangent_conjugate_exterior (f : Fin 2 → ℝ) :
    swapCoordinates (finTwoProdEquiv.symm
      (glideLinearPart (finTwoProdEquiv f))) = glideLinear (swapCoordinates f) := by
  rw [glideLinearPart_equiv_matrix]
  ext i
  fin_cases i <;>
    simp [swapCoordinates, linearTa, Matrix.toLin'_apply, Matrix.mulVec,
      dotProduct, glideLinear,
      InfoGeometry.Topology.KleinQuotientDeckInvariants.deckB_diff,
      Matrix.mulVecLin]

end InfoGeometry.Topology.KleinBottleTangentHolonomy
end noncomputable section
