/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

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
import InfoGeometry.Topology.KleinBottleOrbitQuotient
import InfoGeometry.Canonical.MasterSplitCayleyDicksonKleinDiracBridge
import InfoGeometry.Superalgebra.SplitOctonionTwistedParityElement

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
open KleinBottleOrbitQuotient
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

/-! ## The lifted glide action on the existing split-octonion parity family -/

open InfoGeometry.Superalgebra.MadelungNonassociativeVortex
open InfoGeometry.Superalgebra.WittenMoebiusParity

/-- The existing Witten--Möbius parity family evaluated along the actual
universal-cover coordinate used by the Klein glide. -/
def glideParityReadout (u v : ColorVec3 ℝ) (k : Cover) : SplitOctonion ℝ :=
  parityElement (Real.cos k.1) (Real.sin k.1) u v

/-- The affine Klein glide acts on this readout by the central sign of the
split-octonion carrier. -/
theorem glideParityReadout_antipodal (u v : ColorVec3 ℝ) (k : Cover) :
    glideParityReadout u v (glide k) =
      SplitOctonion.scale (-1) (glideParityReadout u v k) := by
  simpa [glideParityReadout, glide] using
    parityElement_antiperiodic k.1 u v

/-- The projective class of the parity readout is invariant under the actual
affine Klein glide. -/
def glideParityReadoutProjective (u v : ColorVec3 ℝ) (k : Cover) :
    Quotient parityProjectiveSetoid :=
  Quotient.mk' (s := parityProjectiveSetoid) (glideParityReadout u v k)

theorem glideParityReadoutProjective_invariant (u v : ColorVec3 ℝ)
    (k : Cover) :
    glideParityReadoutProjective u v (glide k) =
      glideParityReadoutProjective u v k := by
  simpa [glideParityReadoutProjective, glideParityReadout, glide] using
    parityElement_projective_pi_periodic k.1 u v

/-! ## Descent to the actual torus orbit quotient

The cover-level invariance above can be strengthened to an actual map out of
the orbit quotient. First the projective parity readout is descended through
the `2π` circle coordinate, then its `π`-periodicity makes it invariant under
the torus glide.
-/

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- Projective parity at a real angular coordinate. -/
private def projectiveParityAngle (u v : ColorVec3 ℝ) (θ : ℝ) :
    Quotient parityProjectiveSetoid :=
  Quotient.mk' (s := parityProjectiveSetoid)
    (parityElement (Real.cos θ) (Real.sin θ) u v)

/-- The projective parity angle has period `π`, using the sign identification
already defining `parityProjectiveSetoid`. -/
private theorem projectiveParityAngle_add_pi (u v : ColorVec3 ℝ) (θ : ℝ) :
    projectiveParityAngle u v (θ + Real.pi) = projectiveParityAngle u v θ := by
  exact parityElement_projective_pi_periodic θ u v

/-- The parity angle descends from the real line to the momentum circle. -/
noncomputable def projectiveParityOnMomentumCircle (u v : ColorVec3 ℝ)
    (θ : MomentumCircle) : Quotient parityProjectiveSetoid :=
  AddCircle.liftIco (2 * Real.pi) 0 (projectiveParityAngle u v) θ

private theorem projectiveParityOnMomentumCircle_coe
    (u v : ColorVec3 ℝ) {θ : ℝ}
    (hθ : θ ∈ Set.Ico (0 : ℝ) (2 * Real.pi)) :
    projectiveParityOnMomentumCircle u v θ = projectiveParityAngle u v θ := by
  exact AddCircle.liftIco_zero_coe_apply hθ

/-- Readback of the circle descent at every real lift. Periodicity of sine
and cosine by integer multiples of `2π` makes this independent of the chosen
representative in `[0, 2π)`. -/
theorem projectiveParityOnMomentumCircle_coe_any
    (u v : ColorVec3 ℝ) (θ : ℝ) :
    projectiveParityOnMomentumCircle u v θ = projectiveParityAngle u v θ := by
  let r : ℝ := (AddCircle.equivIco (2 * Real.pi) 0
    (θ : MomentumCircle)).1
  have hr : r ∈ Set.Ico (0 : ℝ) (2 * Real.pi) := by
    simpa [r] using
      (AddCircle.equivIco (2 * Real.pi) 0
        (θ : MomentumCircle)).2
  have hrθ : (r : MomentumCircle) = (θ : MomentumCircle) :=
    AddCircle.coe_equivIco
  have hperiodic : ((θ - r : ℝ) : MomentumCircle) = 0 := by
    rw [AddCircle.coe_sub, ← hrθ]
    simp
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (p := 2 * Real.pi)).mp hperiodic
  have hn' : (n : ℝ) * (2 * Real.pi) = θ - r := by
    simpa only [zsmul_eq_mul] using hn
  have hθ : θ = r + n * (2 * Real.pi) := by
    linarith
  rw [← hrθ, projectiveParityOnMomentumCircle_coe u v hr]
  change projectiveParityAngle u v r = projectiveParityAngle u v θ
  rw [hθ]
  unfold projectiveParityAngle
  rw [Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

/-- Adding the half-period leaves the circle-valued projective readout
unchanged. The proof compares canonical representatives in `[0, 2π)` and
uses the actual `π`-periodicity of the projective parity class. -/
theorem projectiveParityOnMomentumCircle_add_pi (u v : ColorVec3 ℝ)
    (θ : MomentumCircle) :
    projectiveParityOnMomentumCircle u v (θ + (Real.pi : MomentumCircle)) =
      projectiveParityOnMomentumCircle u v θ := by
  let r : ℝ := (AddCircle.equivIco (2 * Real.pi) 0 θ).1
  let s : ℝ := (AddCircle.equivIco (2 * Real.pi) 0
    (θ + (Real.pi : MomentumCircle))).1
  have hr : r ∈ Set.Ico (0 : ℝ) (2 * Real.pi) := by
    simpa [r] using (AddCircle.equivIco (2 * Real.pi) 0 θ).2
  have hs : s ∈ Set.Ico (0 : ℝ) (2 * Real.pi) := by
    simpa [s] using
      (AddCircle.equivIco (2 * Real.pi) 0
        (θ + (Real.pi : MomentumCircle))).2
  have hrθ : (r : MomentumCircle) = θ := AddCircle.coe_equivIco
  have hsθ : (s : MomentumCircle) = θ + (Real.pi : MomentumCircle) :=
    AddCircle.coe_equivIco
  have hrs : (s : MomentumCircle) = ((r + Real.pi : ℝ) : MomentumCircle) := by
    calc
      (s : MomentumCircle) = θ + (Real.pi : MomentumCircle) := hsθ
      _ = (r : MomentumCircle) + Real.pi := by rw [← hrθ]
      _ = ((r + Real.pi : ℝ) : MomentumCircle) := by rw [AddCircle.coe_add]
  rw [← hsθ, ← hrθ]
  rw [projectiveParityOnMomentumCircle_coe u v hs,
    projectiveParityOnMomentumCircle_coe u v hr]
  by_cases h : r < Real.pi
  · have ht : r + Real.pi ∈ Set.Ico (0 : ℝ) (2 * Real.pi) := by
      constructor
      · linarith [hr.1, Real.pi_pos]
      · linarith [hr.1, Real.pi_pos]
    have hrs' : s = r + Real.pi := by
      exact (AddCircle.coe_eq_coe_iff_of_mem_Ico
        (p := 2 * Real.pi) (a := (0 : ℝ))
        (by simpa only [zero_add] using hs)
        (by simpa only [zero_add] using ht)).mp hrs
    rw [hrs', projectiveParityAngle_add_pi]
  · have hpi : Real.pi ≤ r := le_of_not_gt h
    let t : ℝ := r - Real.pi
    have ht : t ∈ Set.Ico (0 : ℝ) (2 * Real.pi) := by
      constructor
      · dsimp [t]
        linarith [hpi]
      · dsimp [t]
        linarith [hr.2, Real.pi_pos]
    have hshift : t + 2 * Real.pi = r + Real.pi := by
      dsimp [t]
      ring
    have hrt : (r + Real.pi : ℝ) = t + 2 * Real.pi := hshift.symm
    have hrs' : s = t := by
      apply (AddCircle.coe_eq_coe_iff_of_mem_Ico
        (p := 2 * Real.pi) (a := (0 : ℝ))
        (by simpa only [zero_add] using hs)
        (by simpa only [zero_add] using ht)).mp
      calc
        (s : MomentumCircle) = ((r + Real.pi : ℝ) : MomentumCircle) := hrs
        _ = ((t + 2 * Real.pi : ℝ) : MomentumCircle) := by rw [hrt]
        _ = (t : MomentumCircle) := AddCircle.coe_add_period (2 * Real.pi) t
    rw [hrs']
    have htpi : t + Real.pi = r := by
      dsimp [t]
      ring
    rw [← htpi]
    exact (projectiveParityAngle_add_pi u v t).symm

/-- The parity class on the torus is invariant under its Klein glide. -/
def projectiveParityOnTorus (u v : ColorVec3 ℝ) (k : BrillouinTorus) :
    Quotient parityProjectiveSetoid :=
  projectiveParityOnMomentumCircle u v k.1

theorem projectiveParityOnTorus_glide (u v : ColorVec3 ℝ)
    (k : BrillouinTorus) :
    projectiveParityOnTorus u v (torusGlide k) =
      projectiveParityOnTorus u v k := by
  exact projectiveParityOnMomentumCircle_add_pi u v k.1

/-- The projective parity readout descends to the literal Klein orbit
quotient. This is a map on the quotient carrier itself, not only a
glide-invariance statement on the universal cover. -/
def descendedProjectiveParity (u v : ColorVec3 ℝ) :
    KleinBrillouinQuotient → Quotient parityProjectiveSetoid :=
  Quotient.lift (s := glideSetoid) (projectiveParityOnTorus u v)
    (by
      intro x y hxy
      rcases hxy with hxy | hxy
      · simpa [hxy]
      · rw [hxy]
        exact (projectiveParityOnTorus_glide u v x).symm)

/-- The quotient-valued map reads back to the original projective parity
family on the universal cover after the cover-to-torus projection. -/
theorem descendedProjectiveParity_cover_readout
    (u v : ColorVec3 ℝ) (k : Cover) :
    descendedProjectiveParity u v (quotientMap (coverToTorus k)) =
      glideParityReadoutProjective u v k := by
  change projectiveParityOnMomentumCircle u v (k.1 : MomentumCircle) = _
  exact projectiveParityOnMomentumCircle_coe_any u v k.1

end InfoGeometry.Topology.KleinBottleTangentHolonomy
end noncomputable section
