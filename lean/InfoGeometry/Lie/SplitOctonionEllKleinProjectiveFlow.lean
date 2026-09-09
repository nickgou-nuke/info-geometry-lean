import InfoGeometry.Lie.SplitOctonionEllKleinFlow
import InfoGeometry.Lie.SplitOctonionAxialKleinProjective

/-!
# Projective readout of the closed `ell` flow

The active-sector linear flow descends through Mathlib's projectivization and
preserves the transported Klein null predicate.  This is a projective
quadratic-isometry statement; it makes no multiplication-preservation or
exceptional-group claim.
-/

noncomputable section

open scoped LinearAlgebra.Projectivization

namespace InfoGeometry.Lie.SplitOctonionEllKleinProjectiveFlow

open InfoGeometry.Canonical.FierzKleinFoundation
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Lie.SplitOctonionAxialKleinBridge
open InfoGeometry.Lie.SplitOctonionAxialKleinProjective
open InfoGeometry.Lie.SplitOctonionEllClosedFlow
open InfoGeometry.Lie.SplitOctonionEllKleinFlow
open InfoGeometry.Projective.ExteriorKleinProjective
open InfoGeometry.Projective.ExteriorPowerPluckerBridge

abbrev ActiveProjective := ℙ ℝ ActiveSector

def ellFlowActiveProjectiveMap (t : ℝ) :
    ActiveProjective → ActiveProjective :=
  Projectivization.map (ellFlowActive t).toLinearMap
    (ellFlowActive t).injective

private theorem ellFlowActive_ne_zero (t : ℝ) (X : ActiveSector)
    (hX : X ≠ 0) : ellFlowActive t X ≠ 0 := by
  intro h
  apply hX
  apply (ellFlowActive t).injective
  rw [(ellFlowActive t).map_zero]
  exact h

@[simp] theorem ellFlowActiveProjectiveMap_mk (t : ℝ)
    (X : ActiveSector) (hX : X ≠ 0) :
    ellFlowActiveProjectiveMap t (Projectivization.mk ℝ X hX) =
      Projectivization.mk ℝ (ellFlowActive t X)
        (ellFlowActive_ne_zero t X hX) := by
  exact Projectivization.map_mk _ _ _ _

private theorem ellFlowActive_neg_apply (t : ℝ) (X : ActiveSector) :
    ellFlowActive (-t) (ellFlowActive t X) = X := by
  apply Subtype.ext
  have h := congrArg (fun F : Module.End ℝ CanonicalZorn => F X.1)
    (ellFlowPhi_neg_mul t)
  simpa [ellFlowActive, Module.End.mul_apply] using h

private theorem ellFlowActive_apply_neg (t : ℝ) (X : ActiveSector) :
    ellFlowActive t (ellFlowActive (-t) X) = X := by
  apply Subtype.ext
  have h := congrArg (fun F : Module.End ℝ CanonicalZorn => F X.1)
    (ellFlowPhi_mul_neg t)
  simpa [ellFlowActive, Module.End.mul_apply] using h

/-- The projectivized closed flow is a genuine projective equivalence, with
parameter reversal providing its inverse. -/
def ellFlowActiveProjectiveEquiv (t : ℝ) :
    ActiveProjective ≃ ActiveProjective where
  toFun := ellFlowActiveProjectiveMap t
  invFun := ellFlowActiveProjectiveMap (-t)
  left_inv p := by
    refine Projectivization.ind (p := p) ?_
    intro X hX
    simp only [ellFlowActiveProjectiveMap, Projectivization.map_mk]
    congr 1
    exact ellFlowActive_neg_apply t X
  right_inv p := by
    refine Projectivization.ind (p := p) ?_
    intro X hX
    simp only [ellFlowActiveProjectiveMap, Projectivization.map_mk]
    congr 1
    exact ellFlowActive_apply_neg t X

theorem ellFlowActiveProjectiveMap_preserves_Klein_null
    (t : ℝ) (p : ActiveProjective) :
    IsKlein
        (activeExteriorProjectiveMap (ellFlowActiveProjectiveMap t p)) ↔
      IsKlein (activeExteriorProjectiveMap p) := by
  refine Projectivization.ind (p := p) ?_
  intro X hX
  rw [ellFlowActiveProjectiveMap, activeExteriorProjectiveMap,
    Projectivization.map_mk]
  change IsKlein (Projectivization.mk ℝ
      (activeExteriorLinearEquiv (ellFlowActive t X)) _) ↔
    IsKlein (Projectivization.mk ℝ
      (activeExteriorLinearEquiv X) _)
  rw [isKlein_mk_iff, isKlein_mk_iff]
  exact ellFlowActive_kleinForm_eq_zero_iff t X

theorem ellFlowActiveProjectiveMap_add (s t : ℝ)
    (p : ActiveProjective) :
    ellFlowActiveProjectiveMap (s + t) p =
      ellFlowActiveProjectiveMap s (ellFlowActiveProjectiveMap t p) := by
  refine Projectivization.ind (p := p) ?_
  intro X hX
  simp only [ellFlowActiveProjectiveMap_mk]
  congr 1
  apply Subtype.ext
  have h := congrArg (fun F : Module.End ℝ CanonicalZorn => F X.1)
    (ellFlowPhi_add s t)
  simpa [ellFlowActive, Module.End.mul_apply] using h

theorem ellFlowActiveProjectiveEquiv_add_apply (s t : ℝ)
    (p : ActiveProjective) :
    ellFlowActiveProjectiveEquiv (s + t) p =
      ellFlowActiveProjectiveEquiv s
        (ellFlowActiveProjectiveEquiv t p) := by
  change ellFlowActiveProjectiveMap (s + t) p =
    ellFlowActiveProjectiveMap s (ellFlowActiveProjectiveMap t p)
  exact ellFlowActiveProjectiveMap_add s t p

@[simp] theorem ellFlowActiveProjectiveEquiv_apply (t : ℝ)
    (p : ActiveProjective) :
    ellFlowActiveProjectiveEquiv t p = ellFlowActiveProjectiveMap t p :=
  rfl

@[simp] theorem ellFlowActiveProjectiveEquiv_symm_apply (t : ℝ)
    (p : ActiveProjective) :
    (ellFlowActiveProjectiveEquiv t).symm p =
      ellFlowActiveProjectiveMap (-t) p :=
  rfl

end InfoGeometry.Lie.SplitOctonionEllKleinProjectiveFlow
