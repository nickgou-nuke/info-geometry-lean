/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Convex.FenchelConjugate
import InfoGeometry.Geometry.LegendreDuality
import InfoGeometry.Twistor.RealDualTwistor
import Mathlib.Analysis.Convex.Deriv

/-!
# Fenchel contact as homogeneous incidence and a native operator defect

An epigraph point `(x, f x, 1)` and the covector
`(y, t, s) ↦ p y - t - fStar p * s` have pairing equal to minus the existing
Fenchel gap. Both homogeneous factors are nonzero without any assumption on
`x` or `p`. The existing real-dual-twistor dyad therefore has square zero
exactly at Fenchel--Young equality, with its full square equal to minus the
gap times the operator.

The final homogeneous coordinate also supplies a canonical rank-one
projector. At contact the dyad lies in its upper Peirce corner. This supplies
an explicit algebraic input for the existing Peirce superderivation laws.

The algebraic statements allow arbitrary `fStar`; they do not assume it is
a conjugate. The actual real-valued Fenchel conjugate needs boundedness for
the support inequality. At an actual derivative of a globally convex
function, first-order support derives both boundedness and attainment.
The general inequality gives weak separation of the epigraph; contact
additionally requires equality.
These are native real module/endomorphism statements, without a claim of
quantization or of a graded manifold.
-/

noncomputable section

namespace InfoGeometry.Twistor.FenchelContactIncidence

open InfoGeometry.Twistor.RealDualTwistor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The epigraph boundary point in homogeneous coordinates. -/
def homogeneousPoint (f : E → ℝ) (x : E) : E × (ℝ × ℝ) :=
  (x, f x, 1)

/-- The covector of the affine hyperplane `t = p y - c`. -/
def hyperplaneCovector (p : E →L[ℝ] ℝ) (c : ℝ) :
    Module.Dual ℝ (E × (ℝ × ℝ)) where
  toFun z := p z.1 - z.2.1 - c * z.2.2
  map_add' z w := by
    change p (z.1 + w.1) - (z.2.1 + w.2.1) - c * (z.2.2 + w.2.2) =
      (p z.1 - z.2.1 - c * z.2.2) + (p w.1 - w.2.1 - c * w.2.2)
    rw [map_add]
    ring
  map_smul' a z := by
    change p (a • z.1) - a * z.2.1 - c * (a * z.2.2) =
      a * (p z.1 - z.2.1 - c * z.2.2)
    simp only [map_smul, smul_eq_mul]
    ring

@[simp] theorem hyperplaneCovector_apply (p : E →L[ℝ] ℝ) (c : ℝ)
    (z : E × (ℝ × ℝ)) :
    hyperplaneCovector p c z = p z.1 - z.2.1 - c * z.2.2 := rfl

omit [NormedSpace ℝ E] in
theorem homogeneousPoint_ne_zero (f : E → ℝ) (x : E) :
    homogeneousPoint f x ≠ 0 := by
  intro h
  have hlast := congrArg (fun z : E × (ℝ × ℝ) => z.2.2) h
  norm_num [homogeneousPoint] at hlast

theorem hyperplaneCovector_ne_zero (p : E →L[ℝ] ℝ) (c : ℝ) :
    hyperplaneCovector p c ≠ 0 := by
  intro h
  have hheight := LinearMap.congr_fun h (0, 1, 0)
  norm_num [hyperplaneCovector] at hheight

/-- The actual point/covector pair, retaining the affine intercept. -/
def contactPair (f : E → ℝ) (fStar : (E →L[ℝ] ℝ) → ℝ)
    (x : E) (p : E →L[ℝ] ℝ) : Carrier (E × (ℝ × ℝ)) :=
  (homogeneousPoint f x, hyperplaneCovector p (fStar p))

/-- The final homogeneous coordinate, as a native real covector. -/
def homogeneousCoordinate : Module.Dual ℝ (E × (ℝ × ℝ)) :=
  (LinearMap.snd ℝ ℝ ℝ).comp (LinearMap.snd ℝ E (ℝ × ℝ))

/-- Projection onto the homogeneous point using its final coordinate `1`. -/
def contactProjector (f : E → ℝ) (x : E) : Module.End ℝ (E × (ℝ × ℝ)) :=
  dyad (homogeneousPoint f x, homogeneousCoordinate)

theorem contactProjector_sq (f : E → ℝ) (x : E) :
    contactProjector f x * contactProjector f x = contactProjector f x := by
  unfold contactProjector
  rw [dyad_sq]
  change (1 : ℝ) • dyad (homogeneousPoint f x, homogeneousCoordinate) = _
  rw [one_smul]

theorem contactProjector_mul_dyad (f : E → ℝ)
    (fStar : (E →L[ℝ] ℝ) → ℝ) (x : E) (p : E →L[ℝ] ℝ) :
    contactProjector f x * dyad (contactPair f fStar x p) =
      dyad (contactPair f fStar x p) := by
  unfold contactProjector
  rw [dyad_mul]
  change (1 : ℝ) • dyad (contactPair f fStar x p) = _
  rw [one_smul]

/-- The existing Fenchel gap is exactly the negative incidence defect. -/
theorem contactPair_eval (f : E → ℝ) (fStar : (E →L[ℝ] ℝ) → ℝ)
    (x : E) (p : E →L[ℝ] ℝ) :
    (contactPair f fStar x p).2 (contactPair f fStar x p).1 =
      -Geometry.fenchelGap f fStar x p := by
  change p x - f x - fStar p * 1 = -(f x + fStar p - p x)
  ring

/-- The reverse projector product retains the same contact defect. -/
theorem dyad_mul_contactProjector (f : E → ℝ)
    (fStar : (E →L[ℝ] ℝ) → ℝ) (x : E) (p : E →L[ℝ] ℝ) :
    dyad (contactPair f fStar x p) * contactProjector f x =
      (-Geometry.fenchelGap f fStar x p) • contactProjector f x := by
  unfold contactProjector
  rw [dyad_mul]
  change ((contactPair f fStar x p).2 (contactPair f fStar x p).1) •
      dyad (homogeneousPoint f x, homogeneousCoordinate) = _
  rw [contactPair_eval]

/-- At contact, the actual dyad is an upper-corner operator for an actual
idempotent, so it is eligible for the existing Peirce grading laws. -/
theorem dyad_contactProjector_corner_of_equality (f : E → ℝ)
    (fStar : (E →L[ℝ] ℝ) → ℝ) (x : E) (p : E →L[ℝ] ℝ)
    (heq : Geometry.FenchelYoungEquality f fStar x p) :
    contactProjector f x * dyad (contactPair f fStar x p) *
        (1 - contactProjector f x) = dyad (contactPair f fStar x p) := by
  have hgap := (Geometry.fenchelYoungEquality_iff_gap_eq_zero f fStar x p).1 heq
  rw [contactProjector_mul_dyad, mul_sub, mul_one, dyad_mul_contactProjector]
  simp [hgap]

theorem incident_contactPair_iff (f : E → ℝ) (fStar : (E →L[ℝ] ℝ) → ℝ)
    (x : E) (p : E →L[ℝ] ℝ) :
    Incident (contactPair f fStar x p) ↔
      Geometry.FenchelYoungEquality f fStar x p := by
  unfold Incident
  rw [contactPair_eval, neg_eq_zero]
  exact (Geometry.fenchelYoungEquality_iff_gap_eq_zero f fStar x p).symm

/-- Homogeneous augmentation excludes the zero-operator degeneracy. -/
theorem dyad_contactPair_ne_zero (f : E → ℝ) (fStar : (E →L[ℝ] ℝ) → ℝ)
    (x : E) (p : E →L[ℝ] ℝ) :
    dyad (contactPair f fStar x p) ≠ 0 :=
  dyad_ne_zero _ (homogeneousPoint_ne_zero f x)
    (hyperplaneCovector_ne_zero p (fStar p))

/-- The exact endomorphism square retains the full Fenchel defect. -/
theorem dyad_contactPair_square (f : E → ℝ) (fStar : (E →L[ℝ] ℝ) → ℝ)
    (x : E) (p : E →L[ℝ] ℝ) :
    dyad (contactPair f fStar x p) * dyad (contactPair f fStar x p) =
      (-Geometry.fenchelGap f fStar x p) • dyad (contactPair f fStar x p) := by
  rw [dyad_sq, contactPair_eval]

/-- Fenchel equality is equivalent to square-zero of a nonzero native dyad. -/
theorem dyad_contactPair_sq_zero_iff (f : E → ℝ)
    (fStar : (E →L[ℝ] ℝ) → ℝ) (x : E) (p : E →L[ℝ] ℝ) :
    dyad (contactPair f fStar x p) * dyad (contactPair f fStar x p) = 0 ↔
      Geometry.FenchelYoungEquality f fStar x p := by
  rw [dyad_sq_zero_iff _ (homogeneousPoint_ne_zero f x)
    (hyperplaneCovector_ne_zero p (fStar p))]
  exact incident_contactPair_iff f fStar x p

/-- The actual real-valued conjugate gives weak epigraph separation when its
support set is bounded above. Contact is the additional equality condition. -/
theorem fenchel_hyperplane_nonpositive (f : E → ℝ) (p : E →L[ℝ] ℝ)
    (hb : BddAbove (Convex.fenchelSet f p)) (y : E) (t : ℝ)
    (ht : f y ≤ t) :
    hyperplaneCovector p (Convex.fenchelConj f p) (y, t, 1) ≤ 0 := by
  change p y - t - Convex.fenchelConj f p * 1 ≤ 0
  have hy := Convex.fenchelYoung f p y hb
  change p y ≤ f y + Convex.fenchelConj f p at hy
  linarith only [ht, hy]

/-- In the bounded real-conjugate regime, square-zero is exact attainment of
the defining supremum at the selected primal point. -/
theorem dyad_fenchel_sq_zero_iff_isGreatest (f : E → ℝ)
    (x : E) (p : E →L[ℝ] ℝ) (hb : BddAbove (Convex.fenchelSet f p)) :
    dyad (contactPair f (Convex.fenchelConj f) x p) *
        dyad (contactPair f (Convex.fenchelConj f) x p) = 0 ↔
      IsGreatest (Convex.fenchelSet f p) (Convex.dualPair p x - f x) := by
  rw [dyad_contactPair_sq_zero_iff]
  have heq : Geometry.FenchelYoungEquality f (Convex.fenchelConj f) x p ↔
      Convex.fenchelConj f p = Convex.dualPair p x - f x := by
    unfold Geometry.FenchelYoungEquality Convex.dualPair
    constructor <;> intro h <;> linarith
  exact heq.trans (Convex.fenchelConj_eq_iff_isGreatest f p x hb)

/-- First-order convex support makes the actual derivative attain the
conjugate. The line-restriction argument follows the existing
`ConvexFunctional.supporting_ineq_of_convex_differentiable` owner, without
requiring a Riesz identification or differentiability away from `x`. -/
theorem fenchelSet_isGreatest_of_hasFDerivAt (f : E → ℝ)
    (x : E) (p : E →L[ℝ] ℝ) (hconv : ConvexOn ℝ Set.univ f)
    (hd : HasFDerivAt f p x) :
    IsGreatest (Convex.fenchelSet f p) (Convex.dualPair p x - f x) := by
  refine ⟨⟨x, rfl⟩, ?_⟩
  rintro r ⟨z, rfl⟩
  have hline := hconv.comp_affineMap (AffineMap.lineMap x z)
  have hderiv :=
    hd.comp_hasDerivAt_of_eq (0 : ℝ)
      (AffineMap.hasDerivAt_lineMap (a := x) (b := z)) (by simp)
  have hslope := hline.le_slope_of_hasDerivAt
    (by simp) (by simp) (zero_lt_one : (0 : ℝ) < 1) hderiv
  have heval : slope (f ∘ ⇑(AffineMap.lineMap x z)) (0 : ℝ) (1 : ℝ) =
      f z - f x := by
    simp [slope_def_field]
  rw [heval] at hslope
  change p (z - x) ≤ f z - f x at hslope
  rw [map_sub] at hslope
  change p z - f z ≤ p x - f x
  linarith

/-- Convexity and an actual derivative produce a square-zero dyad; contact
and boundedness of the conjugate are derived rather than assumed. The dyad
is nonzero by `dyad_contactPair_ne_zero`. -/
theorem dyad_fenchel_sq_zero_of_hasFDerivAt (f : E → ℝ)
    (x : E) (p : E →L[ℝ] ℝ) (hconv : ConvexOn ℝ Set.univ f)
    (hd : HasFDerivAt f p x) :
    dyad (contactPair f (Convex.fenchelConj f) x p) *
        dyad (contactPair f (Convex.fenchelConj f) x p) = 0 := by
  have hG := fenchelSet_isGreatest_of_hasFDerivAt f x p hconv hd
  have hb := Convex.fenchelSet_bddAbove_of_isGreatest f p x hG
  exact (dyad_fenchel_sq_zero_iff_isGreatest f x p hb).2 hG

end InfoGeometry.Twistor.FenchelContactIncidence
