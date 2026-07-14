import InfoGeometry.Canonical.CanonicalZornSpinVectorAction

/-!
# Real-locus Spin triality and affine projective closure

The repository contains both a real Clifford spin group for the diagonal
quadratic form of signature `(4,4)` and a complex spin group acting on the
canonical Zorn vector carrier. A base-change identification between those
two group objects has not yet been constructed. This file therefore packages
the precise internal real form that is already available: the subgroup of the
complex spin group whose vector action preserves the embedded real split locus
in both directions.

This bidirectional condition is stable under multiplication and inversion. It
produces a total real vector action and removes the hypothesis from the affine
conformal projective closure theorem.
-/

noncomputable section

namespace CanonicalZornRealSpinTrialityClosure

open CanonicalZornCompositionTriality
open CanonicalZornCliffordRepresentation
open CanonicalZornSpinRelatedFiber
open CanonicalZornSpinVectorAction
open CanonicalZornOuterTrialityGroup
open CanonicalZornRealSpin44
open CanonicalZornFiveGradedClosure
open ProjectiveAffineConformalClosure55

/-- A complex spin element preserves the chosen real split locus both forward
and backward. The backward clause makes the locus restriction a group
condition rather than merely a forward-invariant monoid condition. -/
def PreservesRealSplitLocus (g : ComplexSpin44) : Prop :=
  (∀ x : RealSplit44, ∃ y : RealSplit44,
    spinVectorLinear g (realSplit44ToVector8 x) =
      realSplit44ToVector8 y) ∧
  (∀ x : RealSplit44, ∃ y : RealSplit44,
    spinVectorLinear g⁻¹ (realSplit44ToVector8 x) =
      realSplit44ToVector8 y)

theorem preservesRealSplitLocus_one :
    PreservesRealSplitLocus 1 := by
  constructor <;> intro x <;> refine ⟨x, ?_⟩
  · rw [spinVectorLinear_one]
    rfl
  · rw [inv_one, spinVectorLinear_one]
    rfl

theorem preservesRealSplitLocus_mul
    {g h : ComplexSpin44}
    (hg : PreservesRealSplitLocus g)
    (hh : PreservesRealSplitLocus h) :
    PreservesRealSplitLocus (g * h) := by
  constructor
  · intro x
    obtain ⟨y, hy⟩ := hh.1 x
    obtain ⟨z, hz⟩ := hg.1 y
    refine ⟨z, ?_⟩
    rw [spinVectorLinear_mul]
    change spinVectorLinear g
      (spinVectorLinear h (realSplit44ToVector8 x)) = _
    rw [hy, hz]
  · intro x
    obtain ⟨y, hy⟩ := hg.2 x
    obtain ⟨z, hz⟩ := hh.2 y
    refine ⟨z, ?_⟩
    rw [mul_inv_rev, spinVectorLinear_mul]
    change spinVectorLinear h⁻¹
      (spinVectorLinear g⁻¹ (realSplit44ToVector8 x)) = _
    rw [hy, hz]

theorem preservesRealSplitLocus_inv
    {g : ComplexSpin44}
    (hg : PreservesRealSplitLocus g) :
    PreservesRealSplitLocus g⁻¹ := by
  constructor
  · exact hg.2
  · intro x
    obtain ⟨y, hy⟩ := hg.1 x
    refine ⟨y, ?_⟩
    simpa only [inv_inv] using hy

/-- The real-locus-preserving subgroup of the canonical complex spin group. -/
def realLocusSpin44 : Subgroup ComplexSpin44 where
  carrier := {g | PreservesRealSplitLocus g}
  one_mem' := preservesRealSplitLocus_one
  mul_mem' hg hh := preservesRealSplitLocus_mul hg hh
  inv_mem' hg := preservesRealSplitLocus_inv hg

/-- Canonical related-triple representation restricted to the real-locus spin
subgroup. -/
def realLocusSpinRelatedRepresentation :
    realLocusSpin44 →* CartanTrialityGroup :=
  complexSpinRelatedRepresentation.comp realLocusSpin44.subtype

/-- The real image point selected from the forward preservation certificate. -/
def realLocusVectorAction
    (g : realLocusSpin44) (x : RealSplit44) : RealSplit44 :=
  Classical.choose (g.2.1 x)

/-- The selected real action agrees exactly with the complex vector action
after embedding into the canonical Zorn carrier. -/
theorem realLocusVectorAction_spec
    (g : realLocusSpin44) (x : RealSplit44) :
    spinVectorLinear g.1 (realSplit44ToVector8 x) =
      realSplit44ToVector8 (realLocusVectorAction g x) :=
  Classical.choose_spec (g.2.1 x)

theorem realLocusVectorAction_one (x : RealSplit44) :
    realLocusVectorAction 1 x = x := by
  apply realSplit44ToVector8_injective
  rw [← realLocusVectorAction_spec]
  change spinVectorLinear (1 : ComplexSpin44)
    (realSplit44ToVector8 x) = realSplit44ToVector8 x
  rw [spinVectorLinear_one]
  rfl

theorem realLocusVectorAction_mul
    (g h : realLocusSpin44) (x : RealSplit44) :
    realLocusVectorAction (g * h) x =
      realLocusVectorAction g (realLocusVectorAction h x) := by
  apply realSplit44ToVector8_injective
  rw [← realLocusVectorAction_spec, ← realLocusVectorAction_spec,
    ← realLocusVectorAction_spec]
  exact LinearMap.congr_fun (spinVectorLinear_mul g.1 h.1)
    (realSplit44ToVector8 x)

/-- The selected real-locus action is genuinely real-linear. -/
def realLocusVectorLinear (g : realLocusSpin44) :
    Module.End ℝ RealSplit44 where
  toFun := realLocusVectorAction g
  map_add' x y := by
    apply realSplit44ToVector8_injective
    rw [← realLocusVectorAction_spec]
    change spinVectorLinear g.1
      (realSplit44ToVector8 (x + y)) =
      realSplit44ToVector8
        (realLocusVectorAction g x + realLocusVectorAction g y)
    rw [map_add]
    rw [(spinVectorLinear g.1).map_add]
    rw [realLocusVectorAction_spec,
      realLocusVectorAction_spec]
    exact (realSplit44ToVector8.map_add _ _).symm
  map_smul' c x := by
    apply realSplit44ToVector8_injective
    rw [← realLocusVectorAction_spec]
    change spinVectorLinear g.1
      (realSplit44ToVector8 (c • x)) =
      realSplit44ToVector8 (c • realLocusVectorAction g x)
    rw [realSplit44ToVector8.map_smul]
    change spinVectorLinear g.1
      ((c : ℂ) • realSplit44ToVector8 x) =
      realSplit44ToVector8 (c • realLocusVectorAction g x)
    rw [map_smul, realLocusVectorAction_spec]
    exact (realSplit44ToVector8.map_smul c _).symm

theorem realLocusVectorLinear_one : realLocusVectorLinear 1 = 1 := by
  apply LinearMap.ext
  exact realLocusVectorAction_one

theorem realLocusVectorLinear_mul (g h : realLocusSpin44) :
    realLocusVectorLinear (g * h) =
      realLocusVectorLinear g * realLocusVectorLinear h := by
  apply LinearMap.ext
  exact realLocusVectorAction_mul g h

/-- Genuine real eight-dimensional representation of the real-locus spin
subgroup. -/
def realLocusSpinVectorRepresentation :
    realLocusSpin44 →* LinearMap.GeneralLinearGroup ℝ RealSplit44 where
  toFun g :=
    { val := realLocusVectorLinear g
      inv := realLocusVectorLinear g⁻¹
      val_inv := by
        rw [← realLocusVectorLinear_mul, mul_inv_cancel,
          realLocusVectorLinear_one]
      inv_val := by
        rw [← realLocusVectorLinear_mul, inv_mul_cancel,
          realLocusVectorLinear_one] }
  map_one' := by
    apply Units.ext
    exact realLocusVectorLinear_one
  map_mul' g h := by
    apply Units.ext
    exact realLocusVectorLinear_mul g h

theorem realLocusSpinVectorRepresentation_spec
    (g : realLocusSpin44) (x : RealSplit44) :
    realSplit44ToVector8
        (((realLocusSpinVectorRepresentation g :
          LinearMap.GeneralLinearGroup ℝ RealSplit44) :
            Module.End ℝ RealSplit44) x) =
      spinVectorLinear g.1 (realSplit44ToVector8 x) := by
  exact (realLocusVectorAction_spec g x).symm

/-- The induced real action preserves the diagonal `(4,4)` quadratic form. -/
theorem realQuadratic44_realLocusVectorAction
    (g : realLocusSpin44) (x : RealSplit44) :
    realQuadratic44 (realLocusVectorAction g x) = realQuadratic44 x := by
  exact relatedTriple_realQuadratic_preserved
    (realLocusSpinRelatedRepresentation g) x
    (realLocusVectorAction g x) (realLocusVectorAction_spec g x)

/-- The affine conformal projective and grade `+1` closure is unconditional
on the real-locus spin subgroup. -/
theorem realLocusSpin_affine_projective_five_grade
    (g : realLocusSpin44) (x : RealSplit44) :
    realQuadratic44 (realLocusVectorAction g x) = realQuadratic44 x ∧
    Q55 (conformalEmbed44to55
      (realSplit44ToPAC44 (realLocusVectorAction g x))) = 0 ∧
    relatedVectorGradePlus (realLocusSpinRelatedRepresentation g)
        (realSplit44ToVector8 x) ∈
      conformalGrade TKKJordanPairData.TKKGrade.p1 := by
  exact relatedTriple_affine_projective_five_grade
    (realLocusSpinRelatedRepresentation g) x
    (realLocusVectorAction g x) (realLocusVectorAction_spec g x)

/-- Real-form capstone joining the related triple, order-three outer triality,
the three five-grade lanes, and the affine conformal projective null lift. -/
theorem realLocusSpin_outer_triality_projective_closure
    (g : realLocusSpin44) (x : RealSplit44)
    (S : SpinorPlus8) (C : SpinorMinus8) :
    cartanTrialityOuterEquiv
        (cartanTrialityOuterEquiv
          (cartanTrialityOuterEquiv
            (realLocusSpinRelatedRepresentation g))) =
      realLocusSpinRelatedRepresentation g ∧
    relatedVectorGradePlus (realLocusSpinRelatedRepresentation g)
        (realSplit44ToVector8 x) ∈
      conformalGrade TKKJordanPairData.TKKGrade.p1 ∧
    relatedSpinorGradePlus (realLocusSpinRelatedRepresentation g) S ∈
      conformalGrade TKKJordanPairData.TKKGrade.p1 ∧
    relatedSpinorGradeMinus (realLocusSpinRelatedRepresentation g) C ∈
      conformalGrade TKKJordanPairData.TKKGrade.m1 ∧
    realQuadratic44 (realLocusVectorAction g x) = realQuadratic44 x ∧
    Q55 (conformalEmbed44to55
      (realSplit44ToPAC44 (realLocusVectorAction g x))) = 0 := by
  exact outer_triality_five_grade_projective_closure
    (realLocusSpinRelatedRepresentation g) x
    (realLocusVectorAction g x) (realLocusVectorAction_spec g x) S C

end CanonicalZornRealSpinTrialityClosure

end noncomputable section
