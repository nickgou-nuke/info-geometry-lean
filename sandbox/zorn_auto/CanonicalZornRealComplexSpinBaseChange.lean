import CanonicalZornRealSpinTrialityClosure

/-!
# Scalar extension from the real split Clifford algebra

This file constructs the explicit heterobasic Clifford homomorphism induced by
the real Zorn isometry `realSplit44ToVector8`.  It is the first half of the
comparison between Mathlib's real `Spin(4,4)` object and the real-locus subgroup
inside the canonical complex Zorn spin group.
-/

noncomputable section

namespace CanonicalZornRealComplexSpinBaseChange

set_option synthInstance.maxHeartbeats 100000

open CanonicalZornCompositionTriality
open CanonicalZornCliffordRepresentation
open CanonicalZornRealSpin44
open CanonicalZornSpinRelatedFiber
open CanonicalZornSpinVectorAction
open CanonicalZornRealSpinTrialityClosure
open CanonicalZornOuterTrialityGroup
open CanonicalZornFiveGradedClosure
open ProjectiveAffineConformalClosure55

/-- The real generator map into the complex canonical Clifford algebra. -/
def realToComplexCliffordGenerator :
    RealSplit44 →ₗ[ℝ] CliffordAlgebra vectorQuadratic :=
  (CliffordAlgebra.ι vectorQuadratic).restrictScalars ℝ ∘ₗ
    realSplit44ToVector8

theorem realToComplexCliffordGenerator_sq (x : RealSplit44) :
    realToComplexCliffordGenerator x *
        realToComplexCliffordGenerator x =
      algebraMap ℝ (CliffordAlgebra vectorQuadratic)
        (realQuadratic44 x) := by
  change CliffordAlgebra.ι vectorQuadratic (realSplit44ToVector8 x) *
      CliffordAlgebra.ι vectorQuadratic (realSplit44ToVector8 x) = _
  rw [CliffordAlgebra.ι_sq_scalar,
    vectorQuadratic_realSplit44ToVector8]
  rfl

/-- Universal scalar-extension homomorphism from the real split Clifford
algebra into the complex Zorn Clifford algebra. -/
def realToComplexClifford :
    CliffordAlgebra realQuadratic44 →ₐ[ℝ]
      CliffordAlgebra vectorQuadratic :=
  CliffordAlgebra.lift realQuadratic44
    ⟨realToComplexCliffordGenerator, realToComplexCliffordGenerator_sq⟩

@[simp] theorem realToComplexClifford_ι (x : RealSplit44) :
    realToComplexClifford (CliffordAlgebra.ι realQuadratic44 x) =
      CliffordAlgebra.ι vectorQuadratic (realSplit44ToVector8 x) := by
  exact CliffordAlgebra.lift_ι_apply
    realToComplexCliffordGenerator realToComplexCliffordGenerator_sq x

/-- Scalar extension intertwines the two already-constructed Dirac gamma
representations after forgetting complex linearity. -/
theorem realToComplexClifford_dirac_generator (x : RealSplit44) :
    (zornCliffordRepresentation
      (realToComplexClifford
        (CliffordAlgebra.ι realQuadratic44 x))).restrictScalars ℝ =
      realClifford44Representation
        (CliffordAlgebra.ι realQuadratic44 x) := by
  rw [realToComplexClifford_ι, zornCliffordRepresentation_ι,
    realClifford44Representation_ι]
  rfl

/-- Forgetting complex linearity is an algebra homomorphism on endomorphism
algebras. -/
def restrictComplexEndAlgHom :
    Module.End ℂ DiracSpinor16 →ₐ[ℝ] Module.End ℝ DiracSpinor16 where
  toFun f := f.restrictScalars ℝ
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The complete real Clifford representation is the restriction of the
complex Zorn representation along scalar extension. -/
theorem real_clifford_representation_base_change :
    restrictComplexEndAlgHom.comp
        ((zornCliffordRepresentation.restrictScalars ℝ).comp
          realToComplexClifford) =
      realClifford44Representation := by
  apply CliffordAlgebra.hom_ext
  apply LinearMap.ext
  intro x
  change (zornCliffordRepresentation
      (realToComplexClifford
        (CliffordAlgebra.ι realQuadratic44 x))).restrictScalars ℝ =
    realClifford44Representation
      (CliffordAlgebra.ι realQuadratic44 x)
  exact realToComplexClifford_dirac_generator x

theorem real_clifford_representation_base_change_apply
    (a : CliffordAlgebra realQuadratic44) :
    (zornCliffordRepresentation
      (realToComplexClifford a)).restrictScalars ℝ =
      realClifford44Representation a := by
  exact AlgHom.congr_fun real_clifford_representation_base_change a

/-! ## Compatibility with Clifford involutions and parity -/

theorem realToComplexClifford_involute
    (a : CliffordAlgebra realQuadratic44) :
    realToComplexClifford (CliffordAlgebra.involute a) =
      CliffordAlgebra.involute (realToComplexClifford a) := by
  induction a using CliffordAlgebra.induction with
  | algebraMap r =>
      rw [AlgHom.commutes
          (CliffordAlgebra.involute (Q := realQuadratic44)),
        AlgHom.commutes realToComplexClifford]
      exact (AlgHom.commutes
        (CliffordAlgebra.involute (Q := vectorQuadratic)) r).symm
  | ι x =>
      rw [CliffordAlgebra.involute_ι, map_neg,
        realToComplexClifford_ι]
      exact (CliffordAlgebra.involute_ι _).symm
  | mul a b ha hb =>
      rw [map_mul, map_mul, ha, hb]
      rw [map_mul realToComplexClifford a b]
      exact (map_mul
        (CliffordAlgebra.involute (Q := vectorQuadratic))
          (realToComplexClifford a) (realToComplexClifford b)).symm
  | add a b ha hb =>
      rw [map_add, map_add, ha, hb]
      rw [map_add realToComplexClifford a b]
      exact (map_add
        (CliffordAlgebra.involute (Q := vectorQuadratic))
          (realToComplexClifford a) (realToComplexClifford b)).symm

theorem realToComplexClifford_reverse
    (a : CliffordAlgebra realQuadratic44) :
    realToComplexClifford (CliffordAlgebra.reverse a) =
      CliffordAlgebra.reverse (realToComplexClifford a) := by
  induction a using CliffordAlgebra.induction with
  | algebraMap r =>
      rw [CliffordAlgebra.reverse.commutes (Q := realQuadratic44),
        AlgHom.commutes realToComplexClifford]
      exact (CliffordAlgebra.reverse.commutes
        (Q := vectorQuadratic) r).symm
  | ι x =>
      rw [CliffordAlgebra.reverse_ι, realToComplexClifford_ι]
      exact (CliffordAlgebra.reverse_ι _).symm
  | mul a b ha hb =>
      rw [CliffordAlgebra.reverse.map_mul, map_mul, ha, hb,
        map_mul, CliffordAlgebra.reverse.map_mul]
  | add a b ha hb =>
      rw [map_add, map_add, ha, hb]
      rw [map_add realToComplexClifford a b]
      exact (map_add (CliffordAlgebra.reverse (Q := vectorQuadratic))
        (realToComplexClifford a) (realToComplexClifford b)).symm

theorem realToComplexClifford_star
    (a : CliffordAlgebra realQuadratic44) :
    realToComplexClifford (star a) = star (realToComplexClifford a) := by
  rw [CliffordAlgebra.star_def, CliffordAlgebra.star_def,
    realToComplexClifford_reverse, realToComplexClifford_involute]

theorem realToComplexClifford_mem_even
    (a : CliffordAlgebra realQuadratic44)
    (ha : a ∈ CliffordAlgebra.even realQuadratic44) :
    realToComplexClifford a ∈ CliffordAlgebra.even vectorQuadratic := by
  induction a, ha using CliffordAlgebra.even_induction with
  | algebraMap r =>
      rw [AlgHom.commutes]
      exact SetLike.algebraMap_mem_graded _ _
  | add a b _ _ ha hb =>
      rw [map_add]
      exact Submodule.add_mem _ ha hb
  | ι_mul_ι_mul x y a _ ha =>
      rw [map_mul, map_mul, realToComplexClifford_ι,
        realToComplexClifford_ι]
      have hp := SetLike.mul_mem_graded
        (CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero vectorQuadratic
          (realSplit44ToVector8 x) (realSplit44ToVector8 y)) ha
      simpa only [zero_add] using hp

/-! ## Mapping the real spin group -/

def realToComplexCliffordUnits :
    (CliffordAlgebra realQuadratic44)ˣ →*
      (CliffordAlgebra vectorQuadratic)ˣ :=
  Units.map realToComplexClifford.toRingHom.toMonoidHom

theorem realToComplexCliffordUnits_mem_lipschitz
    (u : (CliffordAlgebra realQuadratic44)ˣ)
    (hu : u ∈ lipschitzGroup realQuadratic44) :
    realToComplexCliffordUnits u ∈ lipschitzGroup vectorQuadratic := by
  induction hu using Subgroup.closure_induction'' with
  | mem u hu =>
      apply Subgroup.subset_closure
      obtain ⟨x, hx⟩ := hu
      refine ⟨realSplit44ToVector8 x, ?_⟩
      change CliffordAlgebra.ι vectorQuadratic
          (realSplit44ToVector8 x) =
        realToComplexClifford (u : CliffordAlgebra realQuadratic44)
      rw [← hx, realToComplexClifford_ι]
  | inv_mem u hu =>
      rw [map_inv]
      apply Subgroup.inv_mem
      apply Subgroup.subset_closure
      obtain ⟨x, hx⟩ := hu
      refine ⟨realSplit44ToVector8 x, ?_⟩
      change CliffordAlgebra.ι vectorQuadratic
          (realSplit44ToVector8 x) =
        realToComplexClifford (u : CliffordAlgebra realQuadratic44)
      rw [← hx, realToComplexClifford_ι]
  | one =>
      rw [map_one]
      exact Subgroup.one_mem _
  | mul u v _ _ hu hv =>
      rw [map_mul]
      exact Subgroup.mul_mem _ hu hv

theorem realToComplexClifford_mem_unitary
    (a : CliffordAlgebra realQuadratic44)
    (ha : a ∈ unitary (CliffordAlgebra realQuadratic44)) :
    realToComplexClifford a ∈
      unitary (CliffordAlgebra vectorQuadratic) := by
  constructor
  · rw [← realToComplexClifford_star, ← map_mul, ha.1, map_one]
  · rw [← realToComplexClifford_star, ← map_mul, ha.2, map_one]

theorem realSpin_image_mem_complexSpin
    (g : spinGroup realQuadratic44) :
    realToComplexClifford (g : CliffordAlgebra realQuadratic44) ∈
      spinGroup vectorQuadratic := by
  constructor
  · change (↑(realToComplexCliffordUnits (spinGroup.toUnits g)) :
        CliffordAlgebra vectorQuadratic) ∈ pinGroup vectorQuadratic
    rw [pinGroup.units_mem_iff]
    constructor
    · exact realToComplexCliffordUnits_mem_lipschitz
        (spinGroup.toUnits g)
        (spinGroup.units_mem_lipschitzGroup g.2)
    · exact realToComplexClifford_mem_unitary _
        (pinGroup.mem_unitary (spinGroup.mem_pin g.2))
  · exact realToComplexClifford_mem_even _ (spinGroup.mem_even g.2)

/-- Explicit scalar-extension homomorphism from Mathlib's real split spin
group to the canonical complex Zorn spin group. -/
def realSpinToComplexSpin :
    spinGroup realQuadratic44 →* ComplexSpin44 where
  toFun g := ⟨realToComplexClifford
    (g : CliffordAlgebra realQuadratic44),
      realSpin_image_mem_complexSpin g⟩
  map_one' := by
    apply Subtype.ext
    exact map_one realToComplexClifford
  map_mul' g h := by
    apply Subtype.ext
    exact map_mul realToComplexClifford
      (g : CliffordAlgebra realQuadratic44)
      (h : CliffordAlgebra realQuadratic44)

/-! ## Real vector conjugation and comparison -/

theorem realGammaLinear_injective :
    Function.Injective realGammaLinear := by
  intro x y h
  have happ := LinearMap.congr_fun h
    (CanonicalZornSpinVectorAction.identitySpinorPlus, 0)
  have hsnd := congrArg Prod.snd happ
  change (diracGamma (realSplit44ToVector8 x)
      (CanonicalZornSpinVectorAction.identitySpinorPlus, 0)).2 =
    (diracGamma (realSplit44ToVector8 y)
      (CanonicalZornSpinVectorAction.identitySpinorPlus, 0)).2 at hsnd
  rw [CanonicalZornSpinVectorAction.diracGamma_identitySpinor,
    CanonicalZornSpinVectorAction.diracGamma_identitySpinor] at hsnd
  have hv : realSplit44ToVector8 x = realSplit44ToVector8 y := by
    apply ZornCopy.ext
    exact congrArg (fun C : SpinorMinus8 => C.val) hsnd
  exact realSplit44ToVector8_injective hv

theorem realCliffordIota_injective :
    Function.Injective (CliffordAlgebra.ι realQuadratic44) := by
  intro x y h
  apply realGammaLinear_injective
  change realGammaLinear x = realGammaLinear y
  simpa only [realClifford44Representation_ι] using
    congrArg realClifford44Representation h

def realVectorIotaEquivRange :
    RealSplit44 ≃ₗ[ℝ]
      LinearMap.range (CliffordAlgebra.ι realQuadratic44) :=
  LinearEquiv.ofInjective (CliffordAlgebra.ι realQuadratic44)
    realCliffordIota_injective

def realSpinConjugateIotaLinear
    (g : spinGroup realQuadratic44) :
    RealSplit44 →ₗ[ℝ]
      LinearMap.range (CliffordAlgebra.ι realQuadratic44) where
  toFun x :=
    ⟨ConjAct.toConjAct (spinGroup.toUnits g) •
        CliffordAlgebra.ι realQuadratic44 x,
      spinGroup.conjAct_smul_ι_mem_range_ι g.2 x⟩
  map_add' x y := by
    apply Subtype.ext
    simp
  map_smul' c x := by
    apply Subtype.ext
    change ConjAct.toConjAct (spinGroup.toUnits g) •
        CliffordAlgebra.ι realQuadratic44 (c • x) =
      c • (ConjAct.toConjAct (spinGroup.toUnits g) •
        CliffordAlgebra.ι realQuadratic44 x)
    rw [map_smul]
    exact smul_comm (ConjAct.toConjAct (spinGroup.toUnits g)) c
      (CliffordAlgebra.ι realQuadratic44 x)

def realSpinVectorLinear (g : spinGroup realQuadratic44) :
    Module.End ℝ RealSplit44 :=
  realVectorIotaEquivRange.symm.toLinearMap.comp
    (realSpinConjugateIotaLinear g)

theorem realCliffordIota_realSpinVectorLinear
    (g : spinGroup realQuadratic44) (x : RealSplit44) :
    CliffordAlgebra.ι realQuadratic44 (realSpinVectorLinear g x) =
      ConjAct.toConjAct (spinGroup.toUnits g) •
        CliffordAlgebra.ι realQuadratic44 x := by
  change CliffordAlgebra.ι realQuadratic44
      (realVectorIotaEquivRange.symm
        (realSpinConjugateIotaLinear g x)) = _
  exact LinearEquiv.ofInjective_symm_apply
    (CliffordAlgebra.ι realQuadratic44)
      (realSpinConjugateIotaLinear g x)

theorem realCliffordIota_realSpinVector_conjugate
    (g : spinGroup realQuadratic44) (x : RealSplit44) :
    CliffordAlgebra.ι realQuadratic44 (realSpinVectorLinear g x) =
      (g : CliffordAlgebra realQuadratic44) *
        CliffordAlgebra.ι realQuadratic44 x *
        (↑((spinGroup.toUnits g)⁻¹) :
          CliffordAlgebra realQuadratic44) := by
  rw [realCliffordIota_realSpinVectorLinear]
  rfl

/-- Scalar extension intertwines the real and complex vector actions. -/
theorem realSpinToComplexSpin_vector_compatible
    (g : spinGroup realQuadratic44) (x : RealSplit44) :
    spinVectorLinear (realSpinToComplexSpin g)
        (realSplit44ToVector8 x) =
      realSplit44ToVector8 (realSpinVectorLinear g x) := by
  apply cliffordIota_injective
  rw [cliffordIota_spinVector_conjugate]
  rw [← realToComplexClifford_ι]
  rw [← realToComplexClifford_ι]
  rw [realCliffordIota_realSpinVector_conjugate]
  rw [map_mul, map_mul]
  have hunit :
      spinGroup.toUnits (realSpinToComplexSpin g) =
        realToComplexCliffordUnits (spinGroup.toUnits g) := by
    apply Units.ext
    rfl
  have hinv :
      (↑((spinGroup.toUnits (realSpinToComplexSpin g))⁻¹) :
          CliffordAlgebra vectorQuadratic) =
        realToComplexClifford
          (↑((spinGroup.toUnits g)⁻¹) :
            CliffordAlgebra realQuadratic44) := by
    rw [hunit]
    rfl
  rw [hinv]
  rfl

theorem realSpin_image_preserves_real_locus
    (g : spinGroup realQuadratic44) :
    PreservesRealSplitLocus (realSpinToComplexSpin g) := by
  constructor
  · intro x
    exact ⟨realSpinVectorLinear g x,
      realSpinToComplexSpin_vector_compatible g x⟩
  · intro x
    refine ⟨realSpinVectorLinear g⁻¹ x, ?_⟩
    rw [← map_inv]
    exact realSpinToComplexSpin_vector_compatible g⁻¹ x

/-- The scalar-extension comparison factors through the real-locus subgroup
used by the triality/projective closure. -/
def realSpinToRealLocusSpin :
    spinGroup realQuadratic44 →* realLocusSpin44 where
  toFun g := ⟨realSpinToComplexSpin g,
    realSpin_image_preserves_real_locus g⟩
  map_one' := by
    apply Subtype.ext
    exact map_one realSpinToComplexSpin
  map_mul' g h := by
    apply Subtype.ext
    exact map_mul realSpinToComplexSpin g h

theorem realSpinToRealLocusSpin_vector_action
    (g : spinGroup realQuadratic44) (x : RealSplit44) :
    realLocusVectorAction (realSpinToRealLocusSpin g) x =
      realSpinVectorLinear g x := by
  apply realSplit44ToVector8_injective
  rw [← realLocusVectorAction_spec]
  exact realSpinToComplexSpin_vector_compatible g x

/-- The real Mathlib spin action therefore inherits the complete triality,
five-grade, and affine conformal projective closure. -/
theorem realSpin44_affine_projective_triality_closure
    (g : spinGroup realQuadratic44) (x : RealSplit44)
    (S : SpinorPlus8) (C : SpinorMinus8) :
    cartanTrialityOuterEquiv
        (cartanTrialityOuterEquiv
          (cartanTrialityOuterEquiv
            (realLocusSpinRelatedRepresentation
              (realSpinToRealLocusSpin g)))) =
      realLocusSpinRelatedRepresentation (realSpinToRealLocusSpin g) ∧
    relatedVectorGradePlus
        (realLocusSpinRelatedRepresentation (realSpinToRealLocusSpin g))
        (realSplit44ToVector8 x) ∈
      conformalGrade TKKJordanPairData.TKKGrade.p1 ∧
    relatedSpinorGradePlus
        (realLocusSpinRelatedRepresentation (realSpinToRealLocusSpin g)) S ∈
      conformalGrade TKKJordanPairData.TKKGrade.p1 ∧
    relatedSpinorGradeMinus
        (realLocusSpinRelatedRepresentation (realSpinToRealLocusSpin g)) C ∈
      conformalGrade TKKJordanPairData.TKKGrade.m1 ∧
    realQuadratic44 (realSpinVectorLinear g x) = realQuadratic44 x ∧
    Q55 (conformalEmbed44to55
      (realSplit44ToPAC44 (realSpinVectorLinear g x))) = 0 := by
  simpa only [realSpinToRealLocusSpin_vector_action] using
    realLocusSpin_outer_triality_projective_closure
      (realSpinToRealLocusSpin g) x S C

end CanonicalZornRealComplexSpinBaseChange

end noncomputable section
