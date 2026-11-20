/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.InformationGeometry.PositiveMeasureDifferential
import InfoGeometry.Probability.FiniteWeightedSplitKreinAdjoint
import InfoGeometry.Canonical.ParaComplexNeutralForm
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# The finite KL contrast: Fréchet Hessian and neutral mixed pairing

The ambient extension below uses the existing `PositiveMeasure.gklTerm` sum.
Its first and second derivatives are actual native Fréchet derivatives on the
open positive cone. At coincidence the full joint Hessian is positive
semidefinite, with diagonal kernel. Its negative mixed block is the Fisher
pairing. The latter separately constructs a nondegenerate neutral form on the
doubled space, using the existing weighted split-pairing owner, and a concrete
algebraic `ParaComplexNeutralForm.NondegenerateDatum`. No manifold,
connection, or closed differential
two-form is inferred from these finite algebraic facts.
-/

noncomputable section

namespace InfoGeometry.InformationGeometry.PositiveMeasureContrast

open scoped BigOperators Topology
open InfoGeometry.PositiveMeasure InfoGeometry.Probability
open InfoGeometry.Canonical.ParaComplexConnection
open InfoGeometry.Canonical.ParaComplexNeutralForm

private theorem hasFDerivAt_ratio
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {p q : V → ℝ} {p' q' : V →L[ℝ] ℝ} {z : V}
    (hp : HasFDerivAt p p' z) (hq : HasFDerivAt q q' z) (hq0 : q z ≠ 0) :
    HasFDerivAt (fun x => p x / q x)
      ((q z)⁻¹ • p' - (p z / (q z) ^ 2) • q') z := by
  have h := hp.mul ((hasDerivAt_inv hq0).comp_hasFDerivAt z hq)
  simp only [div_eq_mul_inv] at ⊢
  apply h.congr_fderiv
  ext v
  simp only [_root_.add_apply, _root_.sub_apply,
    _root_.smul_apply, smul_eq_mul, Function.comp_apply]
  ring

private theorem hasFDerivAt_logRatio
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {p q : V → ℝ} {p' q' : V →L[ℝ] ℝ} {z : V}
    (hp : HasFDerivAt p p' z) (hq : HasFDerivAt q q' z)
    (hp0 : p z ≠ 0) (hq0 : q z ≠ 0) :
    HasFDerivAt (fun x => Real.log (p x / q x))
      ((p z)⁻¹ • p' - (q z)⁻¹ • q') z := by
  apply ((hasFDerivAt_ratio hp hq hq0).log (div_ne_zero hp0 hq0)).congr_fderiv
  ext v
  simp only [_root_.sub_apply, _root_.smul_apply, smul_eq_mul]
  field_simp [hp0, hq0]

private theorem hasFDerivAt_gklTerm
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {p q : V → ℝ} {p' q' : V →L[ℝ] ℝ} {z : V}
    (hp : HasFDerivAt p p' z) (hq : HasFDerivAt q q' z)
    (hp0 : p z ≠ 0) (hq0 : q z ≠ 0) :
    HasFDerivAt (fun x => gklTerm (p x) (q x))
      (Real.log (p z / q z) • p' + (1 - p z / q z) • q') z := by
  have h := ((hp.mul (hasFDerivAt_logRatio hp hq hp0 hq0)).sub hp).add hq
  change HasFDerivAt (fun x => p x * Real.log (p x / q x) - p x + q x) _ z
  apply h.congr_fderiv
  ext v
  simp only [_root_.add_apply, _root_.sub_apply,
    _root_.smul_apply, smul_eq_mul]
  field_simp [hp0, hq0]
  ring

variable {α : Type*} [Fintype α]

local notation "V" => (α → ℝ)
local notation "E" => ((α → ℝ) × (α → ℝ))

private def sourceCoord (i : α) : E →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ V V)

private def referenceCoord (i : α) : E →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ V V)

omit [Fintype α] in
@[simp] private theorem sourceCoord_apply (i : α) (z : E) : sourceCoord i z = z.1 i := rfl

omit [Fintype α] in
@[simp] private theorem referenceCoord_apply (i : α) (z : E) : referenceCoord i z = z.2 i := rfl

/-- Ambient extension of the existing finite generalized KL sum. -/
def jointGeneralizedKL (z : E) : ℝ := ∑ i, gklTerm (z.1 i) (z.2 i)

/-- On positive measures this is exactly the existing divergence. -/
theorem jointGeneralizedKL_eq_generalizedKL (p q : InfoGeometry.PositiveMeasure α ℝ) :
    jointGeneralizedKL (p.mass, q.mass) = generalizedKL p q := rfl

/-- The first differential, represented by a native continuous linear map. -/
def firstVariation (z : E) : E →L[ℝ] ℝ :=
  ∑ i, (Real.log (z.1 i / z.2 i) • sourceCoord i +
    (1 - z.1 i / z.2 i) • referenceCoord i)

/-- The full derivative of the first differential, before restriction to the
diagonal or to a single tangent direction. -/
def jointHessian (z : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  ∑ i, (((z.1 i)⁻¹ • sourceCoord i - (z.2 i)⁻¹ • referenceCoord i).smulRight
      (sourceCoord i) +
    (-(z.2 i)⁻¹ • sourceCoord i + (z.1 i / (z.2 i) ^ 2) • referenceCoord i).smulRight
      (referenceCoord i))

/-- Joint Fréchet differentiability on the positive cone. -/
theorem hasFDerivAt_jointGeneralizedKL (z : E)
    (hp : ∀ i, 0 < z.1 i) (hq : ∀ i, 0 < z.2 i) :
    HasFDerivAt jointGeneralizedKL (firstVariation z) z := by
  classical
  exact HasFDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    hasFDerivAt_gklTerm (sourceCoord i).hasFDerivAt (referenceCoord i).hasFDerivAt
      (hp i).ne' (hq i).ne'

/-- The coefficients of the first differential are themselves Fréchet
differentiable; this proves the operator-valued second derivative. -/
theorem hasFDerivAt_firstVariation (z : E)
    (hp : ∀ i, 0 < z.1 i) (hq : ∀ i, 0 < z.2 i) :
    HasFDerivAt firstVariation (jointHessian z) z := by
  classical
  apply HasFDerivAt.fun_sum (u := Finset.univ)
  intro i _
  have hlog := hasFDerivAt_logRatio (sourceCoord i).hasFDerivAt
    (referenceCoord i).hasFDerivAt (hp i).ne' (hq i).ne'
  have hratio := (hasFDerivAt_ratio (sourceCoord i).hasFDerivAt
    (referenceCoord i).hasFDerivAt (hq i).ne').const_sub 1
  have h := (hlog.smul_const (sourceCoord i)).add (hratio.smul_const (referenceCoord i))
  apply h.congr_fderiv
  apply ContinuousLinearMap.ext
  intro x
  apply ContinuousLinearMap.ext
  intro y
  simp only [_root_.add_apply, _root_.sub_apply,
    _root_.neg_apply, _root_.smul_apply,
    ContinuousLinearMap.smulRight_apply, sourceCoord_apply, referenceCoord_apply, smul_eq_mul]
  ring

/-- This is a derivative of the actual native `fderiv` of the existing sum,
not merely the derivative of a separately stipulated response map. -/
theorem hasFDerivAt_fderiv_jointGeneralizedKL (z : E)
    (hp : ∀ i, 0 < z.1 i) (hq : ∀ i, 0 < z.2 i) :
    HasFDerivAt (fderiv ℝ jointGeneralizedKL) (jointHessian z) z := by
  have hp_near : ∀ᶠ w : E in 𝓝 z, ∀ i, 0 < w.1 i := by
    apply Filter.eventually_all.2
    intro i
    exact continuousAt_const.eventually_lt (sourceCoord i).continuous.continuousAt (hp i)
  have hq_near : ∀ᶠ w : E in 𝓝 z, ∀ i, 0 < w.2 i := by
    apply Filter.eventually_all.2
    intro i
    exact continuousAt_const.eventually_lt (referenceCoord i).continuous.continuousAt (hq i)
  apply (hasFDerivAt_firstVariation z hp hq).congr_of_eventuallyEq
  filter_upwards [hp_near, hq_near] with w hpw hqw
  exact (hasFDerivAt_jointGeneralizedKL w hpw hqw).fderiv

/-- Coordinate evaluation of the full joint Hessian. -/
theorem jointHessian_apply (z x y : E) :
    jointHessian z x y = ∑ i,
      ((x.1 i / z.1 i - x.2 i / z.2 i) * y.1 i +
        (-x.1 i / z.2 i + z.1 i * x.2 i / (z.2 i) ^ 2) * y.2 i) := by
  classical
  simp only [jointHessian, sum_apply, _root_.add_apply,
    _root_.sub_apply, ContinuousLinearMap.smulRight_apply,
    _root_.smul_apply, sourceCoord_apply, referenceCoord_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Native bilinear packaging of the existing weighted pairing, at inverse
positive-measure weights. Normalization of the measure is not required. -/
def fisherForm (p : InfoGeometry.PositiveMeasure α ℝ) : LinearMap.BilinForm ℝ V :=
  LinearMap.mk₂ ℝ (weightedVectorPairing (fun i => (p i)⁻¹))
    (weightedVectorPairing_add_left _)
    (weightedVectorPairing_smul_left _)
    (fun u v w => by
      simp only [weightedVectorPairing, Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun c u v => by
      simp only [weightedVectorPairing, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => mul_left_comm _ _ _)

/-- The inverse-weighted pairing is the usual positive-cone Fisher form. -/
theorem fisherForm_apply (p : InfoGeometry.PositiveMeasure α ℝ) (u v : V) :
    fisherForm p u v = ∑ i, u i * v i / p i := by
  unfold fisherForm weightedVectorPairing
  apply Finset.sum_congr rfl
  intro i _
  simp only [div_eq_mul_inv]
  ring

theorem fisherForm_symm (p : InfoGeometry.PositiveMeasure α ℝ) (u v : V) :
    fisherForm p u v = fisherForm p v u := by
  simp only [fisherForm_apply, mul_comm]

theorem fisherForm_self_nonneg (p : InfoGeometry.PositiveMeasure α ℝ) (u : V) :
    0 ≤ fisherForm p u u := by
  rw [fisherForm_apply]
  exact Finset.sum_nonneg fun i _ => div_nonneg (mul_self_nonneg _) (p.pos i).le

/-- Positive weights make the Fisher form definite on the full cone tangent. -/
theorem fisherForm_self_eq_zero_iff (p : InfoGeometry.PositiveMeasure α ℝ) (u : V) :
    fisherForm p u u = 0 ↔ u = 0 := by
  classical
  constructor
  · intro h
    rw [fisherForm_apply] at h
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ Finset.univ) => div_nonneg (mul_self_nonneg (u i)) (p.pos i).le)).mp h
    funext i
    have hi : u i * u i = 0 :=
      (div_eq_zero_iff.mp (hz i (Finset.mem_univ i))).resolve_right (p.pos i).ne'
    exact (mul_self_eq_zero.mp hi)
  · rintro rfl
    simp

/-- At coincident states, the actual joint Hessian measures relative tangent
motion. It is not the neutral cross-pairing constructed below. -/
theorem second_fderiv_diagonal (p : InfoGeometry.PositiveMeasure α ℝ) (x y : E) :
    fderiv ℝ (fderiv ℝ jointGeneralizedKL) (p.mass, p.mass) x y =
      fisherForm p (x.1 - x.2) (y.1 - y.2) := by
  rw [(hasFDerivAt_fderiv_jointGeneralizedKL (p.mass, p.mass) p.pos p.pos).fderiv,
    jointHessian_apply, fisherForm_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.sub_apply]
  field_simp [(p.pos i).ne']
  ring

/-- Eguchi's negative mixed derivative is the Fisher pairing. -/
theorem negative_mixed_second_fderiv (p : InfoGeometry.PositiveMeasure α ℝ) (u v : V) :
    -(fderiv ℝ (fderiv ℝ jointGeneralizedKL) (p.mass, p.mass) (u, 0) (0, v)) =
      fisherForm p u v := by
  rw [second_fderiv_diagonal]
  simp

/-- The joint Hessian is positive semidefinite at coincidence. -/
theorem second_fderiv_diagonal_nonneg (p : InfoGeometry.PositiveMeasure α ℝ) (x : E) :
    0 ≤ fderiv ℝ (fderiv ℝ jointGeneralizedKL) (p.mass, p.mass) x x := by
  rw [second_fderiv_diagonal]
  exact fisherForm_self_nonneg p _

/-- Its null quadratic directions are exactly simultaneous equal motion of
the two distributions. -/
theorem second_fderiv_diagonal_self_eq_zero_iff
    (p : InfoGeometry.PositiveMeasure α ℝ) (x : E) :
    fderiv ℝ (fderiv ℝ jointGeneralizedKL) (p.mass, p.mass) x x = 0 ↔ x.1 = x.2 := by
  rw [second_fderiv_diagonal, fisherForm_self_eq_zero_iff, sub_eq_zero]

/-- The same diagonal space is the actual kernel of the Hessian pairing. -/
theorem second_fderiv_diagonal_kernel_iff (p : InfoGeometry.PositiveMeasure α ℝ) (x : E) :
    (∀ y, fderiv ℝ (fderiv ℝ jointGeneralizedKL) (p.mass, p.mass) x y = 0) ↔
      x.1 = x.2 := by
  constructor
  · intro h
    exact (second_fderiv_diagonal_self_eq_zero_iff p x).mp (h x)
  · intro h y
    rw [second_fderiv_diagonal, h, sub_self]
    simp

/-- Native bilinear packaging of the existing doubled neutral pairing. -/
def neutralForm (p : InfoGeometry.PositiveMeasure α ℝ) : LinearMap.BilinForm ℝ E :=
  LinearMap.mk₂ ℝ (splitWeightedPairing (fun i => (p i)⁻¹))
    (fun x y z => by
      simp only [splitWeightedPairing, Prod.fst_add, Prod.snd_add,
        weightedVectorPairing_add_left]
      exact add_add_add_comm _ _ _ _)
    (fun c x y => by
      simp only [splitWeightedPairing, Prod.smul_fst, Prod.smul_snd,
        weightedVectorPairing_smul_left, smul_eq_mul]
      exact (mul_add _ _ _).symm)
    (fun x y z => by
      simp only [splitWeightedPairing, weightedVectorPairing, Prod.fst_add,
        Prod.snd_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      exact add_add_add_comm _ _ _ _)
    (fun c x y => by
      simp only [splitWeightedPairing, weightedVectorPairing, Prod.smul_fst,
        Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_add]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;>
        exact mul_left_comm _ _ _)

theorem neutralForm_apply (p : InfoGeometry.PositiveMeasure α ℝ) (x y : E) :
    neutralForm p x y = fisherForm p x.1 y.2 + fisherForm p x.2 y.1 := rfl

/-- The concrete neutral form is assembled from the two negative mixed
blocks of the actual KL Fréchet Hessian. -/
theorem neutralForm_eq_negative_mixed_second_fderiv
    (p : InfoGeometry.PositiveMeasure α ℝ) (x y : E) :
    neutralForm p x y =
      -(fderiv ℝ (fderiv ℝ jointGeneralizedKL) (p.mass, p.mass) (x.1, 0) (0, y.2)) -
        fderiv ℝ (fderiv ℝ jointGeneralizedKL) (p.mass, p.mass) (x.2, 0) (0, y.1) := by
  rw [neutralForm_apply, ← negative_mixed_second_fderiv p x.1 y.2,
    ← negative_mixed_second_fderiv p x.2 y.1]
  ring

theorem neutralForm_symm (p : InfoGeometry.PositiveMeasure α ℝ) (x y : E) :
    neutralForm p x y = neutralForm p y x := by
  rw [neutralForm_apply, neutralForm_apply,
    fisherForm_symm p x.1 y.2, fisherForm_symm p x.2 y.1]
  ring

/-- Unlike the joint Hessian, the doubled cross-form is nondegenerate. -/
theorem neutralForm_nondegenerate (p : InfoGeometry.PositiveMeasure α ℝ) :
    (neutralForm p).Nondegenerate := by
  have hleft : (neutralForm p).SeparatingLeft := by
    intro x hx
    have hx1 : fisherForm p x.1 x.1 = 0 := by
      simpa only [neutralForm_apply, map_zero, add_zero] using hx (0, x.1)
    have hx2 : fisherForm p x.2 x.2 = 0 := by
      simpa only [neutralForm_apply, map_zero, zero_add] using hx (x.2, 0)
    exact Prod.ext ((fisherForm_self_eq_zero_iff p x.1).mp hx1)
      ((fisherForm_self_eq_zero_iff p x.2).mp hx2)
  refine ⟨hleft, ?_⟩
  intro x hx
  apply hleft x
  intro y
  rw [neutralForm_symm]
  exact hx y

/-- Linear packaging of the existing sheet polarization. -/
def polarization : E →ₗ[ℝ] E where
  toFun := splitWeightedPolarization
  map_add' x y := by simp [splitWeightedPolarization, add_comm]
  map_smul' c x := by simp [splitWeightedPolarization]

omit [Fintype α] in
theorem polarization_sq : (polarization (α := α)).comp polarization = LinearMap.id := by
  apply LinearMap.ext
  intro x
  change (x.1, -(-x.2)) = x
  exact Prod.ext rfl (neg_neg _)

theorem neutralForm_anti_compatible (p : InfoGeometry.PositiveMeasure α ℝ) (x y : E) :
    neutralForm p (polarization x) (polarization y) = -neutralForm p x y := by
  rw [neutralForm_apply, neutralForm_apply]
  change fisherForm p x.1 (-y.2) + fisherForm p (-x.2) y.1 =
    -(fisherForm p x.1 y.2 + fisherForm p x.2 y.1)
  simp only [map_neg, LinearMap.neg_apply]
  ring

/-- The existing canonical para-complex structure, instantiated by the
actual product polarization. -/
def fisherParaComplex : ParaComplexStructure E where
  tau := polarization
  tau_sq x := LinearMap.congr_fun polarization_sq x

/-- Concrete neutral data, using the existing canonical owner and proving
its symmetry and anti-isometry fields from the constructed Fisher pairing. -/
def fisherNeutralDatum (p : InfoGeometry.PositiveMeasure α ℝ) :
    Datum (fisherParaComplex (α := α)) where
  form := neutralForm p
  symmetric := neutralForm_symm p
  anti_isometry := neutralForm_anti_compatible p

/-- The same actual data satisfy the canonical nondegenerate interface.
Cross-sheet nondegeneracy is derived from the concrete positive weights and
the canonical Peirce decomposition; no such property is assumed. -/
def fisherNondegenerateDatum (p : InfoGeometry.PositiveMeasure α ℝ) :
    NondegenerateDatum (fisherParaComplex (α := α)) where
  form := neutralForm p
  symmetric := neutralForm_symm p
  anti_compatible := antiCompatible_of_anti_isometry fisherParaComplex (fisherNeutralDatum p)
  nondegenerate := (neutralForm_nondegenerate p).1
  plus_cross_nondegenerate := by
    intro u hu hcross
    apply (neutralForm_nondegenerate p).1 u
    intro y
    have hdecomp := congrArg (neutralForm p u) (peirce_sum_id fisherParaComplex y)
    rw [map_add, hcross _ (peircePlus_mem_plusEigenspace fisherParaComplex y),
      minus_isotropic fisherParaComplex (neutralForm p)
        (antiCompatible_of_anti_isometry fisherParaComplex (fisherNeutralDatum p))
        hu (peirceMinus_mem_minusEigenspace fisherParaComplex y), zero_add] at hdecomp
    exact hdecomp.symm
  minus_cross_nondegenerate := by
    intro u hu hcross
    apply (neutralForm_nondegenerate p).1 u
    intro y
    have hdecomp := congrArg (neutralForm p u) (peirce_sum_id fisherParaComplex y)
    rw [map_add,
      plus_isotropic fisherParaComplex (neutralForm p)
        (antiCompatible_of_anti_isometry fisherParaComplex (fisherNeutralDatum p))
        hu (peircePlus_mem_plusEigenspace fisherParaComplex y),
      hcross _ (peirceMinus_mem_minusEigenspace fisherParaComplex y), zero_add] at hdecomp
    exact hdecomp.symm

/-- Its fundamental alternating pairing is the existing weighted split
symplectic form at inverse-measure weights. -/
theorem fisherNeutralDatum_twoForm (p : InfoGeometry.PositiveMeasure α ℝ) (x y : E) :
    (fisherNeutralDatum p).form (fisherParaComplex.tau x) y =
      splitWeightedSymplectic (fun i => (p i)⁻¹) x y := by
  change fisherForm p x.1 y.2 + fisherForm p (-x.2) y.1 =
    fisherForm p x.1 y.2 - fisherForm p x.2 y.1
  simp only [map_neg, LinearMap.neg_apply]
  ring

/-- Explicit positive and negative directions distinguish the neutral form
from the positive semidefinite joint Hessian. -/
theorem neutralForm_opposite_signs (p : InfoGeometry.PositiveMeasure α ℝ)
    (u : V) (hu : u ≠ 0) :
    0 < neutralForm p (u, u) (u, u) ∧ neutralForm p (u, -u) (u, -u) < 0 := by
  have hpos : 0 < fisherForm p u u :=
    lt_of_le_of_ne (fisherForm_self_nonneg p u)
      (Ne.symm (fun h => hu ((fisherForm_self_eq_zero_iff p u).mp h)))
  simp only [neutralForm_apply, map_neg, LinearMap.neg_apply]
  constructor <;> linarith

end InfoGeometry.InformationGeometry.PositiveMeasureContrast
