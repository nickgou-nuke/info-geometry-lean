/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.HestenesLoxodromicRotor
import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.LinearAlgebra.Projection
import Mathlib.Tactic.Ring

/-!
# Real loxodromic actions preserve a specified bilinear pairing

The existing real boost and rotor actions become native bilinear-form
isometries when their generators are skew-adjoint for that form. The form
need not be positive or nondegenerate. Its preservation is therefore distinct
from boundedness in an observer norm.

The two axes commute only where needed for a group inverse and for preserving
the boost eigenspaces. Vectors and other operators are not required to commute.
No scalar complex phase or modular state is introduced.
-/

noncomputable section

namespace InfoGeometry.Krein.LoxodromicPairingFlow

open InfoGeometry.Canonical

private theorem reflection_pairing_polynomial (a b : ℝ) :
    a - 2 * (a - b) = -(a - 2 * b) := by ring

private theorem boost_pairing_polynomial (c s a b : ℝ) :
    c * (c * a + s * (-b)) + s * (c * b + s * (-a)) =
      (c ^ 2 - s ^ 2) * a := by ring

private theorem rotor_pairing_polynomial (c s a b : ℝ) :
    c * (c * a + s * (-b)) + s * (c * b + s * a) =
      (c ^ 2 + s ^ 2) * a := by ring

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable (B : LinearMap.BilinForm ℝ V) (K J : Module.End ℝ V)

/-- The reflection associated to an actual projection is a real involution. -/
theorem projection_reflection_involution (p : Module.End ℝ V)
    (hp : IsIdempotentElem p) : IsRealInvolution (1 - (2 : ℝ) • p) := by
  ext x
  have hpx : p (p x) = p x := LinearMap.congr_fun hp x
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, Module.End.one_apply,
    LinearMap.smul_apply, map_sub, map_smul, hpx, LinearMap.id_apply]
  module

/-- The exchanged-adjoint equation produces the skew boost generator `1-2p`. -/
theorem projection_reflection_skewAdjoint (p : Module.End ℝ V)
    (hAdj : ∀ x y, B (p x) y = B x ((1 - p) y)) :
    B.IsSkewAdjoint ((1 - (2 : ℝ) • p) : Module.End ℝ V) := by
  intro x y
  change B (x - (2 : ℝ) • p x) y = B x (-(y - (2 : ℝ) • p y))
  have hadj : B (p x) y = B x y - B x (p y) := by
    simpa only [LinearMap.sub_apply, Module.End.one_apply, map_sub] using hAdj x y
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    map_neg, smul_eq_mul, hadj]
  exact reflection_pairing_polynomial (B x y) (B x (p y))

/-- The chosen projector range is the negative boost eigenspace. -/
theorem projection_reflection_on_range (p : Module.End ℝ V)
    (hp : IsIdempotentElem p) (x : LinearMap.range p) :
    (1 - (2 : ℝ) • p) x.val = -x.val := by
  have hx := (LinearMap.IsIdempotentElem.mem_range_iff hp).mp x.property
  simp only [LinearMap.sub_apply, Module.End.one_apply, LinearMap.smul_apply, hx]
  module

/-- The complementary range is the positive boost eigenspace. -/
theorem projection_reflection_on_complement (p : Module.End ℝ V)
    (hp : IsIdempotentElem p) (x : LinearMap.range (1 - p)) :
    (1 - (2 : ℝ) • p) x.val = x.val := by
  have hx : p x.val = 0 := by
    have hfixed :=
      (LinearMap.IsIdempotentElem.mem_range_iff (IsIdempotentElem.one_sub hp)).mp x.property
    simpa only [LinearMap.sub_apply, Module.End.one_apply, sub_eq_self] using hfixed
  simp only [LinearMap.sub_apply, Module.End.one_apply, LinearMap.smul_apply,
    hx, smul_zero, sub_zero]

/-- Skew-adjointness with an involutive axis reverses the bilinear pairing. -/
theorem pairing_involution (hK : IsRealInvolution K) (hKB : B.IsSkewAdjoint K)
    (x y : V) : B (K x) (K y) = -B x y := by
  have hKy : K (K y) = y := by
    have h := congrArg (fun f : Module.End ℝ V => f y) hK
    simpa only [IsRealInvolution, LinearMap.comp_apply, LinearMap.id_apply] using h
  simpa only [Pi.neg_apply, hKy, map_neg] using hKB x (K y)

/-- A negative-square skew-adjoint axis preserves the bilinear pairing. -/
theorem pairing_complexStructure (hJ : IsRealComplexStructure J)
    (hJB : B.IsSkewAdjoint J) (x y : V) : B (J x) (J y) = B x y := by
  simpa only [Pi.neg_apply, realComplexStructure_apply_sq J hJ, neg_neg] using
    hJB x (J y)

/-- The real boost preserves an indefinite pairing for which its axis is skew. -/
theorem realBoostAction_pairing (hK : IsRealInvolution K)
    (hKB : B.IsSkewAdjoint K) (t : ℝ) (x y : V) :
    B (realBoostAction K t x) (realBoostAction K t y) = B x y := by
  have hcross : B (K x) y = -B x (K y) := by
    simpa only [Pi.neg_apply, map_neg] using hKB x y
  have hdiag := pairing_involution B K hK hKB x y
  calc
    B (realBoostAction K t x) (realBoostAction K t y) =
        (Real.cosh t ^ 2 - Real.sinh t ^ 2) * B x y := by
      simp only [realBoostAction, map_add, map_smul, LinearMap.add_apply,
        LinearMap.smul_apply, smul_eq_mul, hcross, hdiag]
      exact boost_pairing_polynomial _ _ _ _
    _ = B x y := by rw [Real.cosh_sq_sub_sinh_sq, one_mul]

/-- The internal real rotor preserves the same specified pairing. -/
theorem realRotorAction_pairing (hJ : IsRealComplexStructure J)
    (hJB : B.IsSkewAdjoint J) (θ : ℝ) (x y : V) :
    B (realRotorAction J θ x) (realRotorAction J θ y) = B x y := by
  have hcross : B (J x) y = -B x (J y) := by
    simpa only [Pi.neg_apply, map_neg] using hJB x y
  have hdiag := pairing_complexStructure B J hJ hJB x y
  calc
    B (realRotorAction J θ x) (realRotorAction J θ y) =
        (Real.cos θ ^ 2 + Real.sin θ ^ 2) * B x y := by
      simp only [realRotorAction, map_add, map_smul, LinearMap.add_apply,
        LinearMap.smul_apply, smul_eq_mul, hcross, hdiag]
      exact rotor_pairing_polynomial _ _ _ _
    _ = B x y := by rw [Real.cos_sq_add_sin_sq, one_mul]

/-- Preservation of the pairing by the composed action needs no commuting-axis
hypothesis: each factor separately preserves it. -/
theorem realLoxodromicAction_pairing
    (hK : IsRealInvolution K) (hJ : IsRealComplexStructure J)
    (hKB : B.IsSkewAdjoint K) (hJB : B.IsSkewAdjoint J)
    (t θ : ℝ) (x y : V) :
    B (realLoxodromicAction K J t θ x) (realLoxodromicAction K J t θ y) = B x y := by
  unfold realLoxodromicAction
  rw [realBoostAction_pairing B K hK hKB, realRotorAction_pairing B J hJ hJB]

/-- The existing real loxodromic action as a native bilinear isometry equivalence.
Commutation supplies the inverse with both parameters negated. -/
def loxodromicIsometryEquiv
    (hK : IsRealInvolution K) (hJ : IsRealComplexStructure J)
    (hKJ : K.comp J = J.comp K)
    (hKB : B.IsSkewAdjoint K) (hJB : B.IsSkewAdjoint J)
    (t θ : ℝ) : B.IsometryEquiv B where
  toFun := realLoxodromicAction K J t θ
  invFun := realLoxodromicAction K J (-t) (-θ)
  left_inv := realLoxodromicAction_inverse K J hK hJ hKJ t θ
  right_inv x := by
    simpa only [neg_neg] using realLoxodromicAction_inverse K J hK hJ hKJ (-t) (-θ) x
  map_add' x y := by
    simp only [realLoxodromicAction, realBoostAction, realRotorAction,
      map_add, smul_add]
    module
  map_smul' c x := by
    let boost : Module.End ℝ V :=
      Real.cosh t • LinearMap.id + Real.sinh t • K
    let rotor : Module.End ℝ V :=
      Real.cos θ • LinearMap.id + Real.sin θ • J
    change (boost.comp rotor) (c • x) = c • (boost.comp rotor) x
    exact (boost.comp rotor).map_smul c x
  map_app' := realLoxodromicAction_pairing B K J hK hJ hKB hJB t θ

/-- A common elliptic rotation preserves the positive boost eigenspace. -/
theorem rotor_in_positive_eigenspace (hKJ : K.comp J = J.comp K)
    {x : V} (hx : K x = x) (θ : ℝ) :
    K (realRotorAction J θ x) = realRotorAction J θ x := by
  have hcomm : K (J x) = J (K x) := congrArg (fun f : Module.End ℝ V => f x) hKJ
  simp only [realRotorAction, map_add, map_smul, hcomm, hx]

/-- A common elliptic rotation preserves the negative boost eigenspace. -/
theorem rotor_in_negative_eigenspace (hKJ : K.comp J = J.comp K)
    {x : V} (hx : K x = -x) (θ : ℝ) :
    K (realRotorAction J θ x) = -realRotorAction J θ x := by
  have hcomm : K (J x) = J (K x) := congrArg (fun f : Module.End ℝ V => f x) hKJ
  simp only [realRotorAction, map_add, map_smul, hcomm, hx, map_neg,
    smul_neg, neg_add_rev]
  abel

/-- Positive boost eigenvectors acquire the expanding real weight. -/
theorem realLoxodromicAction_positive (hKJ : K.comp J = J.comp K)
    {x : V} (hx : K x = x) (t θ : ℝ) :
    realLoxodromicAction K J t θ x =
      Real.exp t • realRotorAction J θ x := by
  unfold realLoxodromicAction realBoostAction
  rw [rotor_in_positive_eigenspace K J hKJ hx, ← add_smul, Real.cosh_add_sinh]

/-- Negative boost eigenvectors acquire the contracting real weight. -/
theorem realLoxodromicAction_negative (hKJ : K.comp J = J.comp K)
    {x : V} (hx : K x = -x) (t θ : ℝ) :
    realLoxodromicAction K J t θ x =
      Real.exp (-t) • realRotorAction J θ x := by
  unfold realLoxodromicAction realBoostAction
  rw [rotor_in_negative_eigenspace K J hKJ hx, smul_neg, ← sub_eq_add_neg,
    ← sub_smul, Real.cosh_sub_sinh]

/-- The cross pairing at unequal boost parameters records their difference.
At equal parameters the reciprocal real weights cancel exactly. -/
theorem mixed_time_cross_pairing (hJ : IsRealComplexStructure J)
    (hKJ : K.comp J = J.comp K) (hJB : B.IsSkewAdjoint J)
    {x y : V} (hx : K x = -x) (hy : K y = y) (t u θ : ℝ) :
    B (realLoxodromicAction K J t θ x) (realLoxodromicAction K J u θ y) =
      Real.exp (u - t) * B x y := by
  rw [realLoxodromicAction_negative K J hKJ hx,
    realLoxodromicAction_positive K J hKJ hy]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [realRotorAction_pairing B J hJ hJB]
  rw [← mul_assoc, ← Real.exp_add]
  simp only [sub_eq_add_neg]

/-- A form preserved by the rotor scales by the square of the negative weight.
Positivity is not assumed; a positive observer form is one specialization. -/
theorem negative_eigenspace_quadratic_scaling (hJ : IsRealComplexStructure J)
    (hKJ : K.comp J = J.comp K) (hJB : B.IsSkewAdjoint J)
    {x : V} (hx : K x = -x) (t θ : ℝ) :
    B (realLoxodromicAction K J t θ x) (realLoxodromicAction K J t θ x) =
      Real.exp (-2 * t) * B x x := by
  rw [realLoxodromicAction_negative K J hKJ hx]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [realRotorAction_pairing B J hJ hJB]
  rw [← mul_assoc, ← Real.exp_add]
  simp only [neg_mul, two_mul, neg_add]

/-- The opposite eigenspace has the reciprocal quadratic scaling. -/
theorem positive_eigenspace_quadratic_scaling (hJ : IsRealComplexStructure J)
    (hKJ : K.comp J = J.comp K) (hJB : B.IsSkewAdjoint J)
    {x : V} (hx : K x = x) (t θ : ℝ) :
    B (realLoxodromicAction K J t θ x) (realLoxodromicAction K J t θ x) =
      Real.exp (2 * t) * B x x := by
  rw [realLoxodromicAction_positive K J hKJ hx]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [realRotorAction_pairing B J hJ hJB]
  rw [← mul_assoc, ← Real.exp_add]
  rw [← two_mul]

end InfoGeometry.Krein.LoxodromicPairingFlow
