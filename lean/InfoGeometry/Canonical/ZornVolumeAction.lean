/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ZornWittBorn
import InfoGeometry.Lie.CanonicalZornRegularNorm

/-!
# Oriented volume action on the native real Dirac module

The ordered diagonal basis is transported through the actual quadratic
isometry. Two sparse products of native left actions determine the sign of
the represented volume. The resulting operator is positive on the first
Zorn summand and negative on the second.
-/

noncomputable section

namespace InfoGeometry.Canonical.ZornVolumeAction

open InfoGeometry.Canonical.ZornClifford
open InfoGeometry.Canonical.ZornWittBorn
open InfoGeometry.Clifford.Cl44Witt
open InfoGeometry.Clifford.Cl44VolumeElement
open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
open InfoGeometry.Lie.CanonicalZornRegularNorm

local notation "L" => leftRegularRepresentation
local notation "Γ" => (diracGammaLinear (R := ℝ))
local notation "q[" i "]" =>
  (ZornMatrix.chiralUpperBasis i - ZornMatrix.chiralLowerBasis i : ZornMatrix ℝ)
local notation "h[" i "]" =>
  (ZornMatrix.chiralUpperBasis i + ZornMatrix.chiralLowerBasis i : ZornMatrix ℝ)
local notation "ell" =>
  (ZornMatrix.zornPlus - ZornMatrix.zornMinus : ZornMatrix ℝ)

private def reflect (z : ZornMatrix ℝ) : ZornMatrix ℝ :=
  { a := z.b, b := z.a, x := -z.y, y := -z.x }

private theorem reflect_reflect (z : ZornMatrix ℝ) : reflect (reflect z) = z := by
  ext i <;> simp [reflect]

private theorem positive_triple (z : ZornMatrix ℝ) :
    L q[0] (L q[1] (L q[2] z)) = reflect z := by
  change q[0] * (q[1] * (q[2] * z)) = reflect z
  ext i <;> (try fin_cases i) <;>
    norm_num [reflect, ZornMatrix.chiralUpperBasis, ZornMatrix.chiralLowerBasis,
      ZornMatrix.mul_def, ZornMatrix.mul, ZornMatrix.dot, ZornMatrix.cross,
      Matrix.vecHead, Matrix.vecTail, Pi.single_apply]

private theorem negative_quadruple (z : ZornMatrix ℝ) :
    L ell (L h[0] (L h[1] (L h[2] z))) = reflect z := by
  change ell * (h[0] * (h[1] * (h[2] * z))) = reflect z
  ext i <;> (try fin_cases i) <;>
    norm_num [reflect, ZornMatrix.zornPlus, ZornMatrix.zornMinus,
      ZornMatrix.chiralUpperBasis, ZornMatrix.chiralLowerBasis,
      ZornMatrix.mul_def, ZornMatrix.mul, ZornMatrix.dot, ZornMatrix.cross,
      Matrix.vecHead, Matrix.vecTail, Pi.single_apply]

private theorem conj_q (i : Fin 3) : zornConj q[i] = -q[i] := by
  ext j <;> simp [zornConj, ZornMatrix.chiralUpperBasis, ZornMatrix.chiralLowerBasis]

private theorem conj_h (i : Fin 3) : zornConj h[i] = -h[i] := by
  ext j <;> simp [zornConj, ZornMatrix.chiralUpperBasis, ZornMatrix.chiralLowerBasis]

private theorem conj_ell : zornConj ell = -ell := by
  ext j <;> simp [zornConj, ZornMatrix.zornPlus, ZornMatrix.zornMinus]

private theorem gamma_imaginary_apply (v : ZornMatrix ℝ) (hv : zornConj v = -v)
    (s t : ZornMatrix ℝ) : Γ v (s, t) = (L v t, -(L v s)) := by
  change (L v t, L (zornConj v) s) = _
  rw [hv, map_neg]

private theorem gamma_one_apply (s t : ZornMatrix ℝ) :
    Γ (1 : ZornMatrix ℝ) (s, t) = (t, s) := by
  have hconj : zornConj (1 : ZornMatrix ℝ) = 1 := by
    ext i <;> simp [zornConj]
  change (L 1 t, L (zornConj 1) s) = _
  rw [hconj, leftRegular_one]

private theorem positive_product_apply (s t : ZornMatrix ℝ) :
    cl44Representation (e 0 * e 1 * e 2 * e 3) (s, t) =
      (reflect s, -(reflect t)) := by
  simp only [map_mul, e, cl44Representation_ι, splitZornIsometry_eVec_zero]
  change Γ (1 : ZornMatrix ℝ)
    (Γ (splitZornIsometry (eVec (Fin.succ 0)))
      (Γ (splitZornIsometry (eVec (Fin.succ 1)))
        (Γ (splitZornIsometry (eVec (Fin.succ 2))) (s, t)))) = _
  rw [splitZornIsometry_eVec_succ, splitZornIsometry_eVec_succ,
    splitZornIsometry_eVec_succ]
  rw [gamma_imaginary_apply _ (conj_q 2), gamma_imaginary_apply _ (conj_q 1),
    gamma_imaginary_apply _ (conj_q 0), gamma_one_apply]
  simp only [map_neg, neg_neg, positive_triple]

private theorem born_apply_reflect (s t : ZornMatrix ℝ) :
    cl44Representation bornElement (s, t) = (reflect s, reflect t) := by
  rw [bornElement_ordered_product]
  simp only [map_mul, f, cl44Representation_ι, splitZornIsometry_fVec_zero]
  change Γ ell
    (Γ (splitZornIsometry (fVec (Fin.succ 0)))
      (Γ (splitZornIsometry (fVec (Fin.succ 1)))
        (Γ (splitZornIsometry (fVec (Fin.succ 2))) (s, t)))) = _
  rw [splitZornIsometry_fVec_succ, splitZornIsometry_fVec_succ,
    splitZornIsometry_fVec_succ]
  rw [gamma_imaginary_apply _ (conj_h 2), gamma_imaginary_apply _ (conj_h 1),
    gamma_imaginary_apply _ (conj_h 0), gamma_imaginary_apply _ conj_ell]
  simp only [map_neg, neg_neg, negative_quadruple]

/-- The represented four-negative-generator product reflects the negative
quaternion coordinates in each existing Zorn summand. -/
theorem bornElement_action (s t : ZornMatrix ℝ) :
    cl44Representation bornElement (s, t) =
      ({ a := s.b, b := s.a, x := -s.y, y := -s.x },
       { a := t.b, b := t.a, x := -t.y, y := -t.x }) :=
  born_apply_reflect s t

private theorem volume_ordered_product :
    volumeElement = (e 0 * e 1 * e 2 * e 3) * bornElement := by
  rw [bornElement_ordered_product]
  simp [volumeElement, InfoGeometry.Clifford.KoszulFoundation.cliffordVolumeElement,
    volumeVectorList, volumeVector, e, f, mul_assoc]

/-- The exact oriented Clifford volume is positive on the upper Zorn summand
and negative on the lower one. -/
theorem volumeElement_action (s t : ZornMatrix ℝ) :
    cl44Representation volumeElement (s, t) = (s, -t) := by
  rw [volume_ordered_product, map_mul]
  change cl44Representation (e 0 * e 1 * e 2 * e 3)
    (cl44Representation bornElement (s, t)) = _
  rw [born_apply_reflect, positive_product_apply, reflect_reflect, reflect_reflect]

/-- The represented volume squares to the identity on the full real module. -/
theorem volumeElement_action_sq :
    cl44Representation volumeElement * cl44Representation volumeElement = 1 := by
  rw [← map_mul, volumeElement_sq, map_one]

/-- The represented volume anticommutes with every native Zorn vector action. -/
theorem volumeElement_anticommutes_gamma (v : ZornMatrix ℝ) :
    cl44Representation volumeElement * Γ v = -(Γ v * cl44Representation volumeElement) := by
  apply LinearMap.ext
  rintro ⟨s, t⟩
  change cl44Representation volumeElement (v * t, zornConj v * s) =
    -(Γ v (cl44Representation volumeElement (s, t)))
  rw [volumeElement_action, volumeElement_action]
  change (L v t, -(L (zornConj v) s)) = -(L v (-t), L (zornConj v) s)
  simp only [map_neg, Prod.neg_mk, neg_neg]

end InfoGeometry.Canonical.ZornVolumeAction
