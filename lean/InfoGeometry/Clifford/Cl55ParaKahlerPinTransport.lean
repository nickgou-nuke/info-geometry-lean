/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.Cl55ParaKahlerMetric
import InfoGeometry.Clifford.Cl55RealSplitPinNullPairAction

/-!
# Orthogonal transport, not fixed-polarization invariance

The selected negative-vector real-Pin lift preserves the positive metric.
It does not preserve the fixed symplectic form. General Q55 isometries
transport the para-complex structure by conjugation; the skew form follows
that transported structure. This is the algebraic fiber layer, not affine
deck descent, a spinor bundle or a holonomy theorem.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl55ParaKahlerPinTransport

open Clifford55 Cl55ParaKahlerMetric ParaKahler55SUSYClosure

/-- Polarization is functorial for the actual native quadratic isometry. -/
theorem polar_isometry (e : Q55.IsometryEquiv Q55) (u v : V55) :
    Q55.polarBilin (e u) (e v) = Q55.polarBilin u v := by
  change Q55 (e u + e v) - Q55 (e u) - Q55 (e v) = _
  rw [← map_add, e.map_app, e.map_app, e.map_app]
  rfl

/-- Transport K as well as the form; do not assume an orthogonal map fixes K. -/
theorem omega_isometry_transport (e : Q55.IsometryEquiv Q55) (u v : V55) :
    diagonalOmega (e.symm u) (e.symm v) =
      -Q55.polarBilin u (e (paraKahlerK (e.symm v))) := by
  rw [diagonalOmega_eq_neg_polar_para]
  have h := polar_isometry e (e.symm u) (paraKahlerK (e.symm v))
  simpa using congrArg Neg.neg h.symm

theorem negativeReflection_positiveMetric (i : Fin 5) (u v : V55) :
    positiveMetric (negativeReflection i u) (negativeReflection i v) =
      positiveMetric u v := by
  have hc : ((negativeReflection i v).1, -(negativeReflection i v).2) =
      negativeReflection i (v.1, -v.2) := by
    apply Prod.ext
    · rfl
    · funext j
      by_cases h : j = i <;> simp [negativeReflection, h]
  rw [positiveMetric_eq_polar_sign, positiveMetric_eq_polar_sign, hc]
  exact polar_isometry (negativeReflectionIsometry i) u (v.1, -v.2)

/-- The positivity statement concerns the existing corrected real split-Pin lift. -/
theorem fNegRealPin_positiveMetric (i : Fin 5) (u v : V55) :
    positiveMetric (realSplitPinNativeOrthogonalAction (fNegRealPin i) u)
      (realSplitPinNativeOrthogonalAction (fNegRealPin i) v) = positiveMetric u v := by
  rw [realSplitPinNativeOrthogonalAction_apply, realSplitPinOrthogonalAction_fNegRealPin]
  exact negativeReflection_positiveMetric i u v

/-- A single reflected Witt pair obstructs invariance of the chosen skew form. -/
theorem negativeReflection_not_symplectic (i : Fin 5) :
    ¬ ∀ u v, diagonalOmega (negativeReflection i u) (negativeReflection i v) =
      diagonalOmega u v := by
  intro h
  have he := h (e_pos i) (f_neg i)
  rw [negativeReflection_apply_e_pos, negativeReflection_apply_f_neg] at he
  simp only [map_neg, diagonalOmega_e_pos] at he
  norm_num [f_neg] at he

/-- Unlike exchange of all five pairs, the glide's one-pair reflection is not
anti-symplectic on the entire ten-dimensional space either. -/
theorem negativeReflection_zero_not_antisymplectic :
    ¬ ∀ u v, diagonalOmega (negativeReflection 0 u) (negativeReflection 0 v) =
      -diagonalOmega u v := by
  intro h
  have he := h (e_pos 1) (f_neg 1)
  simp only [diagonalOmega_eq_neg_polar_para, polar_apply] at he
  norm_num [negativeReflection, e_pos, f_neg, paraKahlerK, fst55, snd55,
    Fin.sum_univ_succ] at he

end InfoGeometry.Clifford.Cl55ParaKahlerPinTransport
