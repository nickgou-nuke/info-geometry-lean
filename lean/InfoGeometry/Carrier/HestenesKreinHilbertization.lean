/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Carrier.HestenesKrein
import Mathlib.Analysis.InnerProductSpace.Basic

/-! # Positive real Hilbert structure induced by a Hestenes–Krein symmetry

The Krein class supplies a positive quadratic form `x ↦ K(x, J x)`, but does
not require its associated bilinear form to be symmetric. Symmetrizing that
bilinear form preserves its diagonal and yields a native real inner-product
space without changing the underlying vector carrier.
-/

noncomputable section

namespace InfoGeometry.Carrier.HestenesKreinSpace

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The symmetric part of the positive bilinear pairing induced by the Krein
form and its fundamental involution. Its diagonal is `krein_form x (J x)`. -/
def positiveBilinForm (K : HestenesKreinSpace V) : LinearMap.BilinForm ℝ V :=
  (1 / 2 : ℝ) •
    (K.krein_form.compRight K.J + (K.krein_form.compRight K.J).flip)

theorem positiveBilinForm_symm (K : HestenesKreinSpace V) (x y : V) :
    K.positiveBilinForm x y = K.positiveBilinForm y x := by
  simp [positiveBilinForm, add_comm]

theorem positiveBilinForm_apply_self (K : HestenesKreinSpace V) (x : V) :
    K.positiveBilinForm x x = K.krein_form x (K.J x) := by
  simp [positiveBilinForm]
  ring

theorem positiveBilinForm_pos (K : HestenesKreinSpace V) {x : V} (hx : x ≠ 0) :
    0 < K.positiveBilinForm x x := by
  rw [K.positiveBilinForm_apply_self]
  exact K.induced_hilbert_identity x hx

/-- A native positive-definite real inner-product core on the Krein carrier,
using the symmetric part of its induced positive pairing. -/
def inducedInnerProductCore (K : HestenesKreinSpace V) :
    InnerProductSpace.Core ℝ V where
  inner := fun x y => K.positiveBilinForm x y
  conj_inner_symm := by
    intro x y
    simpa using (K.positiveBilinForm_symm x y).symm
  re_inner_nonneg := by
    intro x
    by_cases hx : x = 0
    · subst x
      simp
    · change 0 ≤ K.positiveBilinForm x x
      exact le_of_lt (K.positiveBilinForm_pos hx)
  add_left := by
    intro x y z
    exact LinearMap.congr_fun (K.positiveBilinForm.map_add x y) z
  smul_left := by
    intro x y r
    change K.positiveBilinForm (r • x) y = r * K.positiveBilinForm x y
    exact LinearMap.congr_fun (K.positiveBilinForm.map_smul r x) y
  definite := by
    intro x hx
    by_contra hne
    change K.positiveBilinForm x x = 0 at hx
    have hpos := K.positiveBilinForm_pos hne
    rw [hx] at hpos
    exact (lt_self_iff_false 0).mp hpos

end InfoGeometry.Carrier.HestenesKreinSpace

end
