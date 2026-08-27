/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib
import InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction
import InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis
import InfoGeometry.Exceptional.G2SimpleRootPhaseReadback

namespace InfoGeometry.Exceptional.G2CircularRootLabelTransport

open InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction
open InfoGeometry.Exceptional.G2DiagonalPhase

/-!
# Typed transport between the circular and `G₂` root carriers

The circular state carrier has eight labels, whereas the signed `G₂` root
carrier has twelve. Consequently this owner records an injection, not an
equivalence. A concrete choice of labels is data supplied by a later owner.
-/

abbrev CircularLabel := Fin 8
abbrev RootLabel := G2CoordinateRoot

structure RootLabelTransport where
  label : CircularLabel → RootLabel
  injective : Function.Injective label

def circularRootLabel : CircularLabel → RootLabel
  | 0 => signedRootCoordinate (false, .alpha)
  | 1 => signedRootCoordinate (false, .beta)
  | 2 => signedRootCoordinate (false, .alpha_add_beta)
  | 3 => signedRootCoordinate (false, .two_alpha_beta)
  | 4 => signedRootCoordinate (false, .three_alpha_beta)
  | 5 => signedRootCoordinate (false, .three_alpha_two_beta)
  | 6 => signedRootCoordinate (true, .alpha)
  | 7 => signedRootCoordinate (true, .beta)

theorem circularRootLabel_injective : Function.Injective circularRootLabel := by
  intro i j h
  revert i j
  decide

def circularRootTransport : RootLabelTransport where
  label := circularRootLabel
  injective := circularRootLabel_injective

theorem s1_transport_alpha :
    s1Root (circularRootTransport.label 0) =
      circularRootTransport.label 6 := by
  exact s1Root_alpha1_readback

theorem s2_transport_beta :
    s2Root (circularRootTransport.label 1) =
      circularRootTransport.label 7 := by
  exact s2Root_alpha2_readback

theorem circularRootTransport_not_s1_stable :
    ¬ (∀ i : CircularLabel, ∃ j : CircularLabel,
      s1Root (circularRootTransport.label i) = circularRootTransport.label j) := by
  native_decide

theorem no_circular_root_equivalence :
    ¬ Nonempty (CircularLabel ≃ RootLabel) := by
  rintro ⟨e⟩
  have hcard := Fintype.card_congr e
  have hroot : Fintype.card RootLabel = 12 := by
    native_decide
  rw [hroot] at hcard
  norm_num at hcard

def restrictToCircular
    {R : Type*} [Semiring R]
    (t : RootLabelTransport) : (RootLabel → R) →ₗ[R] (CircularLabel → R) where
  toFun f i := f (t.label i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem restrictToCircular_apply
    {R : Type*} [Semiring R]
    (t : RootLabelTransport) (f : RootLabel → R) (i : CircularLabel) :
    restrictToCircular t f i = f (t.label i) := rfl

noncomputable def extendFromCircular
    {R : Type*} [Semiring R]
    (t : RootLabelTransport) : (CircularLabel → R) →ₗ[R] (RootLabel → R) where
  toFun f r := ∑ i : CircularLabel, if t.label i = r then f i else 0
  map_add' f g := by
    funext r
    dsimp
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  map_smul' c f := by
    funext r
    dsimp
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp

@[simp] theorem extendFromCircular_apply
    {R : Type*} [Semiring R]
    (t : RootLabelTransport) (f : CircularLabel → R) (r : RootLabel) :
    extendFromCircular t f r =
      ∑ i : CircularLabel, if t.label i = r then f i else 0 := rfl

theorem restrict_extend
    {R : Type*} [Semiring R]
    (t : RootLabelTransport) (f : CircularLabel → R) :
    restrictToCircular t (extendFromCircular t f) = f := by
  funext i
  classical
  simp only [restrictToCircular_apply, extendFromCircular_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    rw [if_neg]
    intro hlabel
    exact hji (t.injective hlabel)
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

theorem extendFromCircular_injective
    {R : Type*} [Semiring R]
    (t : RootLabelTransport) :
    Function.Injective (extendFromCircular (R := R) t) := by
  intro f g h
  have h' := congrArg (restrictToCircular (R := R) t) h
  simpa [restrict_extend] using h'

noncomputable def transportOperator
    {R : Type*} [Semiring R]
    (t : RootLabelTransport)
    (T : Module.End R (CircularLabel → R)) :
    Module.End R (RootLabel → R) :=
  (extendFromCircular t).comp (T.comp (restrictToCircular t))

theorem transportOperator_intertwines
    {R : Type*} [Semiring R]
    (t : RootLabelTransport)
    (T : Module.End R (CircularLabel → R))
    (f : CircularLabel → R) :
    transportOperator t T (extendFromCircular t f) =
      extendFromCircular t (T f) := by
  simp [transportOperator, restrict_extend]

theorem transportOperator_square_zero_on_image
    {R : Type*} [Ring R]
    (t : RootLabelTransport)
    (T : Module.End R (CircularLabel → R))
    (hT : T * T = 0)
    (f : CircularLabel → R) :
    transportOperator t T (transportOperator t T (extendFromCircular t f)) = 0 := by
  rw [transportOperator_intertwines, transportOperator_intertwines]
  have hTf : T (T f) = 0 := by
    exact congrArg (fun S => S f) hT
  rw [hTf]
  simp

theorem transportOperator_bivector_on_image
    {R : Type*} [Ring R]
    (t : RootLabelTransport)
    (T : Module.End R (CircularLabel → R))
    (hT : T * T = -(1 : Module.End R (CircularLabel → R)))
    (f : CircularLabel → R) :
    transportOperator t T (transportOperator t T (extendFromCircular t f)) =
      -extendFromCircular t f := by
  rw [transportOperator_intertwines, transportOperator_intertwines]
  have hTf : T (T f) = -(1 : Module.End R (CircularLabel → R)) f := by
    exact congrArg (fun S => S f) hT
  rw [hTf]
  simpa using (extendFromCircular t).map_neg f

theorem label_ne_of_ne
    (t : RootLabelTransport) {i j : CircularLabel} (h : i ≠ j) :
    t.label i ≠ t.label j := by
  intro h'
  exact h (t.injective h')

end InfoGeometry.Exceptional.G2CircularRootLabelTransport
