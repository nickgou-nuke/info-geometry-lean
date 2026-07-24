import Mathlib
import Mathlib.Algebra.Star.Basic
import Mathlib.CategoryTheory.Category.Preorder

namespace InfoGeometry.Categorical.CategoricalZetaMobius

open CategoryTheory

section NoncommutativePoset

variable (A : Type*) [Ring A] [StarRing A]

/-- A self-adjoint projector in a star-ring (e.g. von Neumann algebra, C*-algebra). -/
structure Projector where
  p : A
  is_proj : p * p = p
  is_self_adjoint : star p = p

namespace Projector

variable {A}

/-- The quantum ordering relation on projectors: P ≤ Q iff P * Q = P. -/
def le (P Q : Projector A) : Prop :=
  P.p * Q.p = P.p

instance : LE (Projector A) := ⟨le⟩

theorem le_refl (P : Projector A) : P ≤ P :=
  P.is_proj

theorem le_trans (P Q R : Projector A) (hPQ : P ≤ Q) (hQR : Q ≤ R) : P ≤ R := by
  dsimp [LE.le, le] at *
  calc
    P.p * R.p = (P.p * Q.p) * R.p := by rw [hPQ]
    _ = P.p * (Q.p * R.p) := by rw [mul_assoc]
    _ = P.p * Q.p := by rw [hQR]
    _ = P.p := hPQ

theorem le_antisymm (P Q : Projector A) (hPQ : P ≤ Q) (hQP : Q ≤ P) : P = Q := by
  dsimp [LE.le, le] at *
  have hP_eq : P.p = star P.p := P.is_self_adjoint.symm
  have hQ_eq : Q.p = star Q.p := Q.is_self_adjoint.symm
  have h_conj : star (P.p * Q.p) = star P.p := by rw [hPQ]
  rw [star_mul, P.is_self_adjoint, Q.is_self_adjoint] at h_conj
  have h_eq : P.p = Q.p := by
    calc
      P.p = Q.p * P.p := h_conj.symm
      _ = Q.p := hQP
  rcases P with ⟨p_val, p_proj, p_sa⟩
  rcases Q with ⟨q_val, q_proj, q_sa⟩
  dsimp at h_eq
  subst h_eq
  rfl

instance : PartialOrder (Projector A) where
  le := le
  le_refl := le_refl
  le_trans := le_trans
  le_antisymm := le_antisymm

end Projector

end NoncommutativePoset

section LeinsterZeta

open Classical

variable {C : Type*} [Category C]

/-- The categorical zeta function of a category C.
    For any pair of objects X and Y, it is the cardinality of the morphism set Hom X Y. -/
noncomputable def categoryZeta (X Y : C) (inst : _root_.Fintype (X ⟶ Y)) : ℤ :=
  (@_root_.Fintype.card (X ⟶ Y) inst : ℤ)

variable {α : Type*} [PartialOrder α]

/-- Leinster's categorical zeta function for the preorder category.
    Returns 1 if there is a morphism (X ≤ Y) and 0 otherwise. -/
noncomputable def leinsterZeta (X Y : α) : ℤ :=
  if X ≤ Y then 1 else 0

/-- Duality Theorem: Leinster's category-theoretic zeta function on a poset category
    coincides exactly with the poset's incidence algebra zeta function. -/
theorem categoryZeta_poset_eq (X Y : α) (inst : _root_.Fintype (X ⟶ Y)) :
    categoryZeta X Y inst = leinsterZeta X Y := by
  dsimp [categoryZeta, leinsterZeta]
  split_ifs with h
  · have h_hom : X ⟶ Y := ⟨⟨h⟩⟩
    haveI : Unique (X ⟶ Y) := ⟨⟨h_hom⟩, fun x => Subsingleton.elim x h_hom⟩
    have h_card : @_root_.Fintype.card (X ⟶ Y) inst = 1 := _root_.Fintype.card_unique
    rw [h_card]
    rfl
  · have h_empty : IsEmpty (X ⟶ Y) := ⟨fun f => h f.down.down⟩
    have h_card : @_root_.Fintype.card (X ⟶ Y) inst = 0 := _root_.Fintype.card_eq_zero
    rw [h_card]
    rfl

end LeinsterZeta

end InfoGeometry.Categorical.CategoricalZetaMobius
