import Mathlib.Tactic
import InfoGeometry.Exceptional.Freudenthal

/-!
# InfoGeometry.Exceptional.FreudenthalAction

Abstract non-compact transformation layer for Freudenthal charge space.

This file does **not** construct `E₇(7)` or a specific matrix model.  It only
packages an action on the abstract Freudenthal charge space together with the
witnesses needed to preserve the two fundamental invariants already present in
the repo:

* the Freudenthal symplectic pairing;
* the Freudenthal quartic invariant.

The action is theorem-safe and suitable as a target for later concrete
instantiations.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

open scoped BigOperators

/-- The zero Freudenthal charge. -/
def zeroCharge (J : Type*) [AddCommGroup J] [Module ℝ J] : FreudenthalCharge J where
  alpha := 0
  beta := 0
  x := 0
  y := 0

theorem zeroCharge_eq_iff
    {J : Type*} [AddCommGroup J] [Module ℝ J]
    (Q : FreudenthalCharge J) :
    Q = zeroCharge J ↔ Q.alpha = 0 ∧ Q.beta = 0 ∧ Q.x = 0 ∧ Q.y = 0 := by
  constructor
  · intro h
    subst h
    exact ⟨rfl, rfl, rfl, rfl⟩
  · rintro ⟨hα, hβ, hx, hy⟩
    cases Q with
    | mk alpha beta x y =>
        simp only at hα hβ hx hy
        simp [zeroCharge, hα, hβ, hx, hy]

/-- Freudenthal regularity: nonzero quartic invariant. -/
def FreudenthalRegular
    {J : Type*} [AddCommGroup J] [Module ℝ J]
    (D : CubicJordanDatum J) (Q : FreudenthalCharge J) : Prop :=
  FreudenthalCharge.quarticInvariant D Q ≠ 0

/-- Freudenthal boundary: zero quartic invariant and nonzero charge. -/
def FreudenthalBoundary
    {J : Type*} [AddCommGroup J] [Module ℝ J]
    (D : CubicJordanDatum J) (Q : FreudenthalCharge J) : Prop :=
  FreudenthalCharge.quarticInvariant D Q = 0 ∧ Q ≠ zeroCharge J

/-- Abstract transformation action on the Freudenthal charge space. -/
structure FreudenthalInvariantAction
    (G : Type*) [Group G]
    (J : Type*) [AddCommGroup J] [Module ℝ J]
    (D : CubicJordanDatum J) where
  /-- Group action on Freudenthal charges. -/
  act : G → FreudenthalCharge J → FreudenthalCharge J

  /-- Identity acts trivially. -/
  act_one : act 1 = id

  /-- Multiplication acts by composition. -/
  act_mul : ∀ g h : G, act (g * h) = fun Q => act g (act h Q)

  /-- The action preserves the Freudenthal symplectic pairing. -/
  preserves_symplecticForm :
    ∀ g : G, ∀ Q₁ Q₂ : FreudenthalCharge J,
      FreudenthalCharge.symplecticForm D (act g Q₁) (act g Q₂) =
        FreudenthalCharge.symplecticForm D Q₁ Q₂

  /-- The action preserves the Freudenthal quartic invariant. -/
  preserves_quarticInvariant :
    ∀ g : G, ∀ Q : FreudenthalCharge J,
      FreudenthalCharge.quarticInvariant D (act g Q) =
        FreudenthalCharge.quarticInvariant D Q

  /-- The zero charge is fixed. -/
  preserves_zeroCharge :
    ∀ g : G, act g (zeroCharge J) = zeroCharge J

namespace FreudenthalInvariantAction

variable {G : Type*} [Group G]
variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable {D : CubicJordanDatum J}
variable (A : FreudenthalInvariantAction G J D)

/-! ### 2a. Invariant actions lift to the Heisenberg carrier -/

/-- The lift of an invariant Freudenthal action to the central Heisenberg carrier. -/
def actHeisenberg
    (g : G) (X : HeisenbergElement J) : HeisenbergElement J where
  charge := A.act g X.charge
  center := X.center

@[simp] theorem actHeisenberg_charge
    (g : G) (X : HeisenbergElement J) :
    (A.actHeisenberg g X).charge = A.act g X.charge := rfl

@[simp] theorem actHeisenberg_center
    (g : G) (X : HeisenbergElement J) :
    (A.actHeisenberg g X).center = X.center := rfl

@[simp] theorem actHeisenberg_one
    (X : HeisenbergElement J) :
    A.actHeisenberg 1 X = X := by
  apply HeisenbergElement.ext
  · simpa [actHeisenberg] using congrFun A.act_one X.charge
  · rfl

theorem actHeisenberg_mul
    (g h : G) (X : HeisenbergElement J) :
    A.actHeisenberg (g * h) X =
      A.actHeisenberg g (A.actHeisenberg h X) := by
  apply HeisenbergElement.ext
  · simpa [actHeisenberg] using congrFun (A.act_mul g h) X.charge
  · rfl

/-- The lifted action preserves the Freudenthal Heisenberg bracket. -/
theorem actHeisenberg_bracket
    (g : G) (X Y : HeisenbergElement J) :
    HeisenbergElement.bracket D
        (A.actHeisenberg g X) (A.actHeisenberg g Y) =
      HeisenbergElement.bracket D X Y := by
  apply HeisenbergElement.ext
  · rfl
  · exact A.preserves_symplecticForm g X.charge Y.charge

/-- Readback: the action preserves the symplectic pairing. -/
@[simp]
theorem symplecticForm_act
    (g : G) (Q₁ Q₂ : FreudenthalCharge J) :
    FreudenthalCharge.symplecticForm D (A.act g Q₁) (A.act g Q₂) =
      FreudenthalCharge.symplecticForm D Q₁ Q₂ :=
  A.preserves_symplecticForm g Q₁ Q₂

/-- Readback: the action preserves the quartic invariant. -/
@[simp]
theorem quarticInvariant_act
    (g : G) (Q : FreudenthalCharge J) :
    FreudenthalCharge.quarticInvariant D (A.act g Q) =
      FreudenthalCharge.quarticInvariant D Q :=
  A.preserves_quarticInvariant g Q

/-- Readback: the zero charge is fixed. -/
@[simp]
theorem act_zeroCharge (g : G) :
    A.act g (zeroCharge J) = zeroCharge J :=
  A.preserves_zeroCharge g

/-- Regularity is preserved by the action. -/
theorem regular_iff
    (g : G) (Q : FreudenthalCharge J) :
    FreudenthalRegular D (A.act g Q) ↔ FreudenthalRegular D Q := by
  unfold FreudenthalRegular
  rw [A.preserves_quarticInvariant]

/-- The action sends zero to zero iff it preserves zero and is invertible. -/
theorem act_eq_zero_iff
    (g : G) (Q : FreudenthalCharge J) :
    A.act g Q = zeroCharge J ↔ Q = zeroCharge J := by
  constructor
  · intro hzero
    have hback := congrArg (A.act g⁻¹) hzero
    have hleft : A.act g⁻¹ (A.act g Q) = Q := by
      have hmul := congrArg (fun f : FreudenthalCharge J → FreudenthalCharge J => f Q)
        (A.act_mul (g⁻¹) g)
      have h1 : A.act (g⁻¹ * g) Q = Q := by
        simp [A.act_one]
      calc
        A.act g⁻¹ (A.act g Q) = A.act (g⁻¹ * g) Q := hmul.symm
        _ = Q := h1
    have hzero' : A.act g⁻¹ (zeroCharge J) = zeroCharge J := A.act_zeroCharge (g⁻¹)
    calc
      Q = A.act g⁻¹ (A.act g Q) := hleft.symm
      _ = A.act g⁻¹ (zeroCharge J) := hback
      _ = zeroCharge J := hzero'
  · intro hzero
    rw [hzero]
    simp [A.act_zeroCharge]

/-- Boundary status is preserved by the action. -/
theorem boundary_iff
    (g : G) (Q : FreudenthalCharge J) :
    FreudenthalBoundary D (A.act g Q) ↔ FreudenthalBoundary D Q := by
  unfold FreudenthalBoundary
  constructor
  · intro h
    rcases h with ⟨hQ, hneq⟩
    constructor
    · rw [← A.preserves_quarticInvariant]
      exact hQ
    · intro hzero
      apply hneq
      exact (A.act_eq_zero_iff (D := D) g Q).2 hzero
  · intro h
    rcases h with ⟨hQ, hneq⟩
    constructor
    · rw [A.preserves_quarticInvariant]
      exact hQ
    · intro hzero
      apply hneq
      exact (A.act_eq_zero_iff (D := D) g Q).1 hzero

/-- The action preserves the zero-charge complement. -/
theorem act_ne_zero_iff
    (g : G) (Q : FreudenthalCharge J) :
    A.act g Q ≠ zeroCharge J ↔ Q ≠ zeroCharge J := by
  constructor
  · intro hQ hzero
    apply hQ
    exact (A.act_eq_zero_iff (D := D) g Q).2 hzero
  · intro hQ hzero
    apply hQ
    exact (A.act_eq_zero_iff (D := D) g Q).1 hzero

end FreudenthalInvariantAction

end InfoGeometry.Exceptional.Freudenthal
