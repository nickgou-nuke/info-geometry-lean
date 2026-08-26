import Mathlib.Tactic
import InfoGeometry.Algebra.H3ZornJordanIdentity
import InfoGeometry.Algebra.H3ZornCubicNormStructure
import InfoGeometry.Exceptional.Freudenthal
import InfoGeometry.Exceptional.FreudenthalAction

/-!
# Freudenthal quartic for the native `H3Zorn ℝ` cubic datum

This owner specializes the existing abstract Freudenthal construction.  It
keeps the cubic Jordan norm and the quartic charge invariant distinct and
does not postulate an exceptional-group representation.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Algebra.H3ZornFreudenthal

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Exceptional.Freudenthal

def quarticInvariant
    (Q : FreudenthalCharge (H3Zorn ℝ)) : ℝ :=
  FreudenthalCharge.quarticInvariant h3zornCubicJordanDatum Q

def symplecticForm
    (Q₁ Q₂ : FreudenthalCharge (H3Zorn ℝ)) : ℝ :=
  FreudenthalCharge.symplecticForm h3zornCubicJordanDatum Q₁ Q₂

def Regular (Q : FreudenthalCharge (H3Zorn ℝ)) : Prop :=
  FreudenthalRegular h3zornCubicJordanDatum Q

def Boundary (Q : FreudenthalCharge (H3Zorn ℝ)) : Prop :=
  FreudenthalBoundary h3zornCubicJordanDatum Q

theorem symplecticForm_expanded
    (Q₁ Q₂ : FreudenthalCharge (H3Zorn ℝ)) :
    symplecticForm Q₁ Q₂ =
      Q₁.alpha * Q₂.beta - Q₁.beta * Q₂.alpha
        + H3Zorn.traceBilin Q₁.x Q₂.y
        - H3Zorn.traceBilin Q₁.y Q₂.x := by
  rfl

@[simp]
theorem adjointQuad_zero :
    H3Zorn.adjointQuad (0 : H3Zorn ℝ) = 0 := by
  simpa using
    (H3Zorn.adjointQuad_smul (R := ℝ) (0 : ℝ) (1 : H3Zorn ℝ))

@[simp] theorem symplecticForm_self
    (Q : FreudenthalCharge (H3Zorn ℝ)) :
    symplecticForm Q Q = 0 := by
  exact FreudenthalCharge.symplectic_form_alternating
    h3zornCubicJordanDatum Q

theorem symplecticForm_skew
    (Q₁ Q₂ : FreudenthalCharge (H3Zorn ℝ)) :
    symplecticForm Q₂ Q₁ = -symplecticForm Q₁ Q₂ := by
  exact FreudenthalCharge.symplectic_form_skew
    h3zornCubicJordanDatum Q₁ Q₂

@[simp] theorem quarticInvariant_zeroCharge :
    quarticInvariant (zeroCharge (H3Zorn ℝ)) = 0 := by
  exact FreudenthalCharge.quarticInvariant_zeroCharge
    h3zornCubicJordanDatum H3Zorn.normCubic_zero adjointQuad_zero

def scalarCharge (α β : ℝ) : FreudenthalCharge (H3Zorn ℝ) where
  alpha := α
  beta := β
  x := 0
  y := 0

def electricCharge (α : ℝ) (X : H3Zorn ℝ) :
    FreudenthalCharge (H3Zorn ℝ) where
  alpha := α
  beta := 0
  x := X
  y := 0

def magneticCharge (β : ℝ) (Y : H3Zorn ℝ) :
    FreudenthalCharge (H3Zorn ℝ) where
  alpha := 0
  beta := β
  x := 0
  y := Y

theorem quarticInvariant_scalarCharge (α β : ℝ) :
    quarticInvariant (scalarCharge α β) = (α * β) ^ 2 := by
  change
    (α * β - H3Zorn.traceBilin (0 : H3Zorn ℝ) 0) ^ 2 -
        4 * (α * H3Zorn.normCubic 0 + β * H3Zorn.normCubic 0 -
          H3Zorn.traceBilin (H3Zorn.adjointQuad 0)
            (H3Zorn.adjointQuad 0)) = (α * β) ^ 2
  rw [H3Zorn.normCubic_zero, adjointQuad_zero,
    H3Zorn.traceBilin_zero_left]
  ring_nf

/- A scalar charge is Freudenthal-regular exactly when both scalar
   coordinates are nonzero. -/
theorem regular_scalarCharge_iff (α β : ℝ) :
    Regular (scalarCharge α β) ↔ α ≠ 0 ∧ β ≠ 0 := by
  unfold Regular FreudenthalRegular
  change quarticInvariant (scalarCharge α β) ≠ 0 ↔ α ≠ 0 ∧ β ≠ 0
  rw [quarticInvariant_scalarCharge]
  constructor
  · intro h
    have hprod : α * β ≠ 0 := by
      intro hz
      apply h
      simp [hz]
    exact mul_ne_zero_iff.mp hprod
  · rintro ⟨hα, hβ⟩
    exact pow_ne_zero 2 (mul_ne_zero hα hβ)

theorem boundary_scalarCharge_iff (α β : ℝ) :
    Boundary (scalarCharge α β) ↔
      (α = 0 ∨ β = 0) ∧ (α ≠ 0 ∨ β ≠ 0) := by
  unfold Boundary FreudenthalBoundary
  change
    quarticInvariant (scalarCharge α β) = 0 ∧
      scalarCharge α β ≠ zeroCharge (H3Zorn ℝ) ↔ _
  rw [quarticInvariant_scalarCharge]
  by_cases hα : α = 0 <;> by_cases hβ : β = 0 <;>
    simp [hα, hβ, scalarCharge, zeroCharge]

theorem quarticInvariant_electricCharge (α : ℝ) (X : H3Zorn ℝ) :
    quarticInvariant (electricCharge α X) =
      -4 * (α * H3Zorn.normCubic X) := by
  change
    (α * 0 - H3Zorn.traceBilin X 0) ^ 2 -
        4 * (α * H3Zorn.normCubic X + 0 * H3Zorn.normCubic 0 -
          H3Zorn.traceBilin (H3Zorn.adjointQuad X)
            (H3Zorn.adjointQuad 0)) = -4 * (α * H3Zorn.normCubic X)
  rw [H3Zorn.normCubic_zero, adjointQuad_zero,
    H3Zorn.traceBilin_zero_right, H3Zorn.traceBilin_zero_right]
  ring

theorem regular_electricCharge_iff (α : ℝ) (X : H3Zorn ℝ) :
    Regular (electricCharge α X) ↔
      α ≠ 0 ∧ H3Zorn.normCubic X ≠ 0 := by
  unfold Regular FreudenthalRegular
  change quarticInvariant (electricCharge α X) ≠ 0 ↔ _
  rw [quarticInvariant_electricCharge]
  constructor
  · intro h
    constructor
    · intro hα
      apply h
      simp [hα]
    · intro hN
      apply h
      simp [hN]
  · rintro ⟨hα, hN⟩
    exact mul_ne_zero (by norm_num : (-4 : ℝ) ≠ 0) (mul_ne_zero hα hN)

theorem quarticInvariant_magneticCharge (β : ℝ) (Y : H3Zorn ℝ) :
    quarticInvariant (magneticCharge β Y) =
      -4 * (β * H3Zorn.normCubic Y) := by
  change
    (0 * β - H3Zorn.traceBilin 0 Y) ^ 2 -
        4 * (0 * H3Zorn.normCubic 0 + β * H3Zorn.normCubic Y -
          H3Zorn.traceBilin (H3Zorn.adjointQuad 0)
            (H3Zorn.adjointQuad Y)) = -4 * (β * H3Zorn.normCubic Y)
  rw [H3Zorn.normCubic_zero, adjointQuad_zero,
    H3Zorn.traceBilin_zero_left, H3Zorn.traceBilin_zero_left]
  ring_nf

theorem regular_magneticCharge_iff (β : ℝ) (Y : H3Zorn ℝ) :
    Regular (magneticCharge β Y) ↔
      β ≠ 0 ∧ H3Zorn.normCubic Y ≠ 0 := by
  unfold Regular FreudenthalRegular
  change quarticInvariant (magneticCharge β Y) ≠ 0 ↔ _
  rw [quarticInvariant_magneticCharge]
  constructor
  · intro h
    constructor
    · intro hβ
      apply h
      simp [hβ]
    · intro hN
      apply h
      simp [hN]
  · rintro ⟨hβ, hN⟩
    exact mul_ne_zero (by norm_num : (-4 : ℝ) ≠ 0) (mul_ne_zero hβ hN)

theorem cubicNorm_from_quartic (X : H3Zorn ℝ) :
    H3Zorn.normCubic X =
      (-1 / 4 : ℝ) * quarticInvariant (electricCharge 1 X) := by
  rw [quarticInvariant_electricCharge]
  ring

theorem unit_electric_quartic :
    quarticInvariant (electricCharge 1 (1 : H3Zorn ℝ)) = -4 := by
  rw [quarticInvariant_electricCharge]
  simp

theorem cubic_adjoint_identity (X : H3Zorn ℝ) :
    H3Zorn.adjointQuad (H3Zorn.adjointQuad X) =
      H3Zorn.normCubic X • X :=
  H3Zorn.adjointQuad_adjointQuad X

abbrev InvariantAction (G : Type*) [Group G] :=
  FreudenthalInvariantAction G (H3Zorn ℝ) h3zornCubicJordanDatum

namespace InvariantAction

variable {G : Type*} [Group G]
variable (A : InvariantAction G)

@[simp] theorem quarticInvariant_act
    (g : G) (Q : FreudenthalCharge (H3Zorn ℝ)) :
    quarticInvariant (A.act g Q) = quarticInvariant Q := by
  exact A.preserves_quarticInvariant g Q

@[simp] theorem symplecticForm_act
    (g : G) (Q₁ Q₂ : FreudenthalCharge (H3Zorn ℝ)) :
    symplecticForm (A.act g Q₁) (A.act g Q₂) = symplecticForm Q₁ Q₂ := by
  exact A.preserves_symplecticForm g Q₁ Q₂

theorem regular_iff
    (g : G) (Q : FreudenthalCharge (H3Zorn ℝ)) :
    Regular (A.act g Q) ↔ Regular Q := by
  exact FreudenthalInvariantAction.regular_iff A g Q

theorem boundary_iff
    (g : G) (Q : FreudenthalCharge (H3Zorn ℝ)) :
    Boundary (A.act g Q) ↔ Boundary Q := by
  exact FreudenthalInvariantAction.boundary_iff A g Q

end InvariantAction

end InfoGeometry.Algebra.H3ZornFreudenthal
