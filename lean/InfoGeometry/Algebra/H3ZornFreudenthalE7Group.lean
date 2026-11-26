/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.H3ZornFreudenthalLeviAction
import InfoGeometry.Algebra.H3ZornFreudenthalScaling
import InfoGeometry.Algebra.H3ZornMcCrimmonDualIdentity
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Concrete 56D Freudenthal `E₇(7)` Group Realization on `H3Zorn ℝ`

This module constructs the concrete `E₇(7)` group generators acting on the
56-dimensional split-Albert Freudenthal charge space
`Charge := FreudenthalCharge (H3Zorn ℝ)` and proves that they preserve both
`symplecticForm` and `quarticInvariant`.

Main results:
1. `ChargeGL := LinearMap.GeneralLinearGroup ℝ Charge` and `glLevi := leviChargeGL`.
2. Concrete generators as `Charge ≃ₗ[ℝ] Charge` and `ChargeGL`:
   - `freudenthalInversion` (`J⟨α, β, x, y⟩ = ⟨-β, α, -y, x⟩`) with `J² = -1`;
   - `freudenthalUpperTrans (A : H3Zorn ℝ)` (`t₊(A)`) and `glUpperTrans`;
   - `freudenthalLowerTrans (B : H3Zorn ℝ)` (`t₋(B) = J * t₊(-B) * J⁻¹`) and `glLowerTrans`.
3. Kernel-checked invariance of both `symplecticForm` and `quarticInvariant` for
   `J`, `t₊(A)` (via 1st-order `s`-expansion, `mccrimmon_identity_19`, and
   `is_const_of_deriv_eq_zero`), and `t₋(B)`.
4. Subgroup packaging `freudenthalE7Group ≤ freudenthalInvariantSubgroup`,
   `InvariantAction` instances, and Levi/inversion conjugation laws.
5. Concrete non-triviality, non-commutativity, and sign-sanity witnesses.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Algebra.H3ZornFreudenthal

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Exceptional.Freudenthal

/-- The real general linear group `GL(Charge) ≅ GL₅₆(ℝ)`. -/
abbrev ChargeGL := LinearMap.GeneralLinearGroup ℝ Charge

/-- The `Str₀(H₃(𝕆_s)) = E₆(6)` Levi embedding into `ChargeGL`. -/
abbrev glLevi : h3zornReducedStructureGroup →* ChargeGL := leviChargeGL

section AuxiliaryCubicLemmas

private theorem crossProduct_zero_left (X : H3Zorn ℝ) :
    H3Zorn.crossProduct (0 : H3Zorn ℝ) X = 0 := by
  rw [H3Zorn.crossProduct, zero_add, adjointQuad_zero]
  module

private theorem crossProduct_zero_right (X : H3Zorn ℝ) :
    H3Zorn.crossProduct X (0 : H3Zorn ℝ) = 0 := by
  rw [H3Zorn.crossProduct_symm, crossProduct_zero_left]

@[simp] private theorem charge_neg_alpha (Q : Charge) : (-Q).alpha = -Q.alpha := rfl
@[simp] private theorem charge_neg_beta (Q : Charge) : (-Q).beta = -Q.beta := rfl
@[simp] private theorem charge_neg_x (Q : Charge) : (-Q).x = -Q.x := rfl
@[simp] private theorem charge_neg_y (Q : Charge) : (-Q).y = -Q.y := rfl

private theorem crossProduct_neg_left (A X : H3Zorn ℝ) :
    H3Zorn.crossProduct (-A) X = -H3Zorn.crossProduct A X := by
  rw [show (-A : H3Zorn ℝ) = (-1 : ℝ) • A by module,
    H3Zorn.crossProduct_smul_left]
  module

private theorem crossProduct_neg_right (A X : H3Zorn ℝ) :
    H3Zorn.crossProduct A (-X) = -H3Zorn.crossProduct A X := by
  rw [show (-X : H3Zorn ℝ) = (-1 : ℝ) • X by module,
    H3Zorn.crossProduct_smul_right]
  module

private theorem adjointQuad_neg (A : H3Zorn ℝ) :
    H3Zorn.adjointQuad (-A) = H3Zorn.adjointQuad A := by
  rw [show (-A : H3Zorn ℝ) = (-1 : ℝ) • A by module,
    H3Zorn.adjointQuad_smul]
  norm_num

private theorem normCubic_neg (A : H3Zorn ℝ) :
    H3Zorn.normCubic (-A) = -H3Zorn.normCubic A := by
  rw [show (-A : H3Zorn ℝ) = (-1 : ℝ) • A by module,
    H3Zorn.normCubic_smul]
  ring

private theorem traceBilin_neg_left (X Y : H3Zorn ℝ) :
    H3Zorn.traceBilin (-X) Y = -H3Zorn.traceBilin X Y := by
  rw [show (-X : H3Zorn ℝ) = (-1 : ℝ) • X by module,
    H3Zorn.traceBilin_smul_left]
  ring

private theorem traceBilin_neg_right (X Y : H3Zorn ℝ) :
    H3Zorn.traceBilin X (-Y) = -H3Zorn.traceBilin X Y := by
  rw [show (-Y : H3Zorn ℝ) = (-1 : ℝ) • Y by module,
    H3Zorn.traceBilin_smul_right]
  ring

end AuxiliaryCubicLemmas

section FreudenthalInversion

/-- The canonical symplectic Freudenthal inversion `J⟨α, β, x, y⟩ = ⟨-β, α, -y, x⟩`. -/
def freudenthalInversion : Charge ≃ₗ[ℝ] Charge where
  toFun Q :=
    { alpha := -Q.beta
      beta := Q.alpha
      x := -Q.y
      y := Q.x }
  invFun Q :=
    { alpha := Q.beta
      beta := -Q.alpha
      x := Q.y
      y := -Q.x }
  left_inv Q := by
    apply FreudenthalCharge.ext <;> simp
  right_inv Q := by
    apply FreudenthalCharge.ext <;> simp
  map_add' Q₁ Q₂ := by
    apply FreudenthalCharge.ext <;> dsimp <;> module
  map_smul' r Q := by
    apply FreudenthalCharge.ext <;> simp [smul_neg]

@[simp] theorem freudenthalInversion_alpha (Q : Charge) :
    (freudenthalInversion Q).alpha = -Q.beta := rfl

@[simp] theorem freudenthalInversion_beta (Q : Charge) :
    (freudenthalInversion Q).beta = Q.alpha := rfl

@[simp] theorem freudenthalInversion_x (Q : Charge) :
    (freudenthalInversion Q).x = -Q.y := rfl

@[simp] theorem freudenthalInversion_y (Q : Charge) :
    (freudenthalInversion Q).y = Q.x := rfl

@[simp] theorem freudenthalInversion_symm_alpha (Q : Charge) :
    (freudenthalInversion.symm Q).alpha = Q.beta := rfl

@[simp] theorem freudenthalInversion_symm_beta (Q : Charge) :
    (freudenthalInversion.symm Q).beta = -Q.alpha := rfl

@[simp] theorem freudenthalInversion_symm_x (Q : Charge) :
    (freudenthalInversion.symm Q).x = Q.y := rfl

@[simp] theorem freudenthalInversion_symm_y (Q : Charge) :
    (freudenthalInversion.symm Q).y = -Q.x := rfl

/-- The Freudenthal inversion as an element of `GL(Charge)`. -/
def glInversion : ChargeGL :=
  LinearMap.GeneralLinearGroup.ofLinearEquiv freudenthalInversion

@[simp] theorem glInversion_smul (Q : Charge) :
    glInversion • Q = freudenthalInversion Q := rfl

theorem freudenthalInversion_sq (Q : Charge) :
    (freudenthalInversion * freudenthalInversion) Q = -Q := by
  apply FreudenthalCharge.ext <;> rfl

theorem freudenthalInversion_symm_apply (Q : Charge) :
    freudenthalInversion.symm Q = -freudenthalInversion Q := by
  apply FreudenthalCharge.ext <;> simp

theorem glInversion_sq : glInversion * glInversion = -1 := by
  apply Units.ext
  apply LinearMap.ext
  intro Q
  exact freudenthalInversion_sq Q

theorem freudenthalInversion_sq_eq_neg_one : glInversion ^ 2 = -1 := by
  rw [sq, glInversion_sq]

theorem glInversion_inv : glInversion⁻¹ = -glInversion := by
  apply inv_eq_of_mul_eq_one_left
  calc
    (-glInversion) * glInversion = -(glInversion * glInversion) := neg_mul _ _
    _ = -(-1) := by rw [glInversion_sq]
    _ = 1 := neg_neg 1

theorem freudenthalInversion_preserves_symplecticForm (Q₁ Q₂ : Charge) :
    symplecticForm (freudenthalInversion Q₁) (freudenthalInversion Q₂) =
      symplecticForm Q₁ Q₂ := by
  rw [symplecticForm_expanded, symplecticForm_expanded]
  simp only [freudenthalInversion_alpha, freudenthalInversion_beta,
    freudenthalInversion_x, freudenthalInversion_y,
    traceBilin_neg_left, traceBilin_neg_right]
  ring

theorem freudenthalInversion_preserves_quarticInvariant (Q : Charge) :
    quarticInvariant (freudenthalInversion Q) = quarticInvariant Q := by
  rw [quarticInvariant_expanded, quarticInvariant_expanded]
  simp only [freudenthalInversion_alpha, freudenthalInversion_beta,
    freudenthalInversion_x, freudenthalInversion_y,
    traceBilin_neg_left, normCubic_neg, adjointQuad_neg]
  rw [H3Zorn.traceBilin_symm Q.y Q.x,
    H3Zorn.traceBilin_symm (H3Zorn.adjointQuad Q.y) (H3Zorn.adjointQuad Q.x)]
  ring

end FreudenthalInversion

section UpperTranslation

private def upperTransFun (A : H3Zorn ℝ) (Q : Charge) : Charge where
  alpha :=
    Q.alpha + H3Zorn.traceBilin A Q.y -
      H3Zorn.traceBilin (H3Zorn.adjointQuad A) Q.x -
      Q.beta * H3Zorn.normCubic A
  beta := Q.beta
  x := Q.x + Q.beta • A
  y := Q.y - H3Zorn.crossProduct A Q.x - Q.beta • H3Zorn.adjointQuad A

private theorem upperTransFun_zero (Q : Charge) :
    upperTransFun (0 : H3Zorn ℝ) Q = Q := by
  apply FreudenthalCharge.ext
  · simp only [upperTransFun, H3Zorn.traceBilin_zero_left,
      adjointQuad_zero, H3Zorn.normCubic_zero, sub_zero, add_zero, mul_zero]
  · rfl
  · simp only [upperTransFun, smul_zero, add_zero]
  · simp only [upperTransFun, crossProduct_zero_left, adjointQuad_zero,
      smul_zero, sub_zero]

private theorem upperTransFun_add (A B : H3Zorn ℝ) (Q : Charge) :
    upperTransFun A (upperTransFun B Q) = upperTransFun (A + B) Q := by
  apply FreudenthalCharge.ext
  · simp only [upperTransFun, H3Zorn.traceBilin_add_left,
      H3Zorn.traceBilin_add_right, H3Zorn.traceBilin_sub_right,
      H3Zorn.traceBilin_smul_right, H3Zorn.adjointQuad_add,
      H3Zorn.normCubic_add]
    have hassoc :
        H3Zorn.traceBilin A (H3Zorn.crossProduct B Q.x) =
          H3Zorn.traceBilin (H3Zorn.crossProduct A B) Q.x :=
      (H3Zorn.traceBilin_crossProduct_assoc A B Q.x).symm
    have hsymm :
        H3Zorn.traceBilin A (H3Zorn.adjointQuad B) =
          H3Zorn.traceBilin (H3Zorn.adjointQuad B) A :=
      H3Zorn.traceBilin_symm A (H3Zorn.adjointQuad B)
    rw [hassoc, hsymm]
    ring
  · rfl
  · simp only [upperTransFun]
    module
  · simp only [upperTransFun, H3Zorn.crossProduct_add_left,
      H3Zorn.crossProduct_add_right, H3Zorn.crossProduct_smul_right,
      H3Zorn.adjointQuad_add]
    module

/-- Upper Jordan translation `t₊(A) : Charge ≃ₗ[ℝ] Charge`. -/
def freudenthalUpperTrans (A : H3Zorn ℝ) : Charge ≃ₗ[ℝ] Charge where
  toFun := upperTransFun A
  invFun := upperTransFun (-A)
  left_inv Q := by
    rw [upperTransFun_add, neg_add_cancel, upperTransFun_zero]
  right_inv Q := by
    rw [upperTransFun_add, add_neg_cancel, upperTransFun_zero]
  map_add' Q₁ Q₂ := by
    apply FreudenthalCharge.ext
    · simp only [upperTransFun, alpha_add, beta_add, x_add, y_add,
        H3Zorn.traceBilin_add_right]
      ring
    · rfl
    · simp only [upperTransFun, x_add, beta_add]
      module
    · simp only [upperTransFun, y_add, x_add, beta_add,
        H3Zorn.crossProduct_add_right]
      module
  map_smul' r Q := by
    apply FreudenthalCharge.ext
    · simp only [upperTransFun, alpha_smul, beta_smul, x_smul, y_smul,
        RingHom.id_apply, H3Zorn.traceBilin_smul_right]
      ring
    · rfl
    · simp only [upperTransFun, x_smul, beta_smul, RingHom.id_apply]
      module
    · simp only [upperTransFun, y_smul, x_smul, beta_smul,
        RingHom.id_apply, H3Zorn.crossProduct_smul_right]
      module

@[simp] theorem freudenthalUpperTrans_alpha (A : H3Zorn ℝ) (Q : Charge) :
    (freudenthalUpperTrans A Q).alpha =
      Q.alpha + H3Zorn.traceBilin A Q.y -
        H3Zorn.traceBilin (H3Zorn.adjointQuad A) Q.x -
        Q.beta * H3Zorn.normCubic A := rfl

@[simp] theorem freudenthalUpperTrans_beta (A : H3Zorn ℝ) (Q : Charge) :
    (freudenthalUpperTrans A Q).beta = Q.beta := rfl

@[simp] theorem freudenthalUpperTrans_x (A : H3Zorn ℝ) (Q : Charge) :
    (freudenthalUpperTrans A Q).x = Q.x + Q.beta • A := rfl

@[simp] theorem freudenthalUpperTrans_y (A : H3Zorn ℝ) (Q : Charge) :
    (freudenthalUpperTrans A Q).y =
      Q.y - H3Zorn.crossProduct A Q.x - Q.beta • H3Zorn.adjointQuad A := rfl

@[simp] theorem freudenthalUpperTrans_zero :
    freudenthalUpperTrans (0 : H3Zorn ℝ) = 1 := by
  apply LinearEquiv.ext
  intro Q
  exact upperTransFun_zero Q

theorem freudenthalUpperTrans_mul (A B : H3Zorn ℝ) :
    freudenthalUpperTrans A * freudenthalUpperTrans B =
      freudenthalUpperTrans (A + B) := by
  apply LinearEquiv.ext
  intro Q
  exact upperTransFun_add A B Q

theorem freudenthalUpperTrans_inv (A : H3Zorn ℝ) :
    (freudenthalUpperTrans A)⁻¹ = freudenthalUpperTrans (-A) := by
  apply LinearEquiv.ext
  intro Q
  rfl

/-- Group homomorphism `Multiplicative (H3Zorn ℝ) →* ChargeGL` given by `t₊(A)`. -/
def glUpperTrans : Multiplicative (H3Zorn ℝ) →* ChargeGL where
  toFun A :=
    LinearMap.GeneralLinearGroup.ofLinearEquiv
      (freudenthalUpperTrans (Multiplicative.toAdd A))
  map_one' := by
    change LinearMap.GeneralLinearGroup.ofLinearEquiv
        (freudenthalUpperTrans (0 : H3Zorn ℝ)) = 1
    rw [freudenthalUpperTrans_zero]
    rfl
  map_mul' A B := by
    change LinearMap.GeneralLinearGroup.ofLinearEquiv
        (freudenthalUpperTrans (Multiplicative.toAdd A + Multiplicative.toAdd B)) =
      LinearMap.GeneralLinearGroup.ofLinearEquiv
          (freudenthalUpperTrans (Multiplicative.toAdd A)) *
        LinearMap.GeneralLinearGroup.ofLinearEquiv
          (freudenthalUpperTrans (Multiplicative.toAdd B))
    rw [← LinearMap.GeneralLinearGroup.ofLinearEquiv_mul,
      freudenthalUpperTrans_mul]

@[simp] theorem glUpperTrans_smul (A : Multiplicative (H3Zorn ℝ)) (Q : Charge) :
    glUpperTrans A • Q = freudenthalUpperTrans (Multiplicative.toAdd A) Q := rfl

theorem freudenthalUpperTrans_preserves_symplecticForm
    (A : H3Zorn ℝ) (Q₁ Q₂ : Charge) :
    symplecticForm (freudenthalUpperTrans A Q₁) (freudenthalUpperTrans A Q₂) =
      symplecticForm Q₁ Q₂ := by
  rw [symplecticForm_expanded, symplecticForm_expanded]
  simp only [freudenthalUpperTrans_alpha, freudenthalUpperTrans_beta,
    freudenthalUpperTrans_x, freudenthalUpperTrans_y,
    H3Zorn.traceBilin_add_left, H3Zorn.traceBilin_add_right,
    H3Zorn.traceBilin_sub_left, H3Zorn.traceBilin_sub_right,
    H3Zorn.traceBilin_smul_left, H3Zorn.traceBilin_smul_right]
  have h1 : H3Zorn.traceBilin Q₁.x (H3Zorn.crossProduct A Q₂.x) =
      H3Zorn.traceBilin (H3Zorn.crossProduct A Q₁.x) Q₂.x := by
    calc
      H3Zorn.traceBilin Q₁.x (H3Zorn.crossProduct A Q₂.x)
          = H3Zorn.traceBilin (H3Zorn.crossProduct Q₁.x A) Q₂.x :=
            (H3Zorn.traceBilin_crossProduct_assoc Q₁.x A Q₂.x).symm
      _ = H3Zorn.traceBilin (H3Zorn.crossProduct A Q₁.x) Q₂.x := by
            rw [H3Zorn.crossProduct_symm Q₁.x A]
  have h2 : H3Zorn.traceBilin A Q₁.y = H3Zorn.traceBilin Q₁.y A :=
    H3Zorn.traceBilin_symm A Q₁.y
  have h3 : H3Zorn.traceBilin A Q₂.y = H3Zorn.traceBilin Q₂.y A :=
    H3Zorn.traceBilin_symm A Q₂.y
  have h4 : H3Zorn.traceBilin (H3Zorn.crossProduct A Q₁.x) A =
      2 * H3Zorn.traceBilin (H3Zorn.adjointQuad A) Q₁.x := by
    rw [H3Zorn.traceBilin_symm, ← H3Zorn.traceBilin_crossProduct_assoc,
      H3Zorn.crossProduct_self, H3Zorn.traceBilin_smul_left]
  have h5 : H3Zorn.traceBilin A (H3Zorn.crossProduct A Q₂.x) =
      2 * H3Zorn.traceBilin (H3Zorn.adjointQuad A) Q₂.x := by
    rw [← H3Zorn.traceBilin_crossProduct_assoc, H3Zorn.crossProduct_self,
      H3Zorn.traceBilin_smul_left]
  have h6 : H3Zorn.traceBilin Q₁.x (H3Zorn.adjointQuad A) =
      H3Zorn.traceBilin (H3Zorn.adjointQuad A) Q₁.x :=
    H3Zorn.traceBilin_symm _ _
  have h8 : H3Zorn.traceBilin (H3Zorn.adjointQuad A) A =
      H3Zorn.traceBilin A (H3Zorn.adjointQuad A) :=
    H3Zorn.traceBilin_symm _ _
  rw [h1, h2, h3, h4, h5, h6, h8]
  ring

/-- First-order `s`-expansion of `quarticInvariant (freudenthalUpperTrans (s • A) P)`:
all `s¹` terms cancel identically by `mccrimmon_identity_19`. -/
theorem freudenthalUpperTrans_firstOrder (A : H3Zorn ℝ) (P : Charge) :
    ∃ c₂ c₃ c₄ c₅ c₆ : ℝ, ∀ s : ℝ,
      quarticInvariant (freudenthalUpperTrans (s • A) P) =
        quarticInvariant P +
          s ^ 2 * (c₂ + s * c₃ + s ^ 2 * c₄ + s ^ 3 * c₅ + s ^ 4 * c₆) := by
  let x := P.x
  let y := P.y
  let y1 : H3Zorn ℝ := -H3Zorn.crossProduct A x
  let y2 : H3Zorn ℝ := -(P.beta • H3Zorn.adjointQuad A)
  let x1 : H3Zorn ℝ := P.beta • A
  let ax0 := H3Zorn.adjointQuad x
  let ax1 := P.beta • H3Zorn.crossProduct x A
  let ax2 := P.beta ^ 2 • H3Zorn.adjointQuad A
  let ay0 := H3Zorn.adjointQuad y
  let ay1 := H3Zorn.crossProduct y y1
  let ay2 := H3Zorn.adjointQuad y1 + H3Zorn.crossProduct y y2
  let ay3 := H3Zorn.crossProduct y1 y2
  let ay4 := H3Zorn.adjointQuad y2
  let a0 := P.alpha
  let a1 := H3Zorn.traceBilin A y
  let a2 := -H3Zorn.traceBilin (H3Zorn.adjointQuad A) x
  let a3 := -(P.beta * H3Zorn.normCubic A)
  let t0 := P.alpha * P.beta - H3Zorn.traceBilin x y
  let t1 := 2 * H3Zorn.traceBilin (H3Zorn.adjointQuad x) A
  let t2 := -(P.beta * H3Zorn.traceBilin (H3Zorn.adjointQuad A) x +
    H3Zorn.traceBilin x y2 + H3Zorn.traceBilin x1 y1)
  let t3 := -(P.beta ^ 2 * H3Zorn.normCubic A + H3Zorn.traceBilin x1 y2)
  let nx0 := H3Zorn.normCubic x
  let nx1 := H3Zorn.traceBilin (H3Zorn.adjointQuad x) x1
  let nx2 := H3Zorn.traceBilin (H3Zorn.adjointQuad x1) x
  let nx3 := H3Zorn.normCubic x1
  let ny0 := H3Zorn.normCubic y
  let ny1 := H3Zorn.traceBilin (H3Zorn.adjointQuad y) y1
  let ny2 := H3Zorn.traceBilin (H3Zorn.adjointQuad y1) y +
    H3Zorn.traceBilin (H3Zorn.adjointQuad y) y2
  let ny3 := H3Zorn.normCubic y1 + H3Zorn.traceBilin ay1 y2
  let ny4 := H3Zorn.traceBilin (H3Zorn.adjointQuad y1) y2 +
    H3Zorn.traceBilin (H3Zorn.adjointQuad y2) y
  let ny5 := H3Zorn.traceBilin (H3Zorn.adjointQuad y2) y1
  let ny6 := H3Zorn.normCubic y2
  let p0 := H3Zorn.traceBilin ax0 ay0
  let p1 := H3Zorn.traceBilin ax0 ay1 + H3Zorn.traceBilin ax1 ay0
  let p2 := H3Zorn.traceBilin ax0 ay2 + H3Zorn.traceBilin ax1 ay1 +
    H3Zorn.traceBilin ax2 ay0
  let p3 := H3Zorn.traceBilin ax0 ay3 + H3Zorn.traceBilin ax1 ay2 +
    H3Zorn.traceBilin ax2 ay1
  let p4 := H3Zorn.traceBilin ax0 ay4 + H3Zorn.traceBilin ax1 ay3 +
    H3Zorn.traceBilin ax2 ay2
  let p5 := H3Zorn.traceBilin ax1 ay4 + H3Zorn.traceBilin ax2 ay3
  let p6 := H3Zorn.traceBilin ax2 ay4
  refine ⟨t1 ^ 2 + 2 * t0 * t2 - 4 * (a0 * nx2 + a1 * nx1 + a2 * nx0 +
      P.beta * ny2 + p2),
    2 * t0 * t3 + 2 * t1 * t2 - 4 * (a0 * nx3 + a1 * nx2 + a2 * nx1 + a3 * nx0 +
      P.beta * ny3 + p3),
    t2 ^ 2 + 2 * t1 * t3 - 4 * (a1 * nx3 + a2 * nx2 + a3 * nx1 +
      P.beta * ny4 + p4),
    2 * t2 * t3 - 4 * (a2 * nx3 + a3 * nx2 + P.beta * ny5 + p5),
    t3 ^ 2 - 4 * (a3 * nx3 + P.beta * ny6 + p6), ?_⟩
  intro s
  have halpha : (freudenthalUpperTrans (s • A) P).alpha =
      a0 + s * a1 + s ^ 2 * a2 + s ^ 3 * a3 := by
    simp only [freudenthalUpperTrans_alpha, H3Zorn.traceBilin_smul_left,
      H3Zorn.adjointQuad_smul, H3Zorn.normCubic_smul, a0, a1, a2, a3]
    ring
  have hx : (freudenthalUpperTrans (s • A) P).x = x + s • x1 := by
    simp only [freudenthalUpperTrans_x, x, x1]
    module
  have hy : (freudenthalUpperTrans (s • A) P).y = y + s • y1 + s ^ 2 • y2 := by
    simp only [freudenthalUpperTrans_y, H3Zorn.crossProduct_smul_left,
      H3Zorn.adjointQuad_smul, y, y1, y2]
    module
  have hxy : H3Zorn.traceBilin (x + s • x1) (y + s • y1 + s ^ 2 • y2) =
      H3Zorn.traceBilin x y +
        s * (H3Zorn.traceBilin x y1 + H3Zorn.traceBilin x1 y) +
        s ^ 2 * (H3Zorn.traceBilin x y2 + H3Zorn.traceBilin x1 y1) +
        s ^ 3 * H3Zorn.traceBilin x1 y2 := by
    simp only [H3Zorn.traceBilin_add_left, H3Zorn.traceBilin_add_right,
      H3Zorn.traceBilin_smul_left, H3Zorn.traceBilin_smul_right]
    ring
  have hxy_s1 : H3Zorn.traceBilin x y1 + H3Zorn.traceBilin x1 y =
      P.beta * H3Zorn.traceBilin A y -
        2 * H3Zorn.traceBilin (H3Zorn.adjointQuad x) A := by
    have hxy1 : H3Zorn.traceBilin x y1 =
        -(2 * H3Zorn.traceBilin (H3Zorn.adjointQuad x) A) := by
      dsimp [y1, x]
      rw [traceBilin_neg_right, H3Zorn.crossProduct_symm A P.x,
        ← H3Zorn.traceBilin_crossProduct_assoc, H3Zorn.crossProduct_self,
        H3Zorn.traceBilin_smul_left]
    have hx1y : H3Zorn.traceBilin x1 y = P.beta * H3Zorn.traceBilin A y := by
      dsimp [x1, y]
      rw [H3Zorn.traceBilin_smul_left]
    rw [hxy1, hx1y]
    ring
  have hterm1 : (freudenthalUpperTrans (s • A) P).alpha *
        (freudenthalUpperTrans (s • A) P).beta -
      H3Zorn.traceBilin (freudenthalUpperTrans (s • A) P).x
        (freudenthalUpperTrans (s • A) P).y =
      t0 + s * t1 + s ^ 2 * t2 + s ^ 3 * t3 := by
    rw [halpha, hx, hy, freudenthalUpperTrans_beta, hxy, hxy_s1]
    dsimp [t0, t1, t2, t3, a0, a1, a2, a3]
    ring
  have hNx : H3Zorn.normCubic (freudenthalUpperTrans (s • A) P).x =
      nx0 + s * nx1 + s ^ 2 * nx2 + s ^ 3 * nx3 := by
    rw [hx, H3Zorn.normCubic_line]
  have hNy : H3Zorn.normCubic (freudenthalUpperTrans (s • A) P).y =
      ny0 + s * ny1 + s ^ 2 * ny2 + s ^ 3 * ny3 + s ^ 4 * ny4 +
        s ^ 5 * ny5 + s ^ 6 * ny6 := by
    rw [hy, H3Zorn.normCubic_add (y + s • y1) (s ^ 2 • y2),
      H3Zorn.normCubic_line, H3Zorn.normCubic_smul, H3Zorn.adjointQuad_smul,
      H3Zorn.traceBilin_smul_right, H3Zorn.traceBilin_smul_left]
    have hadj_y : H3Zorn.adjointQuad (y + s • y1) =
        H3Zorn.adjointQuad y + s • ay1 + s ^ 2 • H3Zorn.adjointQuad y1 := by
      rw [H3Zorn.adjointQuad_add, H3Zorn.crossProduct_smul_right,
        H3Zorn.adjointQuad_smul]
    rw [hadj_y, H3Zorn.traceBilin_add_left, H3Zorn.traceBilin_add_left,
      H3Zorn.traceBilin_smul_left, H3Zorn.traceBilin_smul_left,
      H3Zorn.traceBilin_add_right, H3Zorn.traceBilin_smul_right]
    dsimp [ny0, ny1, ny2, ny3, ny4, ny5, ny6]
    ring
  have hadj_x : H3Zorn.adjointQuad (freudenthalUpperTrans (s • A) P).x =
      ax0 + s • ax1 + s ^ 2 • ax2 := by
    rw [hx, H3Zorn.adjointQuad_add, H3Zorn.crossProduct_smul_right,
      H3Zorn.adjointQuad_smul]
    simp only [ax0, ax1, ax2, x1, H3Zorn.crossProduct_smul_right,
      H3Zorn.adjointQuad_smul, smul_smul]
  have hadj_y : H3Zorn.adjointQuad (freudenthalUpperTrans (s • A) P).y =
      ay0 + s • ay1 + s ^ 2 • ay2 + s ^ 3 • ay3 + s ^ 4 • ay4 := by
    rw [hy, H3Zorn.adjointQuad_add (y + s • y1) (s ^ 2 • y2),
      H3Zorn.adjointQuad_add y (s • y1)]
    simp only [H3Zorn.crossProduct_add_left,
      H3Zorn.crossProduct_smul_left, H3Zorn.crossProduct_smul_right,
      H3Zorn.adjointQuad_smul, ay0, ay1, ay2, ay3, ay4, smul_add, smul_smul]
    have hs3 : s ^ 2 * s = s ^ 3 := by ring
    have hs4 : (s ^ 2) ^ 2 = s ^ 4 := by ring
    rw [hs3, hs4]
    module
  have hadj_pair :
      H3Zorn.traceBilin
        (H3Zorn.adjointQuad (freudenthalUpperTrans (s • A) P).x)
        (H3Zorn.adjointQuad (freudenthalUpperTrans (s • A) P).y) =
      p0 + s * p1 + s ^ 2 * p2 + s ^ 3 * p3 + s ^ 4 * p4 +
        s ^ 5 * p5 + s ^ 6 * p6 := by
    rw [hadj_x, hadj_y]
    simp only [H3Zorn.traceBilin_add_left, H3Zorn.traceBilin_add_right,
      H3Zorn.traceBilin_smul_left, H3Zorn.traceBilin_smul_right]
    dsimp [p0, p1, p2, p3, p4, p5, p6]
    ring
  have hs1_cancel :
      2 * t0 * t1 - 4 * (a0 * nx1 + a1 * nx0 + P.beta * ny1 + p1) = 0 := by
    have hnx1_eq : nx1 = P.beta * H3Zorn.traceBilin (H3Zorn.adjointQuad x) A := by
      dsimp [nx1, x1]
      rw [H3Zorn.traceBilin_smul_right]
    have h_cross : P.beta * ny1 + H3Zorn.traceBilin ax1 ay0 = 0 := by
      dsimp [ny1, y1, ax1, ay0]
      rw [traceBilin_neg_right, H3Zorn.traceBilin_smul_left,
        H3Zorn.crossProduct_symm x A,
        H3Zorn.traceBilin_symm (H3Zorn.adjointQuad y) (H3Zorn.crossProduct A x)]
      ring
    have h_mccrimmon : H3Zorn.traceBilin ax0 ay1 =
        -(H3Zorn.traceBilin x y * H3Zorn.traceBilin (H3Zorn.adjointQuad x) A +
          H3Zorn.traceBilin A y * H3Zorn.normCubic x) := by
      dsimp [ax0, ay1, y1]
      rw [crossProduct_neg_right, traceBilin_neg_right,
        ← H3Zorn.traceBilin_crossProduct_assoc,
        H3Zorn.crossProduct_symm A x,
        H3Zorn.traceBilin_symm,
        H3Zorn.crossProduct_symm x A,
        H3Zorn.traceBilin_crossProduct_assoc,
        H3Zorn.mccrimmon_identity_19 x y,
        H3Zorn.traceBilin_add_right, H3Zorn.traceBilin_smul_right,
        H3Zorn.traceBilin_smul_right, H3Zorn.traceBilin_symm A (H3Zorn.adjointQuad x)]
      ring
    dsimp [p1]
    rw [show 2 * t0 * t1 - 4 * (a0 * nx1 + a1 * nx0 + P.beta * ny1 +
        (H3Zorn.traceBilin ax0 ay1 + H3Zorn.traceBilin ax1 ay0)) =
      2 * t0 * t1 - 4 * (a0 * nx1 + a1 * nx0 + (P.beta * ny1 +
        H3Zorn.traceBilin ax1 ay0) + H3Zorn.traceBilin ax0 ay1) by ring]
    rw [h_cross, h_mccrimmon, hnx1_eq]
    dsimp [t0, t1, a0, a1, nx0]
    ring
  rw [quarticInvariant_expanded, quarticInvariant_expanded]
  rw [hterm1, halpha, freudenthalUpperTrans_beta, hNx, hNy, hadj_pair]
  have hexpand :
      (t0 + s * t1 + s ^ 2 * t2 + s ^ 3 * t3) ^ 2 -
        4 * ((a0 + s * a1 + s ^ 2 * a2 + s ^ 3 * a3) *
            (nx0 + s * nx1 + s ^ 2 * nx2 + s ^ 3 * nx3) +
          P.beta * (ny0 + s * ny1 + s ^ 2 * ny2 + s ^ 3 * ny3 +
            s ^ 4 * ny4 + s ^ 5 * ny5 + s ^ 6 * ny6) +
          (p0 + s * p1 + s ^ 2 * p2 + s ^ 3 * p3 +
            s ^ 4 * p4 + s ^ 5 * p5 + s ^ 6 * p6)) =
      (t0 ^ 2 - 4 * (a0 * nx0 + P.beta * ny0 + p0)) +
        s * (2 * t0 * t1 - 4 * (a0 * nx1 + a1 * nx0 + P.beta * ny1 + p1)) +
        s ^ 2 * ((t1 ^ 2 + 2 * t0 * t2 - 4 * (a0 * nx2 + a1 * nx1 + a2 * nx0 +
            P.beta * ny2 + p2)) +
          s * (2 * t0 * t3 + 2 * t1 * t2 - 4 * (a0 * nx3 + a1 * nx2 + a2 * nx1 +
            a3 * nx0 + P.beta * ny3 + p3)) +
          s ^ 2 * (t2 ^ 2 + 2 * t1 * t3 - 4 * (a1 * nx3 + a2 * nx2 + a3 * nx1 +
            P.beta * ny4 + p4)) +
          s ^ 3 * (2 * t2 * t3 - 4 * (a2 * nx3 + a3 * nx2 + P.beta * ny5 + p5)) +
          s ^ 4 * (t3 ^ 2 - 4 * (a3 * nx3 + P.beta * ny6 + p6))) := by
    ring
  rw [hexpand, hs1_cancel, mul_zero, add_zero]

/-- Every upper Jordan translation `t₊(A)` preserves the Freudenthal quartic invariant. -/
theorem freudenthalUpperTrans_preserves_quarticInvariant
    (A : H3Zorn ℝ) (Q : Charge) :
    quarticInvariant (freudenthalUpperTrans A Q) = quarticInvariant Q := by
  let g : ℝ → ℝ := fun t => quarticInvariant (freudenthalUpperTrans (t • A) Q)
  have hg_shift : ∀ t s : ℝ,
      g (t + s) = quarticInvariant (freudenthalUpperTrans (s • A)
        (freudenthalUpperTrans (t • A) Q)) := by
    intro t s
    dsimp [g]
    have hsmul : (t + s) • A = s • A + t • A := by
      rw [add_smul, add_comm]
    rw [hsmul, ← freudenthalUpperTrans_mul]
    rfl
  have hg_deriv : ∀ t : ℝ, HasDerivAt g 0 t := by
    intro t
    obtain ⟨c₂, c₃, c₄, c₅, c₆, hfo⟩ :=
      freudenthalUpperTrans_firstOrder A (freudenthalUpperTrans (t • A) Q)
    have hfun : (fun s : ℝ => g (t + s)) =
        fun s : ℝ => g t + c₂ * s ^ 2 + c₃ * s ^ 3 +
          c₄ * s ^ 4 + c₅ * s ^ 5 + c₆ * s ^ 6 := by
      funext s
      rw [hg_shift t s, hfo s]
      dsimp [g]
      ring
    have h0 : HasDerivAt (fun _ : ℝ => g t) 0 0 := hasDerivAt_const 0 (g t)
    have h2 : HasDerivAt (fun s : ℝ => c₂ * s ^ 2) 0 0 := by
      simpa using (hasDerivAt_pow 2 (0 : ℝ)).const_mul c₂
    have h3 : HasDerivAt (fun s : ℝ => c₃ * s ^ 3) 0 0 := by
      simpa using (hasDerivAt_pow 3 (0 : ℝ)).const_mul c₃
    have h4 : HasDerivAt (fun s : ℝ => c₄ * s ^ 4) 0 0 := by
      simpa using (hasDerivAt_pow 4 (0 : ℝ)).const_mul c₄
    have h5 : HasDerivAt (fun s : ℝ => c₅ * s ^ 5) 0 0 := by
      simpa using (hasDerivAt_pow 5 (0 : ℝ)).const_mul c₅
    have h6 : HasDerivAt (fun s : ℝ => c₆ * s ^ 6) 0 0 := by
      simpa using (hasDerivAt_pow 6 (0 : ℝ)).const_mul c₆
    have hshift_deriv : HasDerivAt (fun s : ℝ => g (t + s)) 0 0 := by
      rw [hfun]
      simpa using ((((h0.fun_add h2).fun_add h3).fun_add h4).fun_add h5).fun_add h6
    have hsub : HasDerivAt (fun x : ℝ => x - t) 1 t :=
      (hasDerivAt_id t).sub_const t
    have hcomp : HasDerivAt ((fun s : ℝ => g (t + s)) ∘ fun x : ℝ => x - t) (0 * 1) t :=
      hshift_deriv.comp_of_eq t hsub (sub_self t).symm
    simpa [Function.comp_def, add_sub_cancel] using hcomp
  have hg_const : g 1 = g 0 :=
    is_const_of_deriv_eq_zero
      (fun t => (hg_deriv t).differentiableAt)
      (fun t => (hg_deriv t).deriv) 1 0
  have h1 : g 1 = quarticInvariant (freudenthalUpperTrans A Q) := by
    simp only [g, one_smul]
  have h0 : g 0 = quarticInvariant Q := by
    simp only [g, zero_smul, freudenthalUpperTrans_zero]
    rfl
  rw [← h1, ← h0, hg_const]

end UpperTranslation

section LowerTranslation

/-- Lower Jordan translation `t₋(B) = J * t₊(-B) * J⁻¹`. -/
def freudenthalLowerTrans (B : H3Zorn ℝ) : Charge ≃ₗ[ℝ] Charge :=
  freudenthalInversion * freudenthalUpperTrans (-B) * freudenthalInversion.symm

theorem freudenthalLowerTrans_eq_conj_upperTrans (B : H3Zorn ℝ) :
    freudenthalLowerTrans B =
      freudenthalInversion * freudenthalUpperTrans (-B) * freudenthalInversion⁻¹ :=
  rfl

theorem freudenthalLowerTrans_apply (B : H3Zorn ℝ) (Q : Charge) :
    freudenthalLowerTrans B Q =
      { alpha := Q.alpha
        beta := Q.beta + H3Zorn.traceBilin B Q.x -
          H3Zorn.traceBilin (H3Zorn.adjointQuad B) Q.y -
          Q.alpha * H3Zorn.normCubic B
        x := Q.x - H3Zorn.crossProduct B Q.y - Q.alpha • H3Zorn.adjointQuad B
        y := Q.y + Q.alpha • B } := by
  apply FreudenthalCharge.ext
  · simp only [freudenthalLowerTrans, LinearEquiv.mul_apply,
      freudenthalInversion_alpha, freudenthalUpperTrans_beta,
      freudenthalInversion_symm_beta, neg_neg]
  · simp only [freudenthalLowerTrans, LinearEquiv.mul_apply,
      freudenthalInversion_beta, freudenthalUpperTrans_alpha,
      freudenthalInversion_symm_alpha, freudenthalInversion_symm_beta,
      freudenthalInversion_symm_x, freudenthalInversion_symm_y,
      traceBilin_neg_left, traceBilin_neg_right, adjointQuad_neg, normCubic_neg]
    ring
  · simp only [freudenthalLowerTrans, LinearEquiv.mul_apply,
      freudenthalInversion_x, freudenthalUpperTrans_y,
      freudenthalInversion_symm_beta, freudenthalInversion_symm_x,
      freudenthalInversion_symm_y, crossProduct_neg_left, adjointQuad_neg]
    module
  · simp only [freudenthalLowerTrans, LinearEquiv.mul_apply,
      freudenthalInversion_y, freudenthalUpperTrans_x,
      freudenthalInversion_symm_x, freudenthalInversion_symm_beta,
      neg_smul, smul_neg, neg_neg]

@[simp] theorem freudenthalLowerTrans_alpha (B : H3Zorn ℝ) (Q : Charge) :
    (freudenthalLowerTrans B Q).alpha = Q.alpha := by
  rw [freudenthalLowerTrans_apply]

@[simp] theorem freudenthalLowerTrans_beta (B : H3Zorn ℝ) (Q : Charge) :
    (freudenthalLowerTrans B Q).beta =
      Q.beta + H3Zorn.traceBilin B Q.x -
        H3Zorn.traceBilin (H3Zorn.adjointQuad B) Q.y -
        Q.alpha * H3Zorn.normCubic B := by
  rw [freudenthalLowerTrans_apply]

@[simp] theorem freudenthalLowerTrans_x (B : H3Zorn ℝ) (Q : Charge) :
    (freudenthalLowerTrans B Q).x =
      Q.x - H3Zorn.crossProduct B Q.y - Q.alpha • H3Zorn.adjointQuad B := by
  rw [freudenthalLowerTrans_apply]

@[simp] theorem freudenthalLowerTrans_y (B : H3Zorn ℝ) (Q : Charge) :
    (freudenthalLowerTrans B Q).y = Q.y + Q.alpha • B := by
  rw [freudenthalLowerTrans_apply]

@[simp] theorem freudenthalLowerTrans_zero :
    freudenthalLowerTrans (0 : H3Zorn ℝ) = 1 := by
  rw [freudenthalLowerTrans_eq_conj_upperTrans, neg_zero,
    freudenthalUpperTrans_zero, mul_one]
  exact mul_inv_cancel freudenthalInversion

theorem freudenthalLowerTrans_mul (B₁ B₂ : H3Zorn ℝ) :
    freudenthalLowerTrans B₁ * freudenthalLowerTrans B₂ =
      freudenthalLowerTrans (B₁ + B₂) := by
  rw [freudenthalLowerTrans_eq_conj_upperTrans,
    freudenthalLowerTrans_eq_conj_upperTrans,
    freudenthalLowerTrans_eq_conj_upperTrans]
  calc
    freudenthalInversion * freudenthalUpperTrans (-B₁) * freudenthalInversion⁻¹ *
        (freudenthalInversion * freudenthalUpperTrans (-B₂) * freudenthalInversion⁻¹)
        = freudenthalInversion *
            (freudenthalUpperTrans (-B₁) *
              (freudenthalInversion⁻¹ * freudenthalInversion) *
              freudenthalUpperTrans (-B₂)) *
            freudenthalInversion⁻¹ := by
          simp only [mul_assoc]
    _ = freudenthalInversion *
          (freudenthalUpperTrans (-B₁) * freudenthalUpperTrans (-B₂)) *
          freudenthalInversion⁻¹ := by
          rw [inv_mul_cancel, mul_one]
    _ = freudenthalInversion * freudenthalUpperTrans (-(B₁ + B₂)) *
          freudenthalInversion⁻¹ := by
          rw [freudenthalUpperTrans_mul, neg_add]

theorem freudenthalLowerTrans_inv (B : H3Zorn ℝ) :
    (freudenthalLowerTrans B)⁻¹ = freudenthalLowerTrans (-B) := by
  apply inv_eq_of_mul_eq_one_left
  rw [freudenthalLowerTrans_mul, neg_add_cancel, freudenthalLowerTrans_zero]

/-- Group homomorphism `Multiplicative (H3Zorn ℝ) →* ChargeGL` given by `t₋(B)`. -/
def glLowerTrans : Multiplicative (H3Zorn ℝ) →* ChargeGL where
  toFun B :=
    LinearMap.GeneralLinearGroup.ofLinearEquiv
      (freudenthalLowerTrans (Multiplicative.toAdd B))
  map_one' := by
    change LinearMap.GeneralLinearGroup.ofLinearEquiv
        (freudenthalLowerTrans (0 : H3Zorn ℝ)) = 1
    rw [freudenthalLowerTrans_zero]
    rfl
  map_mul' B₁ B₂ := by
    change LinearMap.GeneralLinearGroup.ofLinearEquiv
        (freudenthalLowerTrans (Multiplicative.toAdd B₁ + Multiplicative.toAdd B₂)) =
      LinearMap.GeneralLinearGroup.ofLinearEquiv
          (freudenthalLowerTrans (Multiplicative.toAdd B₁)) *
        LinearMap.GeneralLinearGroup.ofLinearEquiv
          (freudenthalLowerTrans (Multiplicative.toAdd B₂))
    rw [← LinearMap.GeneralLinearGroup.ofLinearEquiv_mul,
      freudenthalLowerTrans_mul]

@[simp] theorem glLowerTrans_smul (B : Multiplicative (H3Zorn ℝ)) (Q : Charge) :
    glLowerTrans B • Q = freudenthalLowerTrans (Multiplicative.toAdd B) Q := rfl

theorem glLowerTrans_eq_conj (B : H3Zorn ℝ) :
    glLowerTrans (Multiplicative.ofAdd B) =
      glInversion * glUpperTrans (Multiplicative.ofAdd (-B)) * glInversion⁻¹ := by
  rfl

theorem freudenthalLowerTrans_preserves_symplecticForm
    (B : H3Zorn ℝ) (Q₁ Q₂ : Charge) :
    symplecticForm (freudenthalLowerTrans B Q₁) (freudenthalLowerTrans B Q₂) =
      symplecticForm Q₁ Q₂ := by
  rw [freudenthalLowerTrans_eq_conj_upperTrans]
  simp only [LinearEquiv.mul_apply]
  rw [freudenthalInversion_preserves_symplecticForm,
    freudenthalUpperTrans_preserves_symplecticForm]
  change symplecticForm (freudenthalInversion.symm Q₁) (freudenthalInversion.symm Q₂) =
    symplecticForm Q₁ Q₂
  have h1 : freudenthalInversion (freudenthalInversion.symm Q₁) = Q₁ :=
    freudenthalInversion.apply_symm_apply Q₁
  have h2 : freudenthalInversion (freudenthalInversion.symm Q₂) = Q₂ :=
    freudenthalInversion.apply_symm_apply Q₂
  calc
    symplecticForm (freudenthalInversion.symm Q₁) (freudenthalInversion.symm Q₂)
        = symplecticForm (freudenthalInversion (freudenthalInversion.symm Q₁))
            (freudenthalInversion (freudenthalInversion.symm Q₂)) :=
          (freudenthalInversion_preserves_symplecticForm _ _).symm
    _ = symplecticForm Q₁ Q₂ := by rw [h1, h2]

theorem freudenthalLowerTrans_preserves_quarticInvariant
    (B : H3Zorn ℝ) (Q : Charge) :
    quarticInvariant (freudenthalLowerTrans B Q) = quarticInvariant Q := by
  rw [freudenthalLowerTrans_eq_conj_upperTrans]
  simp only [LinearEquiv.mul_apply]
  rw [freudenthalInversion_preserves_quarticInvariant,
    freudenthalUpperTrans_preserves_quarticInvariant]
  calc
    quarticInvariant (freudenthalInversion.symm Q)
        = quarticInvariant (freudenthalInversion (freudenthalInversion.symm Q)) :=
          (freudenthalInversion_preserves_quarticInvariant _).symm
    _ = quarticInvariant Q := by rw [freudenthalInversion.apply_symm_apply]

end LowerTranslation

section SubgroupAndConjugation

/-- The subgroup of `GL(Charge)` preserving both `symplecticForm` and
`quarticInvariant`. -/
def freudenthalInvariantSubgroup : Subgroup ChargeGL where
  carrier :=
    { g : ChargeGL |
      (∀ Q₁ Q₂ : Charge, symplecticForm (g • Q₁) (g • Q₂) = symplecticForm Q₁ Q₂) ∧
      (∀ Q : Charge, quarticInvariant (g • Q) = quarticInvariant Q) }
  one_mem' := ⟨fun _ _ => rfl, fun _ => rfl⟩
  mul_mem' {g₁ g₂} hg₁ hg₂ := by
    refine ⟨fun Q₁ Q₂ => ?_, fun Q => ?_⟩
    · simp only [mul_smul, hg₁.1, hg₂.1]
    · simp only [mul_smul, hg₁.2, hg₂.2]
  inv_mem' {g} hg := by
    refine ⟨fun Q₁ Q₂ => ?_, fun Q => ?_⟩
    · calc
        symplecticForm (g⁻¹ • Q₁) (g⁻¹ • Q₂)
            = symplecticForm (g • (g⁻¹ • Q₁)) (g • (g⁻¹ • Q₂)) := (hg.1 _ _).symm
        _ = symplecticForm Q₁ Q₂ := by rw [smul_inv_smul, smul_inv_smul]
    · calc
        quarticInvariant (g⁻¹ • Q)
            = quarticInvariant (g • (g⁻¹ • Q)) := (hg.2 _).symm
        _ = quarticInvariant Q := by rw [smul_inv_smul]

/-- The concrete `E₇(7)` subgroup of `GL(Charge)` generated by the `Str₀ = E₆(6)`
Levi action, upper/lower Jordan translations `t₊(A)`, `t₋(B)`, and inversion `J`. -/
def freudenthalE7Group : Subgroup ChargeGL :=
  Subgroup.closure
    (Set.range glLevi ∪ Set.range glUpperTrans ∪ Set.range glLowerTrans ∪ {glInversion})

theorem leviChargeGL_mem_freudenthalE7Group (g : h3zornReducedStructureGroup) :
    leviChargeGL g ∈ freudenthalE7Group :=
  Subgroup.subset_closure (Or.inl (Or.inl (Or.inl ⟨g, rfl⟩)))

theorem glUpperTrans_mem_freudenthalE7Group (A : H3Zorn ℝ) :
    glUpperTrans (Multiplicative.ofAdd A) ∈ freudenthalE7Group :=
  Subgroup.subset_closure (Or.inl (Or.inl (Or.inr ⟨Multiplicative.ofAdd A, rfl⟩)))

theorem glLowerTrans_mem_freudenthalE7Group (B : H3Zorn ℝ) :
    glLowerTrans (Multiplicative.ofAdd B) ∈ freudenthalE7Group :=
  Subgroup.subset_closure (Or.inl (Or.inr ⟨Multiplicative.ofAdd B, rfl⟩))

theorem glInversion_mem_freudenthalE7Group :
    glInversion ∈ freudenthalE7Group :=
  Subgroup.subset_closure (Or.inr rfl)

theorem freudenthalE7Group_le_invariantSubgroup :
    freudenthalE7Group ≤ freudenthalInvariantSubgroup := by
  unfold freudenthalE7Group
  rw [Subgroup.closure_le]
  rintro g (((⟨h, rfl⟩ | ⟨A, rfl⟩) | ⟨B, rfl⟩) | rfl)
  · refine ⟨fun Q₁ Q₂ => ?_, fun Q => ?_⟩
    · exact leviChargeEquiv_symplecticForm h Q₁ Q₂
    · exact leviChargeEquiv_quarticInvariant h Q
  · refine ⟨fun Q₁ Q₂ => ?_, fun Q => ?_⟩
    · exact freudenthalUpperTrans_preserves_symplecticForm (Multiplicative.toAdd A) Q₁ Q₂
    · exact freudenthalUpperTrans_preserves_quarticInvariant (Multiplicative.toAdd A) Q
  · refine ⟨fun Q₁ Q₂ => ?_, fun Q => ?_⟩
    · exact freudenthalLowerTrans_preserves_symplecticForm (Multiplicative.toAdd B) Q₁ Q₂
    · exact freudenthalLowerTrans_preserves_quarticInvariant (Multiplicative.toAdd B) Q
  · exact ⟨freudenthalInversion_preserves_symplecticForm,
      freudenthalInversion_preserves_quarticInvariant⟩

/-- Theorem-safe `InvariantAction` packaging for `freudenthalInvariantSubgroup`. -/
def freudenthalInvariantSubgroupAction :
    InvariantAction freudenthalInvariantSubgroup where
  act g Q := g.1 • Q
  act_one := by
    funext Q
    exact one_smul ChargeGL Q
  act_mul g₁ g₂ := by
    funext Q
    exact mul_smul g₁.1 g₂.1 Q
  preserves_symplecticForm g Q₁ Q₂ := g.2.1 Q₁ Q₂
  preserves_quarticInvariant g Q := g.2.2 Q
  preserves_zeroCharge g := by
    have hz : zeroCharge (H3Zorn ℝ) = (0 : Charge) := by
      ext <;> rfl
    rw [hz]
    exact smul_zero g.1

/-- Theorem-safe `InvariantAction` packaging for `freudenthalE7Group`. -/
def freudenthalE7GroupAction :
    InvariantAction freudenthalE7Group where
  act g Q := g.1 • Q
  act_one := by
    funext Q
    exact one_smul ChargeGL Q
  act_mul g₁ g₂ := by
    funext Q
    exact mul_smul g₁.1 g₂.1 Q
  preserves_symplecticForm g Q₁ Q₂ :=
    (freudenthalE7Group_le_invariantSubgroup g.2).1 Q₁ Q₂
  preserves_quarticInvariant g Q :=
    (freudenthalE7Group_le_invariantSubgroup g.2).2 Q
  preserves_zeroCharge g := by
    have hz : zeroCharge (H3Zorn ℝ) = (0 : Charge) := by
      ext <;> rfl
    rw [hz]
    exact smul_zero g.1

private theorem crossProduct_reducedStructure
    (g : h3zornReducedStructureGroup) (X Y : H3Zorn ℝ) :
    H3Zorn.crossProduct (g.1 X) (g.1 Y) =
      h3zornTraceInverseAdjoint g.1 (H3Zorn.crossProduct X Y) := by
  simp only [H3Zorn.crossProduct, ← map_add, adjointQuad_reducedStructure,
    map_sub]

/-- Levi conjugation on upper translations: `L(g) * t₊(A) * L(g)⁻¹ = t₊(g A)`. -/
theorem levi_conj_upperTrans (g : h3zornReducedStructureGroup) (A : H3Zorn ℝ) :
    leviChargeEquiv g * freudenthalUpperTrans A * (leviChargeEquiv g)⁻¹ =
      freudenthalUpperTrans (g.1 A) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply LinearEquiv.ext
  intro Q
  apply FreudenthalCharge.ext
  · simp only [LinearEquiv.mul_apply, leviChargeEquiv_apply,
      leviChargeLinearEquiv_alpha, freudenthalUpperTrans_alpha,
      leviChargeLinearEquiv_beta, leviChargeLinearEquiv_x, leviChargeLinearEquiv_y]
    rw [traceBilin_reducedStructure_pair g.1 A Q.y,
      adjointQuad_reducedStructure g A,
      h3zornTraceInverseAdjoint_traceBilin,
      g.2 A]
  · rfl
  · simp only [LinearEquiv.mul_apply, leviChargeEquiv_apply,
      leviChargeLinearEquiv_x, freudenthalUpperTrans_x,
      leviChargeLinearEquiv_beta, map_add, map_smul]
  · simp only [LinearEquiv.mul_apply, leviChargeEquiv_apply,
      leviChargeLinearEquiv_y, freudenthalUpperTrans_y,
      leviChargeLinearEquiv_x, leviChargeLinearEquiv_beta,
      map_sub, map_smul, crossProduct_reducedStructure,
      adjointQuad_reducedStructure]

private theorem traceInverseAdjoint_traceInverseAdjointReduced
    (g : h3zornReducedStructureGroup) (x : H3Zorn ℝ) :
    h3zornTraceInverseAdjoint (h3zornTraceInverseAdjointReduced g).1 x = g.1 x := by
  apply H3Zorn.eq_of_traceBilin_left_eq
  intro z
  obtain ⟨w, rfl⟩ := (h3zornTraceInverseAdjointReduced g).1.surjective z
  rw [h3zornTraceInverseAdjoint_traceBilin,
    h3zornTraceInverseAdjointReduced_apply,
    traceBilin_reducedStructure_pair g.1 x w]

/-- Inversion conjugation on Levi elements: `J * L(g) * J⁻¹ = L((g⁻¹)†)`. -/
theorem inversion_conj_levi (g : h3zornReducedStructureGroup) :
    freudenthalInversion * leviChargeEquiv g * freudenthalInversion⁻¹ =
      leviChargeEquiv (h3zornTraceInverseAdjointReduced g) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply LinearEquiv.ext
  intro Q
  apply FreudenthalCharge.ext
  · rfl
  · rfl
  · simp only [LinearEquiv.mul_apply, freudenthalInversion_x,
      leviChargeEquiv_apply, leviChargeLinearEquiv_y, leviChargeLinearEquiv_x,
      h3zornTraceInverseAdjointReduced_apply, map_neg]
  · simp only [LinearEquiv.mul_apply, freudenthalInversion_y,
      leviChargeEquiv_apply, leviChargeLinearEquiv_x, leviChargeLinearEquiv_y,
      traceInverseAdjoint_traceInverseAdjointReduced]

private theorem levi_mul_inversion (g : h3zornReducedStructureGroup) :
    leviChargeEquiv g * freudenthalInversion =
      freudenthalInversion * leviChargeEquiv (h3zornTraceInverseAdjointReduced g) := by
  apply LinearEquiv.ext
  intro Q
  apply FreudenthalCharge.ext
  · rfl
  · rfl
  · simp only [LinearEquiv.mul_apply, leviChargeEquiv_apply,
      leviChargeLinearEquiv_x, freudenthalInversion_x,
      map_neg]
    exact congrArg Neg.neg
      (traceInverseAdjoint_traceInverseAdjointReduced g Q.y).symm
  · simp only [LinearEquiv.mul_apply, leviChargeEquiv_apply,
      leviChargeLinearEquiv_y, freudenthalInversion_y,
      leviChargeLinearEquiv_x, h3zornTraceInverseAdjointReduced_apply]

/-- Levi conjugation on lower translations: `L(g) * t₋(B) * L(g)⁻¹ = t₋((g⁻¹)† B)`. -/
theorem levi_conj_lowerTrans (g : h3zornReducedStructureGroup) (B : H3Zorn ℝ) :
    leviChargeEquiv g * freudenthalLowerTrans B * (leviChargeEquiv g)⁻¹ =
      freudenthalLowerTrans (h3zornTraceInverseAdjoint g.1 B) := by
  rw [mul_inv_eq_iff_eq_mul]
  calc
    leviChargeEquiv g * freudenthalLowerTrans B
        = (leviChargeEquiv g * freudenthalInversion) *
            freudenthalUpperTrans (-B) * freudenthalInversion⁻¹ := by
          rw [freudenthalLowerTrans_eq_conj_upperTrans]
          simp only [mul_assoc]
    _ = freudenthalInversion *
          (leviChargeEquiv (h3zornTraceInverseAdjointReduced g) *
            freudenthalUpperTrans (-B)) *
          freudenthalInversion⁻¹ := by
          rw [levi_mul_inversion g]
          simp only [mul_assoc]
    _ = freudenthalInversion *
          (freudenthalUpperTrans ((h3zornTraceInverseAdjointReduced g).1 (-B)) *
            leviChargeEquiv (h3zornTraceInverseAdjointReduced g)) *
          freudenthalInversion⁻¹ := by
          have h := levi_conj_upperTrans (h3zornTraceInverseAdjointReduced g) (-B)
          rw [mul_inv_eq_iff_eq_mul] at h
          rw [h]
    _ = (freudenthalInversion *
            freudenthalUpperTrans (-(h3zornTraceInverseAdjoint g.1 B)) *
            freudenthalInversion⁻¹) *
          ((freudenthalInversion *
            leviChargeEquiv (h3zornTraceInverseAdjointReduced g)) *
            freudenthalInversion⁻¹) := by
          rw [map_neg, h3zornTraceInverseAdjointReduced_apply]
          simp only [mul_assoc, inv_mul_cancel_left]
    _ = freudenthalLowerTrans (h3zornTraceInverseAdjoint g.1 B) *
          leviChargeEquiv g := by
          rw [← freudenthalLowerTrans_eq_conj_upperTrans, ← levi_mul_inversion g,
            mul_assoc (leviChargeEquiv g), mul_inv_cancel, mul_one]

end SubgroupAndConjugation

section NonTrivialityAndSignSanityWitnesses

private theorem traceBilin_one_one :
    H3Zorn.traceBilin (1 : H3Zorn ℝ) 1 = 3 := by
  rw [H3Zorn.traceBilin_one]
  change (1 : ℝ) + 1 + 1 = 3
  norm_num

/-- Sign-sanity witness explicitly checking the corrected `+ ⟨x#, y#⟩` term in
`quarticInvariant`: `t₊(1)⟨α, 1, 0, 0⟩ = ⟨α - 1, 1, 1, -1⟩` has `I₄ = α²`. -/
theorem freudenthalUpperTrans_one_sign_sanity (α : ℝ) :
    quarticInvariant (freudenthalUpperTrans (1 : H3Zorn ℝ) ⟨α, 1, 0, 0⟩) = α ^ 2 := by
  have himg : freudenthalUpperTrans (1 : H3Zorn ℝ) ⟨α, 1, 0, 0⟩ =
      ⟨α - 1, 1, (1 : H3Zorn ℝ), (-1 : H3Zorn ℝ)⟩ := by
    apply FreudenthalCharge.ext
    · simp only [freudenthalUpperTrans_alpha, H3Zorn.traceBilin_zero_right,
        H3Zorn.normCubic_one]
      ring
    · rfl
    · simp
    · simp only [freudenthalUpperTrans_y, H3Zorn.crossProduct_symm (1 : H3Zorn ℝ) 0,
        crossProduct_zero_left, H3Zorn.adjointQuad_one]
      module
  rw [himg, quarticInvariant_expanded]
  simp only [traceBilin_neg_right, H3Zorn.normCubic_one, normCubic_neg,
    H3Zorn.adjointQuad_one, adjointQuad_neg, traceBilin_one_one]
  ring

theorem freudenthalInversion_ne_one : freudenthalInversion ≠ 1 := by
  intro h
  have h0 := congrArg (fun e : Charge ≃ₗ[ℝ] Charge => (e (scalarCharge 1 0)).alpha) h
  change (freudenthalInversion (scalarCharge 1 0)).alpha = (scalarCharge 1 0).alpha at h0
  simp only [freudenthalInversion_alpha, scalarCharge] at h0
  norm_num at h0

theorem freudenthalUpperTrans_one_ne_one :
    freudenthalUpperTrans (1 : H3Zorn ℝ) (scalarCharge 0 1) = ⟨-1, 1, 1, -1⟩ ∧
      freudenthalUpperTrans (1 : H3Zorn ℝ) ≠ 1 := by
  have heq : freudenthalUpperTrans (1 : H3Zorn ℝ) (scalarCharge 0 1) = ⟨-1, 1, 1, -1⟩ := by
    apply FreudenthalCharge.ext
    · simp only [freudenthalUpperTrans_alpha, scalarCharge,
        H3Zorn.traceBilin_zero_right, H3Zorn.normCubic_one]
      norm_num
    · rfl
    · simp only [freudenthalUpperTrans_x, scalarCharge, one_smul, zero_add]
    · simp only [freudenthalUpperTrans_y, scalarCharge, crossProduct_zero_right,
        H3Zorn.adjointQuad_one, one_smul, sub_zero, zero_sub]
  refine ⟨heq, ?_⟩
  intro hone
  have hα := congrArg (fun e : Charge ≃ₗ[ℝ] Charge => (e (scalarCharge 0 1)).alpha) hone
  rw [heq] at hα
  change (-1 : ℝ) = 0 at hα
  norm_num at hα

theorem freudenthalLowerTrans_one_ne_one :
    freudenthalLowerTrans (1 : H3Zorn ℝ) (scalarCharge 1 0) = ⟨1, -1, -1, 1⟩ ∧
      freudenthalLowerTrans (1 : H3Zorn ℝ) ≠ 1 := by
  have heq : freudenthalLowerTrans (1 : H3Zorn ℝ) (scalarCharge 1 0) = ⟨1, -1, -1, 1⟩ := by
    apply FreudenthalCharge.ext
    · simp only [freudenthalLowerTrans_alpha, scalarCharge]
    · simp only [freudenthalLowerTrans_beta, scalarCharge,
        H3Zorn.traceBilin_zero_right, H3Zorn.normCubic_one]
      norm_num
    · simp only [freudenthalLowerTrans_x, scalarCharge, crossProduct_zero_right,
        H3Zorn.adjointQuad_one, one_smul, sub_zero, zero_sub]
    · simp only [freudenthalLowerTrans_y, scalarCharge, one_smul, zero_add]
  refine ⟨heq, ?_⟩
  intro hone
  have hβ := congrArg (fun e : Charge ≃ₗ[ℝ] Charge => (e (scalarCharge 1 0)).beta) hone
  rw [heq] at hβ
  change (-1 : ℝ) = 0 at hβ
  norm_num at hβ

theorem freudenthal_upper_lower_noncommute :
    freudenthalUpperTrans (1 : H3Zorn ℝ) * freudenthalLowerTrans (1 : H3Zorn ℝ) ≠
      freudenthalLowerTrans (1 : H3Zorn ℝ) * freudenthalUpperTrans (1 : H3Zorn ℝ) := by
  intro h
  have hα := congrArg (fun e : Charge ≃ₗ[ℝ] Charge => (e (scalarCharge 1 0)).alpha) h
  have hlow : freudenthalLowerTrans (1 : H3Zorn ℝ) (scalarCharge 1 0) = ⟨1, -1, -1, 1⟩ :=
    freudenthalLowerTrans_one_ne_one.1
  have hup_scalar : freudenthalUpperTrans (1 : H3Zorn ℝ) (scalarCharge 1 0) =
      scalarCharge 1 0 := by
    apply FreudenthalCharge.ext
    · simp only [freudenthalUpperTrans_alpha, scalarCharge,
        H3Zorn.traceBilin_zero_right, H3Zorn.normCubic_one]
      norm_num
    · rfl
    · simp only [freudenthalUpperTrans_x, scalarCharge, zero_smul, add_zero]
    · simp only [freudenthalUpperTrans_y, scalarCharge, crossProduct_zero_right,
        zero_smul, sub_zero]
  simp only [LinearEquiv.mul_apply] at hα
  rw [hlow, hup_scalar, hlow] at hα
  simp only [freudenthalUpperTrans_alpha, traceBilin_neg_right,
    H3Zorn.adjointQuad_one, H3Zorn.normCubic_one, traceBilin_one_one] at hα
  norm_num at hα

theorem glUpperTrans_glLowerTrans_commutator_ne_one :
    glUpperTrans (Multiplicative.ofAdd (1 : H3Zorn ℝ)) *
        glLowerTrans (Multiplicative.ofAdd (1 : H3Zorn ℝ)) *
        (glUpperTrans (Multiplicative.ofAdd (1 : H3Zorn ℝ)))⁻¹ *
        (glLowerTrans (Multiplicative.ofAdd (1 : H3Zorn ℝ)))⁻¹ ≠ 1 := by
  intro h
  have hcomm :
      glUpperTrans (Multiplicative.ofAdd (1 : H3Zorn ℝ)) *
        glLowerTrans (Multiplicative.ofAdd (1 : H3Zorn ℝ)) =
      glLowerTrans (Multiplicative.ofAdd (1 : H3Zorn ℝ)) *
        glUpperTrans (Multiplicative.ofAdd (1 : H3Zorn ℝ)) := by
    have hmul := congrArg
      (fun g : ChargeGL =>
        g * (glLowerTrans (Multiplicative.ofAdd (1 : H3Zorn ℝ)) *
          glUpperTrans (Multiplicative.ofAdd (1 : H3Zorn ℝ)))) h
    simpa [mul_assoc] using hmul
  apply freudenthal_upper_lower_noncommute
  apply LinearEquiv.ext
  intro Q
  exact congrArg (fun g : ChargeGL => g • Q) hcomm

theorem freudenthal_inversion_upper_noncommute :
    freudenthalInversion * freudenthalUpperTrans (1 : H3Zorn ℝ) ≠
      freudenthalUpperTrans (1 : H3Zorn ℝ) * freudenthalInversion := by
  intro h
  have hβ := congrArg (fun e : Charge ≃ₗ[ℝ] Charge => (e (scalarCharge 0 1)).beta) h
  have hup : freudenthalUpperTrans (1 : H3Zorn ℝ) (scalarCharge 0 1) = ⟨-1, 1, 1, -1⟩ :=
    freudenthalUpperTrans_one_ne_one.1
  have hinv : freudenthalInversion (scalarCharge 0 1) = scalarCharge (-1) 0 := by
    apply FreudenthalCharge.ext
    · simp only [freudenthalInversion_alpha, scalarCharge]
    · simp only [freudenthalInversion_beta, scalarCharge]
    · simp only [freudenthalInversion_x, scalarCharge, neg_zero]
    · simp only [freudenthalInversion_y, scalarCharge]
  simp only [LinearEquiv.mul_apply] at hβ
  rw [hup, hinv] at hβ
  simp only [freudenthalInversion_beta, freudenthalUpperTrans_beta, scalarCharge] at hβ
  norm_num at hβ

end NonTrivialityAndSignSanityWitnesses

end InfoGeometry.Algebra.H3ZornFreudenthal
