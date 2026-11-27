/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.SouriauKKSForm
import InfoGeometry.Canonical.SouriauCoadjointOrbitSymplecticReduction
import Mathlib.LinearAlgebra.Quotient.Bilinear

/-! # The KKS form on its actual radical quotient
The carrier is a module quotient over the given commutative ring. No ideal
assumption, quotient Lie
algebra, or smooth coadjoint orbit is asserted. -/

namespace SouriauReduction
variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The existing KKS pairing as a native bilinear map. -/
def kksBilinear (μ : Module.Dual R L) : L →ₗ[R] L →ₗ[R] R where
  toFun x :=
    { toFun := fun y => SouriauKKS.kksForm μ x y
      map_add' := fun y z => SouriauKKS.kksForm_add_right μ x y z
      map_smul' := fun r y => SouriauKKS.kksForm_smul_right μ r x y }
  map_add' x y := by
    ext z
    exact SouriauKKS.kksForm_add_left μ x y z
  map_smul' r x := by
    ext y
    exact SouriauKKS.kksForm_smul_left μ r x y

@[simp] theorem kksBilinear_apply (μ : Module.Dual R L) (x y : L) :
    kksBilinear μ x y = μ ⁅x, y⁆ := rfl

/-- The actual coadjoint radical, without an assumed isotropy submodule. -/
def kksRadical (μ : Module.Dual R L) : Submodule R L :=
  LinearMap.ker (kksBilinear μ)

@[simp] theorem mem_kksRadical (μ : Module.Dual R L) (x : L) :
    x ∈ kksRadical μ ↔ ∀ y, μ ⁅x, y⁆ = 0 := by
  simp [kksRadical, LinearMap.mem_ker, LinearMap.ext_iff]

theorem kksRadical_le_flip_ker (μ : Module.Dual R L) :
    kksRadical μ ≤ (kksBilinear μ).flip.ker := by
  intro x hx
  apply LinearMap.ext
  intro y
  change μ ⁅y, x⁆ = 0
  rw [← lie_skew y x, map_neg, (mem_kksRadical μ x).mp hx y, neg_zero]

/-- The actual algebraic quotient carrier. -/
abbrev KKSQuotient (μ : Module.Dual R L) := L ⧸ kksRadical μ

/-- Descent in both slots through Mathlib's quotient API. -/
def quotientKKSForm (μ : Module.Dual R L) :
    KKSQuotient μ →ₗ[R] KKSQuotient μ →ₗ[R] R :=
  (kksBilinear μ).liftQ₂ (kksRadical μ) (kksRadical μ)
    (le_refl _) (kksRadical_le_flip_ker μ)

@[simp] theorem quotientKKSForm_mk (μ : Module.Dual R L) (x y : L) :
    quotientKKSForm μ (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      μ ⁅x, y⁆ := rfl

theorem quotientKKSForm_pullback (μ : Module.Dual R L) (x y : L) :
    quotientKKSForm μ ((kksRadical μ).mkQ x) ((kksRadical μ).mkQ y) =
      kksForm μ x y := rfl

theorem quotientKKSForm_alternating (μ : Module.Dual R L) (x : KKSQuotient μ) :
    quotientKKSForm μ x x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | _ x => simp

theorem quotientKKSForm_skew (μ : Module.Dual R L) (x y : KKSQuotient μ) :
    quotientKKSForm μ x y = -quotientKKSForm μ y x := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    induction y using Submodule.Quotient.induction_on with
    | _ y => exact SouriauKKS.kksForm_skew μ x y

theorem quotientKKSForm_separatingLeft (μ : Module.Dual R L) :
    (quotientKKSForm μ).SeparatingLeft := by
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    intro hx
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    apply (mem_kksRadical μ x).mpr
    intro y
    exact hx (Submodule.Quotient.mk y)

/-- Nondegeneracy is proved from the constructed radical quotient. -/
theorem quotientKKSForm_nondegenerate (μ : Module.Dual R L) :
    (quotientKKSForm μ).Nondegenerate := by
  refine ⟨quotientKKSForm_separatingLeft μ, ?_⟩
  intro y hy
  apply quotientKKSForm_separatingLeft μ y
  intro x
  rw [quotientKKSForm_skew, hy, neg_zero]

theorem quotient_class_eq_zero_iff (μ : Module.Dual R L) (x : L) :
    (Submodule.Quotient.mk x : KKSQuotient μ) = 0 ↔ ∀ y, μ ⁅x, y⁆ = 0 := by
  rw [Submodule.Quotient.mk_eq_zero, mem_kksRadical]

theorem quotientKKSForm_ne_zero_of_pairing (μ : Module.Dual R L) (x y : L)
    (h : μ ⁅x, y⁆ ≠ 0) : quotientKKSForm μ ≠ 0 := by
  intro hz
  apply h
  have := congrArg (fun b : KKSQuotient μ →ₗ[R] KKSQuotient μ →ₗ[R] R =>
    b (Submodule.Quotient.mk x) (Submodule.Quotient.mk y)) hz
  simpa using this

end SouriauReduction
