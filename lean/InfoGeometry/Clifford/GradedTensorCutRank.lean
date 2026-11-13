/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.LinearMap
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.Tactic.Module

/-!
# Real tensor cut rank and a controlled parity twist

The cut rank of a genuine tensor `t : V ⊗[ℝ] W` is the dimension of the
range of its canonical contraction `V* →ₗ[ℝ] W`. Only the left space is
assumed finite dimensional. In particular, the right space may retain an
arbitrary operator coefficient algebra of infinite real dimension.

The controlled twist is the actual tensor endomorphism
`id ⊗ p₀ + T ⊗ p₁`. Its cut rank is at most twice the original cut rank.
For an involution `T` and complementary projections `p₀`, `p₁`, the twist
is involutive, so the reverse factor-of-two inequality holds as well.
These inequalities apply to arbitrary tensors, including inhomogeneous
ones. They do not assert minimality of a particular tensor train.
-/

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace InfoGeometry.Clifford.GradedTensorCutRank

universe u v

variable {V : Type u} {W : Type v}
variable [AddCommGroup V] [Module ℝ V]
variable [AddCommGroup W] [Module ℝ W]

/-- Canonical contraction of the left factor against its real algebraic dual. -/
def contraction : V ⊗[ℝ] W →ₗ[ℝ] (Module.Dual ℝ V →ₗ[ℝ] W) :=
  (dualTensorHom ℝ (Module.Dual ℝ V) W).comp
    ((Module.Dual.eval ℝ V).rTensor W)

@[simp] theorem contraction_tmul_apply (x : V) (y : W)
    (φ : Module.Dual ℝ V) :
    contraction (x ⊗ₜ[ℝ] y) φ = φ x • y := rfl

/-- Contraction is natural in both factors; the left map acts by its dual. -/
theorem contraction_map (f : Module.End ℝ V) (g : Module.End ℝ W)
    (t : V ⊗[ℝ] W) :
    contraction (TensorProduct.map f g t) =
      g.comp ((contraction t).comp f.dualMap) := by
  induction t with
  | tmul x y =>
      ext φ
      simp [LinearMap.comp_apply]
  | add s t hs ht =>
      ext φ
      simpa only [map_add, LinearMap.add_apply, LinearMap.comp_apply] using
        congrArg₂ (· + ·) (LinearMap.congr_fun hs φ) (LinearMap.congr_fun ht φ)

/-- Real cut rank, measured by the range of the native contraction map. -/
def cutRank (t : V ⊗[ℝ] W) : ℕ :=
  Module.finrank ℝ (LinearMap.range (contraction t))

@[simp] theorem cutRank_zero : cutRank (0 : V ⊗[ℝ] W) = 0 := by
  simp [cutRank]

section FiniteLeft

variable [FiniteDimensional ℝ V]

/-- Finite left dimension makes contraction an equivalence, even for infinite `W`. -/
def contractionEquiv :
    V ⊗[ℝ] W ≃ₗ[ℝ] (Module.Dual ℝ V →ₗ[ℝ] W) :=
  ((Module.evalEquiv ℝ V).rTensor W).trans
    (dualTensorHomEquiv ℝ (Module.Dual ℝ V) W)

@[simp] theorem contractionEquiv_apply (t : V ⊗[ℝ] W) :
    contractionEquiv t = contraction t := rfl

theorem contraction_injective :
    Function.Injective (contraction (V := V) (W := W)) := by
  intro s t h
  apply (contractionEquiv (V := V) (W := W)).injective
  simpa only [contractionEquiv_apply] using h

/-- Cut rank cannot exceed the finite dimension of the left factor. -/
theorem cutRank_le_left (t : V ⊗[ℝ] W) :
    cutRank t ≤ Module.finrank ℝ V := by
  simpa only [cutRank, Subspace.dual_finrank_eq] using
    (contraction t).finrank_range_le

/-- Subadditivity uses finite-dimensional contraction ranges, not finite `W`. -/
theorem cutRank_add_le (s t : V ⊗[ℝ] W) :
    cutRank (s + t) ≤ cutRank s + cutRank t := by
  unfold cutRank
  rw [map_add]
  apply Module.finrank_le_of_rank_le
  simpa only [LinearMap.rank, Nat.cast_add, Module.finrank_eq_rank] using
    LinearMap.rank_add_le (contraction s) (contraction t)

/-- Independent real linear maps on the two factors cannot increase cut rank. -/
theorem cutRank_map_le (f : Module.End ℝ V) (g : Module.End ℝ W)
    (t : V ⊗[ℝ] W) :
    cutRank (TensorProduct.map f g t) ≤ cutRank t := by
  unfold cutRank
  rw [contraction_map]
  apply Module.finrank_le_of_rank_le
  have hpre := LinearMap.rank_comp_le_left f.dualMap (contraction t)
  have hpost :=
    LinearMap.rank_comp_le_right ((contraction t).comp f.dualMap) g
  simpa only [LinearMap.rank, Module.finrank_eq_rank] using hpost.trans hpre

/-- Invertible changes within the two sides preserve their real cut rank. -/
theorem cutRank_map_equiv (f : V ≃ₗ[ℝ] V) (g : W ≃ₗ[ℝ] W)
    (t : V ⊗[ℝ] W) :
    cutRank (TensorProduct.map f.toLinearMap g.toLinearMap t) = cutRank t := by
  apply le_antisymm (cutRank_map_le f.toLinearMap g.toLinearMap t)
  have hinv :
      TensorProduct.map f.symm.toLinearMap g.symm.toLinearMap
        (TensorProduct.map f.toLinearMap g.toLinearMap t) = t := by
    induction t with
    | tmul x y => simp
    | add s t hs ht => simp only [map_add, hs, ht]
  have h := cutRank_map_le f.symm.toLinearMap g.symm.toLinearMap
    (TensorProduct.map f.toLinearMap g.toLinearMap t)
  simpa only [hinv] using h

/-- A right dimension bound requires an explicit finite-dimensional right factor. -/
theorem cutRank_le_right [FiniteDimensional ℝ W] (t : V ⊗[ℝ] W) :
    cutRank t ≤ Module.finrank ℝ W :=
  (LinearMap.range (contraction t)).finrank_le

/-- The two finite factor dimensions bound the cut rank by their minimum. -/
theorem cutRank_le_min [FiniteDimensional ℝ W] (t : V ⊗[ℝ] W) :
    cutRank t ≤ min (Module.finrank ℝ V) (Module.finrank ℝ W) :=
  le_min (cutRank_le_left t) (cutRank_le_right t)

/-- A finite operator-valued tail contributes its real vector-space dimension.
No commutativity of the operator algebra is assumed. -/
theorem cutRank_operator_tail_le_min
    {U B : Type*} [AddCommGroup U] [Module ℝ U]
    [Ring B] [Algebra ℝ B]
    [FiniteDimensional ℝ U] [FiniteDimensional ℝ B]
    (t : V ⊗[ℝ] (U ⊗[ℝ] B)) :
    cutRank t ≤ min (Module.finrank ℝ V)
      (Module.finrank ℝ U * Module.finrank ℝ B) := by
  simpa only [Module.finrank_tensorProduct] using cutRank_le_min t

end FiniteLeft

/-- A genuine tensor endomorphism controlled by the two right-hand parity sectors. -/
def controlledTwist (T : Module.End ℝ V) (p₀ p₁ : Module.End ℝ W) :
    Module.End ℝ (V ⊗[ℝ] W) :=
  TensorProduct.map LinearMap.id p₀ + TensorProduct.map T p₁

@[simp] theorem controlledTwist_tmul
    (T : Module.End ℝ V) (p₀ p₁ : Module.End ℝ W) (x : V) (y : W) :
    controlledTwist T p₀ p₁ (x ⊗ₜ[ℝ] y) =
      x ⊗ₜ[ℝ] p₀ y + T x ⊗ₜ[ℝ] p₁ y := rfl

/-- The tensor twist becomes a sum of two compositions after contraction. -/
theorem contraction_controlledTwist
    (T : Module.End ℝ V) (p₀ p₁ : Module.End ℝ W) (t : V ⊗[ℝ] W) :
    contraction (controlledTwist T p₀ p₁ t) =
      p₀.comp (contraction t) + p₁.comp ((contraction t).comp T.dualMap) := by
  simp only [controlledTwist, LinearMap.add_apply, map_add, contraction_map,
    LinearMap.dualMap_id, LinearMap.comp_id]

/-- Complementary right projections and an involutive left map make the twist involutive. -/
theorem controlledTwist_involutive
    (T : Module.End ℝ V) (p₀ p₁ : Module.End ℝ W)
    (hT : T.comp T = LinearMap.id)
    (h00 : p₀.comp p₀ = p₀) (h11 : p₁.comp p₁ = p₁)
    (h01 : p₀.comp p₁ = 0) (h10 : p₁.comp p₀ = 0)
    (hsum : p₀ + p₁ = LinearMap.id) :
    Function.Involutive (controlledTwist T p₀ p₁) := by
  have hcomp :
      (controlledTwist T p₀ p₁).comp (controlledTwist T p₀ p₁) =
        LinearMap.id := by
    apply TensorProduct.ext'
    intro x y
    have hTx : T (T x) = x := LinearMap.congr_fun hT x
    have h00y : p₀ (p₀ y) = p₀ y := LinearMap.congr_fun h00 y
    have h11y : p₁ (p₁ y) = p₁ y := LinearMap.congr_fun h11 y
    have h01y : p₀ (p₁ y) = 0 := LinearMap.congr_fun h01 y
    have h10y : p₁ (p₀ y) = 0 := LinearMap.congr_fun h10 y
    have hsumy : p₀ y + p₁ y = y := LinearMap.congr_fun hsum y
    change controlledTwist T p₀ p₁
      (controlledTwist T p₀ p₁ (x ⊗ₜ[ℝ] y)) = x ⊗ₜ[ℝ] y
    simp only [controlledTwist_tmul, map_add, hTx, h00y, h11y, h01y, h10y,
      TensorProduct.tmul_zero, add_zero, zero_add]
    rw [← TensorProduct.tmul_add, hsumy]
  intro t
  exact LinearMap.congr_fun hcomp t

section ControlledRank

variable [FiniteDimensional ℝ V]

/-- The sum of the two controlled tensor channels costs at most a factor of two. -/
theorem cutRank_controlledTwist_le
    (T : Module.End ℝ V) (p₀ p₁ : Module.End ℝ W) (t : V ⊗[ℝ] W) :
    cutRank (controlledTwist T p₀ p₁ t) ≤ 2 * cutRank t := by
  calc
    cutRank (controlledTwist T p₀ p₁ t) ≤
        cutRank (TensorProduct.map LinearMap.id p₀ t) +
          cutRank (TensorProduct.map T p₁ t) := cutRank_add_le _ _
    _ ≤ cutRank t + cutRank t :=
      Nat.add_le_add (cutRank_map_le LinearMap.id p₀ t) (cutRank_map_le T p₁ t)
    _ = 2 * cutRank t := (two_mul _).symm

/-- Involutivity supplies the reverse rank inequality without a finite right factor. -/
theorem cutRank_le_twice_controlledTwist
    (T : Module.End ℝ V) (p₀ p₁ : Module.End ℝ W)
    (hT : T.comp T = LinearMap.id)
    (h00 : p₀.comp p₀ = p₀) (h11 : p₁.comp p₁ = p₁)
    (h01 : p₀.comp p₁ = 0) (h10 : p₁.comp p₀ = 0)
    (hsum : p₀ + p₁ = LinearMap.id) (t : V ⊗[ℝ] W) :
    cutRank t ≤ 2 * cutRank (controlledTwist T p₀ p₁ t) := by
  have hinv := controlledTwist_involutive T p₀ p₁ hT h00 h11 h01 h10 hsum
  have h := cutRank_controlledTwist_le T p₀ p₁ (controlledTwist T p₀ p₁ t)
  simpa only [hinv t] using h

/-- Both cut-rank inequalities for a controlled involutive tensor twist. -/
theorem cutRank_controlledTwist_bounds
    (T : Module.End ℝ V) (p₀ p₁ : Module.End ℝ W)
    (hT : T.comp T = LinearMap.id)
    (h00 : p₀.comp p₀ = p₀) (h11 : p₁.comp p₁ = p₁)
    (h01 : p₀.comp p₁ = 0) (h10 : p₁.comp p₀ = 0)
    (hsum : p₀ + p₁ = LinearMap.id) (t : V ⊗[ℝ] W) :
    cutRank (controlledTwist T p₀ p₁ t) ≤ 2 * cutRank t ∧
      cutRank t ≤ 2 * cutRank (controlledTwist T p₀ p₁ t) :=
  ⟨cutRank_controlledTwist_le T p₀ p₁ t,
    cutRank_le_twice_controlledTwist T p₀ p₁ hT h00 h11 h01 h10 hsum t⟩

end ControlledRank

/-- The even projection of a real linear parity operator. -/
def evenProjection (θ : Module.End ℝ W) : Module.End ℝ W :=
  (1 / 2 : ℝ) • (LinearMap.id + θ)

/-- The odd projection of a real linear parity operator. -/
def oddProjection (θ : Module.End ℝ W) : Module.End ℝ W :=
  (1 / 2 : ℝ) • (LinearMap.id - θ)

@[simp] theorem evenProjection_apply (θ : Module.End ℝ W) (y : W) :
    evenProjection θ y = (1 / 2 : ℝ) • (y + θ y) := rfl

@[simp] theorem oddProjection_apply (θ : Module.End ℝ W) (y : W) :
    oddProjection θ y = (1 / 2 : ℝ) • (y - θ y) := rfl

/-- The real even and odd projections sum to the identity. -/
theorem evenProjection_add_oddProjection (θ : Module.End ℝ W) :
    evenProjection θ + oddProjection θ = LinearMap.id := by
  ext y
  simp only [LinearMap.add_apply, LinearMap.id_apply,
    evenProjection_apply, oddProjection_apply]
  module

theorem evenProjection_idempotent (θ : Module.End ℝ W)
    (hθ : θ.comp θ = LinearMap.id) :
    (evenProjection θ).comp (evenProjection θ) = evenProjection θ := by
  ext y
  have hθy : θ (θ y) = y := LinearMap.congr_fun hθ y
  simp only [LinearMap.comp_apply, evenProjection_apply, map_smul, map_add, hθy]
  module

theorem oddProjection_idempotent (θ : Module.End ℝ W)
    (hθ : θ.comp θ = LinearMap.id) :
    (oddProjection θ).comp (oddProjection θ) = oddProjection θ := by
  ext y
  have hθy : θ (θ y) = y := LinearMap.congr_fun hθ y
  simp only [LinearMap.comp_apply, oddProjection_apply, map_smul, map_sub, hθy]
  module

theorem evenProjection_comp_oddProjection (θ : Module.End ℝ W)
    (hθ : θ.comp θ = LinearMap.id) :
    (evenProjection θ).comp (oddProjection θ) = 0 := by
  ext y
  have hθy : θ (θ y) = y := LinearMap.congr_fun hθ y
  simp only [LinearMap.comp_apply, LinearMap.zero_apply,
    evenProjection_apply, oddProjection_apply, map_smul, map_sub, hθy]
  module

theorem oddProjection_comp_evenProjection (θ : Module.End ℝ W)
    (hθ : θ.comp θ = LinearMap.id) :
    (oddProjection θ).comp (evenProjection θ) = 0 := by
  ext y
  have hθy : θ (θ y) = y := LinearMap.congr_fun hθ y
  simp only [LinearMap.comp_apply, LinearMap.zero_apply,
    evenProjection_apply, oddProjection_apply, map_smul, map_add, hθy]
  module

/-- The controlled tensor twist built directly from a real parity operator. -/
def parityTwist (T : Module.End ℝ V) (θ : Module.End ℝ W) :
    Module.End ℝ (V ⊗[ℝ] W) :=
  controlledTwist T (evenProjection θ) (oddProjection θ)

@[simp] theorem parityTwist_tmul
    (T : Module.End ℝ V) (θ : Module.End ℝ W) (x : V) (y : W) :
    parityTwist T θ (x ⊗ₜ[ℝ] y) =
      x ⊗ₜ[ℝ] ((1 / 2 : ℝ) • (y + θ y)) +
        T x ⊗ₜ[ℝ] ((1 / 2 : ℝ) • (y - θ y)) := rfl

/-- Both parity decompositions are constructed, rather than supplied as proof fields. -/
theorem parityTwist_involutive
    (T : Module.End ℝ V) (θ : Module.End ℝ W)
    (hT : T.comp T = LinearMap.id) (hθ : θ.comp θ = LinearMap.id) :
    Function.Involutive (parityTwist T θ) :=
  controlledTwist_involutive T (evenProjection θ) (oddProjection θ) hT
    (evenProjection_idempotent θ hθ) (oddProjection_idempotent θ hθ)
    (evenProjection_comp_oddProjection θ hθ)
    (oddProjection_comp_evenProjection θ hθ)
    (evenProjection_add_oddProjection θ)

/-- Two-sided cut-rank control for an arbitrary right real involutive parity. -/
theorem cutRank_parityTwist_bounds [FiniteDimensional ℝ V]
    (T : Module.End ℝ V) (θ : Module.End ℝ W)
    (hT : T.comp T = LinearMap.id) (hθ : θ.comp θ = LinearMap.id)
    (t : V ⊗[ℝ] W) :
    cutRank (parityTwist T θ t) ≤ 2 * cutRank t ∧
      cutRank t ≤ 2 * cutRank (parityTwist T θ t) :=
  cutRank_controlledTwist_bounds T (evenProjection θ) (oddProjection θ) hT
    (evenProjection_idempotent θ hθ) (oddProjection_idempotent θ hθ)
    (evenProjection_comp_oddProjection θ hθ)
    (oddProjection_comp_evenProjection θ hθ)
    (evenProjection_add_oddProjection θ) t

end InfoGeometry.Clifford.GradedTensorCutRank
