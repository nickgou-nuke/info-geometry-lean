/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.CartanSouriauCocycleGibbsCharacter
import Mathlib.CategoryTheory.Action
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The affine Souriau action groupoid and finite Massieu signs

The groupoid is Mathlib's category of elements of the existing affine action.
It is an algebraic action groupoid. No smooth cotangent-bundle identification
or multiplicative symplectic form is constructed here.

The existing `twistedMassieu` is `log Z`. Its negative therefore obeys the
concavity and inverse-cocycle signs used in the attached Souriau convention.
-/

noncomputable section

namespace InfoGeometry.Canonical.SouriauAffineActionGroupoid

open CategoryTheory SouriauCoadjoint InfoGeometry.Algebra
open scoped BigOperators

variable {G V : Type*} [Group G] [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [LinearGroupAction G V]

/-- The existing affine coadjoint action, bundled as a native group action.
This is a definition rather than a global instance because its cocycle is a parameter. -/
def affineMulAction (Θ : AffineCoadjointCocycle G V) : MulAction G (LieDual V) where
  smul := affineCoadjointAction G V Θ
  one_smul := affineCoadjointAction_one G V Θ
  mul_smul := affineCoadjointAction_mul G V Θ

/-- The existing affine action as a functor out of the one-object group category. -/
def affineActionFunctor (Θ : AffineCoadjointCocycle G V) :
    SingleObj G ⥤ Type _ :=
  letI := affineMulAction Θ
  actionAsFunctor G (LieDual V)

/-- Mathlib supplies all groupoid laws on this category of elements. -/
abbrev AffineActionGroupoid (Θ : AffineCoadjointCocycle G V) :=
  (affineActionFunctor Θ).Elements

/-- The object corresponding to an actual continuous dual vector. -/
def object (Θ : AffineCoadjointCocycle G V) (μ : LieDual V) :
    AffineActionGroupoid Θ :=
  (affineActionFunctor Θ).elementsMk () μ

/-- The arrow labelled by `g` from `μ` to its affine transport. -/
def arrow (Θ : AffineCoadjointCocycle G V) (g : G) (μ : LieDual V) :
    object Θ μ ⟶ object Θ (affineCoadjointAction G V Θ g μ) :=
  Functor.Elements.homMk g rfl

/-- Nonempty hom sets are exactly affine-orbit reachability. -/
theorem nonempty_hom_iff (Θ : AffineCoadjointCocycle G V) (μ ν : LieDual V) :
    Nonempty (object Θ μ ⟶ object Θ ν) ↔
      ∃ g : G, affineCoadjointAction G V Θ g μ = ν := by
  constructor
  · rintro ⟨f⟩
    exact ⟨f.hom, f.map_val⟩
  · rintro ⟨g, hg⟩
    exact ⟨Functor.Elements.homMk g hg⟩

/-- An invariant scalar is constant along actual morphisms of the action groupoid. -/
theorem invariant_on_arrow (Θ : AffineCoadjointCocycle G V)
    (S : LieDual V → ℝ)
    (hS : ∀ g μ, S (affineCoadjointAction G V Θ g μ) = S μ)
    {μ ν : LieDual V} (f : object Θ μ ⟶ object Θ ν) : S μ = S ν := by
  calc
    S μ = S (affineCoadjointAction G V Θ f.hom μ) := (hS f.hom μ).symm
    _ = S ν := congrArg S f.map_val

/-- The inverse-cocycle sign is forced by the existing cocycle law and dual pairing. -/
theorem inverse_cocycle_eval (Θ : AffineCoadjointCocycle G V) (g : G) (β : V) :
    Θ g⁻¹ β = -(Θ g (Ad V g β)) := by
  have h := coadjointCocycle_mul G V Θ g g⁻¹
  rw [mul_inv_cancel, coadjointCocycle_one G V Θ] at h
  have he := congrArg (fun μ : LieDual V => μ (Ad V g β)) h
  have hzero : (0 : ℝ) = Θ g (Ad V g β) + Θ g⁻¹ β := by
    simpa [coadjoint] using he
  linarith

section FiniteEnsemble

variable {State : Type*} [Fintype State] [Nonempty State] [MulAction G State]
variable (Θ : AffineCoadjointCocycle G V) (J : AffineMomentMap G V Θ State)

/-- Souriau's negative-log convention has the inverse group element in its shift. -/
theorem neg_twistedMassieu_ad (g : G) (β : V) :
    -twistedMassieu Θ J (Ad V g β) = -twistedMassieu Θ J β - Θ g⁻¹ β := by
  have h := twistedMassieu_additive_cocycle Θ J g (Ad V g β)
  simp only [ContinuousLinearEquiv.symm_apply_apply] at h
  rw [inverse_cocycle_eval Θ g β]
  linarith

/-- The affine pairing shift and the Massieu shift cancel in the entropy expression. -/
theorem affine_pairing_add_massieu (g : G) (μ : LieDual V) (β : V) :
    affineCoadjointAction G V Θ g μ (Ad V g β) + twistedMassieu Θ J (Ad V g β) =
      μ β + twistedMassieu Θ J β := by
  have h := twistedMassieu_additive_cocycle Θ J g (Ad V g β)
  simp only [ContinuousLinearEquiv.symm_apply_apply] at h
  simp only [affineCoadjointAction, ContinuousLinearMap.add_apply, coadjoint,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply]
  linarith

/-- Midpoint concavity of `-log Z` for the actual finite affine moment-map ensemble. -/
theorem neg_twistedMassieu_midpoint (β₁ β₂ : V) :
    (-twistedMassieu Θ J β₁ + -twistedMassieu Θ J β₂) / 2 ≤
      -twistedMassieu Θ J ((1 / 2 : ℝ) • (β₁ + β₂)) := by
  let α : State → LieDual V := AffineMomentMap.momentMap G V Θ J
  let f : State → ℝ := fun i => Real.exp (-(α i β₁) / 2)
  let g : State → ℝ := fun i => Real.exp (-(α i β₂) / 2)
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
  have hMid : (∑ i, f i * g i) =
      twistedGibbsPartition Θ J ((1 / 2 : ℝ) • (β₁ + β₂)) := by
    unfold twistedGibbsPartition twistedGibbsCharacter
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp [f, g, α]
    rw [← Real.exp_add, map_smul, map_add, smul_eq_mul]
    congr 1
    ring
  have hSq1 : (∑ i, f i ^ 2) = twistedGibbsPartition Θ J β₁ := by
    unfold twistedGibbsPartition twistedGibbsCharacter
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp [f, α]
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num only [Nat.cast_ofNat]
    ring
  have hSq2 : (∑ i, g i ^ 2) = twistedGibbsPartition Θ J β₂ := by
    unfold twistedGibbsPartition twistedGibbsCharacter
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp [g, α]
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num only [Nat.cast_ofNat]
    ring
  rw [hMid, hSq1, hSq2] at hCS
  have hLog := Real.log_le_log
    (pow_pos (twistedGibbsPartition_pos Θ J ((1 / 2 : ℝ) • (β₁ + β₂))) 2) hCS
  rw [Real.log_pow,
    Real.log_mul (ne_of_gt (twistedGibbsPartition_pos Θ J β₁))
      (ne_of_gt (twistedGibbsPartition_pos Θ J β₂))] at hLog
  unfold twistedMassieu
  push_cast at hLog
  linarith

end FiniteEnsemble

end InfoGeometry.Canonical.SouriauAffineActionGroupoid
