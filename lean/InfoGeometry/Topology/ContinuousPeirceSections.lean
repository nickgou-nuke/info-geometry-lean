/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.PeirceSheetExchange
import Mathlib.Topology.Algebra.Algebra.Equiv
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Continuous Peirce sections with sheet-exchanging transition

The native subalgebra of continuous maps satisfying `f (g x) = rho (f x)`
is preserved by the existing even and odd Peirce projections whenever `rho`
exchanges `p` and `1 - p`.  The induced grading is a continuous real-linear
involution and an algebra automorphism when `p` is idempotent.

The construction retains the full noncommutative fibre algebra.  It does not
identify twisted fields with ordinary functions on the coarse quotient or
construct local trivializations.  Continuity or involutivity of the base map
and transition are not needed for the closure laws; concrete geometric
instances supply those facts separately.
-/

noncomputable section

namespace InfoGeometry.Topology.ContinuousPeirceSections

open InfoGeometry.Core

variable {X A : Type*} [TopologicalSpace X]
  [Ring A] [TopologicalSpace A] [IsTopologicalRing A]
  [Algebra ℝ A]

/-- Continuous fields obeying the specified transition law, as a native
real subalgebra with pointwise noncommutative multiplication. -/
def equivariantSections (g : X → X) (ρ : A ≃ₐ[ℝ] A) :
    Subalgebra ℝ C(X, A) where
  carrier := {f | ∀ x, f (g x) = ρ (f x)}
  zero_mem' := by intro x; simp
  one_mem' := by intro x; simp
  add_mem' := by
    intro f h hf hh x
    change f (g x) + h (g x) = ρ (f x + h x)
    rw [hf x, hh x, map_add]
  mul_mem' := by
    intro f h hf hh x
    change f (g x) * h (g x) = ρ (f x * h x)
    rw [hf x, hh x, map_mul]
  algebraMap_mem' := by
    intro r x
    change algebraMap ℝ A r = ρ (algebraMap ℝ A r)
    exact (ρ.commutes r).symm

variable (g : X → X) (ρ : A ≃ₐ[ℝ] A)

instance : IsTopologicalAddGroup (equivariantSections g ρ) :=
  inferInstanceAs (IsTopologicalAddGroup (equivariantSections g ρ).toSubmodule)

@[simp] theorem mem_equivariantSections (f : C(X, A)) :
    f ∈ equivariantSections g ρ ↔ ∀ x, f (g x) = ρ (f x) := Iff.rfl

/-- A fixed fibre element defines a constant equivariant continuous section. -/
def constantSection (a : A) (ha : ρ a = a) : equivariantSections g ρ :=
  ⟨ContinuousMap.const X a, fun _ => ha.symm⟩

@[simp] theorem constantSection_apply (a : A) (ha : ρ a = a) (x : X) :
    (constantSection g ρ a ha).1 x = a := rfl

theorem constantSection_ne_zero (a : A) (ha : ρ a = a) (x : X) (hne : a ≠ 0) :
    constantSection g ρ a ha ≠ 0 := by
  intro h
  exact hne (congrArg (fun f : equivariantSections g ρ => f.1 x) h)

/-- For a continuous fibre transition and Hausdorff fibre, equivariance cuts
out a closed subalgebra in the compact-open topology. -/
theorem isClosed_equivariantSections [T2Space A] (hρ : Continuous ρ) :
    IsClosed (equivariantSections g ρ : Set C(X, A)) := by
  change IsClosed {f : C(X, A) | ∀ x, f (g x) = ρ (f x)}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun x =>
    isClosed_eq (continuous_eval_const (g x))
      (hρ.comp (continuous_eval_const x))

/-- Restrict a pointwise continuous linear map that commutes with the fibre
transition to the actual equivariant-section carrier. -/
def sectionMap (T : A →L[ℝ] A) (hT : Function.Commute ρ T) :
    equivariantSections g ρ →L[ℝ] equivariantSections g ρ :=
  (ContinuousLinearMap.compLeftContinuous ℝ X T).restrict
    (p := (equivariantSections g ρ).toSubmodule)
    (q := (equivariantSections g ρ).toSubmodule) (by
      intro f hf x
      change T (f (g x)) = ρ (T (f x))
      rw [hf x]
      exact (hT (f x)).symm)

@[simp] theorem sectionMap_apply (T : A →L[ℝ] A) (hT : Function.Commute ρ T)
    (f : equivariantSections g ρ) (x : X) :
    (sectionMap g ρ T hT f).1 x = T (f.1 x) := rfl

/-- The existing division-free Peirce projection, with its real linearity and
continuity exposed. -/
def fibreEven (p : A) : A →L[ℝ] A where
  toFun := PeirceGrading.even p
  map_add' := (PeirceGrading.even p).map_add
  map_smul' r a := by
    simp only [PeirceGrading.even_apply, mul_smul_comm, smul_mul_assoc, smul_add,
      RingHom.id_apply]
  cont := by
    change Continuous (fun a : A => p * a * p + (1 - p) * a * (1 - p))
    exact ((continuous_const.mul continuous_id).mul continuous_const).add
      ((continuous_const.mul continuous_id).mul continuous_const)

def fibreOdd (p : A) : A →L[ℝ] A := ContinuousLinearMap.id ℝ A - fibreEven p

def fibreGrading (p : A) : A →L[ℝ] A := fibreEven p - fibreOdd p

@[simp] theorem fibreEven_apply (p a : A) :
    fibreEven p a = PeirceGrading.even p a := rfl

@[simp] theorem fibreOdd_apply (p a : A) :
    fibreOdd p a = PeirceGrading.odd p a := rfl

@[simp] theorem fibreGrading_apply (p a : A) :
    fibreGrading p a = PeirceGrading.conjugation p a := rfl

variable (p : A) (hρ : ρ p = 1 - p)

/-- The diagonal Peirce projection on continuous equivariant sections. -/
def even : equivariantSections g ρ →L[ℝ] equivariantSections g ρ :=
  sectionMap g ρ (fibreEven p)
    (PeirceSheetExchange.map_even_of_sheet_exchange ρ.toRingHom hρ)

/-- The cross-corner Peirce projection on continuous equivariant sections. -/
def odd : equivariantSections g ρ →L[ℝ] equivariantSections g ρ :=
  sectionMap g ρ (fibreOdd p)
    (PeirceSheetExchange.map_odd_of_sheet_exchange ρ.toRingHom hρ)

/-- Operator parity descends although the ordered sheet projectors are exchanged. -/
def grading : equivariantSections g ρ →L[ℝ] equivariantSections g ρ :=
  sectionMap g ρ (fibreGrading p)
    (PeirceSheetExchange.conjugation_commute_of_sheet_exchange ρ.toRingHom hρ)

@[simp] theorem even_apply (f : equivariantSections g ρ) (x : X) :
    (even g ρ p hρ f).1 x = PeirceGrading.even p (f.1 x) := rfl

@[simp] theorem odd_apply (f : equivariantSections g ρ) (x : X) :
    (odd g ρ p hρ f).1 x = PeirceGrading.odd p (f.1 x) := rfl

@[simp] theorem grading_apply (f : equivariantSections g ρ) (x : X) :
    (grading g ρ p hρ f).1 x = PeirceGrading.conjugation p (f.1 x) := rfl

theorem even_add_odd :
    even g ρ p hρ + odd g ρ p hρ =
      ContinuousLinearMap.id ℝ (equivariantSections g ρ) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  exact PeirceGrading.even_add_odd p (f.1 x)

theorem grading_eq_even_sub_odd :
    grading g ρ p hρ = even g ρ p hρ - odd g ρ p hρ := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  rfl

variable (hp : IsIdempotentElem p)

include hp

theorem even_idempotent :
    (even g ρ p hρ).comp (even g ρ p hρ) = even g ρ p hρ := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  exact LinearMap.congr_fun (PeirceGrading.even_idempotent hp).eq (f.1 x)

theorem odd_idempotent :
    (odd g ρ p hρ).comp (odd g ρ p hρ) = odd g ρ p hρ := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  exact LinearMap.congr_fun (PeirceGrading.odd_idempotent hp).eq (f.1 x)

theorem even_comp_odd :
    (even g ρ p hρ).comp (odd g ρ p hρ) = 0 := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  change PeirceGrading.even p
      (f.1 x - PeirceGrading.even p (f.1 x)) = 0
  have hidem : PeirceGrading.even p (PeirceGrading.even p (f.1 x)) =
      PeirceGrading.even p (f.1 x) :=
    LinearMap.congr_fun (PeirceGrading.even_idempotent hp).eq (f.1 x)
  rw [map_sub, hidem, sub_self]

theorem odd_comp_even :
    (odd g ρ p hρ).comp (even g ρ p hρ) = 0 := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  change PeirceGrading.even p (f.1 x) -
      PeirceGrading.even p (PeirceGrading.even p (f.1 x)) = 0
  have hidem : PeirceGrading.even p (PeirceGrading.even p (f.1 x)) =
      PeirceGrading.even p (f.1 x) :=
    LinearMap.congr_fun (PeirceGrading.even_idempotent hp).eq (f.1 x)
  rw [hidem, sub_self]

theorem grading_involutive : Function.Involutive (grading g ρ p hρ) := by
  intro f
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  change PeirceGrading.conjugation p (PeirceGrading.conjugation p (f.1 x)) = f.1 x
  simp only [PeirceGrading.conjugation_apply]
  calc
    _ = (PeirceGrading.reflection p * PeirceGrading.reflection p) * f.1 x *
        (PeirceGrading.reflection p * PeirceGrading.reflection p) := by noncomm_ring
    _ = f.1 x := by rw [PeirceGrading.reflection_sq hp]; simp

theorem grading_mul (f h : equivariantSections g ρ) :
    grading g ρ p hρ (f * h) = grading g ρ p hρ f * grading g ρ p hρ h := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  change PeirceGrading.conjugation p (f.1 x * h.1 x) =
    PeirceGrading.conjugation p (f.1 x) * PeirceGrading.conjugation p (h.1 x)
  simp only [PeirceGrading.conjugation_apply]
  symm
  calc
    _ = PeirceGrading.reflection p * f.1 x *
        (PeirceGrading.reflection p * PeirceGrading.reflection p) *
          h.1 x * PeirceGrading.reflection p := by noncomm_ring
    _ = _ := by rw [PeirceGrading.reflection_sq hp]; simp [mul_assoc]

theorem grading_one : grading g ρ p hρ 1 = 1 := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  change PeirceGrading.conjugation p 1 = 1
  simpa only [PeirceGrading.conjugation_apply, mul_one] using
    PeirceGrading.reflection_sq hp

/-- The grading is an actual real algebra automorphism of the section algebra. -/
def gradingAlgEquiv : equivariantSections g ρ ≃ₐ[ℝ] equivariantSections g ρ where
  toFun := grading g ρ p hρ
  invFun := grading g ρ p hρ
  left_inv := grading_involutive g ρ p hρ hp
  right_inv := grading_involutive g ρ p hρ hp
  map_mul' := grading_mul g ρ p hρ hp
  map_add' := (grading g ρ p hρ).map_add
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, grading_one g ρ p hρ hp]

/-- The grading with multiplication, real linearity, and both directions of
continuity bundled in Mathlib's native continuous algebra equivalence. -/
def gradingContinuousAlgEquiv :
    equivariantSections g ρ ≃A[ℝ] equivariantSections g ρ where
  toAlgEquiv := gradingAlgEquiv g ρ p hρ hp
  continuous_toFun := (grading g ρ p hρ).continuous
  continuous_invFun := (grading g ρ p hρ).continuous

end InfoGeometry.Topology.ContinuousPeirceSections

end
