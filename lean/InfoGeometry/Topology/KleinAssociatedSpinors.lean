/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Topology.KleinCliffordPinLift

/-!
# Associated orbit spaces and equivariant spinor fields

The full affine deck group, not its involutive torus shadow, acts on the fibre.
Thus a negative Clifford lift can be antiperiodic under a full translation.
These are actual quotient carriers and sections. Local triviality and a smooth
connection are not inferred from the algebraic quotient construction alone.
-/
noncomputable section
namespace InfoGeometry.Topology.KleinAssociatedSpinors
open KleinQuotientDeckInvariants KleinDeckRepresentation KleinCliffordPinLift
open scoped KleinDeckRepresentation Matrix
open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Twistor.TwistorKinematicTensor

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- Native module-valued deck equivariance, retaining the spatial base point. -/
def equivariantSections (ρ : KleinDeckGroup →* (E ≃ₗ[ℂ] E)) :
    Submodule ℂ (PlanePoint → E) where
  carrier := {ψ | ∀ g p, ψ (deckAction g p)=ρ g (ψ p)}
  zero_mem' := by intros; simp
  add_mem' := by intro f h hf hh g p; simp [hf g p,hh g p]
  smul_mem' := by intro c f hf g p; simp [hf g p]

/-- The existing affine action on the total space of the trivial cover bundle. -/
def totalAction (ρ : KleinDeckGroup →* (E ≃ₗ[ℂ] E))
    (g : KleinDeckGroup) (x : PlanePoint × E) : PlanePoint × E :=
  (deckAction g x.1, ρ g x.2)

@[simp] theorem totalAction_one (ρ : KleinDeckGroup →* (E ≃ₗ[ℂ] E)) (x : PlanePoint × E) :
    totalAction ρ KleinDeckGroup.one x=x := by
  have hρ : ρ KleinDeckGroup.one = 1 := map_one ρ
  simp [totalAction, deckAction_one, hρ]

theorem totalAction_mul (ρ : KleinDeckGroup →* (E ≃ₗ[ℂ] E))
    (g h : KleinDeckGroup) (x : PlanePoint × E) :
    totalAction ρ (KleinDeckGroup.mul g h) x=totalAction ρ g (totalAction ρ h x) := by
  apply Prod.ext
  · exact deckAction_mul g h x.1
  · exact congrArg (fun f : E ≃ₗ[ℂ] E => f x.2) (map_mul ρ g h)

/-- Full-cover orbit relation; no periodic spinor trivialization is imposed. -/
def associatedSetoid (ρ : KleinDeckGroup →* (E ≃ₗ[ℂ] E)) : Setoid (PlanePoint × E) where
  r x y := ∃ g, totalAction ρ g x=y
  iseqv := by
    constructor
    · intro x; exact ⟨1,totalAction_one ρ x⟩
    · intro x y h
      obtain ⟨g,rfl⟩ := h
      refine ⟨KleinDeckGroup.inv g, ?_⟩
      have hm := totalAction_mul ρ (KleinDeckGroup.inv g) g x
      rw [KleinDeckGroup.mul_left_inv, totalAction_one] at hm
      exact hm.symm
    · intro x y z hxy hyz
      obtain ⟨g,rfl⟩ := hxy
      obtain ⟨h,rfl⟩ := hyz
      exact ⟨h*g,totalAction_mul ρ h g x⟩

def deckOrbitSetoid : Setoid PlanePoint where
  r p q := ∃ g, deckAction g p=q
  iseqv := by
    constructor
    · intro p; exact ⟨1,deckAction_one p⟩
    · intro p q h
      obtain ⟨g,rfl⟩ := h
      refine ⟨KleinDeckGroup.inv g, ?_⟩
      have hm := deckAction_mul (KleinDeckGroup.inv g) g p
      rw [KleinDeckGroup.mul_left_inv, deckAction_one] at hm
      exact hm.symm
    · intro p q r hpq hqr
      obtain ⟨g,rfl⟩ := hpq
      obtain ⟨h,rfl⟩ := hqr
      exact ⟨h*g,deckAction_mul h g p⟩

abbrev DeckOrbitBase := Quotient deckOrbitSetoid
abbrev AssociatedSpace (ρ : KleinDeckGroup →* (E ≃ₗ[ℂ] E)) := Quotient (associatedSetoid ρ)

def bundleProjection (ρ : KleinDeckGroup →* (E ≃ₗ[ℂ] E)) : AssociatedSpace ρ → DeckOrbitBase :=
  Quotient.map Prod.fst (by
    intro x y h
    obtain ⟨g,hg⟩ := h
    exact ⟨g,congrArg Prod.fst hg⟩)

/-- An equivariant field really descends to a section of the associated quotient. -/
def descendedSection (ρ : KleinDeckGroup →* (E ≃ₗ[ℂ] E))
    (ψ : equivariantSections ρ) : DeckOrbitBase → AssociatedSpace ρ :=
  Quotient.lift (fun p => Quotient.mk _ (p,ψ.val p)) (by
    intro p q h
    obtain ⟨g,rfl⟩ := h
    apply Quotient.sound
    exact ⟨g,by simp [totalAction,ψ.property g p]⟩)

theorem descendedSection_projects (ρ : KleinDeckGroup →* (E ≃ₗ[ℂ] E))
    (ψ : equivariantSections ρ) (q : DeckOrbitBase) :
    bundleProjection ρ (descendedSection ρ ψ q)=q := by
  induction q using Quotient.inductionOn
  rfl

/-- The same unit acts on both actual spinor blocks of a twistor. -/
def twistorBlockAction (R : Matˣ) : Twistor4 ≃ₗ[ℂ] Twistor4 where
  toFun Z := (R.val.mulVec Z.1,R.val.mulVec Z.2)
  invFun Z := (R.inv.mulVec Z.1,R.inv.mulVec Z.2)
  left_inv Z := by
    apply Prod.ext
    · change R.inv.mulVec (R.val.mulVec Z.1) = Z.1
      rw [Matrix.mulVec_mulVec, Units.inv_val, Matrix.one_mulVec]
    · change R.inv.mulVec (R.val.mulVec Z.2) = Z.2
      rw [Matrix.mulVec_mulVec, Units.inv_val, Matrix.one_mulVec]
  right_inv Z := by
    apply Prod.ext
    · change R.val.mulVec (R.inv.mulVec Z.1) = Z.1
      rw [Matrix.mulVec_mulVec, Units.val_inv, Matrix.one_mulVec]
    · change R.val.mulVec (R.inv.mulVec Z.2) = Z.2
      rw [Matrix.mulVec_mulVec, Units.val_inv, Matrix.one_mulVec]
  map_add' Z W := by simp [Matrix.mulVec_add]
  map_smul' c Z := by simp [Matrix.mulVec_smul]

def twistorBlockHom : Matˣ →* (Twistor4 ≃ₗ[ℂ] Twistor4) where
  toFun := twistorBlockAction
  map_one' := by ext Z <;> simp [twistorBlockAction]
  map_mul' R S := by
    apply LinearEquiv.ext
    intro Z
    apply Prod.ext <;> ext i <;> fin_cases i <;>
      simp [twistorBlockAction, Matrix.mulVec, Matrix.mul_apply, dotProduct,
        Fin.sum_univ_two] <;> ring

def twistorPlusMonodromy (s t : Bool) : KleinDeckGroup →* (Twistor4 ≃ₗ[ℂ] Twistor4) :=
  twistorBlockHom.comp (plusMonodromy s t)

def twistorMinusMonodromy (s t : Bool) : KleinDeckGroup →* (Twistor4 ≃ₗ[ℂ] Twistor4) :=
  twistorBlockHom.comp (minusMonodromy s t)

/-- Minus-lift monodromy is visible on the twistor, but not on its quadratic kinematics. -/
theorem kinematic_negative_holonomy (Z : Twistor4) : kinematic (-Z)=kinematic Z := by
  simpa using kinematic_phase_invariant (-1 : ℂ) (by norm_num) Z

theorem twistorMinus_double_glide (s t : Bool) (Z : Twistor4) :
    twistorMinusMonodromy s t (KleinDeckGroup.mul KleinDeckGroup.b KleinDeckGroup.b) Z = -Z := by
  change twistorBlockAction (minusMonodromy s t
    (KleinDeckGroup.mul KleinDeckGroup.b KleinDeckGroup.b)) Z = -Z
  have hM := minus_double_glide s t
  apply Prod.ext <;> ext i <;> fin_cases i <;>
    simp [twistorBlockAction, hM, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem equivariant_kinematic_double_glide (s t : Bool)
    (ψ : equivariantSections (twistorMinusMonodromy s t)) (p : PlanePoint) :
    kinematic (ψ.val (p.1,p.2+2))=kinematic (ψ.val p) := by
  have h := ψ.property (KleinDeckGroup.mul KleinDeckGroup.b KleinDeckGroup.b) p
  have hb : deckAction (KleinDeckGroup.mul KleinDeckGroup.b KleinDeckGroup.b) p =
      (p.1,p.2+2) := by simp [deckAction,KleinDeckGroup.mul,KleinDeckGroup.b,signR,signZ]
  rw [hb,twistorMinus_double_glide] at h
  rw [h,kinematic_negative_holonomy]

/-- A nonzero smooth cover-level field realizes the negative-glide boundary condition. -/
def minusWave (p : PlanePoint) : Spinor :=
  Complex.exp (((Real.pi / 2 * p.2 : ℝ) : ℂ) * Complex.I) • ![1,1]

private theorem exp_half_pi :
    Complex.exp (((Real.pi/2 : ℝ):ℂ)*Complex.I)=Complex.I := by
  apply Complex.ext <;> simp [Complex.exp_re,Complex.exp_im]

theorem minusWave_glide (p : PlanePoint) :
    minusWave (deckB p)=reflectionMinus.mulVec (minusWave p) := by
  have harg : (↑Real.pi / 2 : ℂ) * (↑p.2 + 1) * Complex.I =
      ((↑Real.pi / 2 : ℂ) * ↑p.2 * Complex.I) +
        ((↑Real.pi / 2 : ℂ) * Complex.I) := by
    push_cast
    ring
  have hconst : Complex.exp ((↑Real.pi / 2 : ℂ) * Complex.I) = Complex.I := by
    convert exp_half_pi using 1 <;> push_cast <;> ring
  have hphase :
      Complex.exp ((↑Real.pi / 2 : ℂ) * (↑p.2 + 1) * Complex.I) =
        Complex.I * Complex.exp ((↑Real.pi / 2 : ℂ) * ↑p.2 * Complex.I) := by
    rw [harg, Complex.exp_add, hconst]
    ring
  ext i
  fin_cases i <;>
    simp [minusWave, deckB, hphase, reflectionMinus, reflectionPlus,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two, smul_eq_mul]

theorem minusWave_nonzero : minusWave (0,0) ≠ 0 := by
  intro h
  have hh := congrFun h (0 : Fin 2)
  norm_num [minusWave] at hh

end InfoGeometry.Topology.KleinAssociatedSpinors
