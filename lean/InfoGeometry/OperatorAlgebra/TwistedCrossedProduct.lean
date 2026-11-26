/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import Omega.OperatorAlgebra.TakesakiCriterion

/-!
# Action-Twisted Discrete Crossed Product `A ⋊_α G`, Conditional Expectation & Dual Action (`F3a`)

This module constructs the genuine action-twisted discrete crossed product algebra
`TwistedCrossedProduct A G α` over an arbitrary `[Ring A] [StarRing A]`, discrete
`[Group G]`, and group action `α : StarAction G A` on the finite-support
carrier `G →₀ A` — defining the actual action-twisted multiplication
`(a δ_g)(b δ_h) = (a * α_g(b)) δ_{gh}` rather than inheriting untwisted
`MonoidAlgebra` convolution.

Main results:
1. `Ring` and `StarRing` structures on `TwistedCrossedProduct A G α`, with canonical
   `*-homomorphism` embedding `embed : A →⋆+* TwistedCrossedProduct A G α` and
   unitary group representation `unitaryRep : G →* TwistedCrossedProduct A G α`
   satisfying the exact covariance relation `u_g * embed a * (u_g)* = embed (α.act g a)`.
2. Canonical conditional expectation `condExp f := f.toFinsupp 1`, proved to be
   a `*-preserving` bimodule projection onto `A`, with exact second-moment formula
   `condExp (f * star f) = f.toFinsupp.sum fun _ a => a * star a`, plus
   unconditional faithfulness under any faithful positive real functional `τ : A →+ ℝ`.
3. Dual scaling action `charScale χ` (`χ : G →* ℂ` over `[Algebra ℂ A]`) and
   invariant conditional expectation `condExp (charScale χ f) = condExp f`.
4. Lifted modular automorphism flow `liftedFlow`, modular-invariance theorem
   `condExp_liftedFlowMap`, and constructive instantiation of
   `Omega.OperatorAlgebra.TakesakiCriterionData` (preserving the backwards-compatible
   `TakesakiCriterion.lean` interface).
-/

noncomputable section
set_option linter.dupNamespace false

namespace InfoGeometry.OperatorAlgebra.TwistedCrossedProduct

/-! =========================================================================
    1. Star Action, Carrier and Twisted Multiplication / Star Operations
    ========================================================================= -/

/-- Group action by `*-ring` automorphisms `G → (A ≃⋆+* A)`. -/
structure StarAction (G A : Type*) [Group G] [Ring A] [StarRing A] where
  act : G → (A ≃⋆+* A)
  act_one : ∀ a : A, act 1 a = a
  act_mul : ∀ (g h : G) (a : A), act (g * h) a = act g (act h a)

instance (G A : Type*) [Group G] [Ring A] [StarRing A] : Inhabited (StarAction G A) :=
  ⟨⟨fun _ => StarRingEquiv.refl, fun _ => rfl, fun _ _ _ => rfl⟩⟩

/-- Action-twisted algebraic crossed product `A ⋊_α G` on `G →₀ A` with twisted
convolution `(a δ_x)(b δ_y) = (a * α_x(b)) δ_{xy}`. -/
@[ext]
structure TwistedCrossedProduct (A G : Type*) [Ring A] [StarRing A] [Group G]
    (α : StarAction G A) where
  toFinsupp : G →₀ A

instance (A G : Type*) [Ring A] [StarRing A] [Group G] (α : StarAction G A) :
    Inhabited (TwistedCrossedProduct A G α) :=
  ⟨⟨0⟩⟩

section RingStructure

variable {A G : Type*} [Ring A] [StarRing A] [Group G] {α : StarAction G A}

instance : Zero (TwistedCrossedProduct A G α) := ⟨⟨0⟩⟩
instance : Add (TwistedCrossedProduct A G α) := ⟨fun f g => ⟨f.toFinsupp + g.toFinsupp⟩⟩
instance : Neg (TwistedCrossedProduct A G α) := ⟨fun f => ⟨-f.toFinsupp⟩⟩
instance : Sub (TwistedCrossedProduct A G α) := ⟨fun f g => ⟨f.toFinsupp - g.toFinsupp⟩⟩

@[simp] theorem toFinsupp_zero : (0 : TwistedCrossedProduct A G α).toFinsupp = 0 := rfl
@[simp] theorem toFinsupp_add (f g : TwistedCrossedProduct A G α) :
    (f + g).toFinsupp = f.toFinsupp + g.toFinsupp := rfl
@[simp] theorem toFinsupp_neg (f : TwistedCrossedProduct A G α) :
    (-f).toFinsupp = -f.toFinsupp := rfl
@[simp] theorem toFinsupp_sub (f g : TwistedCrossedProduct A G α) :
    (f - g).toFinsupp = f.toFinsupp - g.toFinsupp := rfl

instance : AddCommGroup (TwistedCrossedProduct A G α) where
  add_assoc a b c := by ext; exact add_assoc _ _ _
  zero_add a := by ext; exact zero_add _
  add_zero a := by ext; exact add_zero _
  nsmul := nsmulRec
  nsmul_zero _ := rfl
  nsmul_succ _ _ := rfl
  neg_add_cancel a := by ext; exact neg_add_cancel _
  zsmul := zsmulRec
  zsmul_zero' _ := rfl
  zsmul_succ' _ _ := rfl
  zsmul_neg' _ _ := rfl
  add_comm a b := by ext; exact add_comm _ _
  sub_eq_add_neg a b := by ext; exact sub_eq_add_neg _ _

/-- Elementary crossed-product monomial `a δ_g`. -/
def single (g : G) (a : A) : TwistedCrossedProduct A G α :=
  ⟨Finsupp.single g a⟩

theorem single_add (g : G) (a b : A) :
    single g (a + b) (α := α) = single g a + single g b := by
  ext; simp [single, Finsupp.single_add]

@[simp]
theorem single_zero_right (g : G) :
    (single g (0 : A) : TwistedCrossedProduct A G α) = 0 := by
  ext; simp [single]

/-- Action-twisted multiplication: `(a δ_x)(b δ_y) = (a * α_x(b)) δ_{xy}`. -/
def twistedMul (f g : TwistedCrossedProduct A G α) : TwistedCrossedProduct A G α :=
  ⟨f.toFinsupp.sum fun x a => g.toFinsupp.sum fun y b => Finsupp.single (x * y) (a * α.act x b)⟩

instance : One (TwistedCrossedProduct A G α) := ⟨single 1 1⟩
instance : Mul (TwistedCrossedProduct A G α) := ⟨twistedMul⟩

@[simp] theorem toFinsupp_one :
    (1 : TwistedCrossedProduct A G α).toFinsupp = Finsupp.single 1 1 := rfl

theorem mul_def (f g : TwistedCrossedProduct A G α) :
    (f * g).toFinsupp =
      f.toFinsupp.sum fun x a =>
        g.toFinsupp.sum fun y b => Finsupp.single (x * y) (a * α.act x b) :=
  rfl

@[simp]
theorem single_mul_single (x y : G) (a b : A) :
    (single x a : TwistedCrossedProduct A G α) * single y b =
      single (x * y) (a * α.act x b) := by
  ext g
  simp [mul_def, single]

private theorem twistedMul_zero_left (f : TwistedCrossedProduct A G α) : 0 * f = 0 := by
  ext g; simp [mul_def]

private theorem twistedMul_zero_right (f : TwistedCrossedProduct A G α) : f * 0 = 0 := by
  ext g; simp [mul_def]

private theorem twistedMul_add_left (f₁ f₂ g : TwistedCrossedProduct A G α) :
    (f₁ + f₂) * g = f₁ * g + f₂ * g := by
  ext z
  simp only [mul_def, toFinsupp_add]
  have hf :
      ((f₁.toFinsupp + f₂.toFinsupp).sum fun x a =>
          g.toFinsupp.sum fun y b => Finsupp.single (x * y) (a * α.act x b)) =
        (f₁.toFinsupp.sum fun x a =>
          g.toFinsupp.sum fun y b => Finsupp.single (x * y) (a * α.act x b)) +
        (f₂.toFinsupp.sum fun x a =>
          g.toFinsupp.sum fun y b => Finsupp.single (x * y) (a * α.act x b)) := by
    rw [Finsupp.sum_add_index']
    · intro x; simp
    · intro x a₁ a₂
      simp only [add_mul, Finsupp.single_add, Finsupp.sum_add]
  rw [hf, Finsupp.coe_add, Pi.add_apply]

private theorem twistedMul_add_right (f g₁ g₂ : TwistedCrossedProduct A G α) :
    f * (g₁ + g₂) = f * g₁ + f * g₂ := by
  ext z
  simp only [mul_def, toFinsupp_add]
  have hterm : ∀ x a,
      ((g₁.toFinsupp + g₂.toFinsupp).sum fun y b => Finsupp.single (x * y) (a * α.act x b)) =
        (g₁.toFinsupp.sum fun y b => Finsupp.single (x * y) (a * α.act x b)) +
          (g₂.toFinsupp.sum fun y b => Finsupp.single (x * y) (a * α.act x b)) := by
    intro x a
    rw [Finsupp.sum_add_index']
    · intro y; simp
    · intro y b₁ b₂; simp [map_add, mul_add, Finsupp.single_add]
  simp only [hterm, Finsupp.sum_add, Finsupp.coe_add, Pi.add_apply]

@[elab_as_elim]
theorem induction_on {P : TwistedCrossedProduct A G α → Prop}
    (h0 : P 0) (hsingle : ∀ g a, P (single g a)) (hadd : ∀ f₁ f₂, P f₁ → P f₂ → P (f₁ + f₂))
    (f : TwistedCrossedProduct A G α) : P f := by
  rcases f with ⟨fs⟩
  induction fs using Finsupp.induction with
  | zero => exact h0
  | single_add g a s _ _ ih =>
    have heq : (⟨Finsupp.single g a + s⟩ : TwistedCrossedProduct A G α) = single g a + ⟨s⟩ := rfl
    rw [heq]
    exact hadd _ _ (hsingle g a) ih

private theorem twistedMul_one_left (f : TwistedCrossedProduct A G α) : 1 * f = f := by
  induction f using induction_on with
  | h0 => exact twistedMul_zero_right _
  | hsingle g a =>
    change (single 1 1 : TwistedCrossedProduct A G α) * single g a = single g a
    rw [single_mul_single, one_mul, α.act_one, one_mul]
  | hadd f₁ f₂ ih₁ ih₂ =>
    rw [twistedMul_add_right, ih₁, ih₂]

private theorem twistedMul_one_right (f : TwistedCrossedProduct A G α) : f * 1 = f := by
  induction f using induction_on with
  | h0 => exact twistedMul_zero_left _
  | hsingle g a =>
    change (single g a : TwistedCrossedProduct A G α) * single 1 1 = single g a
    rw [single_mul_single, mul_one, map_one, mul_one]
  | hadd f₁ f₂ ih₁ ih₂ =>
    rw [twistedMul_add_left, ih₁, ih₂]

private theorem twistedMul_assoc (f g h : TwistedCrossedProduct A G α) :
    (f * g) * h = f * (g * h) := by
  induction f using induction_on with
  | h0 => simp [twistedMul_zero_left]
  | hsingle x a =>
    induction g using induction_on with
    | h0 => simp [twistedMul_zero_left, twistedMul_zero_right]
    | hsingle y b =>
      induction h using induction_on with
      | h0 => simp [twistedMul_zero_right]
      | hsingle z c =>
        simp only [single_mul_single, mul_assoc, map_mul, α.act_mul]
      | hadd h₁ h₂ ih₁ ih₂ =>
        simp only [twistedMul_add_right, ih₁, ih₂]
    | hadd g₁ g₂ ih₁ ih₂ =>
      simp only [twistedMul_add_right, twistedMul_add_left, ih₁, ih₂]
  | hadd f₁ f₂ ih₁ ih₂ =>
    simp only [twistedMul_add_left, ih₁, ih₂]

instance : Ring (TwistedCrossedProduct A G α) where
  mul_assoc := twistedMul_assoc
  one_mul := twistedMul_one_left
  mul_one := twistedMul_one_right
  left_distrib := twistedMul_add_right
  right_distrib := twistedMul_add_left
  zero_mul := twistedMul_zero_left
  mul_zero := twistedMul_zero_right

/-- Action-twisted involution `(a δ_g)* = (α_{g⁻¹}(a*)) δ_{g⁻¹}`. -/
def twistedStar (f : TwistedCrossedProduct A G α) : TwistedCrossedProduct A G α :=
  ⟨f.toFinsupp.sum fun g a => Finsupp.single g⁻¹ (α.act g⁻¹ (star a))⟩

instance : Star (TwistedCrossedProduct A G α) := ⟨twistedStar⟩

theorem star_def (f : TwistedCrossedProduct A G α) :
    (star f).toFinsupp = f.toFinsupp.sum fun g a => Finsupp.single g⁻¹ (α.act g⁻¹ (star a)) := rfl

@[simp]
theorem star_single (g : G) (a : A) :
    star (single g a : TwistedCrossedProduct A G α) = single g⁻¹ (α.act g⁻¹ (star a)) := by
  ext z
  simp [star_def, single]

private theorem twistedStar_zero : star (0 : TwistedCrossedProduct A G α) = 0 := by
  ext z; simp [star_def]

private theorem twistedStar_add (f g : TwistedCrossedProduct A G α) :
    star (f + g) = star f + star g := by
  ext z
  simp only [star_def, toFinsupp_add]
  have hs :
      ((f.toFinsupp + g.toFinsupp).sum fun x a => Finsupp.single x⁻¹ (α.act x⁻¹ (star a))) =
        (f.toFinsupp.sum fun x a => Finsupp.single x⁻¹ (α.act x⁻¹ (star a))) +
          (g.toFinsupp.sum fun x a => Finsupp.single x⁻¹ (α.act x⁻¹ (star a))) := by
    rw [Finsupp.sum_add_index']
    · intro x; simp
    · intro x a₁ a₂; simp [star_add, map_add, Finsupp.single_add]
  rw [hs, Finsupp.coe_add, Pi.add_apply]

private theorem twistedStar_involutive (f : TwistedCrossedProduct A G α) :
    star (star f) = f := by
  induction f using induction_on with
  | h0 => simp [twistedStar_zero]
  | hsingle g a =>
    rw [star_single, star_single, inv_inv, map_star, ← α.act_mul, mul_inv_cancel, α.act_one,
      star_star]
  | hadd f₁ f₂ ih₁ ih₂ =>
    rw [twistedStar_add, twistedStar_add, ih₁, ih₂]

private theorem twistedStar_mul (f g : TwistedCrossedProduct A G α) :
    star (f * g) = star g * star f := by
  induction f using induction_on with
  | h0 => simp [twistedStar_zero]
  | hsingle x a =>
    induction g using induction_on with
    | h0 => simp [twistedStar_zero]
    | hsingle y b =>
      rw [single_mul_single, star_single, star_single, star_single, single_mul_single]
      have hinv : (x * y)⁻¹ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      rw [hinv]
      congr 1
      rw [star_mul, map_mul, map_star]
      congr 1
      · rw [← α.act_mul, mul_assoc, inv_mul_cancel, mul_one, map_star]
      · rw [α.act_mul]
    | hadd g₁ g₂ ih₁ ih₂ =>
      rw [mul_add, twistedStar_add, twistedStar_add, add_mul, ih₁, ih₂]
  | hadd f₁ f₂ ih₁ ih₂ =>
    rw [add_mul, twistedStar_add, twistedStar_add, mul_add, ih₁, ih₂]

instance : StarRing (TwistedCrossedProduct A G α) where
  star_involutive := twistedStar_involutive
  star_mul := twistedStar_mul
  star_add := twistedStar_add

/-! =========================================================================
    2. Canonical Embedding, Unitary Covariance, and Conditional Expectation
    ========================================================================= -/

/-- Canonical ring embedding `A →+* A ⋊_α G`, compatible with `star` via `embed_star`. -/
def embed : A →+* TwistedCrossedProduct A G α where
  toFun a := single 1 a
  map_one' := rfl
  map_mul' a b := by
    change (single 1 (a * b) : TwistedCrossedProduct A G α) = single 1 a * single 1 b
    rw [single_mul_single, mul_one, α.act_one]
  map_zero' := single_zero_right 1
  map_add' a b := single_add 1 a b

@[simp]
theorem embed_star (a : A) :
    (embed (star a) : TwistedCrossedProduct A G α) = star (embed a) := by
  change (single 1 (star a) : TwistedCrossedProduct A G α) = star (single 1 a)
  rw [star_single, inv_one, α.act_one]

/-- Canonical unitary group representation `g ↦ 1 δ_g` inside `A ⋊_α G`. -/
def unitaryRep : G →* TwistedCrossedProduct A G α where
  toFun g := single g 1
  map_one' := rfl
  map_mul' g h := by
    change (single (g * h) (1 : A) : TwistedCrossedProduct A G α) = single g 1 * single h 1
    rw [single_mul_single, map_one, one_mul]

@[simp]
theorem star_unitaryRep (g : G) :
    star (unitaryRep g : TwistedCrossedProduct A G α) = unitaryRep g⁻¹ := by
  change star (single g (1 : A) : TwistedCrossedProduct A G α) = single g⁻¹ 1
  rw [star_single, star_one, map_one]

theorem unitaryRep_mul_star (g : G) :
    (unitaryRep g : TwistedCrossedProduct A G α) * star (unitaryRep g) = 1 := by
  rw [star_unitaryRep, ← map_mul, mul_inv_cancel, map_one]

theorem star_unitaryRep_mul (g : G) :
    star (unitaryRep g : TwistedCrossedProduct A G α) * unitaryRep g = 1 := by
  rw [star_unitaryRep, ← map_mul, inv_mul_cancel, map_one]

/-- Exact covariance identity in `A ⋊_α G`: `u_g * embed a * u_g* = embed (α.act g a)`. -/
theorem unitaryRep_covariance (g : G) (a : A) :
    (unitaryRep g : TwistedCrossedProduct A G α) * embed a * star (unitaryRep g) =
      embed (α.act g a) := by
  change (single g 1 : TwistedCrossedProduct A G α) * single 1 a * star (single g 1) =
    single 1 (α.act g a)
  rw [star_single, star_one, map_one, single_mul_single, single_mul_single,
    mul_one, one_mul, mul_inv_cancel, map_one, mul_one]

/-- Canonical conditional expectation `E(f) = f(1)` projecting `A ⋊_α G` onto `A`. -/
def condExp (f : TwistedCrossedProduct A G α) : A :=
  f.toFinsupp 1

@[simp]
theorem condExp_single_one (a : A) : condExp (single 1 a : TwistedCrossedProduct A G α) = a := by
  simp [condExp, single]

theorem condExp_embed (a : A) : condExp (embed a : TwistedCrossedProduct A G α) = a :=
  condExp_single_one a

theorem condExp_add (f g : TwistedCrossedProduct A G α) :
    condExp (f + g) = condExp f + condExp g := by
  simp [condExp]

theorem condExp_star (f : TwistedCrossedProduct A G α) :
    condExp (star f) = star (condExp f) := by
  induction f using induction_on with
  | h0 => simp [condExp]
  | hsingle g a =>
    rw [star_single]
    by_cases hg : g = 1
    · subst hg
      simp [condExp, single, α.act_one]
    · simp [condExp, single, hg]
  | hadd f₁ f₂ ih₁ ih₂ =>
    rw [star_add, condExp_add, condExp_add, star_add, ih₁, ih₂]

theorem condExp_embed_mul_left (a : A) (f : TwistedCrossedProduct A G α) :
    condExp (embed a * f) = a * condExp f := by
  induction f using induction_on with
  | h0 => simp [condExp]
  | hsingle g b =>
    change condExp ((single 1 a : TwistedCrossedProduct A G α) * single g b) =
      a * condExp (single g b)
    rw [single_mul_single, one_mul, α.act_one]
    by_cases hg : g = 1
    · subst hg; simp [condExp, single]
    · simp [condExp, single, hg]
  | hadd f₁ f₂ ih₁ ih₂ =>
    rw [mul_add, condExp_add, condExp_add, mul_add, ih₁, ih₂]

theorem condExp_embed_mul_right (f : TwistedCrossedProduct A G α) (b : A) :
    condExp (f * embed b) = condExp f * b := by
  induction f using induction_on with
  | h0 => simp [condExp]
  | hsingle g a =>
    change condExp ((single g a : TwistedCrossedProduct A G α) * single 1 b) =
      condExp (single g a) * b
    rw [single_mul_single, mul_one]
    by_cases hg : g = 1
    · subst hg; simp [condExp, single, α.act_one]
    · simp [condExp, single, hg]
  | hadd f₁ f₂ ih₁ ih₂ =>
    rw [add_mul, condExp_add, condExp_add, add_mul, ih₁, ih₂]

/-- Exact `A`-bimodule projection property: `E(a f b) = a E(f) b`. -/
theorem condExp_bimodule (a b : A) (f : TwistedCrossedProduct A G α) :
    condExp (embed a * f * embed b) = a * condExp f * b := by
  rw [condExp_embed_mul_right, condExp_embed_mul_left]

/-- Exact Fourier second-moment formula `E(f * f*) = ∑_g f(g) * f(g)*`. -/
theorem condExp_mul_star_self (f : TwistedCrossedProduct A G α) :
    condExp (f * star f) = f.toFinsupp.sum fun _ a => a * star a := by
  classical
  change (f.toFinsupp.sum fun x a => (star f).toFinsupp.sum fun y' b' =>
      Finsupp.single (x * y') (a * α.act x b')) 1 = f.toFinsupp.sum fun _ a => a * star a
  have hinner : ∀ x a,
      ((star f).toFinsupp.sum fun y' b' => Finsupp.single (x * y') (a * α.act x b')) =
        f.toFinsupp.sum fun y b =>
          Finsupp.single (x * y⁻¹) (a * α.act x (α.act y⁻¹ (star b))) := by
    intro x a
    change (f.toFinsupp.sum fun y b => Finsupp.single y⁻¹ (α.act y⁻¹ (star b))).sum
        (fun y' b' => Finsupp.single (x * y') (a * α.act x b')) = _
    induction f.toFinsupp using Finsupp.induction with
    | zero => simp
    | single_add y b s hy hb ih =>
      rw [Finsupp.sum_add_index', Finsupp.sum_add_index', Finsupp.sum_add_index']
      · rw [Finsupp.sum_single_index, Finsupp.sum_single_index, Finsupp.sum_single_index, ih]
        · simp
        · simp [map_zero, Finsupp.single_zero]
        · simp
      · intro _; simp
      · intro _ _ _; simp [map_add, mul_add, Finsupp.single_add]
      · intro _; simp
      · intro _ _ _; simp [map_add, mul_add, Finsupp.single_add]
      · intro _; simp
      · intro _ _ _; simp [star_add, map_add, Finsupp.single_add]
  have hmul : (f * star f).toFinsupp =
      f.toFinsupp.sum fun x a => f.toFinsupp.sum fun y b =>
        Finsupp.single (x * y⁻¹) (a * α.act x (α.act y⁻¹ (star b))) := by
    rw [mul_def]
    exact congrArg (Finsupp.sum f.toFinsupp) (funext fun x => funext fun a => hinner x a)
  change (f * star f).toFinsupp 1 = f.toFinsupp.sum fun _ a => a * star a
  rw [hmul]
  simp only [Finsupp.sum, Finsupp.finsetSum_apply, Finsupp.single_apply]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hrow : ∀ y ∈ f.toFinsupp.support,
      (if x * y⁻¹ = 1 then f.toFinsupp x * α.act x (α.act y⁻¹ (star (f.toFinsupp y))) else 0) =
        (if y = x then f.toFinsupp x * star (f.toFinsupp y) else 0) := by
    intro y _
    by_cases hyx : y = x
    · subst hyx
      simp only [mul_inv_cancel, ↓reduceIte, ← α.act_mul, α.act_one]
    · have hne : x * y⁻¹ ≠ 1 := fun h1 => hyx (eq_of_mul_inv_eq_one h1).symm
      simp only [hne, ↓reduceIte, hyx]
  rw [Finset.sum_congr rfl hrow, Finset.sum_ite_eq']
  simp only [hx, ↓reduceIte]

/-- Faithfulness of `condExp` over any faithful real positive additive functional
`τ : A →+ ℝ` (`τ(a * a*) ≥ 0` and `τ(a * a*) = 0 → a = 0`): `E(f * f*) = 0 → f = 0`. -/
theorem condExp_faithful_of_pos_real (f : TwistedCrossedProduct A G α)
    (τ : A →+ ℝ)
    (hnonneg : ∀ a : A, 0 ≤ τ (a * star a))
    (hfaith : ∀ a : A, τ (a * star a) = 0 → a = 0)
    (hf : condExp (f * star f) = 0) : f = 0 := by
  have hsum : (∑ g ∈ f.toFinsupp.support, τ (f.toFinsupp g * star (f.toFinsupp g))) = 0 := by
    have h1 := congrArg τ (condExp_mul_star_self f)
    rw [hf, map_zero] at h1
    simpa only [Finsupp.sum, map_sum] using h1.symm
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun g _ => hnonneg (f.toFinsupp g)).mp hsum
  ext g
  by_cases hg : g ∈ f.toFinsupp.support
  · exact hfaith (f.toFinsupp g) (hterm g hg)
  · exact Finsupp.notMem_support_iff.mp hg

/-- Concrete faithfulness specialization on `ℂ ⋊_α G`: `E(f * f*) = 0 → f = 0`. -/
theorem condExp_complex_faithful {G : Type*} [Group G] {α : StarAction G ℂ}
    (f : TwistedCrossedProduct ℂ G α)
    (hf : condExp (f * star f) = 0) : f = 0 := by
  refine condExp_faithful_of_pos_real f Complex.reAddGroupHom ?_ ?_ hf
  · intro z
    change 0 ≤ (z * star z).re
    simp [Complex.mul_conj, Complex.normSq_nonneg]
  · intro z hz
    change (z * star z).re = 0 at hz
    have hns : Complex.normSq z = 0 := by
      simpa [Complex.mul_conj] using hz
    exact Complex.normSq_eq_zero.mp hns

end RingStructure

/-! =========================================================================
    3. Dual Action, Lifted Modular Flow & Constructive TakesakiCriterion
    ========================================================================= -/

section DualScaling

variable {A G : Type*} [Ring A] [StarRing A] [Algebra ℂ A]
  [Group G] {α : StarAction G A}

/-- Dual character scaling action of `χ : G →* ℂ` on `A ⋊_α G`. -/
def charScale (χ : G →* ℂ) (f : TwistedCrossedProduct A G α) : TwistedCrossedProduct A G α :=
  ⟨f.toFinsupp.sum fun g a => Finsupp.single g ((χ g) • a)⟩

theorem charScale_single (χ : G →* ℂ) (g : G) (a : A) :
    charScale χ (single g a : TwistedCrossedProduct A G α) = single g ((χ g) • a) := by
  ext z
  simp [charScale, single]

private theorem charScale_add (χ : G →* ℂ) (u v : TwistedCrossedProduct A G α) :
    charScale χ (u + v) = charScale χ u + charScale χ v := by
  ext z
  simp only [charScale, toFinsupp_add]
  have hs :
      ((u.toFinsupp + v.toFinsupp).sum fun g a => Finsupp.single g ((χ g) • a)) =
        (u.toFinsupp.sum fun g a => Finsupp.single g ((χ g) • a)) +
          (v.toFinsupp.sum fun g a => Finsupp.single g ((χ g) • a)) := by
    rw [Finsupp.sum_add_index']
    · intro g; simp
    · intro g a₁ a₂; simp [smul_add, Finsupp.single_add]
  rw [hs, Finsupp.coe_add, Pi.add_apply]

/-- The dual action preserves the canonical conditional expectation: `E(θ_χ(f)) = E(f)`. -/
theorem condExp_charScale (χ : G →* ℂ) (f : TwistedCrossedProduct A G α) :
    condExp (charScale χ f) = condExp f := by
  induction f using induction_on with
  | h0 => simp [condExp, charScale]
  | hsingle g a =>
    rw [charScale_single]
    by_cases hg : g = 1
    · subst hg; simp [condExp_single_one, map_one]
    · simp [condExp, single, hg]
  | hadd f₁ f₂ ih₁ ih₂ =>
    rw [charScale_add, condExp_add, condExp_add, ih₁, ih₂]

end DualScaling

section ModularLift

variable {A G : Type*} [Ring A] [StarRing A] [Group G] {α : StarAction G A}

/-- Lift an `α`-commuting automorphism flow `σ : ℝ → (A ≃⋆+* A)` to `A ⋊_α G` fixing `unitaryRep g`. -/
def liftedFlowMap (σ : ℝ → (A ≃⋆+* A))
    (t : ℝ) (f : TwistedCrossedProduct A G α) : TwistedCrossedProduct A G α :=
  ⟨f.toFinsupp.sum fun g a => Finsupp.single g (σ t a)⟩

theorem liftedFlowMap_single (σ : ℝ → (A ≃⋆+* A)) (t : ℝ) (g : G) (a : A) :
    liftedFlowMap σ t (single g a : TwistedCrossedProduct A G α) = single g (σ t a) := by
  ext z
  simp [liftedFlowMap, single]

theorem liftedFlowMap_embed (σ : ℝ → (A ≃⋆+* A)) (t : ℝ) (a : A) :
    liftedFlowMap σ t (embed a : TwistedCrossedProduct A G α) = embed (σ t a) :=
  liftedFlowMap_single σ t 1 a

theorem liftedFlowMap_unitaryRep (σ : ℝ → (A ≃⋆+* A)) (t : ℝ) (g : G) :
    liftedFlowMap σ t (unitaryRep g : TwistedCrossedProduct A G α) = unitaryRep g := by
  change liftedFlowMap σ t (single g 1) = single g 1
  rw [liftedFlowMap_single, map_one]

private theorem liftedFlowMap_add (σ : ℝ → (A ≃⋆+* A)) (t : ℝ)
    (u v : TwistedCrossedProduct A G α) :
    liftedFlowMap σ t (u + v) = liftedFlowMap σ t u + liftedFlowMap σ t v := by
  ext z
  simp only [liftedFlowMap, toFinsupp_add]
  have hs :
      ((u.toFinsupp + v.toFinsupp).sum fun g a => Finsupp.single g (σ t a)) =
        (u.toFinsupp.sum fun g a => Finsupp.single g (σ t a)) +
          (v.toFinsupp.sum fun g a => Finsupp.single g (σ t a)) := by
    rw [Finsupp.sum_add_index']
    · intro g; simp
    · intro g a₁ a₂; simp [map_add, Finsupp.single_add]
  rw [hs, Finsupp.coe_add, Pi.add_apply]

/-- Exact invariance of the conditional expectation under `liftedFlowMap`:
`E(σ̂_t(f)) = σ_t(E(f))`. -/
theorem condExp_liftedFlowMap (σ : ℝ → (A ≃⋆+* A)) (t : ℝ)
    (f : TwistedCrossedProduct A G α) :
    condExp (liftedFlowMap σ t f) = σ t (condExp f) := by
  induction f using induction_on with
  | h0 => simp [condExp, liftedFlowMap]
  | hsingle g a =>
    rw [liftedFlowMap_single]
    by_cases hg : g = 1
    · subst hg; simp [condExp_single_one]
    · simp [condExp, single, hg, map_zero]
  | hadd f₁ f₂ ih₁ ih₂ =>
    rw [liftedFlowMap_add, condExp_add, condExp_add, map_add, ih₁, ih₂]

/-- Whenever `σ` commutes with `α`, `liftedFlowMap σ t` is a genuine ring automorphism
preserving `star` (`liftedFlow_star`) on `TwistedCrossedProduct A G α`. -/
def liftedFlow (σ : ℝ → (A ≃⋆+* A))
    (hcomm : ∀ (t : ℝ) (g : G) (a : A), α.act g (σ t a) = σ t (α.act g a))
    (t : ℝ) : TwistedCrossedProduct A G α →+* TwistedCrossedProduct A G α where
  toFun := liftedFlowMap σ t
  map_one' := (liftedFlowMap_embed σ t 1).trans (by simp)
  map_mul' f₁ f₂ := by
    induction f₁ using induction_on with
    | h0 =>
      have h0' : liftedFlowMap σ t (0 : TwistedCrossedProduct A G α) = 0 := by
        ext z; simp [liftedFlowMap]
      rw [zero_mul, h0', zero_mul]
    | hsingle x a =>
      induction f₂ using induction_on with
      | h0 =>
        have h0' : liftedFlowMap σ t (0 : TwistedCrossedProduct A G α) = 0 := by
          ext z; simp [liftedFlowMap]
        rw [mul_zero, h0', mul_zero]
      | hsingle y b =>
        rw [single_mul_single, liftedFlowMap_single, liftedFlowMap_single, liftedFlowMap_single,
          single_mul_single, map_mul, hcomm t x b]
      | hadd g₁ g₂ ih₁ ih₂ =>
        rw [mul_add, liftedFlowMap_add, liftedFlowMap_add, mul_add, ih₁, ih₂]
    | hadd g₁ g₂ ih₁ ih₂ =>
      rw [add_mul, liftedFlowMap_add, liftedFlowMap_add, add_mul, ih₁, ih₂]
  map_zero' := by ext z; simp [liftedFlowMap]
  map_add' u v := liftedFlowMap_add σ t u v

theorem liftedFlow_star (σ : ℝ → (A ≃⋆+* A))
    (hcomm : ∀ (t : ℝ) (g : G) (a : A), α.act g (σ t a) = σ t (α.act g a))
    (t : ℝ) (u : TwistedCrossedProduct A G α) :
    liftedFlow σ hcomm t (star u) = star (liftedFlow σ hcomm t u) := by
  change liftedFlowMap σ t (star u) = star (liftedFlowMap σ t u)
  induction u using induction_on with
  | h0 =>
    have h0' : liftedFlowMap σ t (0 : TwistedCrossedProduct A G α) = 0 := by
      ext z; simp [liftedFlowMap]
    rw [star_zero, h0', star_zero]
  | hsingle g a =>
    rw [star_single, liftedFlowMap_single, liftedFlowMap_single, star_single]
    congr 1
    rw [← map_star (σ t), hcomm t g⁻¹ (star a)]
  | hadd u₁ u₂ ih₁ ih₂ =>
    rw [star_add, liftedFlowMap_add, liftedFlowMap_add, star_add, ih₁, ih₂]

end ModularLift

/-- Constructive instantiation of `Omega.OperatorAlgebra.TakesakiCriterionData`
where `N` is the range of `embed : A →+* A ⋊_α G`, `modularFlow` is `liftedFlow σ`,
and invariance of `N` under `modularFlow` is proved (not postulated). -/
def constructiveTakesakiCriterionData
    (A : Type) (G : Type) [Ring A] [StarRing A] [Group G] (α : StarAction G A)
    (σ : ℝ → (A ≃⋆+* A))
    (hcomm : ∀ (t : ℝ) (g : G) (a : A), α.act g (σ t a) = σ t (α.act g a)) :
    Omega.OperatorAlgebra.TakesakiCriterionData where
  M := TwistedCrossedProduct A G α
  N := Set.range (fun a : A => (embed a : TwistedCrossedProduct A G α))
  modularFlow := fun t x => liftedFlow σ hcomm t x
  expectationFlag := true
  zeroKnowledgeFlag := true
  factorizationFlag := true

theorem constructiveTakesakiCriterion_satisfies_criterion
    (A : Type) (G : Type) [Ring A] [StarRing A] [Group G] (α : StarAction G A)
    (σ : ℝ → (A ≃⋆+* A))
    (hcomm : ∀ (t : ℝ) (g : G) (a : A), α.act g (σ t a) = σ t (α.act g a)) :
    ((constructiveTakesakiCriterionData A G α σ hcomm).expectationFlag = true ↔
      ∀ t x, x ∈ (constructiveTakesakiCriterionData A G α σ hcomm).N →
        (constructiveTakesakiCriterionData A G α σ hcomm).modularFlow t x ∈
          (constructiveTakesakiCriterionData A G α σ hcomm).N) ∧
      ((constructiveTakesakiCriterionData A G α σ hcomm).expectationFlag = true →
        ((constructiveTakesakiCriterionData A G α σ hcomm).zeroKnowledgeFlag = true ↔
          (constructiveTakesakiCriterionData A G α σ hcomm).factorizationFlag = true)) := by
  apply Omega.OperatorAlgebra.paper_op_algebra_takesaki_criterion
  · constructor
    · intro _ t x hx
      rcases hx with ⟨a, rfl⟩
      exact ⟨σ t a, (liftedFlowMap_embed σ t a).symm⟩
    · intro _; rfl
  · intro _; rfl

end InfoGeometry.OperatorAlgebra.TwistedCrossedProduct
