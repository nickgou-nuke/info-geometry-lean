/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.Unitary
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Tactic

/-!
# Discrete Action-Twisted Crossed Product `*-Algebra` (`TT-F3a`)

Constructs the algebraic discrete action-twisted convolution `*-algebra`
`TwistedCrossedProduct G A θ` over an arbitrary discrete `[Group G]`, `ℂ`-`*-algebra` `A`,
and group homomorphism `θ : G →* (A ≃⋆ₐ[ℂ] A)` on the finite-support carrier `G →₀ A`:

- Twisted convolution `(f * g) t = ∑ s ∈ f.toFinsupp.support, f.toFinsupp s * θ s (g.toFinsupp (s⁻¹ * t))`,
  matching `(a δ_g) * (b δ_h) = (a * θ g b) δ_{g * h}`.
- Twisted involution `(star f) t = θ t (star (f.toFinsupp t⁻¹))`,
  matching `star (a δ_g) = θ g⁻¹ (star a) δ_{g⁻¹}`.
- Verified `Ring`, `Algebra ℂ`, `StarRing`, and `StarModule ℂ` instances.
- Canonical `*-algebra` embedding `embedAlg : A →⋆ₐ[ℂ] TwistedCrossedProduct G A θ` (`ι`)
  and unitary group embedding `embedGroup : G → TwistedCrossedProduct G A θ` (`u`), bundled
  as `embedUnitary : G →* unitary (TwistedCrossedProduct G A θ)`, satisfying the covariance
  relation `embedGroup g * embedAlg a * star (embedGroup g) = embedAlg (θ g a)`.
- Universal property `covariantLift` for covariant `*-algebra` representations `(π, U)`,
  with uniqueness `covariantLift_unique` and unbundled helper `unitaryRepOf`.
- Dual character action `dualAction` for unitary characters `χ : G →* unitary ℂ`
  (plus helper `unitaryCharOf` for `G →* ℂ`).
- Concrete non-abelian / noncommutative witness in `section Witness` using
  `G := DihedralGroup 4` acting by unitary conjugation on `A := Matrix (Fin 2) (Fin 2) ℂ`.

## Honest Scope Boundary (`F3` Open Frontier)
This module formalizes the **discrete algebraic** action-twisted convolution `*-algebra` only.
It is distinct from untwisted `AddMonoidAlgebra` / `MonoidAlgebra` and does **not** construct a
Banach `L¹(ℝ, N; θ)` crossed product, universal or reduced `C*`-enveloping norm completion,
von Neumann weak closure, or continuous `ℝ`-action crossed products and Takesaki duality; those
analytic completions remain open scope in frontier `F3` (`docs/rn_tomita_typeiii_coverage_matrix.md`).
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Modular.TwistedCrossedProductAlgebra

/-- Carrier for the discrete algebraic action-twisted crossed product `A ⋊_θ G` over `G →₀ A`,
kept distinct from untwisted `MonoidAlgebra` / `AddMonoidAlgebra`. -/
@[ext]
structure TwistedCrossedProduct (G : Type*) [Group G] (A : Type*)
    [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    (θ : G →* (A ≃⋆ₐ[ℂ] A)) where
  toFinsupp : G →₀ A
  deriving Inhabited

namespace TwistedCrossedProduct

variable {G : Type*} [Group G]
variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable {θ : G →* (A ≃⋆ₐ[ℂ] A)}

/-- Single monomial `a δ_g` in `TwistedCrossedProduct G A θ`. -/
def single (g : G) (a : A) : TwistedCrossedProduct G A θ :=
  ⟨Finsupp.single g a⟩

omit [StarModule ℂ A] in
@[simp]
theorem theta_one (a : A) : θ (1 : G) a = a := by
  simp

omit [StarModule ℂ A] in
@[simp]
theorem theta_mul (g h : G) (a : A) : θ (g * h) a = θ g (θ h a) := by
  simp

omit [StarModule ℂ A] in
@[simp]
theorem theta_inv_apply (g : G) (a : A) : θ g⁻¹ (θ g a) = a := by
  rw [← StarAlgEquiv.mul_apply, ← map_mul, inv_mul_cancel, theta_one]

omit [StarModule ℂ A] in
@[simp]
theorem theta_apply_inv (g : G) (a : A) : θ g (θ g⁻¹ a) = a := by
  rw [← StarAlgEquiv.mul_apply, ← map_mul, mul_inv_cancel, theta_one]

instance : Zero (TwistedCrossedProduct G A θ) := ⟨⟨0⟩⟩
instance : Add (TwistedCrossedProduct G A θ) := ⟨fun f g => ⟨f.toFinsupp + g.toFinsupp⟩⟩
instance : Neg (TwistedCrossedProduct G A θ) := ⟨fun f => ⟨-f.toFinsupp⟩⟩
instance : Sub (TwistedCrossedProduct G A θ) := ⟨fun f g => ⟨f.toFinsupp - g.toFinsupp⟩⟩
instance : SMul ℂ (TwistedCrossedProduct G A θ) := ⟨fun c f => ⟨c • f.toFinsupp⟩⟩

@[simp] theorem toFinsupp_zero : (0 : TwistedCrossedProduct G A θ).toFinsupp = 0 := rfl
@[simp] theorem toFinsupp_add (f g : TwistedCrossedProduct G A θ) :
    (f + g).toFinsupp = f.toFinsupp + g.toFinsupp := rfl
@[simp] theorem toFinsupp_neg (f : TwistedCrossedProduct G A θ) :
    (-f).toFinsupp = -f.toFinsupp := rfl
@[simp] theorem toFinsupp_sub (f g : TwistedCrossedProduct G A θ) :
    (f - g).toFinsupp = f.toFinsupp - g.toFinsupp := rfl
@[simp] theorem toFinsupp_smul (c : ℂ) (f : TwistedCrossedProduct G A θ) :
    (c • f).toFinsupp = c • f.toFinsupp := rfl
@[simp] theorem toFinsupp_single (g : G) (a : A) :
    (single (θ := θ) g a).toFinsupp = Finsupp.single g a := rfl

@[simp]
theorem single_zero (g : G) : single (θ := θ) g 0 = 0 := by
  ext
  simp

theorem single_add (g : G) (a b : A) :
    single (θ := θ) g (a + b) = single g a + single g b := by
  ext
  simp [Finsupp.single_add]

@[simp]
theorem smul_single (c : ℂ) (g : G) (a : A) :
    c • single (θ := θ) g a = single g (c • a) := by
  ext
  simp [Finsupp.smul_single]

instance : AddCommGroup (TwistedCrossedProduct G A θ) where
  add_assoc f g h := by ext; exact add_assoc _ _ _
  zero_add f := by ext; exact zero_add _
  add_zero f := by ext; exact add_zero _
  nsmul := nsmulRec
  zsmul := zsmulRec
  sub_eq_add_neg f g := by ext; exact sub_eq_add_neg _ _
  neg_add_cancel f := by ext; exact neg_add_cancel _
  add_comm f g := by ext; exact add_comm _ _

instance : Module ℂ (TwistedCrossedProduct G A θ) where
  one_smul f := by ext; exact one_smul ℂ _
  mul_smul c d f := by ext; exact mul_smul c d _
  smul_zero c := by ext; exact smul_zero c
  smul_add c f g := by ext; exact smul_add c _ _
  add_smul c d f := by ext; exact add_smul c d _
  zero_smul f := by ext; exact zero_smul ℂ _

/-- Linear induction principle on `TwistedCrossedProduct G A θ` from `Finsupp.induction_linear`. -/
theorem induction_linear {motive : TwistedCrossedProduct G A θ → Prop}
    (f : TwistedCrossedProduct G A θ)
    (hzero : motive 0)
    (hadd : ∀ x y, motive x → motive y → motive (x + y))
    (hsingle : ∀ g a, motive (single g a)) : motive f := by
  rcases f with ⟨f₀⟩
  refine Finsupp.induction_linear f₀ hzero ?_ hsingle
  intro x y hx hy
  exact hadd ⟨x⟩ ⟨y⟩ hx hy

/-- Action-twisted convolution product `(a δ_s) * (b δ_r) = (a * θ s b) δ_{s * r}`. -/
def mul (f g : TwistedCrossedProduct G A θ) : TwistedCrossedProduct G A θ :=
  ⟨f.toFinsupp.sum fun s a => g.toFinsupp.sum fun r b =>
    Finsupp.single (s * r) (a * θ s b)⟩

instance : One (TwistedCrossedProduct G A θ) := ⟨single 1 1⟩
instance : Mul (TwistedCrossedProduct G A θ) := ⟨mul⟩

@[simp]
theorem toFinsupp_one :
    (1 : TwistedCrossedProduct G A θ).toFinsupp = Finsupp.single (1 : G) (1 : A) :=
  rfl

theorem mul_def (f g : TwistedCrossedProduct G A θ) :
    (f * g).toFinsupp =
      f.toFinsupp.sum fun s a => g.toFinsupp.sum fun r b =>
        Finsupp.single (s * r) (a * θ s b) :=
  rfl

@[simp]
theorem single_mul_single (s r : G) (a b : A) :
    single (θ := θ) s a * single (θ := θ) r b = single (s * r) (a * θ s b) := by
  ext t
  rw [mul_def]
  change ((Finsupp.single s a).sum fun u a' =>
    (Finsupp.single r b).sum fun v b' => Finsupp.single (u * v) (a' * θ u b')) t =
    (Finsupp.single (s * r) (a * θ s b)) t
  rw [Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]

/-- Explicit pointwise twisted convolution formula for `f * g`. -/
theorem coeff_mul (f g : TwistedCrossedProduct G A θ) (t : G) :
    (f * g).toFinsupp t =
      ∑ s ∈ f.toFinsupp.support, f.toFinsupp s * θ s (g.toFinsupp (s⁻¹ * t)) := by
  classical
  rw [mul_def, Finsupp.sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finsupp.sum_apply, Finsupp.sum_eq_single (s⁻¹ * t)]
  · simp
  · intro r _ hr
    have hsr : s * r ≠ t := by
      intro h
      apply hr
      rw [← h, inv_mul_cancel_left]
    simp [hsr]
  · intro _
    simp

private theorem mul_add_aux (f g h : TwistedCrossedProduct G A θ) :
    f * (g + h) = f * g + f * h := by
  classical
  ext t
  simp only [toFinsupp_add, mul_def]
  have hsum : ∀ s a,
      (g.toFinsupp + h.toFinsupp).sum (fun r b => Finsupp.single (s * r) (a * θ s b)) =
      g.toFinsupp.sum (fun r b => Finsupp.single (s * r) (a * θ s b)) +
      h.toFinsupp.sum (fun r b => Finsupp.single (s * r) (a * θ s b)) := fun s a =>
    Finsupp.sum_add_index' (fun _ => by simp)
      (fun _ _ _ => by simp [mul_add, Finsupp.single_add])
  simp_rw [hsum, Finsupp.sum_add]

private theorem add_mul_aux (f g h : TwistedCrossedProduct G A θ) :
    (f + g) * h = f * h + g * h := by
  classical
  ext t
  simp only [toFinsupp_add, mul_def]
  refine congrArg (fun fn : G →₀ A => fn t) (Finsupp.sum_add_index'
    (fun _ => by simp [Finsupp.sum])
    (fun s a b => ?_))
  have hpt : ∀ r d,
      Finsupp.single (s * r) ((a + b) * θ s d) =
      Finsupp.single (s * r) (a * θ s d) + Finsupp.single (s * r) (b * θ s d) := by
    intro r d
    rw [add_mul, Finsupp.single_add]
  simp_rw [hpt, Finsupp.sum_add]

private theorem zero_mul_aux (f : TwistedCrossedProduct G A θ) : 0 * f = 0 := by
  ext
  simp [mul_def]

private theorem mul_zero_aux (f : TwistedCrossedProduct G A θ) : f * 0 = 0 := by
  ext
  simp [mul_def, Finsupp.sum]

instance : Ring (TwistedCrossedProduct G A θ) where
  mul := (· * ·)
  left_distrib := mul_add_aux
  right_distrib := add_mul_aux
  zero_mul := zero_mul_aux
  mul_zero := mul_zero_aux
  one_mul f := by
    induction f using induction_linear with
    | hzero => exact mul_zero_aux 1
    | hadd x y hx hy => rw [mul_add_aux, hx, hy]
    | hsingle g a =>
        change single (θ := θ) 1 1 * single g a = single g a
        rw [single_mul_single, one_mul, theta_one, one_mul]
  mul_one f := by
    induction f using induction_linear with
    | hzero => exact zero_mul_aux 1
    | hadd x y hx hy => rw [add_mul_aux, hx, hy]
    | hsingle g a =>
        change single (θ := θ) g a * single 1 1 = single g a
        rw [single_mul_single, mul_one, map_one, mul_one]
  mul_assoc f g h := by
    induction f using induction_linear with
    | hzero => simp [zero_mul_aux]
    | hadd x y hx hy => simp [add_mul_aux, hx, hy]
    | hsingle s a =>
        induction g using induction_linear with
        | hzero => simp [zero_mul_aux, mul_zero_aux]
        | hadd x y hx hy => simp [add_mul_aux, mul_add_aux, hx, hy]
        | hsingle r b =>
            induction h using induction_linear with
            | hzero => simp [mul_zero_aux]
            | hadd x y hx hy =>
                rw [mul_add_aux, mul_add_aux, mul_add_aux, ← hx, ← hy]
            | hsingle u d =>
                simp only [single_mul_single, mul_assoc, map_mul, StarAlgEquiv.mul_apply]

instance : Algebra ℂ (TwistedCrossedProduct G A θ) :=
  Algebra.ofModule
    (fun c f g => by
      induction f using induction_linear with
      | hzero => simp
      | hadd x y hx hy => simp [smul_add, add_mul, hx, hy]
      | hsingle s a =>
          induction g using induction_linear with
          | hzero => simp
          | hadd x y hx hy =>
              rw [mul_add, mul_add, smul_add, hx, hy]
          | hsingle r b =>
              simp only [smul_single, single_mul_single, smul_mul_assoc])
    (fun c f g => by
      induction f using induction_linear with
      | hzero => simp
      | hadd x y hx hy => simp [add_mul, smul_add, hx, hy]
      | hsingle s a =>
          induction g using induction_linear with
          | hzero => simp
          | hadd x y hx hy => simp [smul_add, mul_add, hx, hy]
          | hsingle r b =>
              simp only [smul_single, single_mul_single, map_smul, mul_smul_comm])

/-- Action-twisted involution `star (a δ_s) = θ s⁻¹ (star a) δ_{s⁻¹}`. -/
def starOp (f : TwistedCrossedProduct G A θ) : TwistedCrossedProduct G A θ :=
  ⟨f.toFinsupp.sum fun s a => Finsupp.single s⁻¹ (θ s⁻¹ (star a))⟩

private theorem starOp_add (f g : TwistedCrossedProduct G A θ) :
    starOp (f + g) = starOp f + starOp g := by
  classical
  ext t
  change ((f.toFinsupp + g.toFinsupp).sum fun s a =>
    Finsupp.single s⁻¹ (θ s⁻¹ (star a))) t = (starOp f + starOp g).toFinsupp t
  rw [Finsupp.sum_add_index' (fun _ => by simp)
    (fun _ _ _ => by simp [Finsupp.single_add])]
  rfl

private theorem starOp_single (g : G) (a : A) :
    starOp (single (θ := θ) g a) = single g⁻¹ (θ g⁻¹ (star a)) := by
  ext t
  change ((Finsupp.single g a).sum fun s b => Finsupp.single s⁻¹ (θ s⁻¹ (star b))) t =
    (Finsupp.single g⁻¹ (θ g⁻¹ (star a))) t
  rw [Finsupp.sum_single_index (by simp)]

private theorem starOp_zero : starOp (0 : TwistedCrossedProduct G A θ) = 0 := by
  ext
  simp [starOp]

instance : StarRing (TwistedCrossedProduct G A θ) where
  star := starOp
  star_involutive f := by
    induction f using induction_linear with
    | hzero =>
        change starOp (starOp (0 : TwistedCrossedProduct G A θ)) = 0
        rw [starOp_zero, starOp_zero]
    | hadd x y hx hy =>
        change starOp (starOp (x + y)) = x + y
        rw [starOp_add, starOp_add, hx, hy]
    | hsingle s a =>
        change starOp (starOp (single s a)) = single s a
        rw [starOp_single, starOp_single, inv_inv, map_star, theta_apply_inv, star_star]
  star_mul f g := by
    induction f using induction_linear with
    | hzero => simp [starOp_zero]
    | hadd x y hx hy =>
        change starOp ((x + y) * g) = starOp g * starOp (x + y)
        rw [add_mul, starOp_add, starOp_add, mul_add, hx, hy]
    | hsingle s a =>
        induction g using induction_linear with
        | hzero => simp [starOp_zero]
        | hadd x y hx hy =>
            change starOp (single s a * (x + y)) = starOp (x + y) * starOp (single s a)
            rw [mul_add, starOp_add, starOp_add, add_mul, hx, hy]
        | hsingle r b =>
            change starOp (single (θ := θ) s a * single r b) =
              starOp (single r b) * starOp (single s a)
            rw [single_mul_single, starOp_single, starOp_single, starOp_single,
              single_mul_single, mul_inv_rev, star_mul, map_mul,
              theta_mul r⁻¹ s⁻¹ (star (θ s b)), theta_mul r⁻¹ s⁻¹ (star a),
              map_star (θ s⁻¹), theta_inv_apply]
  star_add := starOp_add

theorem star_def (f : TwistedCrossedProduct G A θ) :
    (star f).toFinsupp = f.toFinsupp.sum fun s a => Finsupp.single s⁻¹ (θ s⁻¹ (star a)) :=
  rfl

/-- Explicit pointwise twisted involution formula for `star f`. -/
theorem coeff_star (f : TwistedCrossedProduct G A θ) (t : G) :
    (star f).toFinsupp t = θ t (star (f.toFinsupp t⁻¹)) := by
  classical
  rw [star_def, Finsupp.sum_apply, Finsupp.sum_eq_single t⁻¹]
  · simp
  · intro s _ hs
    have hsinv : s⁻¹ ≠ t := by
      intro h
      apply hs
      rw [← h, inv_inv]
    simp [hsinv]
  · intro _
    simp

@[simp]
theorem star_single (g : G) (a : A) :
    star (single (θ := θ) g a) = single g⁻¹ (θ g⁻¹ (star a)) :=
  starOp_single g a

instance : StarModule ℂ (TwistedCrossedProduct G A θ) where
  star_smul c f := by
    induction f using induction_linear with
    | hzero => simp
    | hadd x y hx hy => simp [smul_add, star_add, hx, hy]
    | hsingle s a =>
        simp only [smul_single, star_single, star_smul, map_smul]

/-! ## Canonical Embeddings and Covariance -/

/-- Canonical `*-algebra` embedding `ι : A →⋆ₐ[ℂ] TwistedCrossedProduct G A θ` via `a ↦ a δ_1`. -/
def embedAlg : A →⋆ₐ[ℂ] TwistedCrossedProduct G A θ where
  toFun a := single 1 a
  map_one' := rfl
  map_mul' a b := by
    rw [single_mul_single, mul_one, theta_one]
  map_zero' := single_zero 1
  map_add' a b := single_add 1 a b
  commutes' c := by
    ext t
    simp [Algebra.algebraMap_eq_smul_one, Finsupp.smul_single]
  map_star' a := by
    rw [star_single, inv_one, theta_one]

@[simp]
theorem embedAlg_apply (a : A) : embedAlg (θ := θ) a = single 1 a :=
  rfl

/-- Canonical group embedding `u : G → TwistedCrossedProduct G A θ` via `g ↦ 1 δ_g`. -/
def embedGroup (g : G) : TwistedCrossedProduct G A θ :=
  single g 1

@[simp]
theorem embedGroup_apply (g : G) : embedGroup (θ := θ) g = single g 1 :=
  rfl

@[simp]
theorem embedGroup_one : embedGroup (θ := θ) 1 = 1 :=
  rfl

@[simp]
theorem embedGroup_mul (g h : G) :
    embedGroup (θ := θ) (g * h) = embedGroup g * embedGroup h := by
  rw [embedGroup_apply, embedGroup_apply, embedGroup_apply, single_mul_single, map_one, mul_one]

@[simp]
theorem embedGroup_star (g : G) :
    star (embedGroup (θ := θ) g) = embedGroup g⁻¹ := by
  rw [embedGroup_apply, star_single, star_one, map_one, embedGroup_apply]

@[simp]
theorem embedGroup_unitary_left (g : G) :
    star (embedGroup (θ := θ) g) * embedGroup g = 1 := by
  rw [embedGroup_star, ← embedGroup_mul, inv_mul_cancel, embedGroup_one]

@[simp]
theorem embedGroup_unitary_right (g : G) :
    embedGroup (θ := θ) g * star (embedGroup g) = 1 := by
  rw [embedGroup_star, ← embedGroup_mul, mul_inv_cancel, embedGroup_one]

/-- Unitary group homomorphism `G →* unitary (TwistedCrossedProduct G A θ)`. -/
def embedUnitary : G →* unitary (TwistedCrossedProduct G A θ) where
  toFun g := ⟨embedGroup g, ⟨embedGroup_unitary_left g, embedGroup_unitary_right g⟩⟩
  map_one' := Subtype.ext embedGroup_one
  map_mul' g h := Subtype.ext (embedGroup_mul g h)

@[simp]
theorem coe_embedUnitary (g : G) :
    (embedUnitary (θ := θ) g : TwistedCrossedProduct G A θ) = embedGroup g :=
  rfl

theorem single_eq_embedAlg_mul_embedGroup (g : G) (a : A) :
    single (θ := θ) g a = embedAlg a * embedGroup g := by
  rw [embedAlg_apply, embedGroup_apply, single_mul_single, one_mul, theta_one, mul_one]

theorem embedGroup_mul_embedAlg (g : G) (a : A) :
    embedGroup (θ := θ) g * embedAlg a = embedAlg (θ g a) * embedGroup g := by
  rw [embedGroup_apply, embedAlg_apply, single_mul_single, embedAlg_apply,
    single_mul_single, one_mul, mul_one, theta_one, mul_one, one_mul]

/-- Fundamental covariance relation `u_g ι(a) u_g* = ι(θ_g(a))`. -/
theorem covariant_relation (g : G) (a : A) :
    embedGroup (θ := θ) g * embedAlg a * star (embedGroup g) = embedAlg (θ g a) := by
  rw [embedGroup_mul_embedAlg, mul_assoc, embedGroup_unitary_right, mul_one]

/-! ## Covariant Representation Universal Property -/

/-- Convenience constructor bundling an unbundled unitary homomorphism `U : G → B` into
`G →* unitary B`. -/
def unitaryRepOf {B : Type*} [Ring B] [StarRing B]
    (U : G → B)
    (h_one : U 1 = 1)
    (h_mul : ∀ g h, U (g * h) = U g * U h)
    (h_star : ∀ g, star (U g) = U g⁻¹) :
    G →* unitary B where
  toFun g := ⟨U g, by
    refine ⟨?_, ?_⟩
    · rw [h_star, ← h_mul, inv_mul_cancel, h_one]
    · rw [h_star, ← h_mul, mul_inv_cancel, h_one]⟩
  map_one' := Subtype.ext h_one
  map_mul' g h := Subtype.ext (h_mul g h)

@[simp]
theorem coe_unitaryRepOf {B : Type*} [Ring B] [StarRing B]
    (U : G → B) (h_one : U 1 = 1) (h_mul : ∀ g h, U (g * h) = U g * U h)
    (h_star : ∀ g, star (U g) = U g⁻¹) (g : G) :
    (unitaryRepOf U h_one h_mul h_star g : B) = U g :=
  rfl

private def covariantLiftAddHom {B : Type*} [Ring B] [StarRing B] [Algebra ℂ B]
    (π : A →⋆ₐ[ℂ] B) (U : G →* unitary B) :
    TwistedCrossedProduct G A θ →+ B where
  toFun f := f.toFinsupp.sum fun g a => π a * (U g : B)
  map_zero' := by simp
  map_add' f g := by
    classical
    rw [toFinsupp_add, Finsupp.sum_add_index' (fun _ => by simp)
      (fun _ _ _ => by simp [add_mul])]

private theorem covariantLiftAddHom_single {B : Type*} [Ring B] [StarRing B] [Algebra ℂ B]
    (π : A →⋆ₐ[ℂ] B) (U : G →* unitary B) (g : G) (a : A) :
    covariantLiftAddHom (θ := θ) π U (single g a) = π a * (U g : B) := by
  change (Finsupp.single g a).sum (fun s b => π b * (U s : B)) = π a * (U g : B)
  rw [Finsupp.sum_single_index (by simp)]

/-- Universal `*-algebra` lift `covariantLift π U hcov : TwistedCrossedProduct G A θ →⋆ₐ[ℂ] B`
for any covariant representation `(π, U)` satisfying `U g * π a * star (U g) = π (θ g a)`. -/
def covariantLift {B : Type*} [Ring B] [StarRing B] [Algebra ℂ B]
    (π : A →⋆ₐ[ℂ] B) (U : G →* unitary B)
    (hcov : ∀ (g : G) (a : A), (U g : B) * π a * star (U g : B) = π (θ g a)) :
    TwistedCrossedProduct G A θ →⋆ₐ[ℂ] B where
  toFun := covariantLiftAddHom (θ := θ) π U
  map_one' := by
    change covariantLiftAddHom (θ := θ) π U (single 1 1) = 1
    rw [covariantLiftAddHom_single, map_one, map_one, OneMemClass.coe_one, mul_one]
  map_mul' f g := by
    have hcomm : ∀ (s : G) (b : A), (U s : B) * π b = π (θ s b) * (U s : B) := by
      intro s b
      calc
        (U s : B) * π b
          = (U s : B) * π b * (star (U s : B) * (U s : B)) := by
              rw [Unitary.coe_star_mul_self, mul_one]
        _ = ((U s : B) * π b * star (U s : B)) * (U s : B) := by
              simp only [mul_assoc]
        _ = π (θ s b) * (U s : B) := by
              rw [hcov s b]
    induction f using induction_linear with
    | hzero => simp
    | hadd x y hx hy => simp [add_mul, map_add, hx, hy]
    | hsingle s a =>
        induction g using induction_linear with
        | hzero => simp
        | hadd x y hx hy => simp [mul_add, map_add, hx, hy]
        | hsingle r b =>
            rw [single_mul_single, covariantLiftAddHom_single, covariantLiftAddHom_single,
              covariantLiftAddHom_single, map_mul, map_mul, Submonoid.coe_mul]
            calc
              π a * π (θ s b) * ((U s : B) * (U r : B))
                = π a * (π (θ s b) * (U s : B)) * (U r : B) := by
                    simp only [mul_assoc]
              _ = π a * ((U s : B) * π b) * (U r : B) := by
                    rw [hcomm s b]
              _ = (π a * (U s : B)) * (π b * (U r : B)) := by
                    simp only [mul_assoc]
  map_zero' := (covariantLiftAddHom (θ := θ) π U).map_zero
  map_add' := (covariantLiftAddHom (θ := θ) π U).map_add
  commutes' c := by
    change covariantLiftAddHom (θ := θ) π U (c • single 1 1) = algebraMap ℂ B c
    rw [smul_single, covariantLiftAddHom_single, ← Algebra.algebraMap_eq_smul_one,
      AlgHomClass.commutes, map_one, OneMemClass.coe_one, mul_one]
  map_star' f := by
    have hcomm : ∀ (s : G) (b : A), (U s : B) * π b = π (θ s b) * (U s : B) := by
      intro s b
      calc
        (U s : B) * π b
          = (U s : B) * π b * (star (U s : B) * (U s : B)) := by
              rw [Unitary.coe_star_mul_self, mul_one]
        _ = ((U s : B) * π b * star (U s : B)) * (U s : B) := by
              simp only [mul_assoc]
        _ = π (θ s b) * (U s : B) := by
              rw [hcov s b]
    induction f using induction_linear with
    | hzero => simp
    | hadd x y hx hy => simp [star_add, map_add, hx, hy]
    | hsingle s a =>
        rw [star_single, covariantLiftAddHom_single, covariantLiftAddHom_single,
          star_mul, ← hcomm s⁻¹ (star a), map_inv U s, ← Unitary.star_eq_inv,
          Unitary.coe_star, map_star π a]

@[simp]
theorem covariantLift_single {B : Type*} [Ring B] [StarRing B] [Algebra ℂ B]
    (π : A →⋆ₐ[ℂ] B) (U : G →* unitary B)
    (hcov : ∀ (g : G) (a : A), (U g : B) * π a * star (U g : B) = π (θ g a))
    (g : G) (a : A) :
    covariantLift π U hcov (single g a) = π a * (U g : B) :=
  covariantLiftAddHom_single π U g a

@[simp]
theorem covariantLift_embedAlg {B : Type*} [Ring B] [StarRing B] [Algebra ℂ B]
    (π : A →⋆ₐ[ℂ] B) (U : G →* unitary B)
    (hcov : ∀ (g : G) (a : A), (U g : B) * π a * star (U g : B) = π (θ g a))
    (a : A) :
    covariantLift π U hcov (embedAlg a) = π a := by
  rw [embedAlg_apply, covariantLift_single, map_one, OneMemClass.coe_one, mul_one]

@[simp]
theorem covariantLift_embedGroup {B : Type*} [Ring B] [StarRing B] [Algebra ℂ B]
    (π : A →⋆ₐ[ℂ] B) (U : G →* unitary B)
    (hcov : ∀ (g : G) (a : A), (U g : B) * π a * star (U g : B) = π (θ g a))
    (g : G) :
    covariantLift π U hcov (embedGroup g) = (U g : B) := by
  rw [embedGroup_apply, covariantLift_single, map_one, one_mul]

theorem covariantLift_unique_of_eq {B : Type*} [Ring B] [StarRing B] [Algebra ℂ B]
    (Φ Ψ : TwistedCrossedProduct G A θ →⋆ₐ[ℂ] B)
    (hA : ∀ a : A, Φ (embedAlg a) = Ψ (embedAlg a))
    (hG : ∀ g : G, Φ (embedGroup g) = Ψ (embedGroup g)) :
    Φ = Ψ := by
  ext f
  induction f using induction_linear with
  | hzero => simp
  | hadd x y hx hy => simp [hx, hy]
  | hsingle g a =>
      rw [single_eq_embedAlg_mul_embedGroup, map_mul, map_mul, hA a, hG g]

theorem covariantLift_unique {B : Type*} [Ring B] [StarRing B] [Algebra ℂ B]
    (π : A →⋆ₐ[ℂ] B) (U : G →* unitary B)
    (hcov : ∀ (g : G) (a : A), (U g : B) * π a * star (U g : B) = π (θ g a))
    (Φ : TwistedCrossedProduct G A θ →⋆ₐ[ℂ] B)
    (hA : ∀ a : A, Φ (embedAlg a) = π a)
    (hG : ∀ g : G, Φ (embedGroup g) = (U g : B)) :
    Φ = covariantLift π U hcov := by
  refine covariantLift_unique_of_eq Φ (covariantLift π U hcov) ?_ ?_
  · intro a
    rw [hA, covariantLift_embedAlg]
  · intro g
    rw [hG, covariantLift_embedGroup]

/-! ## Dual Character Action -/

/-- Helper promoting an unbundled unitary character `χ : G →* ℂ` satisfying
`∀ g, star (χ g) * χ g = 1` to `G →* unitary ℂ`. -/
def unitaryCharOf (χ : G →* ℂ) (hχ : ∀ g, star (χ g) * χ g = 1) : G →* unitary ℂ where
  toFun g := ⟨χ g, ⟨hχ g, by rw [mul_comm]; exact hχ g⟩⟩
  map_one' := Subtype.ext (map_one χ)
  map_mul' g h := Subtype.ext (map_mul χ g h)

@[simp]
theorem coe_unitaryCharOf (χ : G →* ℂ) (hχ : ∀ g, star (χ g) * χ g = 1) (g : G) :
    (unitaryCharOf χ hχ g : ℂ) = χ g :=
  rfl

/-- Dual `*-algebra` endomorphism `dualAction χ` associated to a unitary character
`χ : G →* unitary ℂ`: fixes `embedAlg a` and scales `embedGroup g` by `(χ g : ℂ)`. -/
def dualAction (χ : G →* unitary ℂ) :
    TwistedCrossedProduct G A θ →⋆ₐ[ℂ] TwistedCrossedProduct G A θ :=
  covariantLift embedAlg
    { toFun := fun g => χ g • embedUnitary g
      map_one' := by
        apply Subtype.ext
        simp [Unitary.coe_smul]
      map_mul' := fun g h => by
        apply Subtype.ext
        simp [Unitary.coe_smul, map_mul, smul_mul_smul_comm] }
    (fun g a => by
      change ((χ g : ℂ) • embedGroup g) * embedAlg a * star ((χ g : ℂ) • embedGroup g) =
        embedAlg (θ g a)
      rw [star_smul, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, smul_smul,
        mul_comm (star (χ g : ℂ)) (χ g : ℂ), ← Unitary.coe_star,
        Unitary.coe_mul_star_self (χ g), one_smul, covariant_relation])

@[simp]
theorem dualAction_embedAlg (χ : G →* unitary ℂ) (a : A) :
    dualAction (θ := θ) χ (embedAlg a) = embedAlg a :=
  covariantLift_embedAlg _ _ _ a

@[simp]
theorem dualAction_embedGroup (χ : G →* unitary ℂ) (g : G) :
    dualAction (θ := θ) χ (embedGroup g) = (χ g : ℂ) • embedGroup g :=
  covariantLift_embedGroup _ _ _ g

@[simp]
theorem dualAction_single (χ : G →* unitary ℂ) (g : G) (a : A) :
    dualAction (θ := θ) χ (single g a) = single g ((χ g : ℂ) • a) := by
  rw [single_eq_embedAlg_mul_embedGroup, map_mul, dualAction_embedAlg, dualAction_embedGroup,
    mul_smul_comm, ← single_eq_embedAlg_mul_embedGroup, smul_single]

theorem coeff_dualAction (χ : G →* unitary ℂ) (f : TwistedCrossedProduct G A θ) (g : G) :
    (dualAction (θ := θ) χ f).toFinsupp g = (χ g : ℂ) • f.toFinsupp g := by
  classical
  induction f using induction_linear with
  | hzero => simp
  | hadd x y hx hy => simp [hx, hy, smul_add]
  | hsingle s a =>
      simp only [dualAction_single, toFinsupp_single]
      by_cases h : s = g
      · subst h
        simp
      · simp [Finsupp.single_eq_of_ne (Ne.symm h)]

@[simp]
theorem dualAction_one :
    dualAction (G := G) (A := A) (θ := θ) 1 = StarAlgHom.id ℂ _ := by
  refine covariantLift_unique_of_eq _ _ ?_ ?_
  · intro a
    simp
  · intro g
    simp

@[simp]
theorem dualAction_comp (χ₁ χ₂ : G →* unitary ℂ) :
    (dualAction (G := G) (A := A) (θ := θ) χ₁).comp (dualAction χ₂) =
      dualAction (χ₁ * χ₂) := by
  refine covariantLift_unique_of_eq _ _ ?_ ?_
  · intro a
    simp
  · intro g
    simp [smul_smul]

/-- Dual character action bundled as a `*-algebra` automorphism. -/
def dualActionAut (χ : G →* unitary ℂ) :
    TwistedCrossedProduct G A θ ≃⋆ₐ[ℂ] TwistedCrossedProduct G A θ :=
  StarAlgEquiv.ofStarAlgHom (dualAction χ) (dualAction χ⁻¹)
    (by
      have h : χ⁻¹ * χ = 1 := by
        ext g
        simp
      rw [dualAction_comp, h, dualAction_one])
    (by
      have h : χ * χ⁻¹ = 1 := by
        ext g
        simp
      rw [dualAction_comp, h, dualAction_one])

@[simp]
theorem dualActionAut_apply (χ : G →* unitary ℂ) (f : TwistedCrossedProduct G A θ) :
    dualActionAut (θ := θ) χ f = dualAction χ f :=
  rfl

/-- Group homomorphism from unitary characters `G →* unitary ℂ` into
`*-automorphisms` of `TwistedCrossedProduct G A θ`. -/
def dualActionHom :
    (G →* unitary ℂ) →* (TwistedCrossedProduct G A θ ≃⋆ₐ[ℂ] TwistedCrossedProduct G A θ) where
  toFun := dualActionAut
  map_one' := by
    apply StarAlgEquiv.ext
    intro f
    simp
  map_mul' χ₁ χ₂ := by
    apply StarAlgEquiv.ext
    intro f
    have hcomp := congrArg (fun Φ => Φ f) (dualAction_comp (G := G) (A := A) (θ := θ) χ₁ χ₂)
    exact hcomp.symm

end TwistedCrossedProduct

/-! ## Non-Trivial Noncommutative Witness (`DihedralGroup 4` acting on `M₂(ℂ)`) -/

section Witness

open TwistedCrossedProduct

/-- Explicit noncommutativity witness in `Matrix (Fin 2) (Fin 2) ℂ` (T16). -/
theorem mat2_complex_noncomm_witness :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A * B ≠ B * A := by
  let E01 : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of ![![0, 1], ![0, 0]]
  let E10 : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of ![![0, 0], ![1, 0]]
  refine ⟨E01, E10, ?_⟩
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
  have hL : (E01 * E10) 0 0 = 1 := by
    simp [E01, E10, Matrix.mul_apply, Fin.sum_univ_two]
  have hR : (E10 * E01) 0 0 = 0 := by
    simp [E01, E10, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hL, hR] at h00
  exact one_ne_zero h00

private def rotR : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, -1; 1, 0]

private def diagZ2 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, -1]

private def rotMat2 (i : ZMod 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  rotR ^ i.val

private theorem rotR_pow_four : rotR ^ 4 = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [rotR, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]

private theorem rotR_pow_mod_four (k : ℕ) : rotR ^ (k % 4) = rotR ^ k := by
  calc
    rotR ^ (k % 4)
      = rotR ^ (k % 4) * (rotR ^ 4) ^ (k / 4) := by rw [rotR_pow_four, one_pow, mul_one]
    _ = rotR ^ (k % 4 + 4 * (k / 4)) := by rw [← pow_mul, ← pow_add]
    _ = rotR ^ k := by rw [Nat.mod_add_div]

private theorem rotMat2_zero : rotMat2 0 = 1 := by
  rw [rotMat2, ZMod.val_zero, pow_zero]

private theorem rotMat2_add (i j : ZMod 4) :
    rotMat2 (i + j) = rotMat2 i * rotMat2 j := by
  rw [rotMat2, ZMod.val_add, rotR_pow_mod_four, pow_add]
  rfl

private theorem rotMat2_sub (i j : ZMod 4) :
    rotMat2 (j - i) = rotMat2 (-i) * rotMat2 j := by
  rw [sub_eq_neg_add, rotMat2_add]

private theorem diagZ2_sq : diagZ2 * diagZ2 = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [diagZ2, Matrix.mul_apply, Fin.sum_univ_two]

private theorem rotR_mul_star : rotR * star rotR = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [rotR, Matrix.star_eq_conjTranspose, Matrix.mul_apply, Fin.sum_univ_two]

private theorem star_rotR_eq_pow : star rotR = rotR ^ 3 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [rotR, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]

private theorem commute_rotR_star : Commute rotR (star rotR) := by
  rw [star_rotR_eq_pow]
  exact Commute.pow_right rfl 3

private theorem rotMat2_mul_star (i : ZMod 4) :
    rotMat2 i * star (rotMat2 i) = 1 := by
  rw [rotMat2, star_pow, ← commute_rotR_star.mul_pow, rotR_mul_star, one_pow]

private theorem star_rotMat2 (i : ZMod 4) :
    star (rotMat2 i) = rotMat2 (-i) := by
  calc
    star (rotMat2 i)
      = 1 * star (rotMat2 i) := by rw [one_mul]
    _ = (rotMat2 (-i) * rotMat2 i) * star (rotMat2 i) := by
          rw [← rotMat2_add, neg_add_cancel, rotMat2_zero]
    _ = rotMat2 (-i) * (rotMat2 i * star (rotMat2 i)) := by rw [mul_assoc]
    _ = rotMat2 (-i) := by rw [rotMat2_mul_star, mul_one]

private theorem rotR_mul_diagZ2 : rotR * diagZ2 = diagZ2 * star rotR := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [rotR, diagZ2, Matrix.star_eq_conjTranspose, Matrix.mul_apply, Fin.sum_univ_two]

private theorem rotR_pow_mul_diagZ2 (k : ℕ) :
    rotR ^ k * diagZ2 = diagZ2 * (star rotR) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        rotR ^ (k + 1) * diagZ2
          = rotR ^ k * (rotR * diagZ2) := by rw [pow_succ, mul_assoc]
        _ = rotR ^ k * (diagZ2 * star rotR) := by rw [rotR_mul_diagZ2]
        _ = (rotR ^ k * diagZ2) * star rotR := by rw [mul_assoc]
        _ = diagZ2 * (star rotR) ^ k * star rotR := by rw [ih]
        _ = diagZ2 * (star rotR) ^ (k + 1) := by rw [mul_assoc, ← pow_succ]

private theorem rotMat2_mul_diagZ2 (i : ZMod 4) :
    rotMat2 i * diagZ2 = diagZ2 * rotMat2 (-i) := by
  rw [← star_rotMat2, rotMat2, star_pow, rotR_pow_mul_diagZ2]

private theorem star_diagZ2 : star diagZ2 = diagZ2 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [diagZ2]

private def dihedral4Mat : DihedralGroup 4 → Matrix (Fin 2) (Fin 2) ℂ
  | DihedralGroup.r i => rotMat2 i
  | DihedralGroup.sr i => diagZ2 * rotMat2 i

private theorem dihedral4Mat_one : dihedral4Mat 1 = 1 := by
  change dihedral4Mat (DihedralGroup.r 0) = 1
  simp [dihedral4Mat, rotMat2_zero]

private theorem dihedral4Mat_mul (g h : DihedralGroup 4) :
    dihedral4Mat (g * h) = dihedral4Mat g * dihedral4Mat h := by
  rcases g with i | i <;> rcases h with j | j
  · simp [dihedral4Mat, DihedralGroup.r_mul_r, rotMat2_add]
  · simp [dihedral4Mat, DihedralGroup.r_mul_sr, rotMat2_sub, ← mul_assoc, rotMat2_mul_diagZ2]
  · simp [dihedral4Mat, DihedralGroup.sr_mul_r, mul_assoc, rotMat2_add]
  · simp only [dihedral4Mat, DihedralGroup.sr_mul_sr, rotMat2_sub]
    calc
      rotMat2 (-i) * rotMat2 j
        = 1 * rotMat2 (-i) * rotMat2 j := by rw [one_mul]
      _ = (diagZ2 * diagZ2) * rotMat2 (-i) * rotMat2 j := by rw [diagZ2_sq]
      _ = diagZ2 * (diagZ2 * rotMat2 (-i)) * rotMat2 j := by simp only [mul_assoc]
      _ = diagZ2 * (rotMat2 i * diagZ2) * rotMat2 j := by rw [← rotMat2_mul_diagZ2]
      _ = diagZ2 * rotMat2 i * (diagZ2 * rotMat2 j) := by simp only [mul_assoc]

private theorem dihedral4Mat_star (g : DihedralGroup 4) :
    star (dihedral4Mat g) = dihedral4Mat g⁻¹ := by
  rcases g with i | i
  · change star (rotMat2 i) = dihedral4Mat (DihedralGroup.r (-i))
    simp [dihedral4Mat, star_rotMat2]
  · change star (diagZ2 * rotMat2 i) = dihedral4Mat (DihedralGroup.sr i)
    simp [dihedral4Mat, star_mul, star_rotMat2, star_diagZ2, rotMat2_mul_diagZ2]

/-- Faithful unitary representation of the non-abelian group `DihedralGroup 4` in `M₂(ℂ)`. -/
def dihedral4UnitaryHom : DihedralGroup 4 →* unitary (Matrix (Fin 2) (Fin 2) ℂ) :=
  unitaryRepOf dihedral4Mat dihedral4Mat_one dihedral4Mat_mul dihedral4Mat_star

/-- Unitary conjugation action of `DihedralGroup 4` on `M₂(ℂ)`. -/
def dihedral4Action :
    DihedralGroup 4 →* (Matrix (Fin 2) (Fin 2) ℂ ≃⋆ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ) :=
  (Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ)).comp dihedral4UnitaryHom

/-- Concrete noncommutative crossed product `M₂(ℂ) ⋊_θ D₄`. -/
abbrev WitnessCrossedProduct : Type :=
  TwistedCrossedProduct (DihedralGroup 4) (Matrix (Fin 2) (Fin 2) ℂ) dihedral4Action

private def e00Mat2 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, 0]

/-- The conjugation action `dihedral4Action` is genuinely non-trivial. -/
theorem dihedral4Action_nontrivial :
    dihedral4Action (DihedralGroup.r 1) e00Mat2 ≠ e00Mat2 := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
  have hval : (dihedral4Action (DihedralGroup.r 1) e00Mat2) 0 0 = 0 := by
    have hval1 : (1 : ZMod 4).val = 1 := rfl
    simp [dihedral4Action, dihedral4UnitaryHom, dihedral4Mat, rotMat2, hval1, rotR, e00Mat2,
      Unitary.conjStarAlgAut_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.star_eq_conjTranspose]
  have he00 : e00Mat2 0 0 = 1 := by
    simp [e00Mat2]
  rw [hval, he00] at h00
  exact zero_ne_one h00

/-- Non-trivial twist prevents `embedGroup (r 1)` and `embedAlg e00Mat2` from commuting. -/
theorem witness_twist_noncommute :
    embedGroup (θ := dihedral4Action) (DihedralGroup.r 1) * embedAlg e00Mat2 ≠
      embedAlg e00Mat2 * embedGroup (θ := dihedral4Action) (DihedralGroup.r 1) := by
  intro h
  have hcoeff := congrArg (fun x : WitnessCrossedProduct => x.toFinsupp (DihedralGroup.r 1)) h
  rw [embedGroup_mul_embedAlg] at hcoeff
  simp only [embedAlg_apply, embedGroup_apply, single_mul_single, one_mul, theta_one,
    mul_one, toFinsupp_single, Finsupp.single_eq_same] at hcoeff
  exact dihedral4Action_nontrivial hcoeff

/-- Concrete covariance identity for `DihedralGroup 4` acting on `M₂(ℂ)`. -/
theorem witness_covariant_relation :
    embedGroup (θ := dihedral4Action) (DihedralGroup.r 1) * embedAlg e00Mat2 *
        star (embedGroup (θ := dihedral4Action) (DihedralGroup.r 1)) =
      embedAlg (dihedral4Action (DihedralGroup.r 1) e00Mat2) :=
  covariant_relation (θ := dihedral4Action) (DihedralGroup.r 1) e00Mat2

/-- Non-abelian group multiplication transfers directly to `embedGroup`. -/
theorem witness_group_noncommute :
    embedGroup (θ := dihedral4Action) (DihedralGroup.r 1) *
        embedGroup (θ := dihedral4Action) (DihedralGroup.sr 0) ≠
      embedGroup (θ := dihedral4Action) (DihedralGroup.sr 0) *
        embedGroup (θ := dihedral4Action) (DihedralGroup.r 1) := by
  intro h
  rw [← embedGroup_mul, ← embedGroup_mul] at h
  have hcoeff := congrArg (fun x : WitnessCrossedProduct =>
    x.toFinsupp (DihedralGroup.r 1 * DihedralGroup.sr 0)) h
  have hne : DihedralGroup.sr 0 * DihedralGroup.r (1 : ZMod 4) ≠
      DihedralGroup.r 1 * DihedralGroup.sr 0 := by
    decide
  simp only [embedGroup_apply, toFinsupp_single, Finsupp.single_eq_same] at hcoeff
  rw [Finsupp.single_eq_of_ne hne.symm] at hcoeff
  exact one_ne_zero hcoeff

/-- Existence of noncommuting elements in `WitnessCrossedProduct`. -/
theorem witness_noncommutative :
    ∃ x y : WitnessCrossedProduct, x * y ≠ y * x :=
  ⟨embedGroup (DihedralGroup.r 1), embedAlg e00Mat2, witness_twist_noncommute⟩

/-- Canonical covariant lift of the identity representation of `M₂(ℂ)` and `dihedral4UnitaryHom`. -/
def witnessCovariantLift : WitnessCrossedProduct →⋆ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  covariantLift (StarAlgHom.id ℂ _) dihedral4UnitaryHom (fun _ _ => rfl)

/-- `witnessCovariantLift` recovers both `M₂(ℂ)` and `DihedralGroup 4` and distinguishes
the noncommuting product `u_{r 1} * ι(e₀₀)` from `ι(e₀₀) * u_{r 1}`. -/
theorem witness_covariantLift_nontrivial :
    witnessCovariantLift (embedAlg e00Mat2) = e00Mat2 ∧
      witnessCovariantLift (embedGroup (DihedralGroup.r 1)) =
        (dihedral4UnitaryHom (DihedralGroup.r 1) : Matrix (Fin 2) (Fin 2) ℂ) ∧
      witnessCovariantLift
          (embedGroup (θ := dihedral4Action) (DihedralGroup.r 1) * embedAlg e00Mat2) ≠
        witnessCovariantLift
          (embedAlg e00Mat2 * embedGroup (θ := dihedral4Action) (DihedralGroup.r 1)) := by
  have hA : witnessCovariantLift (embedAlg e00Mat2) = e00Mat2 :=
    covariantLift_embedAlg _ _ _ _
  have hG : witnessCovariantLift (embedGroup (DihedralGroup.r 1)) =
      (dihedral4UnitaryHom (DihedralGroup.r 1) : Matrix (Fin 2) (Fin 2) ℂ) :=
    covariantLift_embedGroup _ _ _ _
  refine ⟨hA, hG, ?_⟩
  intro h
  rw [map_mul, map_mul, hG, hA] at h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
  have hval1 : (1 : ZMod 4).val = 1 := rfl
  have hvalL :
      ((dihedral4UnitaryHom (DihedralGroup.r 1) : Matrix (Fin 2) (Fin 2) ℂ) * e00Mat2) 0 1 =
        0 := by
    simp [dihedral4UnitaryHom, dihedral4Mat, rotMat2, hval1, rotR, e00Mat2, Matrix.mul_apply,
      Fin.sum_univ_two]
  have hvalR :
      (e00Mat2 * (dihedral4UnitaryHom (DihedralGroup.r 1) : Matrix (Fin 2) (Fin 2) ℂ)) 0 1 =
        -1 := by
    simp [dihedral4UnitaryHom, dihedral4Mat, rotMat2, hval1, rotR, e00Mat2, Matrix.mul_apply,
      Fin.sum_univ_two]
  rw [hvalL, hvalR] at h01
  norm_num at h01

private def dihedralSignFun : DihedralGroup 4 →* ℂ where
  toFun g := match g with | DihedralGroup.r _ => 1 | DihedralGroup.sr _ => -1
  map_one' := rfl
  map_mul' g h := by
    rcases g with i | i <;> rcases h with j | j <;> simp

private def dihedralSignChar : DihedralGroup 4 →* unitary ℂ :=
  unitaryCharOf dihedralSignFun (fun g => by
    rcases g with i | i
    · change star (1 : ℂ) * 1 = 1
      simp
    · change star (-1 : ℂ) * (-1 : ℂ) = 1
      simp)

/-- Concrete non-triviality of `dualAction`: preserves `embedAlg e00Mat2` and negates
`embedGroup (sr 0)`. -/
theorem witness_dualAction_nontrivial :
    dualAction (θ := dihedral4Action) dihedralSignChar (embedAlg e00Mat2) = embedAlg e00Mat2 ∧
      dualAction (θ := dihedral4Action) dihedralSignChar (embedGroup (DihedralGroup.sr 0)) =
        (-1 : ℂ) • embedGroup (θ := dihedral4Action) (DihedralGroup.sr 0) ∧
      dualAction (θ := dihedral4Action) dihedralSignChar (embedGroup (DihedralGroup.sr 0)) ≠
        embedGroup (θ := dihedral4Action) (DihedralGroup.sr 0) := by
  refine ⟨dualAction_embedAlg _ _, ?_, ?_⟩
  · rw [dualAction_embedGroup]
    rfl
  · intro h
    rw [dualAction_embedGroup] at h
    have hval : (dihedralSignChar (DihedralGroup.sr 0) : ℂ) = -1 := rfl
    rw [hval] at h
    have hcoeff := congrArg (fun x : WitnessCrossedProduct =>
      (x.toFinsupp (DihedralGroup.sr 0)) 0 0) h
    simp at hcoeff
    norm_num at hcoeff

end Witness

end InfoGeometry.Modular.TwistedCrossedProductAlgebra
