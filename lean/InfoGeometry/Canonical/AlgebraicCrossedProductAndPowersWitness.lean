/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Tactic
import InfoGeometry.Algebra.UHFColimitCStarCompletion

/-!
# Algebraic Skew-Group Crossed Product, Conditional Expectation & Powers `ω_λ` Point-Spectrum Witness (`F3`)

This module formalizes two constructive components for the Type III / crossed-product
frontier (`F3`), strictly respecting mathematical carrier boundaries:

1. **Action-Twisted Skew-Group \*-Algebra `TwistedCrossedProduct α`** (algebraic `G →₀ A`
   carrier, matching the underlying vector space of `AddMonoidAlgebra A G` while separating
   its twisted `Mul`/`Star` instances from untwisted `AddMonoidAlgebra`; explicitly **not** a
   norm-completed C\*-crossed product, which requires an additional C\*-norm / regular-representation
   completion):
   - Twisted multiplication `(a δ_g) * (b δ_h) = (a * α.act g b) δ_{g+h}`.
   - Twisted involution `(a δ_g)⋆ = α.act (-g) (star a) δ_{-g}`.
   - Dual character action `dualAction χ`, canonical conditional expectation `condExp f = f.toFinsupp 0`,
     bimodularity, faithfulness (given finite-sum positive-cone faithfulness on `A`), and exact
     commutation with any `α`-commuting modular automorphism flow (constructive conditional-
     expectation criterion on the skew-group algebra).

2. **Compatible Powers `ω_λ` (`0 < λ < 1`) State Family on `UHFStage k` & Point Spectrum `{λ^m : m ∈ ℤ}`**:
   - Defines `powersState lam k : Matrix (Fin (2^k)) (Fin (2^k)) ℂ → ℂ` with weights
     `(1 / (1 + λ))^k * λ^(bitPopcount i)` and proves exact compatibility with `uhfStep`:
     `powersState lam (k + 1) (uhfStep k A) = powersState lam k A`.
   - Proves the exact finite-stage KMS identity and exhibits for every integer `m : ℤ` a nonzero
     eigenoperator `E` at stage `k = m.natAbs` with eigenvalue `(λ^m : ℂ)`.
   - **Honest scope note**: `{λ^m : m ∈ ℤ}` is the algebraic **point spectrum** across finite UHF
     stages; the full GNS modular spectrum of the infinite completion includes `0` as a limit point
     when `λ ≠ 1`, and a finite-dimensional `UHFStage k` is never a Type `III` factor (factor and
     Type `III_λ` classification live on the weak closure / completion).
-/

noncomputable section

namespace InfoGeometry.Canonical.AlgebraicCrossedProductAndPowersWitness

/-! ## Part 1: Algebraic Action-Twisted Skew-Group \*-Algebra `A ⋊_α G` -/

section SkewGroupAlgebra

/-- Group action of an additive abelian group `G` by `ℂ`-`*-algebra` automorphisms on `A`. -/
structure StarAction (A : Type*) [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
    (G : Type*) [AddCommGroup G] where
  act : G → (A →⋆ₐ[ℂ] A)
  act_zero : ∀ a : A, act 0 a = a
  act_add : ∀ g h : G, ∀ a : A, act (g + h) a = act g (act h a)

theorem StarAction.act_neg_act {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
    {G : Type*} [AddCommGroup G] (α : StarAction A G) (g : G) (a : A) :
    α.act (-g) (α.act g a) = a := by
  rw [← α.act_add, neg_add_cancel, α.act_zero]

theorem StarAction.act_act_neg {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
    {G : Type*} [AddCommGroup G] (α : StarAction A G) (g : G) (a : A) :
    α.act g (α.act (-g) a) = a := by
  rw [← α.act_add, add_neg_cancel, α.act_zero]

/-- Carrier for the algebraic skew-group `*-algebra` `A ⋊_α G` over `G →₀ A`
    (the underlying additive carrier of `AddMonoidAlgebra A G`, wrapped so twisted
    multiplication and twisted star do not clash with untwisted `AddMonoidAlgebra`). -/
@[ext]
structure TwistedCrossedProduct {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
    {G : Type*} [AddCommGroup G] (α : StarAction A G) where
  toFinsupp : G →₀ A

namespace TwistedCrossedProduct

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
variable {G : Type*} [AddCommGroup G] {α : StarAction A G}

/-- Single monomial `a δ_g` in `A ⋊_α G`. -/
def single (g : G) (a : A) : TwistedCrossedProduct α :=
  ⟨Finsupp.single g a⟩

@[simp]
theorem single_zero (g : G) : single (α := α) g 0 = ⟨0⟩ := by
  simp [single]

instance : Zero (TwistedCrossedProduct α) := ⟨⟨0⟩⟩
instance : Add (TwistedCrossedProduct α) := ⟨fun f g => ⟨f.toFinsupp + g.toFinsupp⟩⟩
instance : Neg (TwistedCrossedProduct α) := ⟨fun f => ⟨-f.toFinsupp⟩⟩
instance : Sub (TwistedCrossedProduct α) := ⟨fun f g => ⟨f.toFinsupp - g.toFinsupp⟩⟩
instance : SMul ℂ (TwistedCrossedProduct α) := ⟨fun c f => ⟨c • f.toFinsupp⟩⟩

instance : AddCommGroup (TwistedCrossedProduct α) where
  add_assoc f g h := by ext; exact add_assoc _ _ _
  zero_add f := by ext; exact zero_add _
  add_zero f := by ext; exact add_zero _
  nsmul n f := ⟨n • f.toFinsupp⟩
  nsmul_zero f := by ext1; exact zero_smul ℕ f.toFinsupp
  nsmul_succ n f := by ext1; exact succ_nsmul f.toFinsupp n
  zsmul n f := ⟨n • f.toFinsupp⟩
  zsmul_zero' f := by ext1; exact zero_smul ℤ f.toFinsupp
  zsmul_succ' n f := by
    ext1
    change (((n : ℤ) + 1) • f.toFinsupp) = (n : ℤ) • f.toFinsupp + f.toFinsupp
    rw [add_zsmul, one_zsmul]
  zsmul_neg' n f := by
    ext1
    change ((Int.negSucc n : ℤ) • f.toFinsupp) = -(((n + 1 : ℕ) : ℤ) • f.toFinsupp)
    rw [Int.negSucc_eq, neg_zsmul]
    rfl
  neg_add_cancel f := by ext; exact neg_add_cancel _
  add_comm f g := by ext; exact add_comm _ _
  sub_eq_add_neg f g := by ext; exact sub_eq_add_neg _ _

instance : Module ℂ (TwistedCrossedProduct α) where
  one_smul f := by ext; exact one_smul ℂ _
  mul_smul c d f := by ext; exact mul_smul c d _
  smul_zero c := by ext; exact smul_zero c
  smul_add c f g := by ext; exact smul_add c _ _
  add_smul c d f := by ext; exact add_smul c d _
  zero_smul f := by ext; exact zero_smul ℂ _

@[simp] theorem toFinsupp_zero : (0 : TwistedCrossedProduct α).toFinsupp = 0 := rfl
@[simp] theorem toFinsupp_add (f g : TwistedCrossedProduct α) :
    (f + g).toFinsupp = f.toFinsupp + g.toFinsupp := rfl
@[simp] theorem toFinsupp_neg (f : TwistedCrossedProduct α) : (-f).toFinsupp = -f.toFinsupp := rfl
@[simp] theorem toFinsupp_sub (f g : TwistedCrossedProduct α) :
    (f - g).toFinsupp = f.toFinsupp - g.toFinsupp := rfl
@[simp] theorem toFinsupp_smul (c : ℂ) (f : TwistedCrossedProduct α) :
    (c • f).toFinsupp = c • f.toFinsupp := rfl
@[simp] theorem toFinsupp_single (g : G) (a : A) :
    (single (α := α) g a).toFinsupp = Finsupp.single g a := rfl

/-- Twisted multiplication `(a δ_g) * (b δ_h) = (a * α.act g b) δ_{g+h}`. -/
def mul (f g : TwistedCrossedProduct α) : TwistedCrossedProduct α :=
  ⟨f.toFinsupp.sum fun x a => g.toFinsupp.sum fun y b => Finsupp.single (x + y) (a * α.act x b)⟩

instance : One (TwistedCrossedProduct α) := ⟨single 0 1⟩
instance : Mul (TwistedCrossedProduct α) := ⟨mul⟩

@[simp] theorem toFinsupp_one : (1 : TwistedCrossedProduct α).toFinsupp = Finsupp.single 0 1 := rfl

theorem single_mul_single (x y : G) (a b : A) :
    single (α := α) x a * single (α := α) y b = single (x + y) (a * α.act x b) := by
  change (⟨(Finsupp.single x a).sum fun u a' =>
    (Finsupp.single y b).sum fun v b' => Finsupp.single (u + v) (a' * α.act u b')⟩ :
      TwistedCrossedProduct α) = single (x + y) (a * α.act x b)
  rw [Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
  rfl

theorem mul_def (f g : TwistedCrossedProduct α) :
    (f * g).toFinsupp =
      f.toFinsupp.sum fun x a => g.toFinsupp.sum fun y b => Finsupp.single (x + y) (a * α.act x b) :=
  rfl

instance : Ring (TwistedCrossedProduct α) where
  mul := (· * ·)
  left_distrib f g h := by
    classical
    ext z
    simp only [toFinsupp_add, mul_def]
    have hsum : ∀ x a,
        (g.toFinsupp + h.toFinsupp).sum (fun y b => Finsupp.single (x + y) (a * α.act x b)) =
        g.toFinsupp.sum (fun y b => Finsupp.single (x + y) (a * α.act x b)) +
        h.toFinsupp.sum (fun y b => Finsupp.single (x + y) (a * α.act x b)) := fun x a =>
      Finsupp.sum_add_index (fun _ _ => by simp)
        (fun _ _ _ _ => by simp [mul_add, Finsupp.single_add])
    simp_rw [hsum]
    have houter :
        (f.toFinsupp.sum fun x a =>
          (g.toFinsupp.sum fun y b => Finsupp.single (x + y) (a * α.act x b)) +
          (h.toFinsupp.sum fun y b => Finsupp.single (x + y) (a * α.act x b))) =
        (f.toFinsupp.sum fun x a => g.toFinsupp.sum fun y b => Finsupp.single (x + y) (a * α.act x b)) +
        (f.toFinsupp.sum fun x a => h.toFinsupp.sum fun y b => Finsupp.single (x + y) (a * α.act x b)) :=
      Finsupp.sum_add
    exact congrArg (fun fn : G →₀ A => fn z) houter
  right_distrib f g h := by
    classical
    ext z
    simp only [toFinsupp_add, mul_def]
    have hsum :
        (f.toFinsupp + g.toFinsupp).sum (fun x a =>
          h.toFinsupp.sum fun y b => Finsupp.single (x + y) (a * α.act x b)) =
        (f.toFinsupp.sum fun x a =>
          h.toFinsupp.sum fun y b => Finsupp.single (x + y) (a * α.act x b)) +
        (g.toFinsupp.sum fun x a =>
          h.toFinsupp.sum fun y b => Finsupp.single (x + y) (a * α.act x b)) := by
      refine Finsupp.sum_add_index (fun _ _ => by simp) (fun x _ a b => ?_)
      have hsub : (fun y d => Finsupp.single (x + y) ((a + b) * α.act x d)) =
          fun y d => Finsupp.single (x + y) (a * α.act x d) +
            Finsupp.single (x + y) (b * α.act x d) := by
        funext y d; rw [add_mul, Finsupp.single_add]
      rw [hsub, Finsupp.sum_add]
    exact congrArg (fun fn : G →₀ A => fn z) hsum
  zero_mul f := by ext; simp [mul_def]
  mul_zero f := by ext; simp [mul_def]
  one_mul f := by
    ext z
    change ((Finsupp.single (0 : G) (1 : A)).sum fun x a =>
      f.toFinsupp.sum fun y b => Finsupp.single (x + y) (a * α.act x b)) z = f.toFinsupp z
    rw [Finsupp.sum_single_index (by simp)]
    simp [α.act_zero]
  mul_one f := by
    ext z
    change (f.toFinsupp.sum fun x a =>
      (Finsupp.single (0 : G) (1 : A)).sum fun y b =>
        Finsupp.single (x + y) (a * α.act x b)) z = f.toFinsupp z
    have h1 : ∀ x a,
        (Finsupp.single (0 : G) (1 : A)).sum (fun y b => Finsupp.single (x + y) (a * α.act x b)) =
        Finsupp.single x a := fun x a => by
      rw [Finsupp.sum_single_index (by simp)]
      simp
    simp_rw [h1]
    rw [Finsupp.sum_single]
  mul_assoc f g h := by
    ext w
    change ((f * g).toFinsupp.sum fun xy c => h.toFinsupp.sum fun z d =>
        Finsupp.single (xy + z) (c * α.act xy d)) w =
      (f.toFinsupp.sum fun x a => (g * h).toFinsupp.sum fun yz c =>
        Finsupp.single (x + yz) (a * α.act x c)) w
    have hL :
        ((f * g).toFinsupp.sum fun xy c => h.toFinsupp.sum fun z d =>
          Finsupp.single (xy + z) (c * α.act xy d)) =
        f.toFinsupp.sum fun x a => g.toFinsupp.sum fun y b => h.toFinsupp.sum fun z d =>
          Finsupp.single ((x + y) + z) ((a * α.act x b) * α.act (x + y) d) := by
      rw [mul_def]
      rw [Finsupp.sum_sum_index (f := f.toFinsupp) (fun _ => by simp)
        (fun _ _ _ => by simp [add_mul])]
      refine Finsupp.sum_congr fun x _ => ?_
      rw [Finsupp.sum_sum_index (f := g.toFinsupp) (fun _ => by simp)
        (fun _ _ _ => by simp [add_mul])]
      refine Finsupp.sum_congr fun y _ => ?_
      exact Finsupp.sum_single_index (by simp)
    have hR :
        (f.toFinsupp.sum fun x a => (g * h).toFinsupp.sum fun yz c =>
          Finsupp.single (x + yz) (a * α.act x c)) =
        f.toFinsupp.sum fun x a => g.toFinsupp.sum fun y b => h.toFinsupp.sum fun z d =>
          Finsupp.single (x + (y + z)) (a * (α.act x b * α.act x (α.act y d))) := by
      refine Finsupp.sum_congr fun x _ => ?_
      rw [mul_def]
      rw [Finsupp.sum_sum_index (f := g.toFinsupp) (fun _ => by simp)
        (fun _ _ _ => by simp [mul_add])]
      refine Finsupp.sum_congr fun y _ => ?_
      rw [Finsupp.sum_sum_index (f := h.toFinsupp) (fun _ => by simp)
        (fun _ _ _ => by simp [mul_add])]
      refine Finsupp.sum_congr fun z _ => ?_
      rw [Finsupp.sum_single_index (by simp)]
      simp [map_mul]
    have hterm :
        (f.toFinsupp.sum fun x a => g.toFinsupp.sum fun y b => h.toFinsupp.sum fun z d =>
          Finsupp.single ((x + y) + z) ((a * α.act x b) * α.act (x + y) d)) =
        (f.toFinsupp.sum fun x a => g.toFinsupp.sum fun y b => h.toFinsupp.sum fun z d =>
          Finsupp.single (x + (y + z)) (a * (α.act x b * α.act x (α.act y d)))) := by
      refine Finsupp.sum_congr fun x _ => Finsupp.sum_congr fun y _ => Finsupp.sum_congr fun z _ => ?_
      rw [add_assoc, mul_assoc, α.act_add]
    exact congrArg (fun fn : G →₀ A => fn w) (hL.trans (hterm.trans hR.symm))

/-- Algebra instance over `ℂ`. -/
instance : Algebra ℂ (TwistedCrossedProduct α) :=
  Algebra.ofModule
    (fun c f g => by
      ext z
      simp only [toFinsupp_smul, mul_def]
      have hterm :
          ((c • f.toFinsupp).sum fun x a =>
            g.toFinsupp.sum fun y b => Finsupp.single (x + y) (a * α.act x b)) =
          c • (f.toFinsupp.sum fun x a =>
            g.toFinsupp.sum fun y b => Finsupp.single (x + y) (a * α.act x b)) := by
        rw [Finsupp.sum_smul_index' (b := c) (fun _ => by simp), Finsupp.smul_sum]
        refine Finsupp.sum_congr fun x _ => ?_
        rw [Finsupp.smul_sum]
        refine Finsupp.sum_congr fun y _ => ?_
        rw [smul_mul_assoc, ← Finsupp.smul_single]
      exact congrArg (fun fn : G →₀ A => fn z) hterm)
    (fun c f g => by
      ext z
      simp only [toFinsupp_smul, mul_def]
      have hterm :
          (f.toFinsupp.sum fun x a =>
            (c • g.toFinsupp).sum fun y b => Finsupp.single (x + y) (a * α.act x b)) =
          c • (f.toFinsupp.sum fun x a =>
            g.toFinsupp.sum fun y b => Finsupp.single (x + y) (a * α.act x b)) := by
        rw [Finsupp.smul_sum]
        refine Finsupp.sum_congr fun x _ => ?_
        rw [Finsupp.sum_smul_index' (b := c) (fun _ => by simp), Finsupp.smul_sum]
        refine Finsupp.sum_congr fun y _ => ?_
        rw [map_smul, mul_smul_comm, ← Finsupp.smul_single]
      exact congrArg (fun fn : G →₀ A => fn z) hterm)

/-- Twisted star involution `(a δ_g)⋆ = α.act (-g) (star a) δ_{-g}`. -/
def starOp (f : TwistedCrossedProduct α) : TwistedCrossedProduct α :=
  ⟨f.toFinsupp.sum fun x a => Finsupp.single (-x) (α.act (-x) (star a))⟩

instance : StarRing (TwistedCrossedProduct α) where
  star := starOp
  star_involutive f := by
    ext z
    change ((f.toFinsupp.sum fun x a => Finsupp.single (-x) (α.act (-x) (star a))).sum fun y b =>
      Finsupp.single (-y) (α.act (-y) (star b))) z = f.toFinsupp z
    rw [Finsupp.sum_sum_index (f := f.toFinsupp) (fun _ => by simp)
      (fun _ _ _ => by simp [Finsupp.single_add])]
    have hpt : ∀ x a,
        ((Finsupp.single (-x) (α.act (-x) (star a))).sum fun y b =>
          Finsupp.single (-y) (α.act (-y) (star b))) = Finsupp.single x a := fun x a => by
      rw [Finsupp.sum_single_index (by simp), neg_neg, map_star, α.act_act_neg, star_star]
    simp_rw [hpt, Finsupp.sum_single]
  star_mul f g := by
    ext z
    change ((f * g).toFinsupp.sum fun u c => Finsupp.single (-u) (α.act (-u) (star c))) z =
      (starOp g * starOp f).toFinsupp z
    have hL :
        ((f * g).toFinsupp.sum fun u c => Finsupp.single (-u) (α.act (-u) (star c))) =
        g.toFinsupp.sum fun y b => f.toFinsupp.sum fun x a =>
          Finsupp.single (-y + -x) (α.act (-y) (star b) * α.act (-y) (α.act (-x) (star a))) := by
      rw [mul_def]
      rw [Finsupp.sum_sum_index (f := f.toFinsupp) (fun _ => by simp)
        (fun _ _ _ => by simp [Finsupp.single_add])]
      have hswap :
          (f.toFinsupp.sum fun x a =>
            (g.toFinsupp.sum fun y b => Finsupp.single (x + y) (a * α.act x b)).sum fun u c =>
              Finsupp.single (-u) (α.act (-u) (star c))) =
          g.toFinsupp.sum fun y b => f.toFinsupp.sum fun x a =>
            Finsupp.single (-(x + y)) (α.act (-(x + y)) (star (a * α.act x b))) := by
        have hstep :
            (f.toFinsupp.sum fun x a =>
              (g.toFinsupp.sum fun y b => Finsupp.single (x + y) (a * α.act x b)).sum fun u c =>
                Finsupp.single (-u) (α.act (-u) (star c))) =
            f.toFinsupp.sum fun x a => g.toFinsupp.sum fun y b =>
              Finsupp.single (-(x + y)) (α.act (-(x + y)) (star (a * α.act x b))) := by
          refine Finsupp.sum_congr fun x _ => ?_
          rw [Finsupp.sum_sum_index (f := g.toFinsupp) (fun _ => by simp)
            (fun _ _ _ => by simp [Finsupp.single_add])]
          exact Finsupp.sum_congr fun y _ => Finsupp.sum_single_index (by simp)
        rw [hstep, Finsupp.sum_comm]
      rw [hswap]
      refine Finsupp.sum_congr fun y _ => Finsupp.sum_congr fun x _ => ?_
      have hidx : -(x + y) = -y + -x := by rw [neg_add, add_comm]
      have h1 : α.act (-y + -x) (star (α.act x (g.toFinsupp y))) = α.act (-y) (star (g.toFinsupp y)) := by
        rw [← map_star (α.act x), α.act_add, α.act_neg_act]
      have h2 : α.act (-y + -x) (star (f.toFinsupp x)) = α.act (-y) (α.act (-x) (star (f.toFinsupp x))) :=
        α.act_add (-y) (-x) _
      rw [hidx, star_mul, map_mul, h1, h2]
    have hR :
        (starOp g * starOp f).toFinsupp =
        g.toFinsupp.sum fun y b => f.toFinsupp.sum fun x a =>
          Finsupp.single (-y + -x) (α.act (-y) (star b) * α.act (-y) (α.act (-x) (star a))) := by
      rw [mul_def]
      unfold starOp
      rw [Finsupp.sum_sum_index (f := g.toFinsupp) (fun _ => by simp)
        (fun _ _ _ => by simp [add_mul])]
      refine Finsupp.sum_congr fun y _ => ?_
      rw [Finsupp.sum_single_index (by simp)]
      rw [Finsupp.sum_sum_index (f := f.toFinsupp) (fun _ => by simp)
        (fun _ _ _ => by simp [mul_add])]
      refine Finsupp.sum_congr fun x _ => Finsupp.sum_single_index (by simp)
    exact congrArg (fun fn : G →₀ A => fn z) (hL.trans hR.symm)
  star_add f g := by
    classical
    ext z
    change ((f.toFinsupp + g.toFinsupp).sum fun x a => Finsupp.single (-x) (α.act (-x) (star a))) z = _
    have hsum :
        (f.toFinsupp + g.toFinsupp).sum (fun x a => Finsupp.single (-x) (α.act (-x) (star a))) =
        (f.toFinsupp.sum fun x a => Finsupp.single (-x) (α.act (-x) (star a))) +
        (g.toFinsupp.sum fun x a => Finsupp.single (-x) (α.act (-x) (star a))) :=
      Finsupp.sum_add_index (fun _ _ => by simp) (fun _ _ _ _ => by simp [Finsupp.single_add])
    exact congrArg (fun fn : G →₀ A => fn z) hsum

instance : StarModule ℂ (TwistedCrossedProduct α) where
  star_smul c f := by
    ext z
    change ((c • f.toFinsupp).sum fun x a => Finsupp.single (-x) (α.act (-x) (star a))) z =
      (star c • starOp f).toFinsupp z
    have hterm :
        ((c • f.toFinsupp).sum fun x a => Finsupp.single (-x) (α.act (-x) (star a))) =
        star c • (f.toFinsupp.sum fun x a => Finsupp.single (-x) (α.act (-x) (star a))) := by
      rw [Finsupp.sum_smul_index' (b := c) (fun _ => by simp), Finsupp.smul_sum]
      refine Finsupp.sum_congr fun x _ => ?_
      ext w
      simp [star_smul, map_smul]
    exact congrArg (fun fn : G →₀ A => fn z) hterm

theorem star_single (g : G) (a : A) :
    star (single (α := α) g a) = single (-g) (α.act (-g) (star a)) := by
  ext z
  change ((Finsupp.single g a).sum fun x b => Finsupp.single (-x) (α.act (-x) (star b))) z =
    (Finsupp.single (-g) (α.act (-g) (star a))) z
  rw [Finsupp.sum_single_index (by simp)]

/-- Canonical embedding `A →⋆ₐ[ℂ] (A ⋊_α G)` via `a ↦ single 0 a`. -/
def embed : A →⋆ₐ[ℂ] TwistedCrossedProduct α where
  toFun a := single 0 a
  map_one' := rfl
  map_mul' a b := by
    rw [single_mul_single, add_zero, α.act_zero]
  map_zero' := single_zero 0
  map_add' a b := by
    ext; simp [Finsupp.single_add]
  commutes' c := by
    ext z
    change (Finsupp.single (0 : G) (algebraMap ℂ A c)) z =
      (algebraMap ℂ (TwistedCrossedProduct α) c).toFinsupp z
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    simp
  map_star' a := by
    rw [star_single, neg_zero, α.act_zero]

@[simp]
theorem embed_apply (a : A) : embed (α := α) a = single 0 a := rfl

/-- Unitary character `χ : G → ℂ` generating the dual action `θ_χ` on `A ⋊_α G`. -/
structure GroupChar (G : Type*) [AddCommGroup G] where
  toFun : G → ℂ
  map_zero : toFun 0 = 1
  map_add : ∀ x y : G, toFun (x + y) = toFun x * toFun y
  map_neg : ∀ x : G, toFun (-x) = star (toFun x)

/-- Canonical dual `*-automorphism` action `dualAction χ (a δ_g) = χ(g) • a δ_g`. -/
def dualAction (χ : GroupChar G) :
    TwistedCrossedProduct α →⋆ₐ[ℂ] TwistedCrossedProduct α where
  toFun f := ⟨f.toFinsupp.sum fun x a => Finsupp.single x (χ.toFun x • a)⟩
  map_one' := by
    ext z
    change ((Finsupp.single (0 : G) (1 : A)).sum fun x a => Finsupp.single x (χ.toFun x • a)) z =
      (Finsupp.single (0 : G) (1 : A)) z
    rw [Finsupp.sum_single_index (by simp), χ.map_zero, one_smul]
  map_mul' f g := by
    ext z
    rw [mul_def]
    have hL :
        ((f.toFinsupp.sum fun x a => g.toFinsupp.sum fun y b =>
            Finsupp.single (x + y) (a * α.act x b)).sum fun u c =>
            Finsupp.single u (χ.toFun u • c)) =
        f.toFinsupp.sum fun x a => g.toFinsupp.sum fun y b =>
          Finsupp.single (x + y) (χ.toFun (x + y) • (a * α.act x b)) := by
      rw [Finsupp.sum_sum_index (f := f.toFinsupp) (fun _ => by simp)
        (fun _ _ _ => by simp [smul_add, Finsupp.single_add])]
      refine Finsupp.sum_congr fun x _ => ?_
      rw [Finsupp.sum_sum_index (f := g.toFinsupp) (fun _ => by simp)
        (fun _ _ _ => by simp [smul_add, Finsupp.single_add])]
      exact Finsupp.sum_congr fun y _ => Finsupp.sum_single_index (by simp)
    have hR :
        ((⟨f.toFinsupp.sum fun x a => Finsupp.single x (χ.toFun x • a)⟩ :
          TwistedCrossedProduct α) *
          ⟨g.toFinsupp.sum fun y b => Finsupp.single y (χ.toFun y • b)⟩).toFinsupp =
        f.toFinsupp.sum fun x a => g.toFinsupp.sum fun y b =>
          Finsupp.single (x + y) ((χ.toFun x * χ.toFun y) • (a * α.act x b)) := by
      rw [mul_def]
      rw [Finsupp.sum_sum_index (f := f.toFinsupp) (fun _ => by simp)
        (fun _ _ _ => by simp [add_mul])]
      refine Finsupp.sum_congr fun x _ => ?_
      rw [Finsupp.sum_single_index (by simp)]
      rw [Finsupp.sum_sum_index (f := g.toFinsupp) (fun _ => by simp)
        (fun _ _ _ => by simp [mul_add])]
      refine Finsupp.sum_congr fun y _ => ?_
      rw [Finsupp.sum_single_index (by simp)]
      congr 1
      rw [map_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
    have hch :
        (f.toFinsupp.sum fun x a => g.toFinsupp.sum fun y b =>
          Finsupp.single (x + y) (χ.toFun (x + y) • (a * α.act x b))) =
        f.toFinsupp.sum fun x a => g.toFinsupp.sum fun y b =>
          Finsupp.single (x + y) ((χ.toFun x * χ.toFun y) • (a * α.act x b)) := by
      refine Finsupp.sum_congr fun x _ => Finsupp.sum_congr fun y _ => ?_
      rw [χ.map_add]
    exact congrArg (fun fn : G →₀ A => fn z) (hL.trans (hch.trans hR.symm))
  map_zero' := by ext z; simp
  map_add' f g := by
    classical
    ext z
    change ((f.toFinsupp + g.toFinsupp).sum fun x a => Finsupp.single x (χ.toFun x • a)) z = _
    have hsum :
        (f.toFinsupp + g.toFinsupp).sum (fun x a => Finsupp.single x (χ.toFun x • a)) =
        (f.toFinsupp.sum fun x a => Finsupp.single x (χ.toFun x • a)) +
        (g.toFinsupp.sum fun x a => Finsupp.single x (χ.toFun x • a)) :=
      Finsupp.sum_add_index (fun _ _ => by simp)
        (fun _ _ _ _ => by simp [smul_add, Finsupp.single_add])
    exact congrArg (fun fn : G →₀ A => fn z) hsum
  commutes' c := by
    ext z
    change ((algebraMap ℂ (TwistedCrossedProduct α) c).toFinsupp.sum fun x a =>
        Finsupp.single x (χ.toFun x • a)) z =
      (algebraMap ℂ (TwistedCrossedProduct α) c).toFinsupp z
    rw [Algebra.algebraMap_eq_smul_one]
    have hsm : (c • (1 : TwistedCrossedProduct α)).toFinsupp = Finsupp.single (0 : G) (c • (1 : A)) := by
      ext y; simp
    rw [hsm, Finsupp.sum_single_index (by simp), χ.map_zero, one_smul]
  map_star' f := by
    ext z
    change ((starOp f).toFinsupp.sum fun x a => Finsupp.single x (χ.toFun x • a)) z =
      (starOp (⟨f.toFinsupp.sum fun x a => Finsupp.single x (χ.toFun x • a)⟩ :
        TwistedCrossedProduct α)).toFinsupp z
    have hL :
        ((starOp f).toFinsupp.sum fun x a => Finsupp.single x (χ.toFun x • a)) =
        f.toFinsupp.sum fun x a =>
          Finsupp.single (-x) (χ.toFun (-x) • (α.act (-x) (star a))) := by
      unfold starOp
      rw [Finsupp.sum_sum_index (f := f.toFinsupp) (fun _ => by simp)
        (fun _ _ _ => by simp [smul_add, Finsupp.single_add])]
      exact Finsupp.sum_congr fun x _ => Finsupp.sum_single_index (by simp)
    have hR :
        (starOp (⟨f.toFinsupp.sum fun x a => Finsupp.single x (χ.toFun x • a)⟩ :
          TwistedCrossedProduct α)).toFinsupp =
        f.toFinsupp.sum fun x a =>
          Finsupp.single (-x) (χ.toFun (-x) • (α.act (-x) (star a))) := by
      unfold starOp
      dsimp only
      rw [Finsupp.sum_sum_index (f := f.toFinsupp) (fun _ => by simp)
        (fun _ _ _ => by simp [Finsupp.single_add])]
      refine Finsupp.sum_congr fun x _ => ?_
      rw [Finsupp.sum_single_index (by simp), star_smul, map_smul, χ.map_neg]
    exact congrArg (fun fn : G →₀ A => fn z) (hL.trans hR.symm)

@[simp]
theorem dualAction_single (χ : GroupChar G) (g : G) (a : A) :
    dualAction χ (single (α := α) g a) = single g (χ.toFun g • a) := by
  ext z
  change ((Finsupp.single g a).sum fun x b => Finsupp.single x (χ.toFun x • b)) z =
    (Finsupp.single g (χ.toFun g • a)) z
  rw [Finsupp.sum_single_index (by simp)]

/-- Canonical conditional expectation `E : (A ⋊_α G) →ₗ[ℂ] A`, `f ↦ f.toFinsupp 0`. -/
def condExp : TwistedCrossedProduct α →ₗ[ℂ] A where
  toFun f := f.toFinsupp 0
  map_add' f g := by simp
  map_smul' c f := by simp

@[simp] theorem condExp_apply (f : TwistedCrossedProduct α) :
    condExp (α := α) f = f.toFinsupp 0 := rfl

@[simp] theorem condExp_one : condExp (α := α) 1 = 1 := by
  classical
  simp

@[simp] theorem condExp_embed (a : A) : condExp (α := α) (embed a) = a := by
  classical
  simp

omit [Algebra ℂ A] [StarRing A] [StarModule ℂ A] in
private theorem sum_eval_single_eq (f : G →₀ A) (φ : G → A → A)
    (h0 : ∀ g, φ g 0 = 0) :
    (f.sum fun x a => Finsupp.single x (φ x a)) 0 = φ 0 (f 0) := by
  classical
  rw [Finsupp.sum, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro x _ hx; simp [hx]
  · intro hmem
    have hz : f 0 = 0 := Finsupp.notMem_support_iff.mp hmem
    rw [hz, h0 0]
    simp

/-- Left bimodularity of `condExp` over `embed A`. -/
theorem condExp_embed_mul (a : A) (f : TwistedCrossedProduct α) :
    condExp (α := α) (embed a * f) = a * condExp f := by
  change (embed a * f).toFinsupp 0 = a * f.toFinsupp 0
  rw [mul_def, embed_apply, toFinsupp_single, Finsupp.sum_single_index (by simp)]
  simp_rw [zero_add, α.act_zero]
  exact sum_eval_single_eq f.toFinsupp (fun _ b => a * b) (fun _ => mul_zero a)

/-- Right bimodularity of `condExp` over `embed A`. -/
theorem condExp_mul_embed (f : TwistedCrossedProduct α) (b : A) :
    condExp (α := α) (f * embed b) = condExp f * b := by
  change (f * embed b).toFinsupp 0 = f.toFinsupp 0 * b
  rw [mul_def, embed_apply, toFinsupp_single]
  have h1 : ∀ x a,
      (Finsupp.single (0 : G) b).sum (fun y c => Finsupp.single (x + y) (a * α.act x c)) =
      Finsupp.single x (a * α.act x b) := fun x a => by
    rw [Finsupp.sum_single_index (by simp), add_zero]
  simp_rw [h1]
  rw [sum_eval_single_eq f.toFinsupp (fun x a => a * α.act x b) (fun x => zero_mul _)]
  rw [α.act_zero]

/-- Dual-action invariance: `condExp (dualAction χ f) = condExp f`. -/
theorem condExp_dualAction_invariant (χ : GroupChar G) (f : TwistedCrossedProduct α) :
    condExp (dualAction χ f) = condExp f := by
  change (f.toFinsupp.sum fun x a => Finsupp.single x (χ.toFun x • a)) 0 = f.toFinsupp 0
  rw [sum_eval_single_eq f.toFinsupp (fun x a => χ.toFun x • a) (fun _ => smul_zero _),
    χ.map_zero, one_smul]

/-- Exact formula for `condExp (star f * f)`: `∑ g ∈ supp f, α.act (-g) (star (f g) * f g)`. -/
theorem condExp_star_mul_self (f : TwistedCrossedProduct α) :
    condExp (star f * f) =
      f.toFinsupp.sum fun x a => α.act (-x) (star a * a) := by
  classical
  change (starOp f * f).toFinsupp 0 = f.toFinsupp.sum fun x a => α.act (-x) (star a * a)
  rw [mul_def]
  unfold starOp
  rw [Finsupp.sum_sum_index (f := f.toFinsupp) (fun _ => by simp)
    (fun _ _ _ => by simp [add_mul])]
  have hsimp :
      (f.toFinsupp.sum fun x a =>
        (Finsupp.single (-x) (α.act (-x) (star a))).sum fun u d =>
          f.toFinsupp.sum fun y b => Finsupp.single (u + y) (d * α.act u b)) =
      f.toFinsupp.sum fun x a => f.toFinsupp.sum fun y b =>
        Finsupp.single (-x + y) (α.act (-x) (star a * b)) := by
    refine Finsupp.sum_congr fun x _ => ?_
    rw [Finsupp.sum_single_index (by simp)]
    refine Finsupp.sum_congr fun y _ => ?_
    rw [map_mul]
  rw [hsimp, Finsupp.sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finsupp.sum, Finsupp.finsetSum_apply, Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    have hne : -x + y ≠ 0 := fun h => hy (by
      have := congrArg (fun z => x + z) h
      simpa [add_assoc] using this)
    simp [hne.symm]
  · intro hx
    have hz : f.toFinsupp x = 0 := Finsupp.notMem_support_iff.mp hx
    simp [hz]

/-- **Constructive Faithfulness** of `condExp` on `A ⋊_α G`: if finite sums of `star c_i * c_i`
    vanish only when every `c_i = 0`, then `condExp (star f * f) = 0 → f = 0`. -/
theorem condExp_faithful
    (hpos : ∀ (s : Finset G) (c : G → A),
      (∑ g ∈ s, star (c g) * c g) = 0 → ∀ g ∈ s, c g = 0)
    (f : TwistedCrossedProduct α) (hf : condExp (star f * f) = 0) :
    f = 0 := by
  rw [condExp_star_mul_self] at hf
  have hsum :
      (∑ x ∈ f.toFinsupp.support,
        star (α.act (-x) (f.toFinsupp x)) * α.act (-x) (f.toFinsupp x)) = 0 := by
    simpa [Finsupp.sum, map_mul, map_star] using hf
  have hall := hpos f.toFinsupp.support (fun x => α.act (-x) (f.toFinsupp x)) hsum
  ext x
  by_cases hx : x ∈ f.toFinsupp.support
  · have hzero := hall x hx
    have hinj : f.toFinsupp x = α.act x (α.act (-x) (f.toFinsupp x)) :=
      (α.act_act_neg x (f.toFinsupp x)).symm
    rw [hzero, map_zero] at hinj
    exact hinj
  · exact Finsupp.notMem_support_iff.mp hx

/-- Lift any `α`-commuting `*-automorphism` `φ : A →⋆ₐ[ℂ] A` to `A ⋊_α G`,
    proving exact `condExp` commutation `condExp (liftAut φ hcomm f) = φ (condExp f)` (discharging
    Takesaki's conditional-expectation invariance condition constructively on `A ⋊_α G`). -/
def liftAut (φ : A →⋆ₐ[ℂ] A) (hcomm : ∀ g a, φ (α.act g a) = α.act g (φ a)) :
    TwistedCrossedProduct α →⋆ₐ[ℂ] TwistedCrossedProduct α where
  toFun f := ⟨f.toFinsupp.sum fun x a => Finsupp.single x (φ a)⟩
  map_one' := by
    ext z
    change ((Finsupp.single (0 : G) (1 : A)).sum fun x a => Finsupp.single x (φ a)) z = _
    rw [Finsupp.sum_single_index (by simp), map_one]; rfl
  map_mul' f g := by
    ext z
    rw [mul_def]
    have hL :
        ((f.toFinsupp.sum fun x a => g.toFinsupp.sum fun y b =>
            Finsupp.single (x + y) (a * α.act x b)).sum fun u c => Finsupp.single u (φ c)) =
        f.toFinsupp.sum fun x a => g.toFinsupp.sum fun y b =>
          Finsupp.single (x + y) (φ a * α.act x (φ b)) := by
      rw [Finsupp.sum_sum_index (f := f.toFinsupp) (fun _ => by simp)
        (fun _ _ _ => by simp [map_add, Finsupp.single_add])]
      refine Finsupp.sum_congr fun x _ => ?_
      rw [Finsupp.sum_sum_index (f := g.toFinsupp) (fun _ => by simp)
        (fun _ _ _ => by simp [map_add, Finsupp.single_add])]
      refine Finsupp.sum_congr fun y _ => ?_
      rw [Finsupp.sum_single_index (by simp), map_mul, hcomm]
    have hR :
        ((⟨f.toFinsupp.sum fun x a => Finsupp.single x (φ a)⟩ :
          TwistedCrossedProduct α) *
          ⟨g.toFinsupp.sum fun y b => Finsupp.single y (φ b)⟩).toFinsupp =
        f.toFinsupp.sum fun x a => g.toFinsupp.sum fun y b =>
          Finsupp.single (x + y) (φ a * α.act x (φ b)) := by
      rw [mul_def]
      rw [Finsupp.sum_sum_index (f := f.toFinsupp) (fun _ => by simp)
        (fun _ _ _ => by simp [add_mul])]
      refine Finsupp.sum_congr fun x _ => ?_
      rw [Finsupp.sum_single_index (by simp)]
      rw [Finsupp.sum_sum_index (f := g.toFinsupp) (fun _ => by simp)
        (fun _ _ _ => by simp [mul_add])]
      exact Finsupp.sum_congr fun y _ => Finsupp.sum_single_index (by simp)
    exact congrArg (fun fn : G →₀ A => fn z) (hL.trans hR.symm)
  map_zero' := by ext; simp
  map_add' f g := by
    classical
    ext z
    change ((f.toFinsupp + g.toFinsupp).sum fun x a => Finsupp.single x (φ a)) z = _
    have hsum :
        (f.toFinsupp + g.toFinsupp).sum (fun x a => Finsupp.single x (φ a)) =
        (f.toFinsupp.sum fun x a => Finsupp.single x (φ a)) +
        (g.toFinsupp.sum fun x a => Finsupp.single x (φ a)) :=
      Finsupp.sum_add_index (fun _ _ => by simp)
        (fun _ _ _ _ => by simp [map_add, Finsupp.single_add])
    exact congrArg (fun fn : G →₀ A => fn z) hsum
  commutes' c := by
    ext z
    change ((algebraMap ℂ (TwistedCrossedProduct α) c).toFinsupp.sum fun x a =>
        Finsupp.single x (φ a)) z =
      (algebraMap ℂ (TwistedCrossedProduct α) c).toFinsupp z
    rw [Algebra.algebraMap_eq_smul_one]
    have hsm : (c • (1 : TwistedCrossedProduct α)).toFinsupp = Finsupp.single (0 : G) (c • (1 : A)) := by
      classical
      ext y; simp [Finsupp.single_apply]
    rw [hsm, Finsupp.sum_single_index (by simp), map_smul, map_one]
  map_star' f := by
    ext z
    change ((starOp f).toFinsupp.sum fun x a => Finsupp.single x (φ a)) z =
      (starOp (⟨f.toFinsupp.sum fun x a => Finsupp.single x (φ a)⟩ :
        TwistedCrossedProduct α)).toFinsupp z
    have hL :
        ((starOp f).toFinsupp.sum fun x a => Finsupp.single x (φ a)) =
        f.toFinsupp.sum fun x a =>
          Finsupp.single (-x) (φ (α.act (-x) (star a))) := by
      unfold starOp
      rw [Finsupp.sum_sum_index (f := f.toFinsupp) (fun _ => by simp)
        (fun _ _ _ => by simp [map_add, Finsupp.single_add])]
      exact Finsupp.sum_congr fun x _ => Finsupp.sum_single_index (by simp)
    have hR :
        (starOp (⟨f.toFinsupp.sum fun x a => Finsupp.single x (φ a)⟩ :
          TwistedCrossedProduct α)).toFinsupp =
        f.toFinsupp.sum fun x a =>
          Finsupp.single (-x) (φ (α.act (-x) (star a))) := by
      unfold starOp
      dsimp only
      rw [Finsupp.sum_sum_index (f := f.toFinsupp) (fun _ => by simp)
        (fun _ _ _ => by simp [Finsupp.single_add])]
      refine Finsupp.sum_congr fun x _ => ?_
      rw [Finsupp.sum_single_index (by simp), ← map_star φ, ← hcomm]
    exact congrArg (fun fn : G →₀ A => fn z) (hL.trans hR.symm)

theorem condExp_liftAut_comm (φ : A →⋆ₐ[ℂ] A) (hcomm : ∀ g a, φ (α.act g a) = α.act g (φ a))
    (f : TwistedCrossedProduct α) :
    condExp (liftAut φ hcomm f) = φ (condExp f) := by
  change (f.toFinsupp.sum fun x a => Finsupp.single x (φ a)) 0 = φ (f.toFinsupp 0)
  exact sum_eval_single_eq f.toFinsupp (fun _ a => φ a) (fun _ => map_zero φ)

end TwistedCrossedProduct

end SkewGroupAlgebra

/-! ## Part 2: Compatible Powers `ω_λ` States on `UHFStage k` & Point Spectrum `{λ^m : m ∈ ℤ}` -/

section PowersUHF

open InfoGeometry.Algebra.UHFColimitCStarCompletion
open Matrix

/-- Binary Hamming weight (number of `1`-bits in binary expansion of `n`). -/
def bitPopcount (n : ℕ) : ℕ :=
  if h : n = 0 then 0 else n % 2 + bitPopcount (n / 2)
termination_by n
decreasing_by omega

@[simp] theorem bitPopcount_zero : bitPopcount 0 = 0 := by
  simp [bitPopcount]

theorem bitPopcount_step {n : ℕ} (hn : n ≠ 0) :
    bitPopcount n = n % 2 + bitPopcount (n / 2) := by
  conv_lhs => unfold bitPopcount
  simp [hn]

/-- Key binary doubling identity: for every `r < 2^k`, adding `2^k` adds `1` to `bitPopcount`. -/
theorem bitPopcount_twoPow_add : ∀ (k r : ℕ), r < 2 ^ k → bitPopcount (2 ^ k + r) = 1 + bitPopcount r
  | 0, r, hr => by
      have hr0 : r = 0 := by simpa using hr
      subst hr0
      rw [pow_zero, add_zero, bitPopcount_zero, bitPopcount_step (by decide)]
      have hdiv : (1 : ℕ) / 2 = 0 := by decide
      rw [hdiv, bitPopcount_zero]
      norm_num
  | k + 1, r, hr => by
      have hne : 2 ^ (k + 1) + r ≠ 0 := by positivity
      rw [bitPopcount_step hne]
      have hdiv : (2 ^ (k + 1) + r) / 2 = 2 ^ k + r / 2 := by
        have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
        omega
      have hmod : (2 ^ (k + 1) + r) % 2 = r % 2 := by
        have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
        omega
      have hrl : r / 2 < 2 ^ k := by
        have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
        omega
      rw [hdiv, hmod, bitPopcount_twoPow_add k (r / 2) hrl]
      by_cases hr0 : r = 0
      · subst hr0; simp
      · rw [bitPopcount_step hr0]; omega

/-- Binary all-ones number `2^k - 1` has `bitPopcount (2^k - 1) = k`. -/
theorem bitPopcount_twoPow_sub_one : ∀ k : ℕ, bitPopcount (2 ^ k - 1) = k
  | 0 => by simp
  | k + 1 => by
      have hsplit : 2 ^ (k + 1) - 1 = 2 ^ k + (2 ^ k - 1) := by
        have hpow : 1 ≤ 2 ^ k := Nat.one_le_two_pow
        have h2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
        omega
      have hlt : 2 ^ k - 1 < 2 ^ k := Nat.sub_lt (Nat.two_pow_pos (w := k)) (by decide)
      rw [hsplit, bitPopcount_twoPow_add k (2 ^ k - 1) hlt, bitPopcount_twoPow_sub_one k]
      omega

/-- Powers diagonal weight `(1 / (1 + λ))^k * λ^(bitPopcount i)` at UHF stage `k`. -/
def powersWeight (lam : ℝ) (k : ℕ) (i : Fin (2 ^ k)) : ℝ :=
  (1 / (1 + lam)) ^ k * lam ^ (bitPopcount i.val)

theorem powersWeight_pos {lam : ℝ} (hlam : 0 < lam) (k : ℕ) (i : Fin (2 ^ k)) :
    0 < powersWeight lam k i := by
  unfold powersWeight
  positivity

theorem powersWeight_finSum_inl (lam : ℝ) (k : ℕ) (i : Fin (2 ^ k)) :
    powersWeight lam (k + 1) (finSumTwoPow k (Sum.inl i)) =
      (1 / (1 + lam)) * powersWeight lam k i := by
  unfold powersWeight
  have hval : (finSumTwoPow k (Sum.inl i)).val = i.val := by
    simp [finSumTwoPow]
  rw [hval, pow_succ', mul_assoc]

theorem powersWeight_finSum_inr (lam : ℝ) (k : ℕ) (i : Fin (2 ^ k)) :
    powersWeight lam (k + 1) (finSumTwoPow k (Sum.inr i)) =
      (lam / (1 + lam)) * powersWeight lam k i := by
  unfold powersWeight
  have hval : (finSumTwoPow k (Sum.inr i)).val = 2 ^ k + i.val := by
    simp [finSumTwoPow, add_comm]
  rw [hval, bitPopcount_twoPow_add k i.val i.isLt, pow_succ', pow_add, pow_one]
  ring

/-- Stage-`k` Powers linear functional `ω_λ^{(k)}(A) = ∑ i, w_i A_{i,i}` on `UHFStage k`. -/
def powersState (lam : ℝ) (k : ℕ) (A : UHFStage k) : ℂ :=
  ∑ i : Fin (2 ^ k), (powersWeight lam k i : ℂ) * A i i

/-- Sum of `powersWeight lam k` over `finSumTwoPow` pairs collapses stage `(k+1)` to stage `k`. -/
theorem powersState_compatible_uhfStep {lam : ℝ} (hlam : 0 < lam) (k : ℕ) (A : UHFStage k) :
    powersState lam (k + 1) (uhfStep k A) = powersState lam k A := by
  unfold powersState
  rw [← Equiv.sum_comp (finSumTwoPow k)]
  rw [Fintype.sum_sum_type]
  have hinl : ∀ i : Fin (2 ^ k),
      (uhfStep k A) (finSumTwoPow k (Sum.inl i)) (finSumTwoPow k (Sum.inl i)) = A i i := by
    intro i; simp [uhfStep]
  have hinr : ∀ i : Fin (2 ^ k),
      (uhfStep k A) (finSumTwoPow k (Sum.inr i)) (finSumTwoPow k (Sum.inr i)) = A i i := by
    intro i; simp [uhfStep]
  simp_rw [hinl, hinr, powersWeight_finSum_inl, powersWeight_finSum_inr, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1p : (1 + lam : ℝ) ≠ 0 := by linarith
  have hreal : (1 / (1 + lam) + lam / (1 + lam) : ℝ) = 1 := by
    field_simp [h1p]
  have hcmul :
      ((1 / (1 + lam) * powersWeight lam k i : ℝ) : ℂ) * A i i +
        ((lam / (1 + lam) * powersWeight lam k i : ℝ) : ℂ) * A i i =
      (((1 / (1 + lam) + lam / (1 + lam)) * powersWeight lam k i : ℝ) : ℂ) * A i i := by
    push_cast; ring
  rw [hcmul, hreal, one_mul]

/-- Normalization: `powersState lam k 1 = 1` for every stage `k` and `lam > 0`. -/
theorem powersState_one {lam : ℝ} (hlam : 0 < lam) : ∀ k : ℕ, powersState lam k 1 = 1
  | 0 => by
      simp [powersState, powersWeight]
  | k + 1 => by
      rw [← uhfStep_one k, powersState_compatible_uhfStep hlam k 1, powersState_one hlam k]

/-- Stage-`k` Powers modular operator `Δ_k(X)_{i,j} = (w_i / w_j) X_{i,j}`. -/
def powersModularOp (lam : ℝ) (k : ℕ) (X : UHFStage k) : UHFStage k :=
  Matrix.of fun i j => ((powersWeight lam k i / powersWeight lam k j : ℝ) : ℂ) * X i j

/-- Exact finite-stage KMS identity for `powersState`:
    `ω_λ^{(k)}(A * Δ_k(B)) = ω_λ^{(k)}(B * A)`. -/
theorem powersState_kms {lam : ℝ} (hlam : 0 < lam) (k : ℕ) (A B : UHFStage k) :
    powersState lam k (A * powersModularOp lam k B) = powersState lam k (B * A) := by
  unfold powersState powersModularOp
  simp only [Matrix.mul_apply, Matrix.of_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  have hwi : powersWeight lam k i ≠ 0 := (powersWeight_pos hlam k i).ne'
  push_cast
  field_simp [hwi]

/-- Elementary matrix unit `e_{i,j}` in `UHFStage k`. -/
def elemUnit (k : ℕ) (i j : Fin (2 ^ k)) : UHFStage k :=
  Matrix.of fun r c => if r = i ∧ c = j then (1 : ℂ) else 0

theorem elemUnit_ne_zero (k : ℕ) (i j : Fin (2 ^ k)) : elemUnit k i j ≠ 0 := by
  intro h
  have h0 := congrArg (fun M : UHFStage k => M i j) h
  simp [elemUnit] at h0

theorem powersModularOp_elemUnit (lam : ℝ) (k : ℕ) (i j : Fin (2 ^ k)) :
    powersModularOp lam k (elemUnit k i j) =
      ((powersWeight lam k i / powersWeight lam k j : ℝ) : ℂ) • elemUnit k i j := by
  ext r c
  by_cases hrc : r = i ∧ c = j
  · rcases hrc with ⟨rfl, rfl⟩
    simp [powersModularOp, elemUnit]
  · simp [powersModularOp, elemUnit, hrc]

/-- **Powers Point-Spectrum Theorem**: For every integer `m : ℤ`, at stage `k = m.natAbs`
    there exists a nonzero matrix unit `E : UHFStage k` with exact modular eigenvalue `(lam^m : ℂ)`
    (showing every `{λ^m | m ∈ ℤ}` appears in the finite-stage modular point spectrum). -/
theorem powersModularOp_point_spectrum {lam : ℝ} (hlam : 0 < lam) (m : ℤ) :
    ∃ (E : UHFStage m.natAbs),
      E ≠ 0 ∧ powersModularOp lam m.natAbs E = ((lam ^ m : ℝ) : ℂ) • E := by
  let k := m.natAbs
  let i0 : Fin (2 ^ k) := ⟨0, Nat.two_pow_pos (w := k)⟩
  let i1 : Fin (2 ^ k) := ⟨2 ^ k - 1, Nat.sub_lt (Nat.two_pow_pos (w := k)) (by decide)⟩
  have hw_ratio_pos :
      powersWeight lam k i1 / powersWeight lam k i0 = lam ^ k := by
    unfold powersWeight
    have h0 : bitPopcount i0.val = 0 := by simp [i0]
    have h1 : bitPopcount i1.val = k := bitPopcount_twoPow_sub_one k
    rw [h0, h1, pow_zero, mul_one]
    have hc : (1 / (1 + lam)) ^ k ≠ 0 := by positivity
    field_simp [hc]
  have hw_ratio_neg :
      powersWeight lam k i0 / powersWeight lam k i1 = (lam ^ k)⁻¹ := by
    rw [← hw_ratio_pos]
    have hpi0 : powersWeight lam k i0 ≠ 0 := (powersWeight_pos hlam k i0).ne'
    have hpi1 : powersWeight lam k i1 ≠ 0 := (powersWeight_pos hlam k i1).ne'
    field_simp [hpi0, hpi1]
  rcases Int.natAbs_eq m with hm | hm
  · refine ⟨elemUnit k i1 i0, elemUnit_ne_zero k i1 i0, ?_⟩
    rw [powersModularOp_elemUnit lam k i1 i0, hw_ratio_pos]
    have hpow : lam ^ m = lam ^ k := by
      conv_lhs => rw [hm]
      exact zpow_natCast lam k
    rw [hpow]
  · refine ⟨elemUnit k i0 i1, elemUnit_ne_zero k i0 i1, ?_⟩
    rw [powersModularOp_elemUnit lam k i0 i1, hw_ratio_neg]
    have hpow : lam ^ m = (lam ^ k)⁻¹ := by
      conv_lhs => rw [hm]
      exact zpow_neg lam k
    rw [hpow]

end PowersUHF

end InfoGeometry.Canonical.AlgebraicCrossedProductAndPowersWitness
