import Mathlib.Algebra.Lie.Basic
import Mathlib.Tactic

/-!
# Core Involution

Common involutive automorphism abstractions used across symmetric,
Cartan, Clifford, and Krein layers.
-/

namespace InfoGeometry.Core

/-- A bare involutive endomorphism on `M`. -/
structure InvolutiveAutomorphism (M : Type _) where
  toFun : M → M
  involutive : Function.Involutive toFun

attribute [simp] InvolutiveAutomorphism.involutive

instance {M : Type _} :
    CoeFun (InvolutiveAutomorphism M) (fun _ => M → M) where
  coe θ := θ.toFun

/-- Linear structure preservation for an involution. -/
class PreservesLinear
    (V : Type _) [AddCommGroup V] [Module ℝ V]
    (θ : InvolutiveAutomorphism V) : Prop where
  map_add : ∀ x y, θ (x + y) = θ x + θ y
  map_smul : ∀ (a : ℝ) x, θ (a • x) = a • θ x

attribute [simp] PreservesLinear.map_add
attribute [simp] PreservesLinear.map_smul

/-- Multiplicative structure preservation for an involution. -/
class PreservesMul
    (G : Type _) [Group G]
    (θ : InvolutiveAutomorphism G) : Prop where
  map_mul : ∀ x y, θ (x * y) = θ x * θ y
  map_one : θ 1 = 1

attribute [simp] PreservesMul.map_mul
attribute [simp] PreservesMul.map_one

/-- Lie bracket preservation for an involution. -/
class PreservesLieBracket
    (L : Type _) [LieRing L] [LieAlgebra ℝ L]
    (θ : InvolutiveAutomorphism L) : Prop where
  map_lie : ∀ x y, θ ⁅x, y⁆ = ⁅θ x, θ y⁆

namespace InvolutiveAutomorphism

section LinearDerived

variable {V : Type _} [AddCommGroup V] [Module ℝ V]
variable (θ : InvolutiveAutomorphism V) [PreservesLinear V θ]

@[simp]
lemma map_add (x y : V) :
    θ (x + y) = θ x + θ y :=
  PreservesLinear.map_add (V := V) (θ := θ) x y

@[simp]
lemma map_smul (a : ℝ) (x : V) :
    θ (a • x) = a • θ x :=
  PreservesLinear.map_smul (V := V) (θ := θ) a x

@[simp]
lemma map_neg (x : V) :
    θ (-x) = -θ x := by
  simpa using PreservesLinear.map_smul (V := V) (θ := θ) (-1 : ℝ) x

@[simp]
lemma map_sub (x y : V) :
    θ (x - y) = θ x - θ y := by
  simp [sub_eq_add_neg]

end LinearDerived

section LieDerived

variable {L : Type _} [LieRing L] [LieAlgebra ℝ L]
variable (θ : InvolutiveAutomorphism L) [PreservesLieBracket L θ]

lemma map_lie (x y : L) :
    θ ⁅x, y⁆ = ⁅θ x, θ y⁆ :=
  PreservesLieBracket.map_lie (L := L) (θ := θ) x y

end LieDerived

section MulDerived

variable {G : Type _} [Group G]
variable (θ : InvolutiveAutomorphism G) [PreservesMul G θ]

@[simp]
lemma map_mul (x y : G) :
    θ (x * y) = θ x * θ y :=
  PreservesMul.map_mul (G := G) (θ := θ) x y

@[simp]
lemma map_one :
    θ (1 : G) = 1 :=
  PreservesMul.map_one (G := G) (θ := θ)

end MulDerived

end InvolutiveAutomorphism

/-- Backward-compatible linear involution package as a subtype. -/
abbrev LinearInvolutiveAutomorphism
    (V : Type _) [AddCommGroup V] [Module ℝ V] :=
  { θ : InvolutiveAutomorphism V // PreservesLinear V θ }

/-- Backward-compatible multiplicative involution package as a subtype. -/
abbrev MulInvolutiveAutomorphism
    (G : Type _) [Group G] :=
  { θ : InvolutiveAutomorphism G // PreservesMul G θ }

instance {V : Type _} [AddCommGroup V] [Module ℝ V] :
    CoeFun (LinearInvolutiveAutomorphism V) (fun _ => V → V) where
  coe θ := θ.1

instance {G : Type _} [Group G] :
    CoeFun (MulInvolutiveAutomorphism G) (fun _ => G → G) where
  coe θ := θ.1

namespace LinearInvolutiveAutomorphism

section

variable {V : Type _} [AddCommGroup V] [Module ℝ V]
variable (θ : LinearInvolutiveAutomorphism V)

instance instPreservesLinear :
    PreservesLinear V θ.1 := θ.2

@[simp] lemma involutive (x : V) :
    θ (θ x) = x :=
  θ.1.involutive x

@[simp] lemma map_add (x y : V) :
    θ (x + y) = θ x + θ y :=
  PreservesLinear.map_add (V := V) (θ := θ.1) x y

@[simp] lemma map_smul (a : ℝ) (x : V) :
    θ (a • x) = a • θ x :=
  PreservesLinear.map_smul (V := V) (θ := θ.1) a x

@[simp] lemma map_neg (x : V) :
    θ (-x) = -θ x := by
  exact InvolutiveAutomorphism.map_neg (θ := θ.1) x

@[simp] lemma map_sub (x y : V) :
    θ (x - y) = θ x - θ y := by
  exact InvolutiveAutomorphism.map_sub (θ := θ.1) x y

end

end LinearInvolutiveAutomorphism

namespace MulInvolutiveAutomorphism

section

variable {G : Type _} [Group G]
variable (θ : MulInvolutiveAutomorphism G)

instance instPreservesMul :
    PreservesMul G θ.1 := θ.2

@[simp] lemma involutive (x : G) :
    θ (θ x) = x :=
  θ.1.involutive x

@[simp] lemma map_mul (x y : G) :
    θ (x * y) = θ x * θ y :=
  PreservesMul.map_mul (G := G) (θ := θ.1) x y

@[simp] lemma map_one :
    θ (1 : G) = 1 :=
  PreservesMul.map_one (G := G) (θ := θ.1)

end

end MulInvolutiveAutomorphism

namespace Projector

variable {V : Type _} [AddCommGroup V] [Module ℝ V]
variable (θ : InvolutiveAutomorphism V)

/-- +1 projector `(Id + θ)/2`. -/
noncomputable def plus (v : V) : V :=
  ((2 : ℝ)⁻¹) • (v + θ v)

/-- -1 projector `(Id - θ)/2`. -/
noncomputable def minus (v : V) : V :=
  ((2 : ℝ)⁻¹) • (v - θ v)

lemma decomposition (v : V) :
    v = plus θ v + minus θ v := by
  have hhalf : ((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹) = 1 := by norm_num
  symm
  calc
    plus θ v + minus θ v
        = ((2 : ℝ)⁻¹) • (v + θ v)
          + ((2 : ℝ)⁻¹) • (v - θ v) := by
            simp [plus, minus]
    _ = (((2 : ℝ)⁻¹) • v + ((2 : ℝ)⁻¹) • θ v)
          + (((2 : ℝ)⁻¹) • v - ((2 : ℝ)⁻¹) • θ v) := by
            simp [smul_add, smul_sub]
    _ = ((2 : ℝ)⁻¹) • v + ((2 : ℝ)⁻¹) • v := by
          abel_nf
    _ = (((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹) : ℝ) • v := by
          simp [add_smul]
    _ = (1 : ℝ) • v := by simp [hhalf]
    _ = v := by simp

variable [PreservesLinear V θ]

lemma plus_fixed (v : V) :
    θ (plus θ v) = plus θ v := by
  unfold plus
  calc
    θ (((2 : ℝ)⁻¹) • (v + θ v))
        = ((2 : ℝ)⁻¹) • θ (v + θ v) := by simp
    _ = ((2 : ℝ)⁻¹) • (θ v + θ (θ v)) := by simp
    _ = ((2 : ℝ)⁻¹) • (θ v + v) := by rw [θ.involutive v]
    _ = ((2 : ℝ)⁻¹) • (v + θ v) := by simp [add_comm]

lemma minus_neg_fixed (v : V) :
    θ (minus θ v) = -minus θ v := by
  unfold minus
  calc
    θ (((2 : ℝ)⁻¹) • (v - θ v))
        = ((2 : ℝ)⁻¹) • θ (v - θ v) := by simp
    _ = ((2 : ℝ)⁻¹) • (θ v - θ (θ v)) := by simp
    _ = ((2 : ℝ)⁻¹) • (θ v - v) := by rw [θ.involutive v]
    _ = ((2 : ℝ)⁻¹) • (-(v - θ v)) := by
          congr 1
          abel_nf
    _ = -(((2 : ℝ)⁻¹) • (v - θ v)) := by
          rw [smul_neg]

end Projector

section Linear

variable {V : Type _} [AddCommGroup V] [Module ℝ V]

/-- Backward-compatible alias for `Projector.plus`. -/
noncomputable def cartanPlus
    (θ : LinearInvolutiveAutomorphism V) (v : V) : V :=
  letI : PreservesLinear V θ.1 := θ.2
  Projector.plus θ.1 v

/-- Backward-compatible alias for `Projector.minus`. -/
noncomputable def cartanMinus
    (θ : LinearInvolutiveAutomorphism V) (v : V) : V :=
  letI : PreservesLinear V θ.1 := θ.2
  Projector.minus θ.1 v

lemma cartan_decomposition
    (θ : LinearInvolutiveAutomorphism V) (v : V) :
    v = cartanPlus θ v + cartanMinus θ v := by
  letI : PreservesLinear V θ.1 := θ.2
  simpa [cartanPlus, cartanMinus] using (Projector.decomposition (θ := θ.1) v)

lemma cartanPlus_fixed
    (θ : LinearInvolutiveAutomorphism V) (v : V) :
    θ (cartanPlus θ v) = cartanPlus θ v := by
  letI : PreservesLinear V θ.1 := θ.2
  simpa [cartanPlus] using (Projector.plus_fixed (θ := θ.1) v)

lemma cartanMinus_neg_fixed
    (θ : LinearInvolutiveAutomorphism V) (v : V) :
    θ (cartanMinus θ v) = -(cartanMinus θ v) := by
  letI : PreservesLinear V θ.1 := θ.2
  simpa [cartanMinus] using (Projector.minus_neg_fixed (θ := θ.1) v)

end Linear

end InfoGeometry.Core
