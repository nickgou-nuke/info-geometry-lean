import Mathlib.Algebra.Lie.Basic
import Mathlib.Tactic
import InfoGeometry.Meta.Vacuity

/-!
# Core Involution

Common involutive automorphism abstractions used across symmetric,
Cartan, Clifford, and Krein layers.
-/

namespace InfoGeometry.Core

/-- A bare involutive endomorphism on `M`. -/
abbrev InvolutiveAutomorphism (M : Type*) :=
  {f : M → M // Function.Involutive f}

namespace InvolutiveAutomorphism

abbrev toFun (θ : InvolutiveAutomorphism M) : M → M := θ.1

abbrev involutive (θ : InvolutiveAutomorphism M) :
    Function.Involutive θ.toFun := θ.2

def mk (toFun : M → M) (involutive : Function.Involutive toFun) :
    InvolutiveAutomorphism M :=
  ⟨toFun, involutive⟩

end InvolutiveAutomorphism

attribute [simp] InvolutiveAutomorphism.involutive

/-- Compatibility alias emphasizing this is an involutive self-map. -/
abbrev Involution (M : Type*) := InvolutiveAutomorphism M

instance {M : Type*} :
    CoeFun (InvolutiveAutomorphism M) (fun _ => M → M) where
  coe θ := θ.toFun

@[ext] theorem InvolutiveAutomorphism.ext
    {M : Type*} {θ ψ : InvolutiveAutomorphism M}
    (h : ∀ x, θ x = ψ x) : θ = ψ := by
  cases θ with
  | mk θto θinv =>
    cases ψ with
    | mk ψto ψinv =>
      have hfun : θto = ψto := funext h
      subst hfun
      have hproof : θinv = ψinv := Subsingleton.elim _ _
      cases hproof
      rfl

/-- Linear structure preservation for an involution. -/
class PreservesLinear
    (V : Type*) [AddCommGroup V] [Module ℝ V]
    (θ : InvolutiveAutomorphism V) : Prop where
  map_add : ∀ x y, θ (x + y) = θ x + θ y
  map_smul : ∀ (a : ℝ) x, θ (a • x) = a • θ x

attribute [simp] PreservesLinear.map_add
attribute [simp] PreservesLinear.map_smul

/-- Multiplicative structure preservation for an involution. -/
class PreservesMul
    (G : Type*) [Group G]
    (θ : InvolutiveAutomorphism G) : Prop where
  map_mul : ∀ x y, θ (x * y) = θ x * θ y
  map_one : θ 1 = 1

attribute [simp] PreservesMul.map_mul
attribute [simp] PreservesMul.map_one

/-- Lie bracket preservation for an involution. -/
class PreservesLieBracket
    (L : Type*) [LieRing L] [LieAlgebra ℝ L]
    (θ : InvolutiveAutomorphism L) : Prop where
  map_lie : ∀ x y, θ ⁅x, y⁆ = ⁅θ x, θ y⁆

/-- Bundled Lie compatibility: linear + bracket preservation. -/
class PreservesLie
    (L : Type*) [LieRing L] [LieAlgebra ℝ L]
    (θ : InvolutiveAutomorphism L)
    extends PreservesLinear L θ, PreservesLieBracket L θ

instance (L : Type*) [LieRing L] [LieAlgebra ℝ L]
    (θ : InvolutiveAutomorphism L) [PreservesLie L θ] :
    PreservesLinear L θ :=
  PreservesLie.toPreservesLinear

instance (L : Type*) [LieRing L] [LieAlgebra ℝ L]
    (θ : InvolutiveAutomorphism L) [PreservesLie L θ] :
    PreservesLieBracket L θ :=
  PreservesLie.toPreservesLieBracket

namespace InvolutiveAutomorphism

section LinearDerived

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable (θ : InvolutiveAutomorphism V) [PreservesLinear V θ]

lemma map_add (x y : V) :
    θ (x + y) = θ x + θ y :=
  PreservesLinear.map_add (V := V) (θ := θ) x y

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

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]
variable (θ : InvolutiveAutomorphism L) [PreservesLieBracket L θ]

lemma map_lie (x y : L) :
    θ ⁅x, y⁆ = ⁅θ x, θ y⁆ :=
  PreservesLieBracket.map_lie (L := L) (θ := θ) x y

end LieDerived

section MulDerived

variable {G : Type*} [Group G]
variable (θ : InvolutiveAutomorphism G) [PreservesMul G θ]

lemma map_mul (x y : G) :
    θ (x * y) = θ x * θ y :=
  PreservesMul.map_mul (G := G) (θ := θ) x y

lemma map_one :
    θ (1 : G) = 1 :=
  PreservesMul.map_one (G := G) (θ := θ)

@[simp] lemma map_inv (x : G) :
    θ x⁻¹ = (θ x)⁻¹ := by
  exact eq_inv_of_mul_eq_one_left <| by
    calc
      θ x⁻¹ * θ x = θ (x⁻¹ * x) := by
        rw [← map_mul (θ := θ) x⁻¹ x]
      _ = θ 1 := by simp
      _ = 1 := map_one (θ := θ)

@[simp] lemma map_div (x y : G) :
    θ (x / y) = θ x / θ y := by
  simp [div_eq_mul_inv, map_mul (θ := θ), map_inv (θ := θ)]

end MulDerived

end InvolutiveAutomorphism

/-- Backward-compatible linear involution package as a subtype. -/
abbrev LinearInvolutiveAutomorphism
    (V : Type*) [AddCommGroup V] [Module ℝ V] :=
  { θ : InvolutiveAutomorphism V // PreservesLinear V θ }

/-- Backward-compatible multiplicative involution package as a subtype. -/
abbrev MulInvolutiveAutomorphism
    (G : Type*) [Group G] :=
  { θ : InvolutiveAutomorphism G // PreservesMul G θ }

instance {V : Type*} [AddCommGroup V] [Module ℝ V] :
    CoeFun (LinearInvolutiveAutomorphism V) (fun _ => V → V) where
  coe θ := θ.1

instance {G : Type*} [Group G] :
    CoeFun (MulInvolutiveAutomorphism G) (fun _ => G → G) where
  coe θ := θ.1

namespace LinearInvolutiveAutomorphism

section

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable (θ : LinearInvolutiveAutomorphism V)

instance instPreservesLinear :
    PreservesLinear V θ.1 := θ.2

@[simp] lemma involutive (x : V) :
    θ (θ x) = x :=
  θ.1.involutive x

lemma map_add (x y : V) :
    θ (x + y) = θ x + θ y :=
  PreservesLinear.map_add (V := V) (θ := θ.1) x y

lemma map_smul (a : ℝ) (x : V) :
    θ (a • x) = a • θ x :=
  PreservesLinear.map_smul (V := V) (θ := θ.1) a x

lemma map_neg (x : V) :
    θ (-x) = -θ x := by
  exact InvolutiveAutomorphism.map_neg (θ := θ.1) x

lemma map_sub (x y : V) :
    θ (x - y) = θ x - θ y := by
  exact InvolutiveAutomorphism.map_sub (θ := θ.1) x y

end

end LinearInvolutiveAutomorphism

namespace MulInvolutiveAutomorphism

section

variable {G : Type*} [Group G]
variable (θ : MulInvolutiveAutomorphism G)

instance instPreservesMul :
    PreservesMul G θ.1 := θ.2

@[simp] lemma involutive (x : G) :
    θ (θ x) = x :=
  θ.1.involutive x

lemma map_mul (x y : G) :
    θ (x * y) = θ x * θ y :=
  PreservesMul.map_mul (G := G) (θ := θ.1) x y

lemma map_one :
    θ (1 : G) = 1 :=
  PreservesMul.map_one (G := G) (θ := θ.1)

@[simp] lemma map_inv (x : G) :
    θ x⁻¹ = (θ x)⁻¹ := by
  exact InvolutiveAutomorphism.map_inv (θ := θ.1) x

@[simp] lemma map_div (x y : G) :
    θ (x / y) = θ x / θ y := by
  exact InvolutiveAutomorphism.map_div (θ := θ.1) x y

end

end MulInvolutiveAutomorphism

namespace Projector

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
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

lemma plus_add (x y : V) :
    plus θ (x + y) = plus θ x + plus θ y := by
  unfold plus
  simp [smul_add, add_assoc, add_left_comm]

lemma minus_add (x y : V) :
    minus θ (x + y) = minus θ x + minus θ y := by
  unfold minus
  simp [smul_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

lemma plus_smul (a : ℝ) (x : V) :
    plus θ (a • x) = a • plus θ x := by
  unfold plus
  simp [smul_add, smul_smul, mul_comm]

lemma minus_smul (a : ℝ) (x : V) :
    minus θ (a • x) = a • minus θ x := by
  unfold minus
  simp [smul_sub, smul_smul, mul_comm]

lemma plus_idempotent (v : V) :
    plus θ (plus θ v) = plus θ v := by
  unfold plus
  have hhalf : ((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹) = 1 := by norm_num
  calc
    ((2 : ℝ)⁻¹) • (plus θ v + θ (plus θ v))
        = ((2 : ℝ)⁻¹) • (plus θ v + plus θ v) := by
            simp [plus_fixed (θ := θ)]
    _ = (((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹) : ℝ) • (plus θ v) := by
          simp [add_smul]
    _ = (1 : ℝ) • (plus θ v) := by simp [hhalf]
    _ = plus θ v := by simp

lemma minus_idempotent (v : V) :
    minus θ (minus θ v) = minus θ v := by
  unfold minus
  have hhalf : ((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹) = 1 := by norm_num
  calc
    ((2 : ℝ)⁻¹) • (minus θ v - θ (minus θ v))
        = ((2 : ℝ)⁻¹) • (minus θ v - (-minus θ v)) := by
            simp [minus_neg_fixed (θ := θ)]
    _ = ((2 : ℝ)⁻¹) • (minus θ v + minus θ v) := by simp
    _ = (((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹) : ℝ) • (minus θ v) := by
          simp [add_smul]
    _ = (1 : ℝ) • (minus θ v) := by simp [hhalf]
    _ = minus θ v := by simp

lemma plus_minus (v : V) :
    plus θ (minus θ v) = 0 := by
  unfold plus
  simp [minus_neg_fixed (θ := θ)]

lemma minus_plus (v : V) :
    minus θ (plus θ v) = 0 := by
  unfold minus
  simp [plus_fixed (θ := θ)]

omit [PreservesLinear V θ] in
lemma fixed_iff_minus_eq_zero (v : V) :
    θ v = v ↔ minus θ v = 0 := by
  constructor
  · intro hv
    unfold minus
    rw [hv, sub_self, smul_zero]
  · intro hminus
    have hsub : v - θ v = 0 := by
      have htwo :
          (2 : ℝ) • minus θ v = (2 : ℝ) • (0 : V) :=
        congrArg (fun z => (2 : ℝ) • z) hminus
      simpa [minus, smul_smul] using htwo
    exact (sub_eq_zero.mp hsub).symm

omit [PreservesLinear V θ] in
lemma neg_fixed_iff_plus_eq_zero (v : V) :
    θ v = -v ↔ plus θ v = 0 := by
  constructor
  · intro hv
    unfold plus
    rw [hv]
    simp
  · intro hplus
    have hadd : v + θ v = 0 := by
      have htwo :
          (2 : ℝ) • plus θ v = (2 : ℝ) • (0 : V) :=
        congrArg (fun z => (2 : ℝ) • z) hplus
      simpa [plus, smul_smul] using htwo
    exact eq_neg_of_add_eq_zero_right hadd

end Projector

section Linear

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

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

attribute [infrastructure]
  instPreservesLinearOfPreservesLie
  instPreservesLieBracketOfPreservesLie
  InvolutiveAutomorphism.ext_iff
  InvolutiveAutomorphism.map_add
  InvolutiveAutomorphism.map_smul
  InvolutiveAutomorphism.map_neg
  InvolutiveAutomorphism.map_sub
  InvolutiveAutomorphism.map_lie
  InvolutiveAutomorphism.map_mul
  InvolutiveAutomorphism.map_one
  InvolutiveAutomorphism.map_inv
  InvolutiveAutomorphism.map_div
  LinearInvolutiveAutomorphism.involutive
  LinearInvolutiveAutomorphism.map_add
  LinearInvolutiveAutomorphism.map_smul
  LinearInvolutiveAutomorphism.map_neg
  LinearInvolutiveAutomorphism.map_sub
  MulInvolutiveAutomorphism.involutive
  MulInvolutiveAutomorphism.map_mul
  MulInvolutiveAutomorphism.map_one
  MulInvolutiveAutomorphism.map_inv
  MulInvolutiveAutomorphism.map_div

attribute [expository]
  Projector.plus_add
  Projector.minus_add
  Projector.plus_smul
  Projector.minus_smul
  Projector.plus_idempotent
  Projector.minus_idempotent
  Projector.plus_minus
  Projector.minus_plus
  cartan_decomposition
  cartanPlus_fixed
  cartanMinus_neg_fixed

end InfoGeometry.Core
