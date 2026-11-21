/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.DerivationExteriorCalculus
import InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
import InfoGeometry.Optics.OperatorDerivationForms
import InfoGeometry.Continuous.DeRhamBridge
import InfoGeometry.Canonical.NoncommutativeGibbsBKMHessianBridge
import InfoGeometry.Canonical.NoncommutativeGibbsDuhamelTwoPointBridge
import InfoGeometry.Canonical.NoncommutativeGibbsFaithfulNormalizationBridge
import InfoGeometry.Canonical.NoncommutativeGibbsCenteredFrechetBKMBridge

/-!
# Fréchet jets, alternating operator forms, and exchange parity

This is the generic analytic layer below the existing chiral-Hodge owners.
Fréchet jets and alternating forms are different carriers.  The exchange
involution is therefore explicit data; no Hodge adjoint is identified with an
opposite-algebra differential without a compatibility property.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Canonical.OperatorFrechetForms

abbrev OperatorFrechetJet
    (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (n : ℕ) :=
  E → ContinuousMultilinearMap ℂ (fun _ : Fin n => E) F

noncomputable def operatorFrechetJet
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (n : ℕ) (f : E → F) : OperatorFrechetJet E F n :=
  iteratedFDeriv ℂ n f

abbrev OperatorFrechetForm
    (A T M : Type*) [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup T] [NormedSpace ℂ T]
    [NormedAddCommGroup M] [NormedSpace ℂ M] (n : ℕ) :=
  A → (T [⋀^Fin n]→L[ℂ] M)

structure ExchangeInvolution (V : Type*) [AddCommGroup V] [Module ℝ V] where
  exchange : V ≃ₗ[ℝ] V
  exchange_sq : ∀ x, exchange (exchange x) = x

namespace ExchangeInvolution

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable (E : ExchangeInvolution V)

def even : V →ₗ[ℝ] V :=
  (1 / 2 : ℝ) • (LinearMap.id + E.exchange.toLinearMap)

def odd : V →ₗ[ℝ] V :=
  (1 / 2 : ℝ) • (LinearMap.id - E.exchange.toLinearMap)

theorem exchange_even (x : V) :
    E.exchange (E.even x) = E.even x := by
  dsimp [even]
  rw [map_smul, map_add, E.exchange_sq]
  module

theorem exchange_odd (x : V) :
    E.exchange (E.odd x) = -(E.odd x) := by
  dsimp [odd]
  rw [map_smul, map_sub, E.exchange_sq]
  module

theorem even_add_odd (x : V) : E.even x + E.odd x = x := by
  dsimp [even, odd]
  module

theorem even_odd (x : V) : E.even (E.odd x) = 0 := by
  dsimp [even, odd]
  rw [map_smul (E.exchange), map_sub, E.exchange_sq]
  module

theorem odd_even (x : V) : E.odd (E.even x) = 0 := by
  dsimp [even, odd]
  rw [map_smul (E.exchange), map_add, E.exchange_sq]
  module

end ExchangeInvolution

structure ModularFrechetHodgeCompatibility
    (V W : Type*) [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] where
  sourceExchange : ExchangeInvolution V
  targetExchange : ExchangeInvolution W
  leftDifferential : V →ₗ[ℝ] W
  rightDifferential : V →ₗ[ℝ] W
  left_exchange :
    targetExchange.exchange.toLinearMap.comp leftDifferential =
      rightDifferential.comp sourceExchange.exchange.toLinearMap
  right_exchange :
    targetExchange.exchange.toLinearMap.comp rightDifferential =
      leftDifferential.comp sourceExchange.exchange.toLinearMap

namespace ModularFrechetHodgeCompatibility

variable {V W : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]
variable (H : ModularFrechetHodgeCompatibility V W)

def diracPlus : V →ₗ[ℝ] W := H.leftDifferential + H.rightDifferential

def diracMinus : V →ₗ[ℝ] W := H.leftDifferential - H.rightDifferential

theorem exchange_diracPlus :
    H.targetExchange.exchange.toLinearMap.comp H.diracPlus =
      H.diracPlus.comp H.sourceExchange.exchange.toLinearMap := by
  dsimp [diracPlus]
  rw [LinearMap.comp_add, LinearMap.add_comp, H.left_exchange, H.right_exchange]
  module

theorem exchange_diracMinus :
    H.targetExchange.exchange.toLinearMap.comp H.diracMinus =
      -(H.diracMinus.comp H.sourceExchange.exchange.toLinearMap) := by
  dsimp [diracMinus]
  rw [LinearMap.comp_sub, LinearMap.sub_comp, H.left_exchange, H.right_exchange]
  module

end ModularFrechetHodgeCompatibility

structure HodgeOppositeIdentification
    (V W : Type*) [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] where
  modularMetricTransport : V ≃ₗ[ℝ] V
  oppositeDifferential : V →ₗ[ℝ] W
  hodgeAdjoint : V →ₗ[ℝ] W
  modularIdentification :
    hodgeAdjoint =
      oppositeDifferential.comp modularMetricTransport.toLinearMap

/-! ## Degreewise exchange of the two differential legs

The following carrier is the graded form of the preceding one-step bridge.
The exchange is allowed to act differently in each degree; the parity laws
therefore do not assume a single endomorphism of the whole direct sum.
-/

structure GradedExchangeDifferentialData
    (F : ℕ → Type*)
    [∀ n, AddCommGroup (F n)] [∀ n, Module ℝ (F n)] where
  exchange : ∀ n, F n →ₗ[ℝ] F n
  exchange_sq : ∀ n,
    (exchange n).comp (exchange n) = LinearMap.id
  leftDifferential : ∀ n, F n →ₗ[ℝ] F (n + 1)
  rightDifferential : ∀ n, F n →ₗ[ℝ] F (n + 1)
  exchange_left : ∀ n,
    (exchange (n + 1)).comp (leftDifferential n) =
      (rightDifferential n).comp (exchange n)
  exchange_right : ∀ n,
    (exchange (n + 1)).comp (rightDifferential n) =
      (leftDifferential n).comp (exchange n)

namespace GradedExchangeDifferentialData

variable {F : ℕ → Type*}
  [∀ n, AddCommGroup (F n)] [∀ n, Module ℝ (F n)]
variable (D : GradedExchangeDifferentialData F)

def diracPlus (n : ℕ) : F n →ₗ[ℝ] F (n + 1) :=
  D.leftDifferential n + D.rightDifferential n

def diracMinus (n : ℕ) : F n →ₗ[ℝ] F (n + 1) :=
  D.leftDifferential n - D.rightDifferential n

theorem exchange_diracPlus (n : ℕ) :
    (D.exchange (n + 1)).comp (D.diracPlus n) =
      (D.diracPlus n).comp (D.exchange n) := by
  rw [diracPlus, LinearMap.comp_add, LinearMap.add_comp,
    D.exchange_left n, D.exchange_right n]
  module

theorem exchange_diracMinus (n : ℕ) :
    (D.exchange (n + 1)).comp (D.diracMinus n) =
      -(D.diracMinus n).comp (D.exchange n) := by
  rw [diracMinus, LinearMap.comp_sub, LinearMap.sub_comp,
    D.exchange_left n, D.exchange_right n]
  module

theorem diracPlus_add_diracMinus (n : ℕ) :
    D.diracPlus n + D.diracMinus n = (2 : ℝ) • D.leftDifferential n := by
  ext x
  dsimp [diracPlus, diracMinus]
  module

theorem diracPlus_sub_diracMinus (n : ℕ) :
    D.diracPlus n - D.diracMinus n = (2 : ℝ) • D.rightDifferential n := by
  ext x
  dsimp [diracPlus, diracMinus]
  module

theorem diracRecombination (n : ℕ) :
    (D.diracPlus n + D.diracMinus n = (2 : ℝ) • D.leftDifferential n) ∧
    (D.diracPlus n - D.diracMinus n = (2 : ℝ) • D.rightDifferential n) := by
  exact ⟨D.diracPlus_add_diracMinus n, D.diracPlus_sub_diracMinus n⟩

theorem leftDifferential_eq_half_add (n : ℕ) :
    D.leftDifferential n = (1 / 2 : ℝ) • (D.diracPlus n + D.diracMinus n) := by
  ext x
  dsimp [diracPlus, diracMinus]
  module

theorem rightDifferential_eq_half_sub (n : ℕ) :
    D.rightDifferential n = (1 / 2 : ℝ) • (D.diracPlus n - D.diracMinus n) := by
  ext x
  dsimp [diracPlus, diracMinus]
  module

theorem diracReconstruction (n : ℕ) :
    D.leftDifferential n = (1 / 2 : ℝ) • (D.diracPlus n + D.diracMinus n) ∧
    D.rightDifferential n = (1 / 2 : ℝ) • (D.diracPlus n - D.diracMinus n) := by
  exact ⟨D.leftDifferential_eq_half_add n, D.rightDifferential_eq_half_sub n⟩

end GradedExchangeDifferentialData

/-! ## Fréchet exterior derivative on `OperatorFrechetForm` and `OperatorFrechetFormK` -/

section FrechetExteriorDerivative

/-- Scalar-parametric alternating Fréchet `n`-form (`OperatorFrechetForm` is
definitionally the `𝕜 = ℂ` specialization). -/
abbrev OperatorFrechetFormK
    (𝕜 A T M : Type*) [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup A] [NormedSpace 𝕜 A]
    [NormedAddCommGroup T] [NormedSpace 𝕜 T]
    [NormedAddCommGroup M] [NormedSpace 𝕜 M] (n : ℕ) :=
  A → (T [⋀^Fin n]→L[𝕜] M)

/-- Real alternating Fréchet `n`-form, used for real charts such as
`Continuous.DeRhamBridge.Chart α`. -/
abbrev RealOperatorFrechetForm
    (A T M : Type*) [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup T] [NormedSpace ℝ T]
    [NormedAddCommGroup M] [NormedSpace ℝ M] (n : ℕ) :=
  OperatorFrechetFormK ℝ A T M n

/-- Fréchet exterior derivative `d_Fr` over an arbitrary nontrivially normed field `𝕜`. -/
noncomputable def frechetExtDerivK
    {𝕜 A M : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup A] [NormedSpace 𝕜 A]
    [NormedAddCommGroup M] [NormedSpace 𝕜 M] {n : ℕ}
    (ω : OperatorFrechetFormK 𝕜 A A M n) :
    OperatorFrechetFormK 𝕜 A A M (n + 1) :=
  extDeriv ω

/-- Fréchet exterior derivative `d_Fr` on `OperatorFrechetForm A A M n`. -/
noncomputable def frechetExtDeriv
    {A M : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup M] [NormedSpace ℂ M] {n : ℕ}
    (ω : OperatorFrechetForm A A M n) :
    OperatorFrechetForm A A M (n + 1) :=
  frechetExtDerivK ω

/-- Real Fréchet exterior derivative `d_Fr` on `RealOperatorFrechetForm A A M n`. -/
noncomputable def frechetExtDerivReal
    {A M : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup M] [NormedSpace ℝ M] {n : ℕ}
    (ω : RealOperatorFrechetForm A A M n) :
    RealOperatorFrechetForm A A M (n + 1) :=
  frechetExtDerivK ω

theorem frechetExtDerivK_eq_mathlib_extDeriv
    {𝕜 A M : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup A] [NormedSpace 𝕜 A]
    [NormedAddCommGroup M] [NormedSpace 𝕜 M] {n : ℕ}
    (ω : OperatorFrechetFormK 𝕜 A A M n) :
    frechetExtDerivK ω = extDeriv ω :=
  rfl

theorem frechetExtDeriv_eq_mathlib_extDeriv
    {A M : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup M] [NormedSpace ℂ M] {n : ℕ}
    (ω : OperatorFrechetForm A A M n) :
    frechetExtDeriv ω = extDeriv ω :=
  rfl

theorem frechetExtDerivK_apply
    {𝕜 A M : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup A] [NormedSpace 𝕜 A]
    [NormedAddCommGroup M] [NormedSpace 𝕜 M] {n : ℕ}
    {ω : OperatorFrechetFormK 𝕜 A A M n} {x : A}
    (hω : DifferentiableAt 𝕜 ω x) (v : Fin (n + 1) → A) :
    frechetExtDerivK ω x v =
      ∑ i, (-1) ^ i.val • fderiv 𝕜 (fun y => ω y (i.removeNth v)) x (v i) :=
  extDeriv_apply hω v

theorem frechetExtDeriv_apply
    {A M : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup M] [NormedSpace ℂ M] {n : ℕ}
    {ω : OperatorFrechetForm A A M n} {x : A}
    (hω : DifferentiableAt ℂ ω x) (v : Fin (n + 1) → A) :
    frechetExtDeriv ω x v =
      ∑ i, (-1) ^ i.val • fderiv ℂ (fun y => ω y (i.removeNth v)) x (v i) :=
  extDeriv_apply hω v

theorem frechetExtDeriv_add
    {A M : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup M] [NormedSpace ℂ M] {n : ℕ}
    {ω₁ ω₂ : OperatorFrechetForm A A M n} {x : A}
    (hω₁ : DifferentiableAt ℂ ω₁ x) (hω₂ : DifferentiableAt ℂ ω₂ x) :
    frechetExtDeriv (ω₁ + ω₂) x = frechetExtDeriv ω₁ x + frechetExtDeriv ω₂ x :=
  extDeriv_add hω₁ hω₂

theorem frechetExtDeriv_smul
    {A M : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup M] [NormedSpace ℂ M] {n : ℕ}
    (c : ℂ) (ω : OperatorFrechetForm A A M n) (x : A) :
    frechetExtDeriv (c • ω) x = c • frechetExtDeriv ω x :=
  extDeriv_smul c ω

theorem frechetExtDeriv_constOfIsEmpty
    {A M : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup M] [NormedSpace ℂ M]
    (f : A → M) (x : A) :
    frechetExtDeriv (fun y => ContinuousAlternatingMap.constOfIsEmpty ℂ A (Fin 0) (f y)) x =
      ContinuousAlternatingMap.ofSubsingleton ℂ A M (0 : Fin 1) (fderiv ℂ f x) :=
  extDeriv_constOfIsEmpty f x

theorem frechetExtDerivK_frechetExtDeriv_apply
    {𝕜 A M : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup A] [NormedSpace 𝕜 A]
    [NormedAddCommGroup M] [NormedSpace 𝕜 M] {n : ℕ}
    {r : WithTop ℕ∞} {ω : OperatorFrechetFormK 𝕜 A A M n} {x : A}
    (hω : ContDiffAt 𝕜 r ω x) (hr : minSmoothness 𝕜 2 ≤ r) :
    frechetExtDerivK (frechetExtDerivK ω) x = 0 :=
  extDeriv_extDeriv_apply hω hr

theorem frechetExtDerivK_frechetExtDeriv
    {𝕜 A M : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup A] [NormedSpace 𝕜 A]
    [NormedAddCommGroup M] [NormedSpace 𝕜 M] {n : ℕ}
    {r : WithTop ℕ∞} {ω : OperatorFrechetFormK 𝕜 A A M n}
    (hω : ContDiff 𝕜 r ω) (hr : minSmoothness 𝕜 2 ≤ r) :
    frechetExtDerivK (frechetExtDerivK ω) = 0 :=
  extDeriv_extDeriv hω hr

theorem frechetExtDeriv_frechetExtDeriv_apply
    {A M : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup M] [NormedSpace ℂ M] {n : ℕ}
    {r : WithTop ℕ∞} {ω : OperatorFrechetForm A A M n} {x : A}
    (hω : ContDiffAt ℂ r ω x) (hr : minSmoothness ℂ 2 ≤ r) :
    frechetExtDeriv (frechetExtDeriv ω) x = 0 :=
  extDeriv_extDeriv_apply hω hr

theorem frechetExtDeriv_frechetExtDeriv
    {A M : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup M] [NormedSpace ℂ M] {n : ℕ}
    {r : WithTop ℕ∞} {ω : OperatorFrechetForm A A M n}
    (hω : ContDiff ℂ r ω) (hr : minSmoothness ℂ 2 ≤ r) :
    frechetExtDeriv (frechetExtDeriv ω) = 0 :=
  extDeriv_extDeriv hω hr

end FrechetExteriorDerivative

/-! ## Arbitrary-degree Chevalley–Eilenberg alignment via `FrechetOperatorDerivation` -/

section CEAlignment

open InfoGeometry.Algebra
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.Optics.OperatorDerivationForms

/-- Smooth (`C^ω`, i.e. `⊤ : WithTop ℕ∞`) operator-valued maps `A → A` over `𝕜`,
forming a noncommutative `𝕜`-algebra under pointwise operations. -/
structure SmoothOpMap (𝕜 A : Type*) [NontriviallyNormedField 𝕜]
    [NormedRing A] [NormedAlgebra 𝕜 A] where
  toFun : A → A
  contDiff : ContDiff 𝕜 (⊤ : WithTop ℕ∞) toFun

namespace SmoothOpMap

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜]
  [NormedRing A] [NormedAlgebra 𝕜 A]

instance : CoeFun (SmoothOpMap 𝕜 A) (fun _ => A → A) :=
  ⟨fun f => f.toFun⟩

@[ext]
theorem ext {f g : SmoothOpMap 𝕜 A} (h : ∀ x, f x = g x) : f = g := by
  cases f
  cases g
  congr 1
  exact funext h

instance : Zero (SmoothOpMap 𝕜 A) where
  zero := ⟨0, contDiff_const⟩

instance : One (SmoothOpMap 𝕜 A) where
  one := ⟨1, contDiff_const⟩

instance : Add (SmoothOpMap 𝕜 A) where
  add f g := ⟨f.toFun + g.toFun, f.contDiff.add g.contDiff⟩

instance : Neg (SmoothOpMap 𝕜 A) where
  neg f := ⟨-f.toFun, f.contDiff.neg⟩

instance : Sub (SmoothOpMap 𝕜 A) where
  sub f g := ⟨f.toFun - g.toFun, f.contDiff.sub g.contDiff⟩

instance : Mul (SmoothOpMap 𝕜 A) where
  mul f g := ⟨f.toFun * g.toFun, f.contDiff.mul g.contDiff⟩

instance : SMul 𝕜 (SmoothOpMap 𝕜 A) where
  smul c f := ⟨fun x => c • f.toFun x, f.contDiff.const_smul c⟩

@[simp] theorem zero_apply (x : A) : (0 : SmoothOpMap 𝕜 A) x = 0 := rfl
@[simp] theorem one_apply (x : A) : (1 : SmoothOpMap 𝕜 A) x = 1 := rfl
@[simp] theorem add_apply (f g : SmoothOpMap 𝕜 A) (x : A) : (f + g) x = f x + g x := rfl
@[simp] theorem neg_apply (f : SmoothOpMap 𝕜 A) (x : A) : (-f) x = -f x := rfl
@[simp] theorem sub_apply (f g : SmoothOpMap 𝕜 A) (x : A) : (f - g) x = f x - g x := rfl
@[simp] theorem mul_apply (f g : SmoothOpMap 𝕜 A) (x : A) : (f * g) x = f x * g x := rfl
@[simp] theorem smul_apply (c : 𝕜) (f : SmoothOpMap 𝕜 A) (x : A) :
    (c • f) x = c • f x := rfl

instance : Ring (SmoothOpMap 𝕜 A) where
  add_assoc f g h := by ext x; exact add_assoc _ _ _
  zero_add f := by ext x; exact zero_add _
  add_zero f := by ext x; exact add_zero _
  neg_add_cancel f := by ext x; exact neg_add_cancel _
  add_comm f g := by ext x; exact add_comm _ _
  sub_eq_add_neg f g := by ext x; exact sub_eq_add_neg _ _
  nsmul := nsmulRec
  zsmul := zsmulRec
  mul_assoc f g h := by ext x; exact mul_assoc _ _ _
  one_mul f := by ext x; exact one_mul _
  mul_one f := by ext x; exact mul_one _
  left_distrib f g h := by ext x; exact left_distrib _ _ _
  right_distrib f g h := by ext x; exact right_distrib _ _ _
  zero_mul f := by ext x; exact zero_mul _
  mul_zero f := by ext x; exact mul_zero _

@[simp] theorem sum_apply {ι : Type*} (s : Finset ι) (f : ι → SmoothOpMap 𝕜 A) (x : A) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

instance : Algebra 𝕜 (SmoothOpMap 𝕜 A) where
  algebraMap :=
    { toFun := fun c => ⟨fun _ => algebraMap 𝕜 A c, contDiff_const⟩
      map_one' := by ext x; simp
      map_mul' := fun c₁ c₂ => by ext x; simp
      map_zero' := by ext x; simp
      map_add' := fun c₁ c₂ => by ext x; simp }
  commutes' c f := by
    ext x
    change algebraMap 𝕜 A c * f x = f x * algebraMap 𝕜 A c
    exact Algebra.commutes c (f x)
  smul_def' c f := by
    ext x
    change c • f x = algebraMap 𝕜 A c * f x
    exact Algebra.smul_def c (f x)

end SmoothOpMap

/-- A `FrechetOperatorDerivation 𝕜 A` viewed as a linear vector field on `A`,
equipped with the vector-field Lie bracket `⁅D, E⁆ = commutator E D = -(commutator D E)`
so that directional differentiation satisfies `δ_⁅D, E⁆ = [δ_D, δ_E]`. -/
structure FrechetVectorField (𝕜 A : Type*) [NontriviallyNormedField 𝕜]
    [NormedRing A] [NormedAlgebra 𝕜 A] where
  toDerivation : FrechetOperatorDerivation 𝕜 A

namespace FrechetVectorField

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜]
  [NormedRing A] [NormedAlgebra 𝕜 A]

@[ext]
theorem ext {D E : FrechetVectorField 𝕜 A} (h : D.toDerivation = E.toDerivation) : D = E := by
  cases D
  cases E
  congr 1

instance : Zero (FrechetVectorField 𝕜 A) := ⟨⟨0⟩⟩
instance : Add (FrechetVectorField 𝕜 A) := ⟨fun D E => ⟨D.toDerivation + E.toDerivation⟩⟩
instance : Neg (FrechetVectorField 𝕜 A) := ⟨fun D => ⟨-D.toDerivation⟩⟩
instance : Sub (FrechetVectorField 𝕜 A) := ⟨fun D E => ⟨D.toDerivation - E.toDerivation⟩⟩
instance : SMul 𝕜 (FrechetVectorField 𝕜 A) := ⟨fun c D => ⟨c • D.toDerivation⟩⟩

instance : Bracket (FrechetVectorField 𝕜 A) (FrechetVectorField 𝕜 A) where
  bracket D E := ⟨FrechetOperatorDerivation.commutator E.toDerivation D.toDerivation⟩

@[simp] theorem zero_toDerivation :
    (0 : FrechetVectorField 𝕜 A).toDerivation = 0 := rfl
@[simp] theorem add_toDerivation (D E : FrechetVectorField 𝕜 A) :
    (D + E).toDerivation = D.toDerivation + E.toDerivation := rfl
@[simp] theorem neg_toDerivation (D : FrechetVectorField 𝕜 A) :
    (-D).toDerivation = -D.toDerivation := rfl
@[simp] theorem sub_toDerivation (D E : FrechetVectorField 𝕜 A) :
    (D - E).toDerivation = D.toDerivation - E.toDerivation := rfl
@[simp] theorem smul_toDerivation (c : 𝕜) (D : FrechetVectorField 𝕜 A) :
    (c • D).toDerivation = c • D.toDerivation := rfl
@[simp] theorem lie_toDerivation (D E : FrechetVectorField 𝕜 A) :
    ⁅D, E⁆.toDerivation = ⁅E.toDerivation, D.toDerivation⁆ := rfl

instance : AddCommGroup (FrechetVectorField 𝕜 A) where
  add_assoc D E F := by ext a; exact add_assoc (D.toDerivation a) _ _
  zero_add D := by ext a; exact zero_add (D.toDerivation a)
  add_zero D := by ext a; exact add_zero (D.toDerivation a)
  neg_add_cancel D := by ext a; exact neg_add_cancel (D.toDerivation a)
  add_comm D E := by ext a; exact add_comm (D.toDerivation a) _
  sub_eq_add_neg D E := by ext a; exact sub_eq_add_neg (D.toDerivation a) _
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : Module 𝕜 (FrechetVectorField 𝕜 A) where
  one_smul D := by ext a; exact one_smul 𝕜 (D.toDerivation a)
  mul_smul c₁ c₂ D := by ext a; exact mul_smul c₁ c₂ (D.toDerivation a)
  smul_zero c := by ext a; exact smul_zero c
  smul_add c D E := by ext a; exact smul_add c (D.toDerivation a) _
  add_smul c₁ c₂ D := by ext a; exact add_smul c₁ c₂ (D.toDerivation a)
  zero_smul D := by ext a; exact zero_smul 𝕜 (D.toDerivation a)

instance : LieRing (FrechetVectorField 𝕜 A) where
  add_lie D E F := by
    ext a
    simp only [lie_toDerivation, add_toDerivation, FrechetOperatorDerivation.lie_apply,
      FrechetOperatorDerivation.add_apply, FrechetOperatorDerivation.map_add]
    abel
  lie_add D E F := by
    ext a
    simp only [lie_toDerivation, add_toDerivation, FrechetOperatorDerivation.lie_apply,
      FrechetOperatorDerivation.add_apply, FrechetOperatorDerivation.map_add]
    abel
  lie_self D := by ext a; simp
  leibniz_lie D E F := by
    ext a
    have hsub : ∀ G : FrechetOperatorDerivation 𝕜 A, ∀ x y, G (x - y) = G x - G y :=
      fun G x y => G.toContinuousLinearMap.map_sub x y
    simp only [lie_toDerivation, add_toDerivation, FrechetOperatorDerivation.lie_apply,
      FrechetOperatorDerivation.add_apply, hsub]
    abel

instance : LieAlgebra 𝕜 (FrechetVectorField 𝕜 A) where
  lie_smul c D E := by
    ext a
    simp only [lie_toDerivation, smul_toDerivation, FrechetOperatorDerivation.lie_apply,
      FrechetOperatorDerivation.smul_apply, FrechetOperatorDerivation.map_smul, smul_sub]

theorem lie_apply_eq_vectorField_lieBracket
    (D E : FrechetVectorField 𝕜 A) (x : A) :
    ⁅D, E⁆.toDerivation x =
      VectorField.lieBracket 𝕜 (D.toDerivation : A → A) (E.toDerivation : A → A) x := by
  change E.toDerivation (D.toDerivation x) - D.toDerivation (E.toDerivation x) =
    fderiv 𝕜 (E.toDerivation : A → A) x (D.toDerivation x) -
      fderiv 𝕜 (D.toDerivation : A → A) x (E.toDerivation x)
  rw [D.toDerivation.toContinuousLinearMap.fderiv, E.toDerivation.toContinuousLinearMap.fderiv]

end FrechetVectorField

/-- Faithful `DerivationLieLane 𝕜 (SmoothOpMap 𝕜 A)` given by Fréchet directional
differentiation along linear vector fields `FrechetVectorField 𝕜 A`. -/
def frechetVectorFieldDerivationLane (𝕜 A : Type*) [NontriviallyNormedField 𝕜]
    [NormedRing A] [NormedAlgebra 𝕜 A] :
    DerivationLieLane 𝕜 (SmoothOpMap 𝕜 A) where
  L := FrechetVectorField 𝕜 A
  lieRing := inferInstance
  lieAlgebra := inferInstance
  act :=
    { toFun := fun D =>
        ⟨{ toFun := fun f =>
            ⟨fun x => fderiv 𝕜 f.toFun x (D.toDerivation x),
              (f.contDiff.fderiv_right (m := (⊤ : WithTop ℕ∞)) le_top).clm_apply
                D.toDerivation.toContinuousLinearMap.contDiff⟩
           map_add' := fun f g => SmoothOpMap.ext fun x => by
             simp only [SmoothOpMap.add_apply]
             change fderiv 𝕜 (f.toFun + g.toFun) x (D.toDerivation x) = _
             rw [fderiv_add (f.contDiff.differentiable (by simp) x)
                 (g.contDiff.differentiable (by simp) x), add_apply]
           map_smul' := fun c f => SmoothOpMap.ext fun x => by
             change fderiv 𝕜 (c • f.toFun) x (D.toDerivation x) = _
             rw [fderiv_const_smul (f.contDiff.differentiable (by simp) x), smul_apply]
             rfl },
         fun f g => SmoothOpMap.ext fun x => by
           change fderiv 𝕜 (fun y => f.toFun y * g.toFun y) x (D.toDerivation x) =
             fderiv 𝕜 f.toFun x (D.toDerivation x) * g.toFun x +
               f.toFun x * fderiv 𝕜 g.toFun x (D.toDerivation x)
           rw [fderiv_fun_mul' (f.contDiff.differentiable (by simp) x)
               (g.contDiff.differentiable (by simp) x)]
           simp only [add_apply, smul_apply, smul_eq_mul, add_comm]
           rfl ⟩
      map_add' := fun D E => Subtype.ext (LinearMap.ext fun f => SmoothOpMap.ext fun x => by
        simp [FrechetVectorField.add_toDerivation])
      map_smul' := fun c D => Subtype.ext (LinearMap.ext fun f => SmoothOpMap.ext fun x => by
        simp [FrechetVectorField.smul_toDerivation])
      map_lie' := fun {D E} => Subtype.ext (LinearMap.ext fun f => SmoothOpMap.ext fun x => by
        change fderiv 𝕜 f.toFun x (⁅D, E⁆.toDerivation x) = _
        rw [FrechetVectorField.lie_apply_eq_vectorField_lieBracket]
        exact VectorField.fderiv_apply_lieBracket f.contDiff.contDiffAt le_top
          E.toDerivation.toContinuousLinearMap.differentiableAt
          D.toDerivation.toContinuousLinearMap.differentiableAt) }
  faithful := fun D E h => by
    ext a
    have hact := congrArg (fun T : NonAssocDerivation.derivations 𝕜 (SmoothOpMap 𝕜 A) =>
      ((T : Module.End 𝕜 (SmoothOpMap 𝕜 A)) ⟨id, contDiff_id⟩).toFun a) h
    simpa [fderiv_id] using hact

/-- Evaluating a `C^ω` Fréchet `n`-form on `n` `C^ω` vector fields produces a `C^ω` map. -/
theorem contDiff_eval_frechetForm
    {𝕜 A M : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup A] [NormedSpace 𝕜 A]
    [NormedAddCommGroup M] [NormedSpace 𝕜 M] :
    ∀ (n : ℕ) (ω : OperatorFrechetFormK 𝕜 A A M n), ContDiff 𝕜 (⊤ : WithTop ℕ∞) ω →
      ∀ (v : Fin n → A → A), (∀ i, ContDiff 𝕜 (⊤ : WithTop ℕ∞) (v i)) →
        ContDiff 𝕜 (⊤ : WithTop ℕ∞) (fun x => ω x (fun i => v i x))
  | 0, ω, hω, v, _ => by
    have heq : (fun x => ω x (fun i => v i x)) =
        fun x => (ContinuousAlternatingMap.constOfIsEmptyLIE 𝕜 A M (Fin 0)).symm (ω x) := by
      funext x
      change ω x (fun i => v i x) = ω x (fun _ => 0)
      congr 1
      exact Subsingleton.elim _ _
    rw [heq]
    exact (ContinuousAlternatingMap.constOfIsEmptyLIE 𝕜 A M (Fin 0)).symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp hω
  | m + 1, ω, hω, v, hv => by
    have hcurry : ContDiff 𝕜 (⊤ : WithTop ℕ∞) (fun x => (ω x).curryLeft) :=
      ContDiff.comp
        (IsBoundedLinearMap.contDiff (𝕜 := 𝕜) (E := A [⋀^Fin (m + 1)]→L[𝕜] M)
          (F := A →L[𝕜] A [⋀^Fin m]→L[𝕜] M)
          (f := fun f : A [⋀^Fin (m + 1)]→L[𝕜] M => f.curryLeft)
          ⟨⟨fun _ _ => rfl, fun _ _ => rfl⟩, ⟨1, zero_lt_one, fun f => by simp⟩⟩)
        hω
    have hhead : ContDiff 𝕜 (⊤ : WithTop ℕ∞) (fun x => (ω x).curryLeft (v 0 x)) :=
      hcurry.clm_apply (hv 0)
    have ih := contDiff_eval_frechetForm m (fun x => (ω x).curryLeft (v 0 x)) hhead
      (fun i => v i.succ) (fun i => hv i.succ)
    have heq : (fun x => ω x (fun i => v i x)) =
        fun x => (ω x).curryLeft (v 0 x) (fun i => v i.succ x) := by
      funext x
      rw [ContinuousAlternatingMap.curryLeft_apply_apply]
      congr 1
      funext i
      cases i using Fin.cases <;> rfl
    simpa only [heq] using ih

/-- If `ω` is `C^ω`, then its Fréchet exterior derivative `frechetExtDerivK ω` is `C^ω`. -/
theorem contDiff_frechetExtDerivK
    {𝕜 A M : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup A] [NormedSpace 𝕜 A]
    [NormedAddCommGroup M] [NormedSpace 𝕜 M] {n : ℕ}
    {ω : OperatorFrechetFormK 𝕜 A A M n} (hω : ContDiff 𝕜 (⊤ : WithTop ℕ∞) ω) :
    ContDiff 𝕜 (⊤ : WithTop ℕ∞) (frechetExtDerivK ω) := by
  change ContDiff 𝕜 (⊤ : WithTop ℕ∞)
    (fun x => ContinuousAlternatingMap.alternatizeUncurryFinCLM 𝕜 A M (fderiv 𝕜 ω x))
  exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM 𝕜 A M).contDiff.comp
    (hω.fderiv_right le_top)

/-- View a `C^ω` `OperatorFrechetFormK 𝕜 A A A n` as an algebraic
`DerivationOperatorForm (frechetVectorFieldDerivationLane 𝕜 A) n`. -/
def frechetFormToCEForm
    {𝕜 A : Type*} [NontriviallyNormedField 𝕜]
    [NormedRing A] [NormedAlgebra 𝕜 A]
    (n : ℕ) (ω : OperatorFrechetFormK 𝕜 A A A n) (hω : ContDiff 𝕜 (⊤ : WithTop ℕ∞) ω) :
    DerivationOperatorForm (frechetVectorFieldDerivationLane 𝕜 A) n where
  toFun v :=
    ⟨fun x => ω x (fun i => (v i).toDerivation x),
      contDiff_eval_frechetForm n ω hω
        (fun i => (v i).toDerivation)
        (fun i => (v i).toDerivation.toContinuousLinearMap.contDiff)⟩
  map_update_add' v i D E := SmoothOpMap.ext fun x => by
    change ω x (fun j => (Function.update v i (D + E) j).toDerivation x) =
      ω x (fun j => (Function.update v i D j).toDerivation x) +
        ω x (fun j => (Function.update v i E j).toDerivation x)
    have hupd : (fun j => (Function.update v i (D + E) j).toDerivation x) =
        Function.update (fun j => (v j).toDerivation x) i (D.toDerivation x + E.toDerivation x) := by
      ext j
      by_cases hji : j = i
      · subst hji; rw [Function.update_self, Function.update_self]; rfl
      · simp [hji]
    have hupdD : (fun j => (Function.update v i D j).toDerivation x) =
        Function.update (fun j => (v j).toDerivation x) i (D.toDerivation x) := by
      ext j; by_cases hji : j = i <;> simp [hji]
    have hupdE : (fun j => (Function.update v i E j).toDerivation x) =
        Function.update (fun j => (v j).toDerivation x) i (E.toDerivation x) := by
      ext j; by_cases hji : j = i <;> simp [hji]
    rw [hupd, hupdD, hupdE, (ω x).map_update_add]
  map_update_smul' v i c D := SmoothOpMap.ext fun x => by
    change ω x (fun j => (Function.update v i (c • D) j).toDerivation x) =
      c • ω x (fun j => (Function.update v i D j).toDerivation x)
    have hupd : (fun j => (Function.update v i (c • D) j).toDerivation x) =
        Function.update (fun j => (v j).toDerivation x) i (c • D.toDerivation x) := by
      ext j
      by_cases hji : j = i
      · subst hji; rw [Function.update_self, Function.update_self]; rfl
      · simp [hji]
    have hupdD : (fun j => (Function.update v i D j).toDerivation x) =
        Function.update (fun j => (v j).toDerivation x) i (D.toDerivation x) := by
      ext j; by_cases hji : j = i <;> simp [hji]
    rw [hupd, hupdD, (ω x).map_update_smul]
  map_eq_zero_of_eq' v i j hij hne := SmoothOpMap.ext fun x => by
    change ω x (fun k => (v k).toDerivation x) = 0
    exact (ω x).map_eq_zero_of_eq _ (congrArg (fun D : FrechetVectorField 𝕜 A => D.toDerivation x) hij) hne

@[simp]
theorem frechetFormToCEForm_apply
    {𝕜 A : Type*} [NontriviallyNormedField 𝕜]
    [NormedRing A] [NormedAlgebra 𝕜 A]
    (n : ℕ) (ω : OperatorFrechetFormK 𝕜 A A A n) (hω : ContDiff 𝕜 (⊤ : WithTop ℕ∞) ω)
    (v : Fin n → FrechetVectorField 𝕜 A) (x : A) :
    (frechetFormToCEForm n ω hω v).toFun x = ω x (fun i => (v i).toDerivation x) :=
  rfl

/-- General Palais formula for `DerivationExteriorCalculus.actionExteriorDerivative`
at all degrees `n + 1`, matching `VectorField.extDeriv_apply_vectorField`. -/
theorem actionExteriorDerivative_palais
    {R A : Type*} [CommRing R] [AddCommGroup A] [Module R A]
    (K : LieActionLane R A) :
    ∀ (n : ℕ) (ω : ActionOperatorForm K (n + 1)) (v : Fin (n + 2) → K.L),
      actionExteriorDerivative K (n + 1) ω v =
        (∑ i : Fin (n + 2), (-1 : R) ^ i.val • K.operatorAction (v i) (ω (i.removeNth v))) -
          ∑ i : Fin (n + 1), ∑ j ∈ Finset.Ici i,
            (-1 : R) ^ (i + j : ℕ) •
              ω (Matrix.vecCons ⁅v i.castSucc, v j.succ⁆
                (j.removeNth (i.castSucc.removeNth v)))
  | 0, ω, v => by
    change (actionExteriorDerivative K 1 ω).curryLeft (v 0) (Fin.tail v) = _
    rw [actionExteriorDerivative_succ_curryLeft, AlternatingMap.sub_apply,
      lieDeriv_apply, actionExteriorDerivative_zero_apply]
    have h0r : (0 : Fin 2).removeNth v = Fin.tail v := by
      ext i
      simp [Fin.removeNth, Fin.tail_def]
    have h1r : (1 : Fin 2).removeNth v = ![v 0] := by
      ext i
      fin_cases i
      simp [Fin.removeNth]
    have hcons : Matrix.vecCons (v 0) Fin.elim0 = ![v 0] := by
      ext i
      fin_cases i
      rfl
    have htail0 : Fin.tail v 0 = v 1 := rfl
    have hupd : Function.update (Fin.tail v) 0 ⁅v 0, v 1⁆ =
        Matrix.vecCons ⁅v 0, v 1⁆ ((0 : Fin 1).removeNth ((0 : Fin 1).castSucc.removeNth v)) := by
      ext i; fin_cases i; rfl
    have hIci0 : Finset.Ici (0 : Fin 1) = Finset.univ := by decide
    rw [Fin.sum_univ_two, Fin.sum_univ_one, Fin.sum_univ_one, hIci0, Fin.sum_univ_one,
      htail0, h0r, h1r, hupd]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul,
      Fin.castSucc_zero, add_zero, AlternatingMap.curryLeft_apply_apply, hcons, Fin.tail_def]
    change K.operatorAction (v 0) (ω (Fin.tail v)) -
        ω (Matrix.vecCons ⁅v 0, v 1⁆ ((0 : Fin 1).removeNth ((0 : Fin 1).castSucc.removeNth v))) -
        K.operatorAction (v 1) (ω ![v 0]) =
      K.operatorAction (v 0) (ω (Fin.tail v)) + -K.operatorAction (v 1) (ω ![v 0]) -
        ω (Matrix.vecCons ⁅v 0, v 1⁆ ((0 : Fin 1).removeNth ((0 : Fin 1).castSucc.removeNth v)))
    abel
  | m + 1, ω, v => by
    change (actionExteriorDerivative K (m + 2) ω).curryLeft (v 0) (Fin.tail v) = _
    rw [actionExteriorDerivative_succ_curryLeft, AlternatingMap.sub_apply, lieDeriv_apply]
    have ih := actionExteriorDerivative_palais K m (ω.curryLeft (v 0)) (Fin.tail v)
    rw [ih]
    have h0r : (0 : Fin (m + 3)).removeNth v = Fin.tail v := by
      ext k; simp [Fin.removeNth, Fin.tail_def]
    have hsucc_above : ∀ {k : ℕ} (i : Fin (k + 1)) (j : Fin k),
        (i.succ).succAbove j.succ = (i.succAbove j).succ := by
      intro k i j
      simp only [Fin.succAbove, Fin.castSucc_succ, Fin.succ_lt_succ_iff]
      split_ifs <;> rfl
    have hsucc_above0 : ∀ {k : ℕ} (i : Fin (k + 1)),
        (i.succ).succAbove 0 = 0 := by
      intro k i
      simp [Fin.succAbove]
    have hlieSum :
        (∑ j : Fin (m + 2), ω (Function.update (Fin.tail v) j ⁅v 0, (Fin.tail v) j⁆)) =
          ∑ j : Fin (m + 2), (-1 : R) ^ j.val •
            ω (Matrix.vecCons ⁅v 0, v j.succ⁆ (j.removeNth ((0 : Fin (m + 3)).removeNth v))) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      have hjupd : Function.update (Fin.tail v) j ⁅v 0, (Fin.tail v) j⁆ =
          j.insertNth ⁅v 0, v j.succ⁆ (j.removeNth (Fin.tail v)) := by
        ext k
        rcases eq_or_ne k j with rfl | hne
        · simp [Fin.tail_def]
        · rw [Function.update_of_ne hne]
          rcases Fin.exists_succAbove_eq hne with ⟨p, rfl⟩
          simp [Fin.removeNth]
      rw [hjupd, ω.map_insertNth, h0r, ← Int.cast_smul_eq_zsmul R]
      simp
    have hheadSum :
        (∑ i : Fin (m + 3), (-1 : R) ^ i.val • K.operatorAction (v i) (ω (i.removeNth v))) =
          K.operatorAction (v 0) (ω (Fin.tail v)) -
            ∑ i : Fin (m + 2), (-1 : R) ^ i.val •
              K.operatorAction ((Fin.tail v) i) ((ω.curryLeft (v 0)) (i.removeNth (Fin.tail v))) := by
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, one_smul, h0r, Fin.val_succ, pow_succ, mul_neg, mul_one,
        neg_smul, Finset.sum_neg_distrib, ← sub_eq_add_neg]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      have hisucc : i.succ.removeNth v = Matrix.vecCons (v 0) (i.removeNth (Fin.tail v)) := by
        ext k
        cases k using Fin.cases with
        | zero => simp [Fin.removeNth, hsucc_above0]
        | succ p => simp [Fin.removeNth, Fin.tail_def, hsucc_above]
      simp only [AlternatingMap.curryLeft_apply_apply, hisucc, Fin.tail_def]
    have hbrackSum :
        (∑ i : Fin (m + 2), ∑ j ∈ Finset.Ici i,
            (-1 : R) ^ (i + j : ℕ) •
              ω (Matrix.vecCons ⁅v i.castSucc, v j.succ⁆ (j.removeNth (i.castSucc.removeNth v)))) =
          (∑ j : Fin (m + 2), (-1 : R) ^ j.val •
            ω (Matrix.vecCons ⁅v 0, v j.succ⁆ (j.removeNth ((0 : Fin (m + 3)).removeNth v)))) -
          ∑ i : Fin (m + 1), ∑ j ∈ Finset.Ici i,
            (-1 : R) ^ (i + j : ℕ) •
              (ω.curryLeft (v 0))
                (Matrix.vecCons ⁅(Fin.tail v) i.castSucc, (Fin.tail v) j.succ⁆
                  (j.removeNth (i.castSucc.removeNth (Fin.tail v)))) := by
      have hIci0 : Finset.Ici (0 : Fin (m + 2)) = Finset.univ := by ext x; simp
      rw [Fin.sum_univ_succ, sub_eq_add_neg]
      congr 1
      · simp only [Fin.val_zero, Fin.castSucc_zero, hIci0, zero_add]
      · rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hIci : (∑ j ∈ Finset.Ici i.succ,
            (-1 : R) ^ (i.succ + j : ℕ) •
              ω (Matrix.vecCons ⁅v i.succ.castSucc, v j.succ⁆
                (j.removeNth (i.succ.castSucc.removeNth v)))) =
            ∑ j ∈ Finset.Ici i,
              (-1 : R) ^ (i.succ + j.succ : ℕ) •
                ω (Matrix.vecCons ⁅v i.succ.castSucc, v j.succ.succ⁆
                  (j.succ.removeNth (i.succ.castSucc.removeNth v))) := by
          refine (Finset.sum_nbij Fin.succ
            (fun j hj => Finset.mem_Ici.mpr (Fin.succ_le_succ_iff.mpr (Finset.mem_Ici.mp hj)))
            (fun _ _ _ _ h => Fin.succ_inj.mp h) ?_ (fun _ _ => rfl)).symm
          intro k hk
          cases k using Fin.cases with
          | zero => exact (Fin.not_le.mpr (Fin.succ_pos i) (Finset.mem_Ici.mp hk)).elim
          | succ j => exact ⟨j, Finset.mem_Ici.mpr (Fin.succ_le_succ_iff.mp (Finset.mem_Ici.mp hk)), rfl⟩
        rw [hIci, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hpow : (-1 : R) ^ (i.succ + j.succ : ℕ) = (-1 : R) ^ (i + j : ℕ) := by
          rw [show (i.succ + j.succ : ℕ) = (i + j : ℕ) + 2 by simp [Fin.val_succ]; omega,
            pow_add, show (-1 : R) ^ 2 = 1 by ring, mul_one]
        have hrem : j.succ.removeNth (i.succ.castSucc.removeNth v) =
            Matrix.vecCons (v 0) (j.removeNth (i.castSucc.removeNth (Fin.tail v))) := by
          ext k
          cases k using Fin.cases with
          | zero => simp [Fin.removeNth, hsucc_above0]
          | succ p => simp [Fin.removeNth, Fin.tail_def, hsucc_above]
        have hswap : Matrix.vecCons (v 0)
              (Matrix.vecCons ⁅(Fin.tail v) i.castSucc, (Fin.tail v) j.succ⁆
                (j.removeNth (i.castSucc.removeNth (Fin.tail v)))) =
            (Matrix.vecCons ⁅v i.succ.castSucc, v j.succ.succ⁆
              (j.succ.removeNth (i.succ.castSucc.removeNth v))) ∘ Equiv.swap 0 1 := by
          ext k
          cases k using Fin.cases with
          | zero =>
            simp only [Function.comp_apply, Equiv.swap_apply_left, Matrix.cons_val_zero]
            change v 0 = j.succ.removeNth (i.succ.castSucc.removeNth v) 0
            rw [hrem]; rfl
          | succ p =>
            cases p using Fin.cases with
            | zero =>
              simp [Equiv.swap_apply_right, Fin.tail_def, Fin.castSucc_succ]
            | succ q =>
              have hne0 : q.succ.succ ≠ 0 := Fin.succ_ne_zero _
              have hne1 : q.succ.succ ≠ 1 := by simp [Fin.ext_iff]
              simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hne0 hne1,
                Matrix.cons_val_succ]
              change j.removeNth (i.castSucc.removeNth (Fin.tail v)) q =
                j.succ.removeNth (i.succ.castSucc.removeNth v) q.succ
              rw [hrem]; rfl
        rw [AlternatingMap.curryLeft_apply_apply, hswap,
          ω.map_swap _ Fin.zero_ne_one, smul_neg, hpow, neg_neg]
    rw [hlieSum, hheadSum, hbrackSum]
    abel

private theorem ceExteriorDerivative_zero_eval_apply
    {R A : Type*} [CommRing R] [NonUnitalNonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A]
    (K : DerivationLieLane R A) (ω : DerivationOperatorForm K 0) (v : Fin 1 → K.L) :
    ceExteriorDerivative K 0 ω v = K.operatorAction (v 0) (ω Fin.elim0) :=
  actionExteriorDerivative_zero_apply K.toLieActionLane ω v

/-- Arbitrary-degree Palais correspondence: for every `n : ℕ` and smooth `ω`,
Fréchet exterior differentiation `frechetExtDerivK ω` coincides with
Chevalley–Eilenberg `ceExteriorDerivative (frechetVectorFieldDerivationLane 𝕜 A) n`. -/
theorem frechetExtDerivK_linear_eq_ceExteriorDerivative
    {𝕜 A : Type*} [NontriviallyNormedField 𝕜]
    [NormedRing A] [NormedAlgebra 𝕜 A]
    (n : ℕ) (ω : OperatorFrechetFormK 𝕜 A A A n) (hω : ContDiff 𝕜 (⊤ : WithTop ℕ∞) ω) :
    frechetFormToCEForm (n + 1) (frechetExtDerivK ω) (contDiff_frechetExtDerivK hω) =
      ceExteriorDerivative (frechetVectorFieldDerivationLane 𝕜 A) n
        (frechetFormToCEForm n ω hω) := by
  ext v x
  cases n with
  | zero =>
    change frechetExtDerivK ω x (fun i => ((v i : FrechetVectorField 𝕜 A).toDerivation x)) =
      (ceExteriorDerivative (frechetVectorFieldDerivationLane 𝕜 A) 0
        (frechetFormToCEForm 0 ω hω) v).toFun x
    rw [ceExteriorDerivative_zero_eval_apply]
    have hω0 : ω = fun y => ContinuousAlternatingMap.constOfIsEmpty 𝕜 A (Fin 0) (ω y Fin.elim0) := by
      ext y w
      change ω y w = ω y Fin.elim0
      congr 1
      exact Subsingleton.elim _ _
    have hex : frechetExtDerivK ω x =
        ContinuousAlternatingMap.ofSubsingleton 𝕜 A A (0 : Fin 1)
          (fderiv 𝕜 (fun y => ω y Fin.elim0) x) := by
      rw [frechetExtDerivK]
      conv_lhs => rw [hω0]
      exact extDeriv_constOfIsEmpty (fun y => ω y Fin.elim0) x
    rw [hex]
    change fderiv 𝕜 (fun y => ω y Fin.elim0) x ((v 0 : FrechetVectorField 𝕜 A).toDerivation x) =
      fderiv 𝕜 (fun y => ω y (fun i => (Fin.elim0 i : FrechetVectorField 𝕜 A).toDerivation y)) x
        ((v 0 : FrechetVectorField 𝕜 A).toDerivation x)
    congr 2
    ext y
    congr 1
    exact Subsingleton.elim _ _
  | succ m =>
    change frechetExtDerivK ω x (fun i => ((v i : FrechetVectorField 𝕜 A).toDerivation x)) =
      (ceExteriorDerivative (frechetVectorFieldDerivationLane 𝕜 A) (m + 1)
        (frechetFormToCEForm (m + 1) ω hω) v).toFun x
    have hpal := actionExteriorDerivative_palais
      (frechetVectorFieldDerivationLane 𝕜 A).toLieActionLane m
      (frechetFormToCEForm (m + 1) ω hω :
        ActionOperatorForm (frechetVectorFieldDerivationLane 𝕜 A).toLieActionLane (m + 1)) v
    change _ = (actionExteriorDerivative (frechetVectorFieldDerivationLane 𝕜 A).toLieActionLane
      (m + 1) (frechetFormToCEForm (m + 1) ω hω) v).toFun x
    rw [hpal]
    rw [frechetExtDerivK, extDeriv_apply_vectorField
      (hω.differentiable (by simp) x)
      (fun i => (v i).toDerivation.toContinuousLinearMap.differentiableAt)]
    change _ = (∑ i : Fin (m + 2), (-1 : 𝕜) ^ i.val •
        ((frechetVectorFieldDerivationLane 𝕜 A).toLieActionLane.operatorAction (v i)
          ((frechetFormToCEForm (m + 1) ω hω) (i.removeNth v)))).toFun x -
      (∑ i : Fin (m + 1), ∑ j ∈ Finset.Ici i, (-1 : 𝕜) ^ (i + j : ℕ) •
        (frechetFormToCEForm (m + 1) ω hω)
          (Matrix.vecCons ⁅v i.castSucc, v j.succ⁆ (j.removeNth (i.castSucc.removeNth v)))).toFun x
    simp only [SmoothOpMap.sum_apply, SmoothOpMap.smul_apply,
      DerivationLieLane.toLieActionLane_operatorAction]
    have hsm : ∀ (k : ℕ) (a : A), ((-1 : ℤ) ^ k) • a = ((-1 : 𝕜) ^ k) • a := fun k a => by
      rw [← Int.cast_smul_eq_zsmul 𝕜]
      simp
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [hsm]
      change (-1 : 𝕜) ^ i.val •
          fderiv 𝕜 (fun y => ω y (i.removeNth fun j => (v j : FrechetVectorField 𝕜 A).toDerivation y)) x
            ((v i : FrechetVectorField 𝕜 A).toDerivation x) =
        (-1 : 𝕜) ^ i.val •
          fderiv 𝕜 (fun y => ω y (fun k => (i.removeNth v k : FrechetVectorField 𝕜 A).toDerivation y)) x
            ((v i : FrechetVectorField 𝕜 A).toDerivation x)
      rfl
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _hj => ?_
      rw [hsm]
      congr 1
      let v' : Fin (m + 2) → FrechetVectorField 𝕜 A := v
      change ω x (Matrix.vecCons
          (VectorField.lieBracket 𝕜 ((v' i.castSucc).toDerivation : A → A)
            ((v' j.succ).toDerivation : A → A) x)
          (j.removeNth (i.castSucc.removeNth fun k => (v' k).toDerivation x))) =
        ω x (fun k => (Matrix.vecCons ⁅v' i.castSucc, v' j.succ⁆
          (j.removeNth (i.castSucc.removeNth v')) k).toDerivation x)
      congr 1
      ext k
      cases k using Fin.cases with
      | zero =>
        rw [← FrechetVectorField.lie_apply_eq_vectorField_lieBracket]
        rfl
      | succ p =>
        rfl

/-- Complex specialization (`𝕜 = ℂ`) of `frechetExtDerivK_linear_eq_ceExteriorDerivative`. -/
theorem frechetExtDeriv_linear_eq_ceExteriorDerivative
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    (n : ℕ) (ω : OperatorFrechetForm A A A n) (hω : ContDiff ℂ (⊤ : WithTop ℕ∞) ω) :
    frechetFormToCEForm (n + 1) (frechetExtDeriv ω) (contDiff_frechetExtDerivK hω) =
      ceExteriorDerivative (frechetVectorFieldDerivationLane ℂ A) n
        (frechetFormToCEForm n ω hω) :=
  frechetExtDerivK_linear_eq_ceExteriorDerivative n ω hω

/-- Explicit Lie-bracket sign relation: Mathlib's `VectorField.lieBracket` on linear
`FrechetOperatorDerivation`s equals minus `FrechetOperatorDerivation.commutator`. -/
theorem lieBracket_frechetOperatorDerivation
    {𝕜 A : Type*} [NontriviallyNormedField 𝕜]
    [NormedRing A] [NormedAlgebra 𝕜 A]
    (D E : FrechetOperatorDerivation 𝕜 A) (x : A) :
    VectorField.lieBracket 𝕜 (D : A → A) (E : A → A) x =
      -(FrechetOperatorDerivation.commutator D E x) := by
  change fderiv 𝕜 (E : A → A) x (D x) - fderiv 𝕜 (D : A → A) x (E x) = -(D (E x) - E (D x))
  rw [D.toContinuousLinearMap.fderiv, E.toContinuousLinearMap.fderiv]
  abel

/-- Pointwise (`DifferentiableAt` only, no `C^∞` required) Palais evaluation of
`frechetExtDeriv ω` on `FrechetOperatorDerivation`s with explicit commutator sign. -/
theorem frechetExtDeriv_apply_frechetDerivations
    {A M : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [NormedAddCommGroup M] [NormedSpace ℂ M] {n : ℕ}
    {ω : OperatorFrechetForm A A M (n + 1)} {x : A}
    (hω : DifferentiableAt ℂ ω x)
    (D : Fin (n + 2) → FrechetOperatorDerivation ℂ A) :
    frechetExtDeriv ω x (fun i => D i x) =
      (∑ i : Fin (n + 2), (-1) ^ i.val •
          fderiv ℂ (fun y => ω y (i.removeNth fun j => D j y)) x (D i x)) +
        ∑ i : Fin (n + 1), ∑ j ∈ Finset.Ici i,
          (-1) ^ (i + j : ℕ) •
            ω x (Matrix.vecCons (FrechetOperatorDerivation.commutator (D i.castSucc) (D j.succ) x)
              (j.removeNth (i.castSucc.removeNth fun k => D k x))) := by
  rw [frechetExtDeriv, frechetExtDerivK, extDeriv_apply_vectorField hω
    (fun i => (D i).toContinuousLinearMap.differentiableAt)]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [lieBracket_frechetOperatorDerivation, ← smul_neg]
  congr 1
  have hcons : Matrix.vecCons (-(FrechetOperatorDerivation.commutator (D i.castSucc) (D j.succ) x))
      (j.removeNth (i.castSucc.removeNth fun k => D k x)) =
      Function.update
        (Matrix.vecCons (FrechetOperatorDerivation.commutator (D i.castSucc) (D j.succ) x)
          (j.removeNth (i.castSucc.removeNth fun k => D k x)))
        0 (-(FrechetOperatorDerivation.commutator (D i.castSucc) (D j.succ) x)) := by
    ext k; cases k using Fin.cases <;> simp
  have hpos : Matrix.vecCons (FrechetOperatorDerivation.commutator (D i.castSucc) (D j.succ) x)
      (j.removeNth (i.castSucc.removeNth fun k => D k x)) =
      Function.update
        (Matrix.vecCons (FrechetOperatorDerivation.commutator (D i.castSucc) (D j.succ) x)
          (j.removeNth (i.castSucc.removeNth fun k => D k x)))
        0 (FrechetOperatorDerivation.commutator (D i.castSucc) (D j.succ) x) := by
    ext k; cases k using Fin.cases <;> simp
  have hneg :
      (ω x) (Function.update
        (Matrix.vecCons (FrechetOperatorDerivation.commutator (D i.castSucc) (D j.succ) x)
          (j.removeNth (i.castSucc.removeNth fun k => D k x)))
        0 (-(FrechetOperatorDerivation.commutator (D i.castSucc) (D j.succ) x))) =
      -((ω x) (Matrix.vecCons (FrechetOperatorDerivation.commutator (D i.castSucc) (D j.succ) x)
        (j.removeNth (i.castSucc.removeNth fun k => D k x)))) := by
    have hsm := (ω x).map_update_smul
      (Matrix.vecCons (FrechetOperatorDerivation.commutator (D i.castSucc) (D j.succ) x)
        (j.removeNth (i.castSucc.removeNth fun k => D k x)))
      0 (-1 : ℂ) (FrechetOperatorDerivation.commutator (D i.castSucc) (D j.succ) x)
    simp only [neg_one_smul] at hsm
    rw [hsm, ← hpos]
  rw [hcons, hneg, neg_neg]

/-- The coordinate 0-form `x ↦ x` on `A`. -/
def coordZeroForm (A : Type*) [NormedAddCommGroup A] [NormedSpace ℂ A] :
    OperatorFrechetForm A A A 0 :=
  fun x => ContinuousAlternatingMap.constOfIsEmpty ℂ A (Fin 0) x

/-- Degree-0 alignment directly with `FrechetOperatorDerivation.derivationLieLane`
(without opposite-bracket sign flip) on `coordZeroForm A`. -/
theorem frechetExtDeriv_coordZeroForm_eq_ceExteriorDerivative
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    (D : FrechetOperatorDerivation ℂ A) (x : A) :
    frechetExtDeriv (coordZeroForm A) x ![D x] =
      ceExteriorDerivative (FrechetOperatorDerivation.derivationLieLane ℂ A) 0
        (zeroFormAlternatingEquiv _ x) ![D] := by
  have hex : frechetExtDeriv (coordZeroForm A) x =
      ContinuousAlternatingMap.ofSubsingleton ℂ A A (0 : Fin 1) (fderiv ℂ id x) :=
    extDeriv_constOfIsEmpty id x
  rw [hex, ceExteriorDerivative_zero_eval_apply]
  change (fderiv ℂ id x) (D x) = _
  rw [fderiv_id, ContinuousLinearMap.id_apply]
  rfl

/-- Degree-0 alignment with `FrechetOperatorDerivation.derivationLieLane` for any
continuous linear operator `T : A →L[ℂ] A` commuting with `D`. -/
theorem frechetExtDeriv_clmZeroForm_eq_ceExteriorDerivative
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    (T : A →L[ℂ] A) (D : FrechetOperatorDerivation ℂ A) (x : A)
    (hTD : T (D x) = D (T x)) :
    frechetExtDeriv (fun y => ContinuousAlternatingMap.constOfIsEmpty ℂ A (Fin 0) (T y)) x ![D x] =
      ceExteriorDerivative (FrechetOperatorDerivation.derivationLieLane ℂ A) 0
        (zeroFormAlternatingEquiv _ (T x)) ![D] := by
  rw [frechetExtDeriv_constOfIsEmpty, ceExteriorDerivative_zero_eval_apply]
  change (fderiv ℂ T x) (D x) = D (T x)
  rw [T.fderiv]
  exact hTD

end CEAlignment

/-! ## Chart and `DeRhamBridge` alignment (`frechetExtDeriv_chart_eq_mathlib_extDeriv`) -/

section ChartAlignment

open InfoGeometry.Continuous.DeRhamBridge
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms

/-- Alignment linking real `frechetExtDerivReal` on `DeRhamBridge.Chart α`,
Mathlib's `extDeriv`, `DeRhamBridge.exactOneForm`, and
`DerivationExteriorCalculus.actionExteriorDerivative_zero_chart_eq_extDeriv`
on the positive-orthant logarithmic coordinate 0-form (`x i ≠ 0`, `BUCKET 2`). -/
theorem frechetExtDeriv_chart_eq_mathlib_extDeriv
    {α : Type*} [Fintype α] (i : α) {x : Chart α} (hx : x i ≠ 0) (v : Chart α) :
    frechetExtDerivReal
        (fun y => ContinuousAlternatingMap.constOfIsEmpty ℝ (Chart α) (Fin 0) (zeroForm i y))
        x ![v] =
      extDeriv
        (fun y => ContinuousAlternatingMap.constOfIsEmpty ℝ (Chart α) (Fin 0) (zeroForm i y))
        x ![v] ∧
    frechetExtDerivReal
        (fun y => ContinuousAlternatingMap.constOfIsEmpty ℝ (Chart α) (Fin 0) (zeroForm i y))
        x =
      ContinuousAlternatingMap.ofSubsingleton ℝ (Chart α) ℝ (0 : Fin 1) (exactOneForm i x) ∧
    frechetExtDerivReal
        (fun y => ContinuousAlternatingMap.constOfIsEmpty ℝ (Chart α) (Fin 0) (zeroForm i y))
        x ![v] =
      ((actionExteriorDerivative (chartDirectionalLieAction α x) 0
          (AlternatingMap.constLinearEquivOfIsEmpty
            ⟨zeroForm i, (zeroForm_hasFDerivAt i hx).differentiableAt⟩) ![v]).1 x) := by
  refine ⟨rfl, ?_, ?_⟩
  · change extDeriv
        (fun y => ContinuousAlternatingMap.constOfIsEmpty ℝ (Chart α) (Fin 0) (zeroForm i y)) x =
      ContinuousAlternatingMap.ofSubsingleton ℝ (Chart α) ℝ (0 : Fin 1) (exactOneForm i x)
    exact exactOneForm_eq_mathlib_extDeriv i hx
  · exact (actionExteriorDerivative_zero_chart_eq_extDeriv i hx v).symm

/-- Complex chart alignment for `OperatorFrechetForm (EuclideanSpace ℂ α) (EuclideanSpace ℂ α) ℂ 0`. -/
theorem frechetExtDeriv_complexChart_eq_mathlib_extDeriv
    {α : Type*} [Fintype α] (f : EuclideanSpace ℂ α → ℂ)
    {f' : EuclideanSpace ℂ α →L[ℂ] ℂ} {x : EuclideanSpace ℂ α}
    (hf : HasFDerivAt f f' x) :
    frechetExtDeriv
        (fun y => ContinuousAlternatingMap.constOfIsEmpty ℂ (EuclideanSpace ℂ α) (Fin 0) (f y))
        x =
      extDeriv
        (fun y => ContinuousAlternatingMap.constOfIsEmpty ℂ (EuclideanSpace ℂ α) (Fin 0) (f y))
        x ∧
    frechetExtDeriv
        (fun y => ContinuousAlternatingMap.constOfIsEmpty ℂ (EuclideanSpace ℂ α) (Fin 0) (f y))
        x =
      ContinuousAlternatingMap.ofSubsingleton ℂ (EuclideanSpace ℂ α) ℂ (0 : Fin 1) f' := by
  refine ⟨rfl, ?_⟩
  rw [frechetExtDeriv_constOfIsEmpty, hf.fderiv]

end ChartAlignment

/-! ## Nonlinear Banach exponential / Duhamel and finite Gibbs BKM Hessian alignment (`BUCKET 2`) -/

section NonlinearDuhamelAndBKMAlignment

open scoped Interval _root_.Topology
open SouriauOnsagerBKM
open InfoGeometry.OperatorAlgebra
open InfoGeometry.Canonical.NoncommutativeGibbsExpectationBridge
open InfoGeometry.Canonical.NoncommutativeGibbsTwoPointFrechetBridge
open InfoGeometry.Canonical.NoncommutativeGibbsDuhamelTwoPointBridge
open InfoGeometry.Canonical.NoncommutativeGibbsSecondDerivativeCenteredBridge
open InfoGeometry.Canonical.NoncommutativeGibbsCenteredBKMCovariance
open InfoGeometry.Canonical.NoncommutativeGibbsFaithfulNormalizationBridge
open InfoGeometry.Canonical.NoncommutativeGibbsCenteredFrechetBKMBridge
open InfoGeometry.Canonical.NoncommutativeGibbsBKMHessianBridge

/-- The Banach-algebra exponential 0-form `x ↦ exp(x)`. -/
def expFrechetZeroForm (A : Type*) [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] :
    OperatorFrechetForm A A A 0 :=
  fun x => ContinuousAlternatingMap.constOfIsEmpty ℂ A (Fin 0) (NormedSpace.exp x)

theorem frechetExtDeriv_expFrechetZeroForm
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] (a : A) :
    frechetExtDeriv (expFrechetZeroForm A) a =
      ContinuousAlternatingMap.ofSubsingleton ℂ A A (0 : Fin 1)
        (exponentialDerivative (𝕜 := ℂ) a) := by
  unfold expFrechetZeroForm
  rw [frechetExtDeriv_constOfIsEmpty,
    (hasFDerivAt_exp_noncommutative (𝕜 := ℂ) a).fderiv]

theorem frechetExtDeriv_expFrechetZeroForm_eq_duhamelDerivative
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] (a h : A) :
    let _ : NormedAlgebra ℝ A := NormedAlgebra.restrictScalars ℝ ℂ A
    frechetExtDeriv (expFrechetZeroForm A) a ![h] = duhamelDerivative a h := by
  let _ : NormedAlgebra ℝ A := NormedAlgebra.restrictScalars ℝ ℂ A
  rw [frechetExtDeriv_expFrechetZeroForm]
  change exponentialDerivative (𝕜 := ℂ) a h = duhamelDerivative a h
  have hc : HasFDerivAt (NormedSpace.exp : A → A)
      ((exponentialDerivative (𝕜 := ℂ) a).restrictScalars ℝ) a :=
    (hasFDerivAt_exp_noncommutative (𝕜 := ℂ) a).restrictScalars ℝ
  have hr : HasFDerivAt (NormedSpace.exp : A → A)
      (exponentialDerivative (𝕜 := ℝ) a) a :=
    hasFDerivAt_exp_noncommutative (𝕜 := ℝ) a
  have huniq : (exponentialDerivative (𝕜 := ℂ) a).restrictScalars ℝ =
      exponentialDerivative (𝕜 := ℝ) a :=
    hc.unique hr
  have happly : exponentialDerivative (𝕜 := ℂ) a h = exponentialDerivative (𝕜 := ℝ) a h :=
    congrArg (fun L : A →L[ℝ] A => L h) huniq
  rw [happly]
  exact exponentialDerivative_apply_eq_duhamelDerivative_of_continuousAt a h
    (continuous_duhamelDifferenceQuotient a h).continuousAt

theorem frechetExtDeriv_sq_expFrechetZeroForm
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] :
    frechetExtDeriv (frechetExtDeriv (expFrechetZeroForm A)) = 0 := by
  let _ : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℂ A
  have hexp : ContDiff ℂ (⊤ : WithTop ℕ∞) (NormedSpace.exp : A → A) :=
    contDiff_iff_contDiffAt.mpr fun x => (NormedSpace.exp_analytic x).contDiffAt
  have h0 : ContDiff ℂ (⊤ : WithTop ℕ∞) (expFrechetZeroForm A) :=
    (ContinuousAlternatingMap.constOfIsEmptyLIE ℂ A A (Fin 0)).toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp hexp
  exact frechetExtDeriv_frechetExtDeriv h0 le_top

/-- Principal-branch finite Gibbs log-partition 0-form on `FiniteOperatorAlgebra n`. -/
def logPartitionZeroForm (n : ℕ) :
    OperatorFrechetForm (FiniteOperatorAlgebra n) (FiniteOperatorAlgebra n) ℂ 0 :=
  fun H => ContinuousAlternatingMap.constOfIsEmpty ℂ (FiniteOperatorAlgebra n) (Fin 0)
    (logTracedExponential H)

/-- Finite Gibbs log-partition expectation 1-form on `FiniteOperatorAlgebra n`. -/
def logPartitionOneForm (n : ℕ) :
    OperatorFrechetForm (FiniteOperatorAlgebra n) (FiniteOperatorAlgebra n) ℂ 1 :=
  fun H => ContinuousAlternatingMap.ofSubsingleton ℂ (FiniteOperatorAlgebra n) ℂ (0 : Fin 1)
    (logTracedExponentialDerivative H)

theorem frechetExtDeriv_logPartitionZeroForm
    {n : ℕ} (H : FiniteOperatorAlgebra n)
    (hSlit : tracedExponential H ∈ Complex.slitPlane) :
    frechetExtDeriv (logPartitionZeroForm n) H = logPartitionOneForm n H ∧
      ∀ A : FiniteOperatorAlgebra n, frechetExtDeriv (logPartitionZeroForm n) H ![A] =
        operatorExpectation H A := by
  have h1 : frechetExtDeriv (logPartitionZeroForm n) H = logPartitionOneForm n H := by
    unfold logPartitionZeroForm logPartitionOneForm
    rw [frechetExtDeriv_constOfIsEmpty, fderiv_logTracedExponential H hSlit]
  refine ⟨h1, ?_⟩
  intro A
  rw [h1]
  exact logTracedExponentialDerivative_apply_eq_expectation H A

theorem frechetExtDeriv_twoPointNumerator
    {n : ℕ} (H A B : FiniteOperatorAlgebra n) :
    frechetExtDeriv
        (fun X => ContinuousAlternatingMap.constOfIsEmpty ℂ (FiniteOperatorAlgebra n) (Fin 0)
          (twoPointNumerator B X)) H ![A] =
      ∫ s in (0 : ℝ)..1,
        finiteOperatorTrace
          (NormedSpace.exp ((1 - s) • H) * A * NormedSpace.exp (s • H) * B) := by
  rw [frechetExtDeriv_constOfIsEmpty, (hasFDerivAt_twoPointNumerator H B).fderiv]
  change twoPointNumeratorDerivative H B A = _
  rw [twoPointNumeratorDerivative_apply,
    NoncommutativeGibbsDuhamelTwoPointBridge.exponentialDerivative_complex_apply_eq_real H A]
  exact trace_exponentialDerivative_mul_eq_duhamelTwoPoint H A B

theorem frechetExtDeriv_logPartitionOneForm_eq_zero
    {n : ℕ} (H : FiniteOperatorAlgebra n)
    (hSlit : tracedExponential H ∈ Complex.slitPlane) :
    frechetExtDeriv (logPartitionOneForm n) H = 0 := by
  have : CompleteSpace (FiniteOperatorAlgebra n) := FiniteDimensional.complete ℂ _
  let _ : NormedAlgebra ℚ (FiniteOperatorAlgebra n) :=
    NormedAlgebra.restrictScalars ℚ ℂ (FiniteOperatorAlgebra n)
  have hZ_analytic : ∀ X : FiniteOperatorAlgebra n, AnalyticAt ℂ (tracedExponential (n := n)) X :=
    fun X => ((finiteOperatorTraceCLM n).analyticAt (NormedSpace.exp X)).comp
      (NormedSpace.exp_analytic X)
  have hZ_cont : Continuous (tracedExponential (n := n)) :=
    continuous_iff_continuousAt.mpr fun X => (hZ_analytic X).continuousAt
  have hLog : AnalyticAt ℂ (logTracedExponential (n := n)) H :=
    (hZ_analytic H).clog hSlit
  have hSmooth : ContDiffAt ℂ (⊤ : WithTop ℕ∞) (logPartitionZeroForm n) H :=
    (ContinuousAlternatingMap.constOfIsEmptyLIE ℂ (FiniteOperatorAlgebra n) ℂ (Fin 0)).toContinuousLinearEquiv.toContinuousLinearMap.contDiff.contDiffAt.comp H
      hLog.contDiffAt
  have hOpen : IsOpen { X : FiniteOperatorAlgebra n | tracedExponential X ∈ Complex.slitPlane } :=
    Complex.isOpen_slitPlane.preimage hZ_cont
  have hEv : frechetExtDeriv (logPartitionZeroForm n) =ᶠ[𝓝 H] logPartitionOneForm n := by
    filter_upwards [hOpen.mem_nhds hSlit] with X hX
    exact (frechetExtDeriv_logPartitionZeroForm X hX).1
  rw [frechetExtDeriv, frechetExtDerivK, ← hEv.extDeriv_eq]
  exact frechetExtDeriv_frechetExtDeriv_apply hSmooth le_top

/-- Maxwell / Schwarz symmetry of the finite Gibbs BKM Hessian readout
derived directly from `d_Fr² (log Z) = 0` (`frechetExtDeriv (logPartitionOneForm n) H = 0`). -/
theorem secondFDerivLogPartitionReadout_symm_of_extDeriv_sq_zero
    {n : ℕ} (H A B : FiniteOperatorAlgebra n)
    (hSlit : tracedExponential H ∈ Complex.slitPlane) :
    secondFDerivLogPartitionReadout H A B = secondFDerivLogPartitionReadout H B A := by
  have : CompleteSpace (FiniteOperatorAlgebra n) := FiniteDimensional.complete ℂ _
  let _ : NormedAlgebra ℚ (FiniteOperatorAlgebra n) :=
    NormedAlgebra.restrictScalars ℚ ℂ (FiniteOperatorAlgebra n)
  have hZ_analytic : ∀ X : FiniteOperatorAlgebra n, AnalyticAt ℂ (tracedExponential (n := n)) X :=
    fun X => ((finiteOperatorTraceCLM n).analyticAt (NormedSpace.exp X)).comp
      (NormedSpace.exp_analytic X)
  have hZ_cont : Continuous (tracedExponential (n := n)) :=
    continuous_iff_continuousAt.mpr fun X => (hZ_analytic X).continuousAt
  have hLog : AnalyticAt ℂ (logTracedExponential (n := n)) H :=
    (hZ_analytic H).clog hSlit
  have hOpen : IsOpen { X : FiniteOperatorAlgebra n | tracedExponential X ∈ Complex.slitPlane } :=
    Complex.isOpen_slitPlane.preimage hZ_cont
  have hFDerivEv : logTracedExponentialDerivative =ᶠ[𝓝 H]
      fderiv ℂ (logTracedExponential (n := n)) := by
    filter_upwards [hOpen.mem_nhds hSlit] with X hX
    exact (fderiv_logTracedExponential X hX).symm
  have hfderivDiff : DifferentiableAt ℂ (fderiv ℂ (logTracedExponential (n := n))) H :=
    (hLog.contDiffAt.fderiv_right (m := (1 : WithTop ℕ∞)) le_top).differentiableAt one_ne_zero
  have hLogDerivDiff : DifferentiableAt ℂ (logTracedExponentialDerivative (n := n)) H :=
    hfderivDiff.congr_of_eventuallyEq hFDerivEv
  have hFormDiff : DifferentiableAt ℂ (logPartitionOneForm n) H := by
    have hOfSub : logPartitionOneForm n = fun X =>
        (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℂ) (E := FiniteOperatorAlgebra n)
          (F := ℂ) (0 : Fin 1)).toContinuousLinearEquiv.toContinuousLinearMap
          (logTracedExponentialDerivative X) := rfl
    rw [hOfSub]
    exact (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℂ) (E := FiniteOperatorAlgebra n)
      (F := ℂ) (0 : Fin 1)).toContinuousLinearEquiv.toContinuousLinearMap.differentiableAt.comp
      H hLogDerivDiff
  have hEvalDiff : ∀ V : FiniteOperatorAlgebra n,
      DifferentiableAt ℂ (fun X : FiniteOperatorAlgebra n => logTracedExponentialDerivative X V) H :=
    fun V => hLogDerivDiff.clm_apply (differentiableAt_const V)
  have hLine : ∀ U V : FiniteOperatorAlgebra n,
      secondFDerivLogPartitionReadout H U V =
        fderiv ℂ (fun X => logTracedExponentialDerivative X V) H U := fun U V => by
    have hAff : HasDerivAt (fun z : ℂ => H + z • U) U 0 := by
      have h1 := (hasDerivAt_const (0 : ℂ) H).add ((hasDerivAt_id (0 : ℂ)).smul_const U)
      rw [zero_add, one_smul] at h1
      exact h1
    have hComp := (hEvalDiff V).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hAff
      (by rw [zero_smul ℂ U, add_zero])
    have hEq : ((fun X => logTracedExponentialDerivative X V) ∘ fun z : ℂ => H + z • U) =
        logPartitionGradientLine H U V := by
      funext z
      exact (logPartitionGradientLine_eq_logTracedExponentialDerivative H U V z).symm
    rw [hEq] at hComp
    exact hComp.deriv
  have hExt : frechetExtDeriv (logPartitionOneForm n) H ![A, B] =
      fderiv ℂ (fun X => logTracedExponentialDerivative X B) H A -
        fderiv ℂ (fun X => logTracedExponentialDerivative X A) H B := by
    rw [frechetExtDeriv_apply hFormDiff]
    rw [Fin.sum_univ_two]
    have h0 : (0 : Fin 2).removeNth ![A, B] = ![B] := by
      ext i; fin_cases i; rfl
    have h1 : (1 : Fin 2).removeNth ![A, B] = ![A] := by
      ext i; fin_cases i; rfl
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul,
      h0, h1, Matrix.cons_val_zero, Matrix.cons_val_one]
    change fderiv ℂ (fun X => logTracedExponentialDerivative X B) H A +
        -(fderiv ℂ (fun X => logTracedExponentialDerivative X A) H B) = _
    rw [sub_eq_add_neg]
  have hZero : frechetExtDeriv (logPartitionOneForm n) H ![A, B] = 0 := by
    rw [frechetExtDeriv_logPartitionOneForm_eq_zero H hSlit]; rfl
  rw [hLine A B, hLine B A]
  exact sub_eq_zero.mp (hExt.symm.trans hZero)

/-- Full BKM Hessian / Second-Law / Maxwell symmetry alignment for the finite Gibbs
log-partition forms (`BUCKET 2`). -/
theorem frechetExtDeriv_logPartition_bkmHessian_alignment
    {n : ℕ} (H : FiniteOperatorAlgebra n) (hH : IsSelfAdjoint H)
    (hZ : 0 < gibbsPartitionReal H)
    (A B : FiniteOperatorAlgebra n) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    frechetExtDeriv (logPartitionOneForm n) H ![A, B] = 0 ∧
      (secondFDerivLogPartitionReadout H A B).re =
        centeredBKMRealCovariance
          (faithfulGibbsDensity H hH hZ)
          (continuous_faithfulGibbsDensity_rpow H hH hZ) A B ∧
      centeredBKMRealCovariance
          (faithfulGibbsDensity H hH hZ)
          (continuous_faithfulGibbsDensity_rpow H hH hZ) A B =
        centeredBKMRealCovariance
          (faithfulGibbsDensity H hH hZ)
          (continuous_faithfulGibbsDensity_rpow H hH hZ) B A := by
  have hSlit : tracedExponential H ∈ Complex.slitPlane := by
    rw [tracedExponential_eq_gibbsPartitionReal H hH]
    exact Complex.ofReal_mem_slitPlane.mpr hZ
  refine ⟨?_, ?_, ?_⟩
  · rw [frechetExtDeriv_logPartitionOneForm_eq_zero H hSlit]; rfl
  · exact secondFDeriv_logPartition_apply_eq_centeredBKM H hH hZ A B hA
  · rw [← secondFDeriv_logPartition_apply_eq_centeredBKM H hH hZ A B hA,
      ← secondFDeriv_logPartition_apply_eq_centeredBKM H hH hZ B A hB,
      secondFDerivLogPartitionReadout_symm_of_extDeriv_sq_zero H A B hSlit]

end NonlinearDuhamelAndBKMAlignment

/-! ## Typed disambiguation: `OperatorFrechetJet` vs `OperatorFrechetForm` vs `OneFormTuple` / `NOperatorForm` -/

section Disambiguation

open InfoGeometry.Optics.OperatorDerivationForms

/-- Embed an alternating `OperatorFrechetForm A A M n` into symmetric/multilinear
`OperatorFrechetJet A M n` by forgetting alternation. -/
def operatorFrechetFormToJet
    {A M : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup M] [NormedSpace ℂ M] (n : ℕ)
    (ω : OperatorFrechetForm A A M n) : OperatorFrechetJet A M n :=
  fun x => (ω x).toContinuousMultilinearMap

@[simp]
theorem operatorFrechetFormToJet_apply
    {A M : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup M] [NormedSpace ℂ M] (n : ℕ)
    (ω : OperatorFrechetForm A A M n) (x : A) (v : Fin n → A) :
    operatorFrechetFormToJet n ω x v = ω x v :=
  rfl

/-- Every alternating `OperatorFrechetForm` vanishes whenever two arguments coincide. -/
theorem operatorFrechetForm_diag_zero
    {A T M : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup T] [NormedSpace ℂ T]
    [NormedAddCommGroup M] [NormedSpace ℂ M] {n : ℕ}
    (ω : OperatorFrechetForm A T M n) (x : A) {v : Fin n → T}
    {i j : Fin n} (hv : v i = v j) (hij : i ≠ j) :
    ω x v = 0 :=
  (ω x).map_eq_zero_of_eq v hv hij

/-- In degree `2`, `operatorFrechetJet 2 f x` of a `C^2` map is symmetric,
in contrast to alternating `OperatorFrechetForm`. -/
theorem operatorFrechetJet_two_symm
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {r : WithTop ℕ∞} {f : E → F} {x : E}
    (hf : ContDiffAt ℂ r f x) (hr : minSmoothness ℂ 2 ≤ r) (u v : E) :
    operatorFrechetJet 2 f x ![u, v] = operatorFrechetJet 2 f x ![v, u] := by
  have hsymm := hf.isSymmSndFDerivAt hr
  simp only [operatorFrechetJet, iteratedFDeriv_two_apply]
  exact hsymm u v

/-- Non-vacuity witness separating `OperatorFrechetJet 2` from `OperatorFrechetForm _ _ _ 2`:
for `f(z) = z * z` on `ℂ`, `operatorFrechetJet 2 f 0 ![1, 1] = 2 ≠ 0`, whereas every
alternating `OperatorFrechetForm ℂ ℂ ℂ 2` vanishes on `![1, 1]`. -/
theorem operatorFrechetJet_two_diag_nonzero_witness :
    ∃ f : ℂ → ℂ, operatorFrechetJet 2 f 0 (![1, 1] : Fin 2 → ℂ) ≠ 0 ∧
      ∀ ω : OperatorFrechetForm ℂ ℂ ℂ 2, ω 0 (![1, 1] : Fin 2 → ℂ) = 0 := by
  refine ⟨fun z : ℂ => z * z, ?_,
    fun ω => operatorFrechetForm_diag_zero ω 0 (i := (0 : Fin 2)) (j := (1 : Fin 2)) rfl (by decide)⟩
  have h1 : ∀ z : ℂ, fderiv ℂ (fun w : ℂ => w * w) z = ((2 : ℂ) * z) • ContinuousLinearMap.id ℂ ℂ := by
    intro z
    have hd : HasFDerivAt (fun w : ℂ => w * w) (((2 : ℂ) * z) • ContinuousLinearMap.id ℂ ℂ) z := by
      have hid := hasFDerivAt_id (𝕜 := ℂ) z
      have hm := hid.mul hid
      have hfun : (id * id : ℂ → ℂ) = fun w : ℂ => w * w := rfl
      have hidz : id z = z := rfl
      have hder : z • ContinuousLinearMap.id ℂ ℂ + z • ContinuousLinearMap.id ℂ ℂ =
          ((2 : ℂ) * z) • ContinuousLinearMap.id ℂ ℂ := by
        ext
        simp [two_mul]
      rw [hfun, hidz, hder] at hm
      exact hm
    exact hd.fderiv
  have h2 : fderiv ℂ (fun z : ℂ => fderiv ℂ (fun w : ℂ => w * w) z) 0 1 =
      (2 : ℂ) • ContinuousLinearMap.id ℂ ℂ := by
    have hfun : (fun z : ℂ => fderiv ℂ (fun w : ℂ => w * w) z) =
        fun z : ℂ => ((2 : ℂ) * z) • ContinuousLinearMap.id ℂ ℂ := funext h1
    rw [hfun]
    have hd : HasFDerivAt (fun z : ℂ => ((2 : ℂ) * z) • ContinuousLinearMap.id ℂ ℂ)
        (((2 : ℂ) • ContinuousLinearMap.id ℂ ℂ).smulRight (ContinuousLinearMap.id ℂ ℂ)) 0 := by
      have hid : HasFDerivAt (fun z : ℂ => (2 : ℂ) * z) ((2 : ℂ) • ContinuousLinearMap.id ℂ ℂ) 0 := by
        simpa using (hasFDerivAt_id (𝕜 := ℂ) 0).const_mul (2 : ℂ)
      exact hid.smul_const (ContinuousLinearMap.id ℂ ℂ)
    rw [hd.fderiv]
    simp
  simp only [operatorFrechetJet, iteratedFDeriv_two_apply, h2, Matrix.cons_val_zero,
    Matrix.cons_val_one, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, mul_one]
  norm_num

/-- Only in degree `n = 1` do `operatorFrechetJet 1 f` and `frechetExtDeriv` of the
0-form `f` agree. -/
theorem operatorFrechetJet_one_eq_frechetExtDeriv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (f : E → F) (x v : E) :
    operatorFrechetJet 1 f x ![v] =
      frechetExtDeriv (fun y => ContinuousAlternatingMap.constOfIsEmpty ℂ E (Fin 0) (f y)) x ![v] := by
  rw [operatorFrechetJet, iteratedFDeriv_one_apply, frechetExtDeriv_constOfIsEmpty]
  rfl

/-- Convert a degree-1 `OperatorFrechetForm A T M 1` into a length-1 `OneFormTuple A T M 1`. -/
def operatorFrechetFormOneToOneFormTuple
    {A T M : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup T] [NormedSpace ℂ T]
    [NormedAddCommGroup M] [NormedSpace ℂ M]
    (ω : OperatorFrechetForm A T M 1) : OneFormTuple A T M 1 :=
  fun _ x v => ω x (fun _ => v)

/-- Curry an `n`-form `OperatorFrechetForm A T M n` at a frame `v : Fin n → T` into an
`OneFormTuple A T M n` (`NOperatorForm n`) by varying each slot individually. -/
def operatorFrechetFormToOneFormTuple
    {A T M : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup T] [NormedSpace ℂ T]
    [NormedAddCommGroup M] [NormedSpace ℂ M] {n : ℕ}
    (ω : OperatorFrechetForm A T M n) (v : Fin n → T) : OneFormTuple A T M n :=
  fun i x t => ω x (Function.update v i t)

/-- Contrast witness separating `NOperatorForm 2` (`OneFormTuple _ _ _ 2`) from
`RealOperatorFrechetForm ℝ ℝ ℝ 2`: linear `NOperatorForm 2` has nonzero diagonal
values, whereas every alternating `RealOperatorFrechetForm ℝ ℝ ℝ 2` vanishes on `![1, 1]`. -/
theorem nOperatorForm_vs_realOperatorFrechetForm_witness :
    (∃ ω : NOperatorForm (Point := Unit) (Tangent := ℝ) (Value := ℝ) 2,
      (∀ i p, IsLinearMap ℝ (ω i p)) ∧ ω 0 () (1 : ℝ) ≠ 0 ∧ ω 1 () (1 : ℝ) ≠ 0) ∧
    (∀ ω : RealOperatorFrechetForm ℝ ℝ ℝ 2, ω 0 (![1, 1] : Fin 2 → ℝ) = 0) :=
  ⟨nOperatorForm_two_linear_diag_nonzero_witness,
    fun ω => (ω 0).map_eq_zero_of_eq (![1, 1] : Fin 2 → ℝ) (i := (0 : Fin 2)) (j := (1 : Fin 2))
      rfl (by decide)⟩

/-- Complex contrast witness separating `NOperatorForm (Point := ℂ) (Tangent := ℂ) (Value := ℂ) 2`
from `OperatorFrechetForm ℂ ℂ ℂ 2`. -/
theorem nOperatorForm_vs_operatorFrechetForm_witness :
    (∃ ω : NOperatorForm (Point := ℂ) (Tangent := ℂ) (Value := ℂ) 2,
      (∀ i p, IsLinearMap ℂ (ω i p)) ∧ ω 0 0 (1 : ℂ) ≠ 0 ∧ ω 1 0 (1 : ℂ) ≠ 0) ∧
    (∀ ω : OperatorFrechetForm ℂ ℂ ℂ 2, ω 0 (![1, 1] : Fin 2 → ℂ) = 0) :=
  ⟨⟨fun _ _ z => z, fun _ _ => ⟨fun _ _ => rfl, fun _ _ => rfl⟩, one_ne_zero, one_ne_zero⟩,
    fun ω => operatorFrechetForm_diag_zero ω 0 (i := (0 : Fin 2)) (j := (1 : Fin 2)) rfl (by decide)⟩

end Disambiguation

end InfoGeometry.Canonical.OperatorFrechetForms

end noncomputable section
