import Mathlib

/-!
# Fréchet jets, alternating operator forms, and exchange parity

This is the generic analytic layer below the existing chiral-Hodge owners.
Fréchet jets and alternating forms are different carriers.  The exchange
involution is therefore explicit data; no Hodge adjoint is identified with an
opposite-algebra differential without a compatibility property.
-/

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

end InfoGeometry.Canonical.OperatorFrechetForms
