import InfoGeometry.Algebra.FibonacciGrothendieckRing
import InfoGeometry.Canonical.FibonacciGrothendieckLimit

/-!
# InfoGeometry.Canonical.FibonacciGrothendieckLimitBridge

Canonical bridge for the staged Fibonacci Grothendieck / direct-limit lane.

This file only re-exports the finite-stage tensor map, the stationary colimit
readbacks, and the compatible operator lift already proved in the owner file.
It does not add a new Bratteli-diagram theory or a new anyon category.
-/

noncomputable section

namespace FibonacciGrothendieckLimitBridge

open InfoGeometry.Canonical.FibonacciGrothendieckLimit
open InfoGeometry.Algebra.FibonacciGrothendieckRing
open Filter

universe u

variable {𝕜 V : Type u} [Field 𝕜] [CharZero 𝕜]
variable [AddCommGroup V] [Module 𝕜 V]

abbrev fibFusionClass := InfoGeometry.Canonical.FibonacciGrothendieckLimit.fibFusionClass
abbrev fibFusionGrothendieckColimit :=
  InfoGeometry.Canonical.FibonacciGrothendieckLimit.fibFusionGrothendieckColimit

theorem fibFusionOf_tensorTau (n : Nat) (x : fibFusionClass) :
    fibFusionOf (n + 1) (fibFusionTensorTau x) = fibFusionOf n x :=
  InfoGeometry.Canonical.FibonacciGrothendieckLimit.fibFusionOf_tensorTau n x

theorem fibFusionVector_step (n : Nat) :
    fibFusionTensorTau (fibFusionVector n) = fibFusionVector (n + 1) :=
  InfoGeometry.Canonical.FibonacciGrothendieckLimit.fibFusionVector_step n

/-- The staged colimit tensor-by-`τ` map is the algebra owner tensor-by-`τ` map. -/
theorem fibFusionTensorTau_eq_tensorTauRaw :
    fibFusionTensorTau = InfoGeometry.Algebra.FibonacciGrothendieckRing.tensorTauRaw := by
  ext x <;> rfl

/-- In the `ℤ²` Fibonacci fusion-ring model, the staged tensor map is multiplication by `τ`. -/
theorem fibFusionTensorTau_model_mul_tau (x : fibFusionClass) :
    rawToModel (fibFusionTensorTau x) =
      FibonacciRingModel.mul (rawToModel x) FibonacciRingModel.tau := by
  simpa [fibFusionTensorTau_eq_tensorTauRaw] using rawToModel_tensorTau x

theorem fibFusionOf_vector_eq_initial (n : Nat) :
    fibFusionOf n (fibFusionVector n) = fibFusionOf 0 (fibFusionVector 0) :=
  InfoGeometry.Canonical.FibonacciGrothendieckLimit.fibFusionOf_vector_eq_initial n

omit [CharZero 𝕜] in
theorem fibFusionLZeroReadout_tensorTau
    (L : V →ₗ[𝕜] V) (n : Nat) (x : fibFusionClass) :
    fibFusionLZeroReadout L (n + 1) (fibFusionTensorTau x) =
      fibFusionLZeroReadout L n x :=
  InfoGeometry.Canonical.FibonacciGrothendieckLimit.fibFusionLZeroReadout_tensorTau L n x

omit [CharZero 𝕜] in
theorem fibFusionLZeroReadout_tensorMap
    (L : V →ₗ[𝕜] V) (m n : Nat) (h : m ≤ n) (x : fibFusionClass) :
    fibFusionLZeroReadout L n (fibFusionTensorMap m n h x) =
      fibFusionLZeroReadout L m x :=
  InfoGeometry.Canonical.FibonacciGrothendieckLimit.fibFusionLZeroReadout_tensorMap L m n h x

omit [CharZero 𝕜] in
theorem fibFusionGrothendieck_lzero_lift_of_vector
    (L : V →ₗ[𝕜] V) (n : Nat) :
    InfoGeometry.Canonical.FibonacciGrothendieckLimit.fibFusionLZeroLift (V := V) (𝕜 := 𝕜) L
        (fibFusionOf n (fibFusionVector n)) = L :=
  InfoGeometry.Canonical.FibonacciGrothendieckLimit.fibFusionGrothendieck_lzero_lift_of_vector
    (V := V) (𝕜 := 𝕜) L n

theorem fibFusionGrothendieck_lzero_lift_eq_sugawara_lzero
    (heiOper : Int → V →ₗ[𝕜] V)
    (heiTrunc : ∀ v, atTop.Eventually (fun l : Int => heiOper l v = 0))
    (heiComm : ∀ k l,
      (heiOper k).commutator (heiOper l) =
        if k + l = 0 then (k : 𝕜) • (1 : V →ₗ[𝕜] V) else 0)
    (n : Nat) :
    InfoGeometry.Canonical.FibonacciGrothendieckLimit.fibFusionLZeroLift (V := V) (𝕜 := 𝕜)
        (VirasoroProject.sugawaraGen (heiOper := heiOper) heiTrunc 0)
        (fibFusionOf n (fibFusionVector n)) =
      VirasoroProject.sugawaraRepresentation (heiOper := heiOper) heiTrunc heiComm
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 0) :=
  InfoGeometry.Canonical.FibonacciGrothendieckLimit.fibFusionGrothendieck_lzero_lift_eq_sugawara_lzero
    (V := V) (𝕜 := 𝕜) heiOper heiTrunc heiComm n

theorem fibFusionGrothendieck_lzero_lift_eq_chargedFock_sugawara_lzero
    (α : 𝕜) (n : Nat) :
    InfoGeometry.Canonical.FibonacciGrothendieckLimit.fibFusionLZeroLift
        (V := VirasoroProject.ChargedFockSpace 𝕜 α) (𝕜 := 𝕜)
        (VirasoroProject.ChargedFockSpace.sugawaraRepresentation 𝕜 α
          (VirasoroProject.VirasoroAlgebra.lgen 𝕜 0))
        (fibFusionOf n (fibFusionVector n)) =
      VirasoroProject.ChargedFockSpace.sugawaraRepresentation 𝕜 α
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 0) :=
  InfoGeometry.Canonical.FibonacciGrothendieckLimit.fibFusionGrothendieck_lzero_lift_eq_chargedFock_sugawara_lzero
    (𝕜 := 𝕜) α n

end FibonacciGrothendieckLimitBridge
