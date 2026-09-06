import InfoGeometry.Projective.WeylLogScaleBridge
import InfoGeometry.Projective.HadjiivanovKleinMonodromyBridge
import InfoGeometry.Projective.KleinHadjiivanovPeriodMonodromyBridge

/-!
# Weyl logarithms and square-zero monodromy

The complex logarithmic coordinate carries two independent finite readouts:

* `complexifiedWeylScale κ` is the semisimple multiplicative factor;
* `unipotentPeriodMap p` is the square-zero Jordan/shear factor.

This owner packages their product law without identifying a positive real Weyl
connection form with a winding period.  The latter remains the responsibility
of the logarithmic period owners.
-/

namespace InfoGeometry.Projective.WeylLogMonodromyPair

noncomputable section

open Matrix
open InfoGeometry.Projective.WeylLogScaleBridge
open InfoGeometry.Projective.HadjiivanovKleinMonodromyBridge
open InfoGeometry.Projective.KleinQuadric.DeRhamComplex
open InfoGeometry.Projective.KleinHadjiivanovPeriodMonodromyBridge
open InfoGeometry.Projective.KleinQuadric.DeRhamComplex

structure TransportPair where
  scale : ℂ
  shear : Matrix (Fin 2) (Fin 2) ℂ

@[ext] theorem TransportPair.ext {x y : TransportPair}
    (hscale : x.scale = y.scale) (hshear : x.shear = y.shear) : x = y := by
  cases x
  cases y
  simp_all

def pairMul (x y : TransportPair) : TransportPair :=
  ⟨x.scale * y.scale, x.shear * y.shear⟩

def pairTransport (κ p : ℂ) : TransportPair :=
  ⟨complexifiedWeylScale κ, unipotentPeriodMap p⟩

theorem pairTransport_add (κ₁ κ₂ p q : ℂ) :
    pairTransport (κ₁ + κ₂) (p + q) =
      pairMul (pairTransport κ₁ p) (pairTransport κ₂ q) := by
  change
    (⟨complexifiedWeylScale (κ₁ + κ₂), unipotentPeriodMap (p + q)⟩ :
      TransportPair) =
      ⟨complexifiedWeylScale κ₁ * complexifiedWeylScale κ₂,
        unipotentPeriodMap p * unipotentPeriodMap q⟩
  rw [complexifiedWeylScale_add, unipotentPeriodMap_add]

theorem pairTransport_zero :
    pairTransport 0 0 =
      ⟨1, (1 : Matrix (Fin 2) (Fin 2) ℂ)⟩ := by
  change
    (⟨complexifiedWeylScale 0, unipotentPeriodMap 0⟩ : TransportPair) =
      ⟨1, (1 : Matrix (Fin 2) (Fin 2) ℂ)⟩
  rw [unipotentPeriodMap_zero]
  simp [complexifiedWeylScale]

/-- Negating both logarithmic coordinates gives the exact inverse transport pair. -/
theorem pairTransport_neg_mul (κ p : ℂ) :
    pairMul (pairTransport (-κ) (-p)) (pairTransport κ p) =
      pairTransport 0 0 := by
  apply TransportPair.ext
  · change complexifiedWeylScale (-κ) * complexifiedWeylScale κ =
      complexifiedWeylScale 0
    rw [← complexifiedWeylScale_add]
    simp [complexifiedWeylScale]
  · change unipotentPeriodMap (-p) * unipotentPeriodMap p =
      unipotentPeriodMap 0
    rw [unipotentPeriodMap_neg_mul, unipotentPeriodMap_zero]

/-- The inverse transport identity is independent of multiplication order. -/
theorem pairTransport_mul_neg (κ p : ℂ) :
    pairMul (pairTransport κ p) (pairTransport (-κ) (-p)) =
      pairTransport 0 0 := by
  apply TransportPair.ext
  · change complexifiedWeylScale κ * complexifiedWeylScale (-κ) =
      complexifiedWeylScale 0
    rw [← complexifiedWeylScale_add]
    simp [complexifiedWeylScale]
  · change unipotentPeriodMap p * unipotentPeriodMap (-p) =
      unipotentPeriodMap 0
    rw [unipotentPeriodMap_mul_neg, unipotentPeriodMap_zero]

theorem pairTransport_period_class_zero
    {Ω₀ Ω₁ Ω₂ : Type*}
    [AddCommGroup Ω₀] [Module ℂ Ω₀]
    [AddCommGroup Ω₁] [Module ℂ Ω₁]
    [AddCommGroup Ω₂] [Module ℂ Ω₂]
    (d₀ : Ω₀ →ₗ[ℂ] Ω₁) (d₁ : Ω₁ →ₗ[ℂ] Ω₂)
    (hdd : d₁.comp d₀ = 0) (period : Ω₁ →ₗ[ℂ] ℂ)
    (hperiod : ∀ η : Ω₀, period (d₀ η) = 0)
    (c : InfoGeometry.Projective.KleinQuadric.DeRhamComplex.cohomologyModule
      d₀ d₁ hdd)
    (hc : c = 0) :
    pairTransport 0
        (periodClassFactor d₀ d₁ hdd period hperiod c) =
      ⟨1, (1 : Matrix (Fin 2) (Fin 2) ℂ)⟩ := by
  subst c
  rw [pairTransport]
  rw [map_zero, unipotentPeriodMap_zero]
  simp [complexifiedWeylScale]

end
end InfoGeometry.Projective.WeylLogMonodromyPair
