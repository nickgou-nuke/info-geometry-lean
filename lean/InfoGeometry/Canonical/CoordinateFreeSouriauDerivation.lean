import Mathlib

/-!
# InfoGeometry.Canonical.CoordinateFreeSouriauDerivation

Coordinate-free Souriau/Tomita geometric lane:

* `β` is treated as an abstract derivation/generator direction,
* equilibrium is encoded as Lie-derivative invariance of the metric form,
* out-of-equilibrium Weyl/RG deformation is encoded as
  `L_β g = σ · g` (conformal anomaly profile).

No coordinates, no indices.
-/

namespace InfoGeometry.Canonical.CoordinateFreeSouriauDerivation

section

variable {M : Type*}
variable (Tangent : M → Type*)

/-- Coordinate-free metric packet on tangent fibers. -/
structure CoordinateFreeMetric where
  g : ∀ p : M, Tangent p → Tangent p → ℝ

/--
Abstract Lie-derivative readout of the metric along a distinguished generator
`β`, represented through a bracket action on test directions.
-/
def metricLieDerivative
    (g : CoordinateFreeMetric (Tangent := Tangent))
    (bracket : ∀ p : M, Tangent p → Tangent p → Tangent p)
    (β : ∀ p : M, Tangent p)
    (p : M) (X Y : Tangent p) : ℝ :=
  -(g.g p (bracket p (β p) X) Y) - (g.g p X (bracket p (β p) Y))

/-- Equilibrium (Killing-type) condition in coordinate-free form. -/
def IsEquilibrium
    (g : CoordinateFreeMetric (Tangent := Tangent))
    (bracket : ∀ p : M, Tangent p → Tangent p → Tangent p)
    (β : ∀ p : M, Tangent p) : Prop :=
  ∀ p : M, ∀ X Y : Tangent p,
    metricLieDerivative (Tangent := Tangent) g bracket β p X Y = 0

/--
Conformal/Weyl non-equilibrium profile:
the metric Lie derivative equals a scalar dilation `σ(p)` times `g`.
-/
def IsConformalFlow
    (g : CoordinateFreeMetric (Tangent := Tangent))
    (bracket : ∀ p : M, Tangent p → Tangent p → Tangent p)
    (β : ∀ p : M, Tangent p)
    (σ : M → ℝ) : Prop :=
  ∀ p : M, ∀ X Y : Tangent p,
    metricLieDerivative (Tangent := Tangent) g bracket β p X Y = σ p * g.g p X Y

/-- Equilibrium is the zero-dilation conformal profile. -/
theorem equilibrium_iff_conformal_zero
    (g : CoordinateFreeMetric (Tangent := Tangent))
    (bracket : ∀ p : M, Tangent p → Tangent p → Tangent p)
    (β : ∀ p : M, Tangent p) :
    IsEquilibrium (Tangent := Tangent) g bracket β
      ↔ IsConformalFlow (Tangent := Tangent) g bracket β (fun _ => 0) := by
  constructor
  · intro h p X Y
    simpa [IsConformalFlow] using h p X Y
  · intro h p X Y
    simpa [IsConformalFlow] using h p X Y

/-- If a conformal profile has identically zero dilation, it is equilibrium. -/
theorem conformal_zero_implies_equilibrium
    (g : CoordinateFreeMetric (Tangent := Tangent))
    (bracket : ∀ p : M, Tangent p → Tangent p → Tangent p)
    (β : ∀ p : M, Tangent p)
    (h : IsConformalFlow (Tangent := Tangent) g bracket β (fun _ => 0)) :
    IsEquilibrium (Tangent := Tangent) g bracket β := by
  exact (equilibrium_iff_conformal_zero (Tangent := Tangent) g bracket β).2 h

/--
Coordinate-free Souriau packet with inverse-temperature norm readout and
equilibrium witness.
-/
structure CoordinateFreeSouriau where
  metric : CoordinateFreeMetric (Tangent := Tangent)
  beta : ∀ p : M, Tangent p
  bracket : ∀ p : M, Tangent p → Tangent p → Tangent p
  inverseTemperature : M → ℝ
  inverseTemperature_eq_norm :
    ∀ p : M, ∀ norm : Tangent p → ℝ,
      inverseTemperature p = norm (beta p)
  equilibrium :
    IsEquilibrium (Tangent := Tangent) metric bracket beta

/--
Two-lane (real + thermal) coordinate-free derivation context.

This is the real/imaginary decomposition carrier for a complexified flow
parameter `τ = t + iβ`, without introducing coordinates.
-/
structure ComplexifiedDerivationContext where
  metric : CoordinateFreeMetric (Tangent := Tangent)
  bracket : ∀ p : M, Tangent p → Tangent p → Tangent p
  realLane : ∀ p : M, Tangent p
  thermalLane : ∀ p : M, Tangent p

/-- Real lane preserves the metric (`L_t g = 0`). -/
def ComplexifiedDerivationContext.realIsometry
    (C : ComplexifiedDerivationContext (Tangent := Tangent)) : Prop :=
  IsEquilibrium (Tangent := Tangent) C.metric C.bracket C.realLane

/-- Thermal lane preserves the metric (`L_β g = 0`). -/
def ComplexifiedDerivationContext.thermalIsometry
    (C : ComplexifiedDerivationContext (Tangent := Tangent)) : Prop :=
  IsEquilibrium (Tangent := Tangent) C.metric C.bracket C.thermalLane

/--
Split equilibrium packet:
if both real and thermal lanes are isometries, both Lie-derivative readouts
vanish pointwise.
-/
theorem ComplexifiedDerivationContext.split_equilibrium_packet
    (C : ComplexifiedDerivationContext (Tangent := Tangent))
    (hReal : C.realIsometry)
    (hThermal : C.thermalIsometry) :
    (∀ p : M, ∀ X Y : Tangent p,
      metricLieDerivative (Tangent := Tangent) C.metric C.bracket C.realLane p X Y = 0) ∧
    (∀ p : M, ∀ X Y : Tangent p,
      metricLieDerivative (Tangent := Tangent) C.metric C.bracket C.thermalLane p X Y = 0) := by
  exact ⟨hReal, hThermal⟩

end

end InfoGeometry.Canonical.CoordinateFreeSouriauDerivation
