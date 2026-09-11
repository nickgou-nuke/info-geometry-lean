import InfoGeometry.Optics.OperatorQGTGaugeModuli
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Gauge-invariant curvature traces for operator-valued QGT connections

Finite-dimensional traces turn the conjugacy class of the complete QGT
curvature into scalar functions on the native gauge quotient.  All powers are
handled uniformly, so the linear and quadratic curvature readouts are the
first two members of one algebraic family.
-/

noncomputable section

namespace InfoGeometry.Optics.OperatorQGTGaugeInvariants

open InfoGeometry.OperatorAlgebra
open InfoGeometry.Optics.LocalGaugeGroupAction
open InfoGeometry.Optics.OperatorQGTGaugeModuli
open InfoGeometry.Optics.OperatorValuedConnection

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The trace of a finite-dimensional endomorphism is invariant under the
native inner conjugation used by the local gauge action. -/
theorem trace_innerConjugation
    (u : (Module.End ℂ V)ˣ) (A : Module.End ℂ V) :
    LinearMap.trace ℂ V (innerConjugation u A) =
      LinearMap.trace ℂ V A := by
  unfold innerConjugation
  calc
    LinearMap.trace ℂ V (↑u * A * ↑u⁻¹) =
        LinearMap.trace ℂ V (↑u⁻¹ * (↑u * A)) :=
      LinearMap.trace_mul_comm ℂ (↑u * A) ↑u⁻¹
    _ = LinearMap.trace ℂ V ((↑u⁻¹ * ↑u) * A) := by
      rw [mul_assoc]
    _ = LinearMap.trace ℂ V A := by
      rw [Units.inv_mul, one_mul]

/-- Every power trace is invariant under the same finite frame change. -/
theorem trace_pow_innerConjugation
    (u : (Module.End ℂ V)ˣ) (A : Module.End ℂ V) (n : ℕ) :
    LinearMap.trace ℂ V ((innerConjugation u A) ^ n) =
      LinearMap.trace ℂ V (A ^ n) := by
  change LinearMap.trace ℂ V (((innerConjugationRingEquiv u) A) ^ n) = _
  rw [← map_pow]
  exact trace_innerConjugation u (A ^ n)

section QGT

variable {W Point Tangent : Type*} [AddCommGroup W] [Module ℂ W]

/-- The degree-`n` curvature trace of a complete doubled QGT connection. -/
def curvatureTracePower
    (n : ℕ)
    (C : QGTConnection (W := W) (Point := Point) (Tangent := Tangent))
    (p : Point) (X Y : Tangent) : ℂ :=
  LinearMap.trace ℂ (Fin 2 → W) ((curvature C p X Y) ^ n)

@[simp] theorem curvatureTracePower_zero
    [FiniteDimensional ℂ W]
    (C : QGTConnection (W := W) (Point := Point) (Tangent := Tangent))
    (p : Point) (X Y : Tangent) :
    curvatureTracePower 0 C p X Y =
      (Module.finrank ℂ (Fin 2 → W) : ℂ) := by
  simpa only [curvatureTracePower, pow_zero] using
    (LinearMap.trace_one ℂ (Fin 2 → W))

/-- Every curvature power trace is invariant under the native local gauge
group, including point-dependent frames and their Maurer--Cartan terms. -/
theorem curvatureTracePower_smul
    (n : ℕ)
    (G : QGTGaugeGroup (W := W) (Point := Point) (Tangent := Tangent))
    (C : QGTConnection (W := W) (Point := Point) (Tangent := Tangent))
    (p : Point) (X Y : Tangent) :
    curvatureTracePower n (G • C) p X Y =
      curvatureTracePower n C p X Y := by
  rw [curvatureTracePower, rightGaugeGroup_smul_curvature]
  exact trace_pow_innerConjugation (G.frame p) (curvature C p X Y) n

/-- Gauge-equivalent QGT connections have identical curvature power traces. -/
theorem curvatureTracePower_eq_of_gaugeEquivalent
    (n : ℕ)
    {C D : QGTConnection (W := W) (Point := Point) (Tangent := Tangent)}
    (h : QGTGaugeEquivalent C D) :
    curvatureTracePower n C = curvatureTracePower n D := by
  unfold QGTGaugeEquivalent qgtGaugeSetoid MulAction.orbitRel at h
  rcases h with ⟨G, rfl⟩
  funext p X Y
  exact curvatureTracePower_smul n G D p X Y

/-- The full degree-`n` curvature trace descends to the QGT gauge moduli
quotient, rather than depending on a chosen connection representative. -/
def curvatureTracePowerGaugeClass
    (n : ℕ) :
    QGTGaugeModuli (W := W) (Point := Point) (Tangent := Tangent) →
      Point → Tangent → Tangent → ℂ :=
  Quotient.lift (curvatureTracePower n) (by
    intro C D h
    exact curvatureTracePower_eq_of_gaugeEquivalent n h)

@[simp] theorem curvatureTracePowerGaugeClass_mk
    (n : ℕ)
    (C : QGTConnection (W := W) (Point := Point) (Tangent := Tangent)) :
    curvatureTracePowerGaugeClass n
        (Quotient.mk
          (qgtGaugeSetoid (W := W) (Point := Point) (Tangent := Tangent)) C) =
      curvatureTracePower n C :=
  rfl

/-- The ordinary trace of curvature on a gauge class. -/
abbrev curvatureTraceGaugeClass :=
  curvatureTracePowerGaugeClass (W := W) (Point := Point) (Tangent := Tangent) 1

/-- The quadratic curvature trace on a gauge class. -/
abbrev curvatureSquareTraceGaugeClass :=
  curvatureTracePowerGaugeClass (W := W) (Point := Point) (Tangent := Tangent) 2

end QGT

end InfoGeometry.Optics.OperatorQGTGaugeInvariants
