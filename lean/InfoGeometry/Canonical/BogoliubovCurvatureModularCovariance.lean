import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Algebraic covariance of commutator curvature

This is an adapter theorem only.  It does not introduce a new curvature
owner, a C*-completion, or a trace functional.  It records the elementary
fact that inner transport preserves commutators.
-/

namespace InfoGeometry.Canonical

section

variable {A : Type*} [DivisionRing A]

def innerTransport (u a : A) : A := u * a * u⁻¹

def commutatorCurvature (x y : A) : A := x * y - y * x

theorem innerTransport_commutator (u x y : A) (hu : u⁻¹ * u = 1) :
    innerTransport u (commutatorCurvature x y) =
      commutatorCurvature (innerTransport u x) (innerTransport u y) := by
  unfold innerTransport commutatorCurvature
  simp only [mul_sub, sub_mul]
  have h₁ : (u * x * u⁻¹) * (u * y * u⁻¹) =
      u * (x * y) * u⁻¹ := by
    calc
      (u * x * u⁻¹) * (u * y * u⁻¹) =
          u * x * (u⁻¹ * u) * y * u⁻¹ := by simp [mul_assoc]
      _ = u * (x * y) * u⁻¹ := by
        rw [hu]
        simp only [mul_one, mul_assoc]
  have h₂ : (u * y * u⁻¹) * (u * x * u⁻¹) =
      u * (y * x) * u⁻¹ := by
    calc
      (u * y * u⁻¹) * (u * x * u⁻¹) =
          u * y * (u⁻¹ * u) * x * u⁻¹ := by simp [mul_assoc]
      _ = u * (y * x) * u⁻¹ := by
        rw [hu]
        simp only [mul_one, mul_assoc]
  rw [h₁, h₂]

theorem innerTransport_curvature_invariant
    (u f : A) (hu : u * u⁻¹ = 1) (hcomm : u * f = f * u) :
    innerTransport u f = f := by
  unfold innerTransport
  calc
    u * f * u⁻¹ = f * u * u⁻¹ := by rw [hcomm]
    _ = f * (u * u⁻¹) := by rw [mul_assoc]
    _ = f := by rw [hu, mul_one]

end

end InfoGeometry.Canonical
