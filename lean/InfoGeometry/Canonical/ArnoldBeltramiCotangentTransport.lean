/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ArnoldBeltramiFlow
import InfoGeometry.Quantum.MobiusRealCotangentLift

/-!
# Cotangent transport of the real Beltrami shear flow

The derivative of the constructed spatial flow is an invertible shear, generally
not an orthogonal map.  Its real cotangent lift acts on actual curl vorticity and
the metric momentum covector.  For the two signs `s ^ 2 = 1`, this action transports
the physical state to the state at the advected point.  Its neutral quadratic
readout is exactly the signed local helicity.

This is an explicit spatial-flow example, not a construction of the full SDiff
Lie group, its regular dual, or a spectral identification of all chiral modes.
-/

noncomputable section

namespace InfoGeometry.Canonical.ArnoldBeltramiCotangentTransport

open InfoGeometry.Canonical.NavierStokesShearReconstruction
open InfoGeometry.Canonical.ArnoldBeltramiFlow
open InfoGeometry.Quantum.DualFlatKreinGraph
open InfoGeometry.Quantum.MobiusRealCotangentLift
open scoped InnerProductSpace

/-- Explicit identification of the spatial coordinate carrier with the existing
Euclidean cotangent carrier.  It changes the finite-product norm, not coordinates. -/
def coordinateEuclidean : Space ≃ₗ[ℝ] Vector 3 :=
  (WithLp.linearEquiv (2 : ENNReal) ℝ Space).symm

@[simp] theorem coordinateEuclidean_apply (v : Space) (i : Fin 3) :
    coordinateEuclidean v i = v i := rfl

@[simp] theorem coordinateEuclidean_symm_apply (v : Vector 3) (i : Fin 3) :
    coordinateEuclidean.symm v i = v i := rfl

/-- The actual spatial derivative, with its explicitly constructed inverse. -/
def coordinateTangent (s t : ℝ) (x : Space) : Space ≃ₗ[ℝ] Space :=
  { (flowDerivative s t x).toLinearMap with
    invFun := flowDerivative s (-t) x
    left_inv := by
      intro v
      ext i
      fin_cases i <;> simp [flowDerivative_apply]
    right_inv := by
      intro v
      ext i
      fin_cases i <;> simp [flowDerivative_apply] }

@[simp] theorem coordinateTangent_apply (s t : ℝ) (x v : Space) :
    coordinateTangent s t x v = flowDerivative s t x v := rfl

@[simp] theorem coordinateTangent_symm_apply (s t : ℝ) (x v : Space) :
    (coordinateTangent s t x).symm v = flowDerivative s (-t) x v := rfl

/-- The same spatial derivative on the carrier used by the generic cotangent lift. -/
def tangentEquiv (s t : ℝ) (x : Space) : Vector 3 ≃ₗ[ℝ] Vector 3 :=
  coordinateEuclidean.symm.trans ((coordinateTangent s t x).trans coordinateEuclidean)

theorem tangentEquiv_fderiv (s t : ℝ) (x v : Space) :
    tangentEquiv s t x (coordinateEuclidean v) =
      coordinateEuclidean (fderiv ℝ (flow s t) x v) := by
  change coordinateEuclidean (flowDerivative s t x v) = _
  rw [fderiv_flow]

theorem tangentEquiv_apply (s t : ℝ) (x : Space) (v : Vector 3) :
    tangentEquiv s t x v = coordinateEuclidean
      ![v 0 - t * Real.sin (x 2) * v 2,
        v 1 - s * t * Real.cos (x 2) * v 2, v 2] := by
  change coordinateEuclidean (flowDerivative s t x (coordinateEuclidean.symm v)) = _
  rw [flowDerivative_apply]
  rfl

theorem tangentEquiv_symm_apply (s t : ℝ) (x : Space) (v : Vector 3) :
    (tangentEquiv s t x).symm v = coordinateEuclidean
      ![v 0 + t * Real.sin (x 2) * v 2,
        v 1 + s * t * Real.cos (x 2) * v 2, v 2] := by
  change coordinateEuclidean (flowDerivative s (-t) x (coordinateEuclidean.symm v)) = _
  rw [flowDerivative_apply]
  congr 1
  ext i
  fin_cases i <;> simp

/-- Horizontal vectors are fixed by this triangular derivative. -/
theorem tangentEquiv_horizontal (s t : ℝ) (x : Space) (v : Vector 3)
    (hv : v 2 = 0) : tangentEquiv s t x v = v := by
  rw [tangentEquiv_apply]
  ext i
  fin_cases i <;> simp [hv]

/-- The metric momentum covector is constructed by the native real inner product. -/
def momentum (s : ℝ) (x : Space) : Covector 3 :=
  (innerSL ℝ (coordinateEuclidean (velocity s x))).toLinearMap

theorem momentum_apply (s : ℝ) (x : Space) (v : Vector 3) :
    momentum s x v = Real.cos (x 2) * v 0 - s * Real.sin (x 2) * v 1 := by
  change inner ℝ (coordinateEuclidean (velocity s x)) v = _
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, Fin.sum_univ_three, coordinateEuclidean, velocity]
  ring

theorem momentum_flow (s t : ℝ) (x : Space) :
    momentum s (flow s t x) = momentum s x := by
  unfold momentum
  rw [velocity_flow]

/-- The inverse derivative, rather than the forward vector action, transports momentum. -/
theorem momentum_inverse_tangent {s : ℝ} (hs : s ^ 2 = 1)
    (t : ℝ) (x : Space) (v : Vector 3) :
    momentum s x ((tangentEquiv s t x).symm v) = momentum s x v := by
  rw [tangentEquiv_symm_apply, momentum_apply, momentum_apply]
  simp only [coordinateEuclidean_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  calc
    Real.cos (x 2) * (v 0 + t * Real.sin (x 2) * v 2) -
        s * Real.sin (x 2) * (v 1 + s * t * Real.cos (x 2) * v 2) =
        (Real.cos (x 2) * v 0 - s * Real.sin (x 2) * v 1) +
          (1 - s ^ 2) * (t * Real.sin (x 2) * Real.cos (x 2) * v 2) := by ring
    _ = Real.cos (x 2) * v 0 - s * Real.sin (x 2) * v 1 := by rw [hs]; ring

/-- Actual spatial curl paired with the metric momentum covector. -/
def physicalState (s : ℝ) (x : Space) : Carrier 3 :=
  (coordinateEuclidean (curl (velocity s) x), momentum s x)

theorem physicalState_flow (s t : ℝ) (x : Space) :
    physicalState s (flow s t x) = physicalState s x := by
  apply Prod.ext
  · simp only [physicalState, curl_velocity_formula, flow_third]
  · exact momentum_flow s t x

/-- A physical transport theorem using the existing cotangent action and actual derivatives. -/
theorem cotangentLift_physicalState {s : ℝ} (hs : s ^ 2 = 1)
    (t : ℝ) (x : Space) :
    lift (tangentEquiv s t x) (physicalState s x) =
      physicalState s (flow s t x) := by
  rw [physicalState_flow]
  apply Prod.ext
  · change tangentEquiv s t x (coordinateEuclidean (curl (velocity s) x)) = _
    apply tangentEquiv_horizontal
    rw [curl_velocity s hs]
    simp [velocity]
  · change (momentum s x).comp (tangentEquiv s t x).symm.toLinearMap = momentum s x
    ext v
    exact momentum_inverse_tangent hs t x v

theorem momentum_velocity {s : ℝ} (hs : s ^ 2 = 1) (x : Space) :
    momentum s x (coordinateEuclidean (velocity s x)) = 1 := by
  rw [momentum_apply]
  simp only [coordinateEuclidean_apply, velocity, Matrix.cons_val_zero, Matrix.cons_val_one]
  calc
    Real.cos (x 2) * Real.cos (x 2) -
        s * Real.sin (x 2) * (-s * Real.sin (x 2)) =
        Real.cos (x 2) ^ 2 + s ^ 2 * Real.sin (x 2) ^ 2 := by ring
    _ = 1 := by
      rw [hs]
      nlinarith [Real.sin_sq_add_cos_sq (x 2)]

/-- The existing neutral quadratic form is the signed local physical helicity. -/
theorem neutralPair_physicalState (s : ℝ) (x : Space) :
    neutralPair (physicalState s x) (physicalState s x) = s := by
  have hval : momentum s x (coordinateEuclidean (curl (velocity s) x)) = s := by
    change inner ℝ (coordinateEuclidean (velocity s x))
      (coordinateEuclidean (curl (velocity s) x)) = s
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simpa [dotProduct, coordinateEuclidean, mul_comm] using
      helicity_density_velocity s x
  change (momentum s x (coordinateEuclidean (curl (velocity s) x)) +
    momentum s x (coordinateEuclidean (curl (velocity s) x))) / 2 = s
  rw [hval]
  ring

/-- Both signs have a nonzero neutral quadratic value at every spatial point. -/
theorem physicalState_nonnull {s : ℝ} (hs : s ^ 2 = 1) (x : Space) :
    neutralPair (physicalState s x) (physicalState s x) ≠ 0 := by
  rw [neutralPair_physicalState]
  intro hzero
  simp [hzero] at hs

/-- A concrete derivative in the family is volume-preserving but not orthogonal:
the third coordinate vector acquires a nonzero horizontal component. -/
theorem tangentEquiv_nonorthogonal :
    ¬ ∀ v w : Vector 3,
      inner ℝ (tangentEquiv 1 1 (0 : Space) v) (tangentEquiv 1 1 (0 : Space) w) =
        inner ℝ v w := by
  intro h
  have he := h (coordinateEuclidean ![0, 0, 1]) (coordinateEuclidean ![0, 0, 1])
  simp only [tangentEquiv_apply, EuclideanSpace.inner_eq_star_dotProduct] at he
  norm_num [coordinateEuclidean, dotProduct, Fin.sum_univ_three] at he

end InfoGeometry.Canonical.ArnoldBeltramiCotangentTransport
