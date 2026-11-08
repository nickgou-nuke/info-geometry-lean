import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

/-!
# Noncommutative vector-calculus identities

The carrier here is a vector of three elements of an associative ring.  The
bracket is the associative commutator; no multiplication on a nonassociative
Zorn algebra is used.  This file proves the curvature-corrected
Helmholtz--Weitzenböck identity for arbitrary operator components.
-/

namespace InfoGeometry.Canonical.NoncommutativeHelmholtzWeitzenboeck

variable {R : Type*} [Ring R]

abbrev Vec3 := Fin 3 → R

def bracket (x y : R) : R := x * y - y * x

theorem bracket_add_add (a b c d : R) :
    bracket (a + b) (c + d) =
      bracket a c + bracket a d + bracket b c + bracket b d := by
  unfold bracket
  noncomm_ring

theorem single_connection_temporal_curvature (d₀ φ : R) (d a : Vec3 (R := R)) :
    (fun i => bracket (d₀ + φ) (d i + a i)) =
      fun i => bracket d₀ (d i) + bracket d₀ (a i) +
        bracket φ (d i) + bracket φ (a i) := by
  funext i
  exact bracket_add_add d₀ φ (d i) (a i)

def gradient (p : Vec3 (R := R)) (f : R) : Vec3 (R := R) :=
  fun i => bracket (p i) f

def divergence (p v : Vec3 (R := R)) : R :=
  bracket (p 0) (v 0) + bracket (p 1) (v 1) + bracket (p 2) (v 2)

def curl (p v : Vec3 (R := R)) : Vec3 (R := R) := fun i =>
  if i = 0 then bracket (p 1) (v 2) - bracket (p 2) (v 1)
  else if i = 1 then bracket (p 2) (v 0) - bracket (p 0) (v 2)
  else bracket (p 0) (v 1) - bracket (p 1) (v 0)

def magneticCurvature (p : Vec3 (R := R)) : Vec3 (R := R) :=
  fun i => if i = 0 then bracket (p 1) (p 2)
    else if i = 1 then bracket (p 2) (p 0)
    else bracket (p 0) (p 1)

def electricCurvature (a : R) (p : Vec3 (R := R)) : Vec3 (R := R) :=
  fun i => bracket a (p i)

theorem commutator_jacobi (x y z : R) :
    bracket x (bracket y z) =
      bracket (bracket x y) z + bracket y (bracket x z) := by
  unfold bracket
  noncomm_ring

theorem bianchi_faraday (a : R) (p : Vec3 (R := R)) :
    (fun i => bracket a (magneticCurvature p i)) =
      curl p (electricCurvature a p) := by
  funext i
  fin_cases i <;>
    simp [curl, magneticCurvature, electricCurvature, bracket] <;> noncomm_ring

theorem covariant_divergence_magnetic_curvature (p : Vec3 (R := R)) :
    divergence p (magneticCurvature p) = 0 := by
  simp [divergence, magneticCurvature, bracket]
  noncomm_ring

theorem single_connection_spatial_curvature (d a : Vec3 (R := R)) :
    magneticCurvature (d + a) = fun i =>
      if i = 0 then bracket (d 1) (d 2) + bracket (d 1) (a 2) +
          bracket (a 1) (d 2) + bracket (a 1) (a 2)
      else if i = 1 then bracket (d 2) (d 0) + bracket (d 2) (a 0) +
          bracket (a 2) (d 0) + bracket (a 2) (a 0)
      else bracket (d 0) (d 1) + bracket (d 0) (a 1) +
          bracket (a 0) (d 1) + bracket (a 0) (a 1) := by
  funext i
  fin_cases i <;> simp [magneticCurvature, bracket_add_add]

def curvatureAction (b v : Vec3 (R := R)) : Vec3 (R := R) := fun i =>
  if i = 0 then bracket (b 1) (v 2) - bracket (b 2) (v 1)
  else if i = 1 then bracket (b 2) (v 0) - bracket (b 0) (v 2)
  else bracket (b 0) (v 1) - bracket (b 1) (v 0)

def bochnerLaplacian (p v : Vec3 (R := R)) : Vec3 (R := R) := fun i =>
  bracket (p 0) (bracket (p 0) (v i)) +
    bracket (p 1) (bracket (p 1) (v i)) +
    bracket (p 2) (bracket (p 2) (v i))

theorem curl_gradient_curvature (p : Vec3 (R := R)) (f : R) :
    curl p (gradient p f) = fun i => bracket (magneticCurvature p i) f := by
  funext i
  fin_cases i <;> simp [curl, gradient, magneticCurvature, bracket] <;>
    noncomm_ring

theorem divergence_curl_curvature (p v : Vec3 (R := R)) :
    divergence p (curl p v) =
      bracket (magneticCurvature p 0) (v 0) +
      bracket (magneticCurvature p 1) (v 1) +
      bracket (magneticCurvature p 2) (v 2) := by
  simp [divergence, curl, magneticCurvature, bracket]
  noncomm_ring

theorem helmholtz_weitzenboeck (p v : Vec3 (R := R)) :
    (fun i => gradient p (divergence p v) i - curl p (curl p v) i) =
      fun i => bochnerLaplacian p v i - curvatureAction (magneticCurvature p) v i := by
  funext i
  fin_cases i <;>
    simp [gradient, divergence, curl, magneticCurvature, curvatureAction,
      bochnerLaplacian, bracket] <;> noncomm_ring

end InfoGeometry.Canonical.NoncommutativeHelmholtzWeitzenboeck
