/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge
import InfoGeometry.Canonical.NonAbelianCovariantBianchiChernWeilBridge
import Mathlib.Tactic.NoncommRing

/-!
# Naturality of matrix connection curvature under differential-compatible maps

This owner proves the exact transport statements needed to connect two
matrix-valued connection carriers. Ring-homomorphism laws transport the
quadratic term; differential compatibility is stated explicitly for the
connection and the test curvature. No map from the tensor-tower `Stage n` to
this exterior-form carrier is asserted here.
-/

noncomputable section

namespace InfoGeometry.Canonical.MatrixConnectionCurvatureTransport

open ExteriorAlgebra
open InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge
open InfoGeometry.Canonical.MatrixTracedChernWeilBridge
open InfoGeometry.Canonical.NonAbelianCovariantBianchiChernWeilBridge

variable {R V : Type*} [AddCommGroup V] {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) (ExteriorAlgebra R V)

/-- Connection curvature is preserved by a ring homomorphism that intertwines
the matrix exterior derivative on this connection. -/
theorem curvatureFromConnection_map [Field R] [Module R V]
    (f : Mat →+* Mat) (d : Module.End R (ExteriorAlgebra R V)) (A : Mat)
    (hDerivative : matrixExteriorDerivative d (f A) =
      f (matrixExteriorDerivative d A)) :
    f (curvatureFromConnection d A) =
      curvatureFromConnection d (f A) := by
  unfold curvatureFromConnection
  calc
    f (matrixExteriorDerivative d A + A * A) =
        f (matrixExteriorDerivative d A) + f (A * A) := map_add f _ _
    _ = matrixExteriorDerivative d (f A) + f A * f A := by
      rw [map_mul, hDerivative]
    _ = curvatureFromConnection d (f A) := rfl

/-- The matrix covariant derivative is preserved when the ring homomorphism
intertwines the exterior derivative on both the connection and the operator
being differentiated. -/
theorem covariantDerivative_map [CommRing R] [Module R V]
    (f : Mat →+* Mat) (d : Module.End R (ExteriorAlgebra R V)) (A X : Mat)
    (hDerivativeX : matrixExteriorDerivative d (f X) =
      f (matrixExteriorDerivative d X)) :
    f (covariantDerivative A d X) =
      covariantDerivative (f A) d (f X) := by
  unfold covariantDerivative matrixCommutator
  calc
    f (matrixExteriorDerivative d X + (A * X - X * A)) =
        f (matrixExteriorDerivative d X) + (f A * f X - f X * f A) := by
          rw [map_add, map_sub, map_mul, map_mul]
    _ = matrixExteriorDerivative d (f X) + (f A * f X - f X * f A) := by
          rw [hDerivativeX]
    _ = covariantDerivative (f A) d (f X) := rfl

/-- A zero covariant derivative (the Bianchi equation, when `X` is the
curvature) transports along the same explicitly compatible ring map. -/
theorem zero_covariantDerivative_transports [CommRing R] [Module R V]
    (f : Mat →+* Mat) (d : Module.End R (ExteriorAlgebra R V)) (A X : Mat)
    (hDerivativeX : matrixExteriorDerivative d (f X) =
      f (matrixExteriorDerivative d X))
    (hZero : covariantDerivative A d X = 0) :
    covariantDerivative (f A) d (f X) = 0 := by
  rw [← covariantDerivative_map f d A X hDerivativeX,
    hZero, map_zero]

variable [Field R] [Module R V]

/-- Connection curvature and the Bianchi zero equation transport together.
The compatibility premises remain visible: this theorem becomes a bridge
between concrete carriers only after a concrete `f` and its differential laws
are supplied. -/
theorem curvature_and_bianchi_transport
    (f : Mat →+* Mat) (d : Module.End R (ExteriorAlgebra R V)) (A : Mat)
    (hDerivativeA : matrixExteriorDerivative d (f A) =
      f (matrixExteriorDerivative d A))
    (hDerivativeCurvature : matrixExteriorDerivative d
      (f (curvatureFromConnection d A)) =
        f (matrixExteriorDerivative d (curvatureFromConnection d A)))
    (hBianchi : covariantDerivative A d (curvatureFromConnection d A) = 0) :
    f (curvatureFromConnection d A) = curvatureFromConnection d (f A) ∧
    covariantDerivative (f A) d (curvatureFromConnection d (f A)) = 0 := by
  refine ⟨curvatureFromConnection_map f d A hDerivativeA, ?_⟩
  rw [← curvatureFromConnection_map f d A hDerivativeA]
  exact zero_covariantDerivative_transports f d A
    (curvatureFromConnection d A) hDerivativeCurvature hBianchi

end InfoGeometry.Canonical.MatrixConnectionCurvatureTransport

end noncomputable section
