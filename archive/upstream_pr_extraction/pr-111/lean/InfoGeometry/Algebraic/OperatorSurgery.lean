/-
InfoGeometry/Algebraic/OperatorSurgery.lean

Schur-Drazin and Moore-Penrose algebraic surgery.

This module formalizes the surgical extraction of regular cores from 
singular operators using Drazin and Moore-Penrose projectors.
-/

import InfoGeometry.Singular.Drazin
import InfoGeometry.Singular.MoorePenrose

namespace InfoGeometry.Algebraic

open InfoGeometry.Singular.Drazin
open InfoGeometry.Singular.MoorePenrose

section Surgery

variable {R : Type*} [Ring R]

namespace DrazinSurgery

variable {A D : R} {k : ℕ}

/-- The Drazin core projector P_D := A * A^D. -/
def coreProjector (A D : R) : R := A * D

/-- The Drazin null projector P_nil := I - P_D. -/
def nullProjector (A D : R) : R := 1 - coreProjector A D

/-- P_D is idempotent. -/
theorem core_idempotent (hD : IsDrazinInverse A D k) :
    coreProjector A D * coreProjector A D = coreProjector A D :=
  Drazin_Projector_idempotent hD

/-- P_nil is idempotent. -/
theorem null_idempotent (hD : IsDrazinInverse A D k) :
    nullProjector A D * nullProjector A D = nullProjector A D := by
  simp [nullProjector, sub_mul, mul_sub, core_idempotent hD]

/-- The projectors are orthogonal: P_D * P_nil = 0. -/
theorem core_null_orthogonal (hD : IsDrazinInverse A D k) :
    coreProjector A D * nullProjector A D = 0 := by
  simp [nullProjector, mul_sub, core_idempotent hD]

/-- The projectors sum to identity: P_D + P_nil = I. -/
theorem partition_of_unity : coreProjector A D + nullProjector A D = 1 := by
  simp [nullProjector]

end DrazinSurgery

end Surgery

section MetricSurgery

variable {R : Type*} [Ring R] [StarRing R]

namespace MoorePenroseSurgery

variable {A B : R}

/-- The Moore-Penrose projector Π_MP := A * B. -/
def projector (A B : R) : R := A * B

/-- Π_MP is idempotent. -/
theorem idempotent (hMP : IsMoorePenroseInverse A B) :
    projector A B * projector A B = projector A B :=
  MP_Projector_idempotent hMP

/-- Π_MP is self-adjoint with respect to the metric star-operation. -/
theorem self_adjoint (hMP : IsMoorePenroseInverse A B) :
    (projector A B)† = projector A B :=
  MP_Projector_self_adjoint hMP

end MoorePenroseSurgery

end MetricSurgery

end InfoGeometry.Algebraic
