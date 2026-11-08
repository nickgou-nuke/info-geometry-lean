/-
InfoGeometry/Algebraic/OperatorSurgery.lean

Schur-Drazin and Moore-Penrose algebraic surgery.

This module formalizes the surgical extraction of regular cores from 
singular operators using Drazin and Moore-Penrose projectors.
-/

import InfoGeometry.Singular.Drazin
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Singular.MoorePenrose

namespace InfoGeometry.Algebraic

open InfoGeometry.Singular.Drazin
open InfoGeometry.Singular.MoorePenrose

section Surgery

variable {R : Type*} [Ring R]

/-- 
Theorem 3.1: Schur-Drazin Algebraic Surgery.
Isolates the regular core and nilpotent radical.
-/
structure DrazinSurgery (A : R) where
  D : R
  k : ℕ
  hD : IsDrazinInverse A D k

namespace DrazinSurgery

variable {A : R} (S : DrazinSurgery A)

/-- The Drazin core projector P_D := A * A^D. -/
def coreProjector : R := A * S.D

/-- The Drazin null projector P_nil := I - P_D. -/
def nullProjector : R := 1 - S.coreProjector

/-- P_D is idempotent. -/
theorem core_idempotent : S.coreProjector * S.coreProjector = S.coreProjector :=
  Drazin_Projector_idempotent S.hD

/-- P_nil is idempotent. -/
theorem null_idempotent : S.nullProjector * S.nullProjector = S.nullProjector := by
  simp [nullProjector, sub_mul, mul_sub, core_idempotent]

/-- The projectors are orthogonal: P_D * P_nil = 0. -/
theorem core_null_orthogonal : S.coreProjector * S.nullProjector = 0 := by
  simp [nullProjector, mul_sub, core_idempotent]

/-- The projectors sum to identity: P_D + P_nil = I. -/
theorem partition_of_unity : S.coreProjector + S.nullProjector = 1 := by
  simp [nullProjector]

end DrazinSurgery

end Surgery

section MetricSurgery

variable {R : Type*} [Ring R] [StarRing R]

/-- 
Moore-Penrose Metric Surgery.
Requires a star-ring structure for the geometric adjoint.
-/
structure MoorePenroseSurgery (A : R) where
  B : R
  hMP : IsMoorePenroseInverse A B

namespace MoorePenroseSurgery

variable {A : R} (S : MoorePenroseSurgery A)

/-- The Moore-Penrose projector Π_MP := A * B. -/
def projector : R := A * S.B

/-- Π_MP is idempotent. -/
theorem idempotent : S.projector * S.projector = S.projector :=
  MP_Projector_idempotent S.hMP

/-- Π_MP is self-adjoint with respect to the metric star-operation. -/
theorem self_adjoint : S.projector† = S.projector :=
  MP_Projector_self_adjoint S.hMP

end MoorePenroseSurgery

end MetricSurgery

end InfoGeometry.Algebraic
