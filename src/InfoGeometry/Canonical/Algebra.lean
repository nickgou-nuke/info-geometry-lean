/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev.
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Authors: Nikolay Goutev, Dimitar Tonev
-/


import InfoGeometry.Canonical.Drazin
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.MoorePenrose
import Mathlib.Algebra.Module.Basic

namespace InfoGeometry.Canonical

/--
Unified algebraic projection datum.

This structure provides the conductive path between Drazin and Moore-Penrose
projections on a shared module.

PAULI_MANDATE II: This provides a Value-Edge by coordinating two different
inverse theories into a single projective witness.
-/
structure UnifiedProjection (R M : Type*)
    [Ring R] [StarRing R] [AddCommGroup M] [Module R M] where
  /-- The operator element. -/
  op : R
  /-- Drazin inverse witness. -/
  a_d : R
  /-- Moore-Penrose inverse witness. -/
  a_mp : R
  /-- Drazin index. -/
  k : ℕ

  /-- Drazin inverse law must hold. -/
  is_drazin : Drazin.IsDrazinInverse op a_d k
  /-- Moore-Penrose inverse law must hold. -/
  is_mp : MoorePenrose.IsMoorePenroseInverse op a_mp

  /--
  Conductivity Law: The spectral and metric projectors must be identified
  through a provided intertwiner or witness.
  -/
  projectors_compatible :
    Drazin.IsDrazinInverse.projection op a_d =
      MoorePenrose.IsMoorePenroseInverse.leftProjector op a_mp

namespace UnifiedProjection

variable {R M : Type*} [Ring R] [StarRing R] [AddCommGroup M] [Module R M]
variable (P : UnifiedProjection R M)

/-- The unified projector of the system. -/
def projector : R := Drazin.IsDrazinInverse.projection P.op P.a_d

/-- The unified projector is idempotent. -/
theorem projector_idempotent :
    P.projector * P.projector = P.projector :=
  Drazin.IsDrazinInverse.projection_is_idempotent P.is_drazin

/--
The unified projector is self-adjoint, conducting to the Moore-Penrose
metric root.
-/
theorem projector_star :
    star P.projector = P.projector := by
  unfold projector
  rw [P.projectors_compatible]
  exact MoorePenrose.IsMoorePenroseInverse.ba_star P.is_mp

end UnifiedProjection

end InfoGeometry.Canonical
