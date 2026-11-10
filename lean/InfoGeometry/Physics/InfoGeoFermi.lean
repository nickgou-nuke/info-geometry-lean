/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Formalization Team
-/
import Mathlib.Algebra.Lie.Basic

/-!
# Projective states and Fermi/GT transport domains

This file defines the nonzero-state carrier and the domains of two transport
maps.  It does not assign a metric to a generic Lie algebra state or claim an
isometry/deformation result.  Concrete metric results belong to carriers that
actually define the relevant form, such as `InfoGeometry.Physics.TKKZorn`.
-/

namespace InfoGeometry.Physics

variable {R : Type*} [CommRing R]
variable {L : Type*} [LieRing L] [LieAlgebra R L]

/-- A projective state is a nonzero vector in the ambient Lie algebra. -/
structure TKKNuclearState (L : Type*) [Zero L] where
  state_vector : L
  is_projective_ray : state_vector ≠ 0

/-- Fermi transport by the adjoint action, restricted to nonzero outputs. -/
def fermi_operator (g0 : L) (ψ : TKKNuclearState L)
    (h_nonzero : ⁅g0, ψ.state_vector⁆ ≠ 0) : TKKNuclearState L :=
  ⟨⁅g0, ψ.state_vector⁆, h_nonzero⟩

/-- Gamow–Teller transport by a linear map, restricted to nonzero outputs. -/
def gamow_teller_operator (T : L →ₗ[R] L) (ψ : TKKNuclearState L)
    (h_nonzero : T ψ.state_vector ≠ 0) : TKKNuclearState L :=
  ⟨T ψ.state_vector, h_nonzero⟩

end InfoGeometry.Physics
