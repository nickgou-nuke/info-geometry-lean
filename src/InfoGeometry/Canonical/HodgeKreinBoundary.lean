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

import InfoGeometry.Canonical.HodgeKreinTriFacet
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Module.Equiv.Basic

/-!
# Hodge-Krein Boundary Harmonic Transport

This file extends the finite Hodge-Krein tri-facet algebra with the harmonic
kernel and boundary-transport statements used in the Krein/Hodge boundary
dictionary.  The exact, coexact, and harmonic projectors remain owned by
`HodgeKreinTriFacet`; this file only proves how harmonic zero-modes behave
under a conjugating boundary shear and under a symmetric adjoint pairing.

No manifold boundary, nilpotent Lie flow, cohomology theorem, or analytic Hodge
theorem is asserted here.  The boundary operator is an explicit conjugation by
a supplied linear equivalence.

## Audit Protocol Map

- **BUCKET 1: CLOSED FINITE THEOREMS**:
  - `harmonic_iff_P_harm_eq`: harmonic kernel membership is equivalent to
    being fixed by the harmonic projector, under `O^3 = O`.
  - `boundary_harmonic_transport`: harmonic zero-modes transport through a
    conjugated boundary operator.
  - `harmonic_orthogonal_exact`: harmonic vectors decouple from exact-sector
    projector images under an adjoint pairing.
  - `harmonic_orthogonal_coexact`: harmonic vectors decouple from coexact-sector
    projector images under an adjoint pairing.
- **BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES**:
  - The projector/fixed-point equivalence is conditional on the explicit cubic
    law `∀ x, O (O (O x)) = O x`.
  - The metric decoupling statements are conditional on the explicit
    self-adjointness and right-linearity hypotheses for `B`.
- **BUCKET 3: OPEN CLOSURE DEBT**:
  - None for this finite algebraic boundary-transport layer.
-/

namespace InfoGeometry.Canonical.HodgeKreinBoundary

open InfoGeometry.Canonical.HodgeKreinTriFacet

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Harmonic vectors are the kernel of the Hodge-Krein operator shadow. -/
def IsHarmonic (O : V →ₗ[ℝ] V) (x : V) : Prop :=
  O x = 0

/--
For an operator satisfying `O^3 = O`, the harmonic vectors are exactly the fixed
points of the harmonic projector `P_harm = I - O^2`.
-/
theorem harmonic_iff_P_harm_eq
    (O : V →ₗ[ℝ] V)
    (hO3 : ∀ x : V, O (O (O x)) = O x)
    (x : V) :
    IsHarmonic O x ↔ P_harm O x = x := by
  constructor
  · intro hx
    unfold IsHarmonic at hx
    unfold P_harm
    dsimp
    rw [hx, map_zero]
    abel
  · intro hx
    have hmap := congrArg O hx
    rw [O_P_harm O hO3 x] at hmap
    exact hmap.symm

/-- Boundary-localized operator obtained by conjugating `O` by a linear shear. -/
def O_bound (O : V →ₗ[ℝ] V) (N : V ≃ₗ[ℝ] V) : V →ₗ[ℝ] V :=
  N.toLinearMap.comp (O.comp N.symm.toLinearMap)

/--
Harmonic zero-modes are transported to harmonic zero-modes for the conjugated
boundary operator.
-/
theorem boundary_harmonic_transport
    (O : V →ₗ[ℝ] V)
    (N : V ≃ₗ[ℝ] V)
    (x : V)
    (hx : IsHarmonic O x) :
    IsHarmonic (O_bound O N) (N x) := by
  unfold IsHarmonic O_bound
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  change N (O (N.symm (N x))) = 0
  rw [N.symm_apply_apply x]
  rw [hx]
  exact N.map_zero

section Pairing

variable (O : V →ₗ[ℝ] V)
variable (B : V → V → ℝ)

/--
The harmonic kernel decouples from exact-sector projector images under a
self-adjoint Hodge-Krein operator shadow.
-/
theorem harmonic_orthogonal_exact
    (adjoint_O : ∀ x y, B (O x) y = B x (O y))
    (B_add_right : ∀ x y z, B x (y + z) = B x y + B x z)
    (B_smul_right : ∀ c x y, B x (c • y) = c * B x y)
    (B_zero_left : ∀ x, B 0 x = 0)
    (half : ℝ)
    (x y : V)
    (hx : IsHarmonic O x) :
    B x (P_ext O half y) = 0 := by
  unfold P_ext
  dsimp
  rw [B_smul_right half x (O (O y) + O y)]
  rw [B_add_right x (O (O y)) (O y)]
  have hO : ∀ z, B x (O z) = 0 := by
    intro z
    have h_adj : B x (O z) = B (O x) z := (adjoint_O x z).symm
    rw [h_adj, hx, B_zero_left z]
  rw [hO (O y), hO y]
  ring

/--
The harmonic kernel decouples from coexact-sector projector images under a
self-adjoint Hodge-Krein operator shadow.
-/
theorem harmonic_orthogonal_coexact
    (adjoint_O : ∀ x y, B (O x) y = B x (O y))
    (B_sub_right : ∀ x y z, B x (y - z) = B x y - B x z)
    (B_smul_right : ∀ c x y, B x (c • y) = c * B x y)
    (B_zero_left : ∀ x, B 0 x = 0)
    (half : ℝ)
    (x y : V)
    (hx : IsHarmonic O x) :
    B x (P_coext O half y) = 0 := by
  unfold P_coext
  dsimp
  rw [B_smul_right half x (O (O y) - O y)]
  rw [B_sub_right x (O (O y)) (O y)]
  have hO : ∀ z, B x (O z) = 0 := by
    intro z
    have h_adj : B x (O z) = B (O x) z := (adjoint_O x z).symm
    rw [h_adj, hx, B_zero_left z]
  rw [hO (O y), hO y]
  ring

end Pairing

end InfoGeometry.Canonical.HodgeKreinBoundary
