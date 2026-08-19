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

import InfoGeometry.Canonical.HodgeStarSelfDualAlgebra

/-!
# Krein Fundamental-Symmetry Projectors

This file exposes the Krein-space reading of the involutive self-adjoint split
already proved in `HodgeStarSelfDualAlgebra`.  A fundamental symmetry `J`
determines the positive and negative projectors
`K_plus = half • (id + J)` and `K_minus = half • (id - J)`.  Under the explicit
normalization `half + half = 1`, these projectors reconstruct the identity and
are idempotent.  If `J` is self-adjoint for a symmetric pairing, the two sectors
are mutually orthogonal.

No analytic completeness, spectral theorem, or construction of a particular
Krein space is asserted here; this is the closed algebraic projector layer.

## Audit Protocol Map

- **BUCKET 1: CLOSED FINITE THEOREMS**:
  - `K_plus_add_K_minus`: identity reconstruction from the two sectors.
  - `J_K_plus`, `J_K_minus`: eigensector isolation for the fundamental
    symmetry.
  - `K_plus_idempotent`, `K_minus_idempotent`: projector idempotence.
  - `indef_inner_neg_right`: right negation for a symmetric left-linear
    pairing.
  - `K_plus_K_minus_orthogonal`: orthogonality of positive and negative
    sectors.
- **BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES**:
  - The orthogonality theorem is conditional on the explicitly named
    involution, self-adjointness, symmetry, and scalar-linearity hypotheses.
- **BUCKET 3: OPEN CLOSURE DEBT**:
  - None for this algebraic projector layer.
-/

namespace InfoGeometry.Krein.FundamentalSymmetryProjectors

open InfoGeometry.Canonical.HodgeStarSelfDualAlgebra

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The positive Krein eigensector projector of a fundamental symmetry. -/
def K_plus (half : ℝ) (J : V →ₗ[ℝ] V) : V →ₗ[ℝ] V :=
  P_plus half J

/-- The negative Krein eigensector projector of a fundamental symmetry. -/
def K_minus (half : ℝ) (J : V →ₗ[ℝ] V) : V →ₗ[ℝ] V :=
  P_minus half J

/-- Pointwise form of the positive Krein eigensector projector. -/
@[simp]
theorem K_plus_apply (half : ℝ) (J : V →ₗ[ℝ] V) (x : V) :
    K_plus half J x = half • (x + J x) :=
  rfl

/-- Pointwise form of the negative Krein eigensector projector. -/
@[simp]
theorem K_minus_apply (half : ℝ) (J : V →ₗ[ℝ] V) (x : V) :
    K_minus half J x = half • (x - J x) :=
  rfl

/-- The two Krein eigensector projectors reconstruct the original vector. -/
theorem K_plus_add_K_minus
    (J : V →ₗ[ℝ] V)
    (half : ℝ)
    (hhalf : half + half = 1)
    (x : V) :
    K_plus half J x + K_minus half J x = x := by
  dsimp [K_plus, K_minus, P_plus, P_minus]
  rw [smul_add, smul_sub]
  have hcombine :
      half • x + half • J x + (half • x - half • J x) = half • x + half • x := by
    abel
  rw [hcombine, ← add_smul, hhalf, one_smul]

/-- `K_plus` lands in the `+1` eigensector of the fundamental symmetry. -/
theorem J_K_plus
    (J : V →ₗ[ℝ] V)
    (hJ2 : J.comp J = LinearMap.id)
    (half : ℝ)
    (x : V) :
    J (K_plus half J x) = K_plus half J x :=
  S_P_plus half J hJ2 x

/-- `K_minus` lands in the `-1` eigensector of the fundamental symmetry. -/
theorem J_K_minus
    (J : V →ₗ[ℝ] V)
    (hJ2 : J.comp J = LinearMap.id)
    (half : ℝ)
    (x : V) :
    J (K_minus half J x) = -K_minus half J x :=
  S_P_minus half J hJ2 x

/-- The positive Krein eigensector projector is idempotent. -/
theorem K_plus_idempotent
    (J : V →ₗ[ℝ] V)
    (hJ2 : J.comp J = LinearMap.id)
    (half : ℝ)
    (hhalf : half + half = 1)
    (x : V) :
    K_plus half J (K_plus half J x) = K_plus half J x := by
  rw [K_plus_apply, J_K_plus J hJ2 half x]
  rw [smul_add, ← add_smul, hhalf, one_smul]

/-- The negative Krein eigensector projector is idempotent. -/
theorem K_minus_idempotent
    (J : V →ₗ[ℝ] V)
    (hJ2 : J.comp J = LinearMap.id)
    (half : ℝ)
    (hhalf : half + half = 1)
    (x : V) :
    K_minus half J (K_minus half J x) = K_minus half J x := by
  rw [K_minus_apply, J_K_minus J hJ2 half x]
  have hsub : K_minus half J x - -K_minus half J x = K_minus half J x + K_minus half J x := by
    abel
  rw [hsub, smul_add, ← add_smul, hhalf, one_smul]

/-- The positive Krein projector is idempotent as a linear map. -/
theorem K_plus_comp_self
    (J : V →ₗ[ℝ] V)
    (hJ2 : J.comp J = LinearMap.id)
    (half : ℝ)
    (hhalf : half + half = 1) :
    (K_plus half J).comp (K_plus half J) = K_plus half J := by
  apply LinearMap.ext
  intro x
  exact K_plus_idempotent J hJ2 half hhalf x

/-- The negative Krein projector is idempotent as a linear map. -/
theorem K_minus_comp_self
    (J : V →ₗ[ℝ] V)
    (hJ2 : J.comp J = LinearMap.id)
    (half : ℝ)
    (hhalf : half + half = 1) :
    (K_minus half J).comp (K_minus half J) = K_minus half J := by
  apply LinearMap.ext
  intro x
  exact K_minus_idempotent J hJ2 half hhalf x

/-- The two eigensector projectors annihilate each other pointwise. -/
theorem K_plus_K_minus_zero
    (J : V →ₗ[ℝ] V)
    (hJ2 : J.comp J = LinearMap.id)
    (half : ℝ)
    (x : V) :
    K_plus half J (K_minus half J x) = 0 := by
  rw [K_plus_apply, J_K_minus J hJ2 half x]
  have hcancel : K_minus half J x + -K_minus half J x = 0 := by
    exact add_neg_cancel _
  rw [hcancel, smul_zero]

theorem K_minus_K_plus_zero
    (J : V →ₗ[ℝ] V)
    (hJ2 : J.comp J = LinearMap.id)
    (half : ℝ)
    (x : V) :
    K_minus half J (K_plus half J x) = 0 := by
  rw [K_minus_apply, J_K_plus J hJ2 half x]
  have hcancel : K_plus half J x - K_plus half J x = 0 := by
    exact sub_self _
  rw [hcancel, smul_zero]

theorem K_plus_add_K_minus_eq_id
    (J : V →ₗ[ℝ] V)
    (half : ℝ)
    (hhalf : half + half = 1) :
    K_plus half J + K_minus half J = LinearMap.id := by
  apply LinearMap.ext
  intro x
  simpa using K_plus_add_K_minus J half hhalf x

theorem K_plus_comp_K_minus_eq_zero
    (J : V →ₗ[ℝ] V)
    (hJ2 : J.comp J = LinearMap.id)
    (half : ℝ) :
    (K_plus half J).comp (K_minus half J) = 0 := by
  apply LinearMap.ext
  intro x
  simpa using K_plus_K_minus_zero J hJ2 half x

theorem K_minus_comp_K_plus_eq_zero
    (J : V →ₗ[ℝ] V)
    (hJ2 : J.comp J = LinearMap.id)
    (half : ℝ) :
    (K_minus half J).comp (K_plus half J) = 0 := by
  apply LinearMap.ext
  intro x
  simpa using K_minus_K_plus_zero J hJ2 half x

/-- Right negation exits a symmetric left-linear indefinite pairing. -/
theorem indef_inner_neg_right
    (indefInner : V → V → ℝ)
    (indefInner_comm : ∀ x y, indefInner x y = indefInner y x)
    (indefInner_smul_left : ∀ c x y, indefInner (c • x) y = c * indefInner x y)
    (x y : V) :
    indefInner x (-y) = -indefInner x y :=
  B_neg_right indefInner indefInner_comm indefInner_smul_left x y

/--
The positive and negative Krein eigensector projectors are orthogonal under any
symmetric pairing for which the fundamental symmetry is self-adjoint.
-/
theorem K_plus_K_minus_orthogonal
    (indefInner : V → V → ℝ)
    (indefInner_comm : ∀ x y, indefInner x y = indefInner y x)
    (indefInner_smul_left : ∀ c x y, indefInner (c • x) y = c * indefInner x y)
    (J : V →ₗ[ℝ] V)
    (hJ2 : J.comp J = LinearMap.id)
    (hJadj : ∀ x y, indefInner (J x) y = indefInner x (J y))
    (half : ℝ)
    (x y : V) :
    indefInner (K_plus half J x) (K_minus half J y) = 0 :=
  self_dual_anti_self_dual_orthogonal
    indefInner indefInner_comm indefInner_smul_left J hJ2 hJadj half x y

/-- The reverse order of the two Krein eigensectors is orthogonal as well. -/
theorem K_minus_K_plus_orthogonal
    (indefInner : V → V → ℝ)
    (indefInner_comm : ∀ x y, indefInner x y = indefInner y x)
    (indefInner_smul_left : ∀ c x y, indefInner (c • x) y = c * indefInner x y)
    (J : V →ₗ[ℝ] V)
    (hJ2 : J.comp J = LinearMap.id)
    (hJadj : ∀ x y, indefInner (J x) y = indefInner x (J y))
    (half : ℝ)
    (x y : V) :
    indefInner (K_minus half J x) (K_plus half J y) = 0 := by
  calc
    indefInner (K_minus half J x) (K_plus half J y) =
        indefInner (K_plus half J y) (K_minus half J x) :=
      indefInner_comm _ _
    _ = 0 := K_plus_K_minus_orthogonal
      indefInner indefInner_comm indefInner_smul_left J hJ2 hJadj half y x

end InfoGeometry.Krein.FundamentalSymmetryProjectors
