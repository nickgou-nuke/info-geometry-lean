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
# Clifford Infinite Split Algebra

This file packages the finite algebraic core of a split chirality operator.
An involutive real linear map `omega` gives the two Majorana-Weyl projector
shadows `(1 ± omega) / 2`.  An odd Dirac operator `D`, represented by the
anti-commutation rule `D omega = - omega D`, exchanges the two chiral sectors.

This is an abstract linear-algebra layer.  It does not construct `Cl(5,5)`,
an infinite tensor colimit, a spinor representation, or a geometric Dirac
operator.

## Audit Protocol Map

- **BUCKET 1: CLOSED FINITE THEOREMS**:
  - `P_plus`, `P_minus`, `omega_comp_eq_id`.
  - `P_plus_add_P_minus`, `omega_P_plus`, `omega_P_minus`.
  - `P_plus_idempotent`, `P_minus_idempotent`.
  - `P_plus_P_minus_ortho`, `P_minus_P_plus_ortho`.
  - `D_P_plus_eq_P_minus_D`, `D_P_minus_eq_P_plus_D`.
  - `D_maps_plus_to_minus_ortho`, `D_maps_minus_to_plus_ortho`.
- **BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES**:
  - Projector laws are conditional on `half + half = 1` and `omega^2 = id`.
  - Dirac sector exchange laws are conditional on the explicit oddness rule.
- **BUCKET 3: OPEN CLOSURE DEBT**:
  - None for this abstract endomorphism-level chirality layer.
-/

namespace InfoGeometry.Canonical.CliffordInfiniteSplitAlgebra

open InfoGeometry.Canonical.HodgeStarSelfDualAlgebra

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The positive chirality projector `(1 + omega) / 2`. -/
abbrev P_plus (half : ℝ) (omega : V →ₗ[ℝ] V) : V →ₗ[ℝ] V :=
  HodgeStarSelfDualAlgebra.P_plus half omega

/-- The negative chirality projector `(1 - omega) / 2`. -/
abbrev P_minus (half : ℝ) (omega : V →ₗ[ℝ] V) : V →ₗ[ℝ] V :=
  HodgeStarSelfDualAlgebra.P_minus half omega

/-- Pointwise involutivity of `omega` as a linear-map square law. -/
theorem omega_comp_eq_id
    (omega : V →ₗ[ℝ] V)
    (omega_sq : ∀ x : V, omega (omega x) = x) :
    omega.comp omega = LinearMap.id := by
  ext x
  exact omega_sq x

/-- Scalar half of a doubled vector is the vector. -/
theorem half_smul_add_self
    (half : ℝ)
    (h_half : half + half = 1)
    (x : V) :
    half • (x + x) = x := by
  rw [smul_add, ← add_smul, h_half, one_smul]

/-- Scalar half of `x - (-x)` is the vector. -/
theorem half_smul_sub_neg_self
    (half : ℝ)
    (h_half : half + half = 1)
    (x : V) :
    half • (x - -x) = x := by
  have h : x - -x = x + x := by abel
  rw [h]
  exact half_smul_add_self half h_half x

/-- The two chirality projectors reconstruct the original vector. -/
theorem P_plus_add_P_minus
    (half : ℝ)
    (h_half : half + half = 1)
    (omega : V →ₗ[ℝ] V)
    (x : V) :
    P_plus half omega x + P_minus half omega x = x := by
  rw [HodgeStarSelfDualAlgebra.P_plus_apply, HodgeStarSelfDualAlgebra.P_minus_apply]
  rw [smul_add, smul_sub]
  have h :
      half • x + half • omega x + (half • x - half • omega x) =
        half • x + half • x := by
    abel
  rw [h, ← add_smul, h_half, one_smul]

/-- The positive projector lands in the `+1` eigensector of `omega`. -/
theorem omega_P_plus
    (half : ℝ)
    (omega : V →ₗ[ℝ] V)
    (omega_sq : ∀ x : V, omega (omega x) = x)
    (x : V) :
    omega (P_plus half omega x) = P_plus half omega x :=
  HodgeStarSelfDualAlgebra.S_P_plus half omega (omega_comp_eq_id omega omega_sq) x

/-- The negative projector lands in the `-1` eigensector of `omega`. -/
theorem omega_P_minus
    (half : ℝ)
    (omega : V →ₗ[ℝ] V)
    (omega_sq : ∀ x : V, omega (omega x) = x)
    (x : V) :
    omega (P_minus half omega x) = -P_minus half omega x :=
  HodgeStarSelfDualAlgebra.S_P_minus half omega (omega_comp_eq_id omega omega_sq) x

/-- The positive chirality projector is idempotent. -/
theorem P_plus_idempotent
    (half : ℝ)
    (h_half : half + half = 1)
    (omega : V →ₗ[ℝ] V)
    (omega_sq : ∀ x : V, omega (omega x) = x)
    (x : V) :
    P_plus half omega (P_plus half omega x) = P_plus half omega x := by
  rw [HodgeStarSelfDualAlgebra.P_plus_apply]
  rw [omega_P_plus half omega omega_sq x]
  exact half_smul_add_self half h_half (P_plus half omega x)

/-- The negative chirality projector is idempotent. -/
theorem P_minus_idempotent
    (half : ℝ)
    (h_half : half + half = 1)
    (omega : V →ₗ[ℝ] V)
    (omega_sq : ∀ x : V, omega (omega x) = x)
    (x : V) :
    P_minus half omega (P_minus half omega x) = P_minus half omega x := by
  rw [HodgeStarSelfDualAlgebra.P_minus_apply]
  rw [omega_P_minus half omega omega_sq x]
  exact half_smul_sub_neg_self half h_half (P_minus half omega x)

/-- Positive projection annihilates the negative chirality sector. -/
theorem P_plus_P_minus_ortho
    (half : ℝ)
    (omega : V →ₗ[ℝ] V)
    (omega_sq : ∀ x : V, omega (omega x) = x)
    (x : V) :
    P_plus half omega (P_minus half omega x) = 0 := by
  rw [HodgeStarSelfDualAlgebra.P_plus_apply]
  rw [omega_P_minus half omega omega_sq x, add_neg_cancel, smul_zero]

/-- Negative projection annihilates the positive chirality sector. -/
theorem P_minus_P_plus_ortho
    (half : ℝ)
    (omega : V →ₗ[ℝ] V)
    (omega_sq : ∀ x : V, omega (omega x) = x)
    (x : V) :
    P_minus half omega (P_plus half omega x) = 0 := by
  rw [HodgeStarSelfDualAlgebra.P_minus_apply]
  rw [omega_P_plus half omega omega_sq x, sub_self, smul_zero]

/-- An odd Dirac operator maps positive chirality to negative chirality. -/
theorem D_P_plus_eq_P_minus_D
    (half : ℝ)
    (omega D : V →ₗ[ℝ] V)
    (D_omega_anti_comm : ∀ x : V, D (omega x) = -omega (D x))
    (x : V) :
    D (P_plus half omega x) = P_minus half omega (D x) := by
  rw [HodgeStarSelfDualAlgebra.P_plus_apply, HodgeStarSelfDualAlgebra.P_minus_apply]
  rw [map_smul, map_add, D_omega_anti_comm x]
  simp [sub_eq_add_neg]

/-- An odd Dirac operator maps negative chirality to positive chirality. -/
theorem D_P_minus_eq_P_plus_D
    (half : ℝ)
    (omega D : V →ₗ[ℝ] V)
    (D_omega_anti_comm : ∀ x : V, D (omega x) = -omega (D x))
    (x : V) :
    D (P_minus half omega x) = P_plus half omega (D x) := by
  rw [HodgeStarSelfDualAlgebra.P_minus_apply, HodgeStarSelfDualAlgebra.P_plus_apply]
  rw [map_smul, map_sub, D_omega_anti_comm x, sub_neg_eq_add]

/-- The positive projection of a Dirac image of a positive spinor vanishes. -/
theorem D_maps_plus_to_minus_ortho
    (half : ℝ)
    (omega D : V →ₗ[ℝ] V)
    (omega_sq : ∀ x : V, omega (omega x) = x)
    (D_omega_anti_comm : ∀ x : V, D (omega x) = -omega (D x))
    (x : V) :
    P_plus half omega (D (P_plus half omega x)) = 0 := by
  rw [D_P_plus_eq_P_minus_D half omega D D_omega_anti_comm x]
  exact P_plus_P_minus_ortho half omega omega_sq (D x)

/-- The negative projection of a Dirac image of a negative spinor vanishes. -/
theorem D_maps_minus_to_plus_ortho
    (half : ℝ)
    (omega D : V →ₗ[ℝ] V)
    (omega_sq : ∀ x : V, omega (omega x) = x)
    (D_omega_anti_comm : ∀ x : V, D (omega x) = -omega (D x))
    (x : V) :
    P_minus half omega (D (P_minus half omega x)) = 0 := by
  rw [D_P_minus_eq_P_plus_D half omega D D_omega_anti_comm x]
  exact P_minus_P_plus_ortho half omega omega_sq (D x)

end InfoGeometry.Canonical.CliffordInfiniteSplitAlgebra
