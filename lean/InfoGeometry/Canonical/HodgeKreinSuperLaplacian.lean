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

import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-!
# Hodge-Krein Super-Laplacian Endomorphism Algebra

This file proves the rational endomorphism-level form of the Hodge-Krein
tri-facet projector calculus.  Given a linear operator `O` over a rational
vector space with cubic law `O^3 = O`, the exact, coexact, harmonic, core,
and nilpotent projectors are linear maps satisfying reconstruction,
idempotence, mutual annihilation, and the Drazin-Hodge core/nilpotent split.

This is a finite algebraic theorem owner.  It does not construct a geometric
Hodge Laplacian, differential forms, Krein signatures, a Drazin inverse, or an
analytic Hodge decomposition theorem.

## Audit Protocol Map

- **BUCKET 1: CLOSED FINITE THEOREMS**:
  - `P_ext`, `P_coext`, `P_harm`, `P_core`, `P_nil`.
  - `tri_facet_sum`, `O_comp_O_comp_O`, `O_P_ext`, `O_P_coext`,
    `O_P_harm`.
  - `P_ext_idempotent`, `P_coext_idempotent`, `P_harm_idempotent`.
  - `P_ext_P_coext_orthogonal`, `P_coext_P_ext_orthogonal`,
    `P_ext_P_harm_orthogonal`, `P_harm_P_ext_orthogonal`,
    `P_coext_P_harm_orthogonal`, `P_harm_P_coext_orthogonal`.
  - `P_ext_add_P_coext_eq_P_core`, `P_core_eq_P_ext_add_P_coext`,
    `drazin_hodge_split`, `P_core_idempotent`, `P_nil_idempotent`,
    `P_core_P_nil`, `P_nil_P_core`, `O_nilpotent_on_P_nil`.
- **BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES**:
  - The operator laws that use eigensector behavior are conditional on the
    explicit cubic law `O^3 = O`.
- **BUCKET 3: OPEN CLOSURE DEBT**:
  - None for this rational endomorphism-level algebraic layer.
-/

namespace HodgeKreinSuperLaplacian

variable {E : Type*} [AddCommGroup E] [Module ℚ E]

/-- The exact sector projector `P_ext = 1/2 * (O^2 + O)`. -/
def P_ext (O : E →ₗ[ℚ] E) : E →ₗ[ℚ] E :=
  (1 / 2 : ℚ) • (O.comp O + O)

/-- The coexact sector projector `P_coext = 1/2 * (O^2 - O)`. -/
def P_coext (O : E →ₗ[ℚ] E) : E →ₗ[ℚ] E :=
  (1 / 2 : ℚ) • (O.comp O - O)

/-- The harmonic sector projector `P_harm = I - O^2`. -/
def P_harm (O : E →ₗ[ℚ] E) : E →ₗ[ℚ] E :=
  (LinearMap.id : E →ₗ[ℚ] E) - O.comp O

/-- The Drazin-Hodge core projector `P_core = O^2`. -/
def P_core (O : E →ₗ[ℚ] E) : E →ₗ[ℚ] E :=
  O.comp O

/-- The Drazin-Hodge nilpotent projector `P_nil = I - O^2`. -/
def P_nil (O : E →ₗ[ℚ] E) : E →ₗ[ℚ] E :=
  (LinearMap.id : E →ₗ[ℚ] E) - O.comp O

@[simp]
theorem P_ext_apply (O : E →ₗ[ℚ] E) (x : E) :
    P_ext O x = (1 / 2 : ℚ) • (O (O x) + O x) :=
  rfl

@[simp]
theorem P_coext_apply (O : E →ₗ[ℚ] E) (x : E) :
    P_coext O x = (1 / 2 : ℚ) • (O (O x) - O x) :=
  rfl

@[simp]
theorem P_harm_apply (O : E →ₗ[ℚ] E) (x : E) :
    P_harm O x = x - O (O x) :=
  rfl

@[simp]
theorem P_core_apply (O : E →ₗ[ℚ] E) (x : E) :
    P_core O x = O (O x) :=
  rfl

@[simp]
theorem P_nil_apply (O : E →ₗ[ℚ] E) (x : E) :
    P_nil O x = x - O (O x) :=
  rfl

/-- Scalar half of a doubled vector is the vector. -/
theorem half_smul_add_self (x : E) :
    (1 / 2 : ℚ) • (x + x) = x := by
  module

/-- Scalar half of `x - (-x)` is the vector. -/
theorem half_smul_sub_neg_self (x : E) :
    (1 / 2 : ℚ) • (x - -x) = x := by
  module

/-- The two half-scaled `a ± b` components recover `a`. -/
theorem half_smul_add_sub_eq_left (a b : E) :
    (1 / 2 : ℚ) • (a + b) + (1 / 2 : ℚ) • (a - b) = a := by
  module

/-- The tri-facet components sum to the identity map. -/
theorem tri_facet_sum (O : E →ₗ[ℚ] E) :
    P_ext O + P_coext O + P_harm O = (LinearMap.id : E →ₗ[ℚ] E) := by
  ext x
  change
    (1 / 2 : ℚ) • (O (O x) + O x) +
          (1 / 2 : ℚ) • (O (O x) - O x) +
        (x - O (O x)) = x
  rw [half_smul_add_sub_eq_left (O (O x)) (O x)]
  abel

/-- Elementwise form of the cubic law. -/
theorem O_comp_O_comp_O
    (O : E →ₗ[ℚ] E)
    (hO3 : O.comp (O.comp O) = O)
    (x : E) :
    O (O (O x)) = O x := by
  have h := congrArg (fun T : E →ₗ[ℚ] E => T x) hO3
  simpa [LinearMap.comp_apply] using h

/-- The exact projector lands in the `+1` eigensector of `O`. -/
theorem O_P_ext
    (O : E →ₗ[ℚ] E)
    (hO3 : O.comp (O.comp O) = O)
    (x : E) :
    O (P_ext O x) = P_ext O x := by
  change
    O ((1 / 2 : ℚ) • (O (O x) + O x)) =
      (1 / 2 : ℚ) • (O (O x) + O x)
  rw [map_smul, map_add, O_comp_O_comp_O O hO3 x, add_comm]

/-- The coexact projector lands in the `-1` eigensector of `O`. -/
theorem O_P_coext
    (O : E →ₗ[ℚ] E)
    (hO3 : O.comp (O.comp O) = O)
    (x : E) :
    O (P_coext O x) = -P_coext O x := by
  change
    O ((1 / 2 : ℚ) • (O (O x) - O x)) =
      -((1 / 2 : ℚ) • (O (O x) - O x))
  rw [map_smul, map_sub, O_comp_O_comp_O O hO3 x]
  have h : O x - O (O x) = -(O (O x) - O x) := by
    abel
  rw [h, smul_neg]

/-- The harmonic projector lands in the kernel of `O`. -/
theorem O_P_harm
    (O : E →ₗ[ℚ] E)
    (hO3 : O.comp (O.comp O) = O)
    (x : E) :
    O (P_harm O x) = 0 := by
  change O (x - O (O x)) = 0
  rw [map_sub, O_comp_O_comp_O O hO3 x]
  abel

/-- The exact projector is fixed by `O^2`. -/
theorem O_O_P_ext
    (O : E →ₗ[ℚ] E)
    (hO3 : O.comp (O.comp O) = O)
    (x : E) :
    O (O (P_ext O x)) = P_ext O x := by
  rw [O_P_ext O hO3 x, O_P_ext O hO3 x]

/-- The coexact projector is fixed by `O^2`. -/
theorem O_O_P_coext
    (O : E →ₗ[ℚ] E)
    (hO3 : O.comp (O.comp O) = O)
    (x : E) :
    O (O (P_coext O x)) = P_coext O x := by
  rw [O_P_coext O hO3 x, map_neg, O_P_coext O hO3 x]
  abel

/-- The harmonic projector is annihilated by `O^2`. -/
theorem O_O_P_harm
    (O : E →ₗ[ℚ] E)
    (hO3 : O.comp (O.comp O) = O)
    (x : E) :
    O (O (P_harm O x)) = 0 := by
  rw [O_P_harm O hO3 x, map_zero]

/-- The exact projector is idempotent. -/
theorem P_ext_idempotent
    (O : E →ₗ[ℚ] E)
    (hO3 : O.comp (O.comp O) = O) :
    (P_ext O).comp (P_ext O) = P_ext O := by
  ext x
  change
    (1 / 2 : ℚ) • (O (O (P_ext O x)) + O (P_ext O x)) =
      P_ext O x
  rw [O_O_P_ext O hO3 x, O_P_ext O hO3 x]
  exact half_smul_add_self (P_ext O x)

/-- The coexact projector is idempotent. -/
theorem P_coext_idempotent
    (O : E →ₗ[ℚ] E)
    (hO3 : O.comp (O.comp O) = O) :
    (P_coext O).comp (P_coext O) = P_coext O := by
  ext x
  change
    (1 / 2 : ℚ) • (O (O (P_coext O x)) - O (P_coext O x)) =
      P_coext O x
  rw [O_O_P_coext O hO3 x, O_P_coext O hO3 x]
  exact half_smul_sub_neg_self (P_coext O x)

/-- The harmonic projector is idempotent. -/
theorem P_harm_idempotent
    (O : E →ₗ[ℚ] E)
    (hO3 : O.comp (O.comp O) = O) :
    (P_harm O).comp (P_harm O) = P_harm O := by
  ext x
  change P_harm O x - O (O (P_harm O x)) = P_harm O x
  rw [O_O_P_harm O hO3 x]
  abel

/-- Exact projection annihilates the coexact sector. -/
theorem P_ext_P_coext_orthogonal
    (O : E →ₗ[ℚ] E)
    (hO3 : O.comp (O.comp O) = O) :
    (P_ext O).comp (P_coext O) = 0 := by
  ext x
  change
    (1 / 2 : ℚ) • (O (O (P_coext O x)) + O (P_coext O x)) = 0
  rw [O_O_P_coext O hO3 x, O_P_coext O hO3 x, add_neg_cancel, smul_zero]

/-- Coexact projection annihilates the exact sector. -/
theorem P_coext_P_ext_orthogonal
    (O : E →ₗ[ℚ] E)
    (hO3 : O.comp (O.comp O) = O) :
    (P_coext O).comp (P_ext O) = 0 := by
  ext x
  change
    (1 / 2 : ℚ) • (O (O (P_ext O x)) - O (P_ext O x)) = 0
  rw [O_O_P_ext O hO3 x, O_P_ext O hO3 x, sub_self, smul_zero]

/-- Exact projection annihilates the harmonic sector. -/
theorem P_ext_P_harm_orthogonal
    (O : E →ₗ[ℚ] E)
    (hO3 : O.comp (O.comp O) = O) :
    (P_ext O).comp (P_harm O) = 0 := by
  ext x
  change
    (1 / 2 : ℚ) • (O (O (P_harm O x)) + O (P_harm O x)) = 0
  rw [O_O_P_harm O hO3 x, O_P_harm O hO3 x, add_zero, smul_zero]

/-- Harmonic projection annihilates the exact sector. -/
theorem P_harm_P_ext_orthogonal
    (O : E →ₗ[ℚ] E)
    (hO3 : O.comp (O.comp O) = O) :
    (P_harm O).comp (P_ext O) = 0 := by
  ext x
  change P_ext O x - O (O (P_ext O x)) = 0
  rw [O_O_P_ext O hO3 x, sub_self]

/-- Coexact projection annihilates the harmonic sector. -/
theorem P_coext_P_harm_orthogonal
    (O : E →ₗ[ℚ] E)
    (hO3 : O.comp (O.comp O) = O) :
    (P_coext O).comp (P_harm O) = 0 := by
  ext x
  change
    (1 / 2 : ℚ) • (O (O (P_harm O x)) - O (P_harm O x)) = 0
  rw [O_O_P_harm O hO3 x, O_P_harm O hO3 x, sub_zero, smul_zero]

/-- Harmonic projection annihilates the coexact sector. -/
theorem P_harm_P_coext_orthogonal
    (O : E →ₗ[ℚ] E)
    (hO3 : O.comp (O.comp O) = O) :
    (P_harm O).comp (P_coext O) = 0 := by
  ext x
  change P_coext O x - O (O (P_coext O x)) = 0
  rw [O_O_P_coext O hO3 x, sub_self]

/-- Exact plus coexact equals the compact core `O^2`. -/
theorem P_ext_add_P_coext_eq_P_core (O : E →ₗ[ℚ] E) :
    P_ext O + P_coext O = P_core O := by
  ext x
  change
    (1 / 2 : ℚ) • (O (O x) + O x) +
        (1 / 2 : ℚ) • (O (O x) - O x) =
      O (O x)
  exact half_smul_add_sub_eq_left (O (O x)) (O x)

/-- The compact core is exact plus coexact. -/
theorem P_core_eq_P_ext_add_P_coext (O : E →ₗ[ℚ] E) :
    P_core O = P_ext O + P_coext O :=
  (P_ext_add_P_coext_eq_P_core O).symm

/-- The core and nilpotent projectors sum to the identity map. -/
theorem drazin_hodge_split (O : E →ₗ[ℚ] E) :
    P_core O + P_nil O = (LinearMap.id : E →ₗ[ℚ] E) := by
  ext x
  change O (O x) + (x - O (O x)) = x
  abel

/-- The core projector is idempotent. -/
theorem P_core_idempotent
    (O : E →ₗ[ℚ] E)
    (hO3 : O.comp (O.comp O) = O) :
    (P_core O).comp (P_core O) = P_core O := by
  ext x
  change O (O (O (O x))) = O (O x)
  exact O_comp_O_comp_O O hO3 (O x)

/-- The nilpotent projector is idempotent. -/
theorem P_nil_idempotent
    (O : E →ₗ[ℚ] E)
    (hO3 : O.comp (O.comp O) = O) :
    (P_nil O).comp (P_nil O) = P_nil O := by
  ext x
  change P_nil O x - O (O (P_nil O x)) = P_nil O x
  have hnil : O (P_nil O x) = 0 := by
    change O (x - O (O x)) = 0
    rw [map_sub, O_comp_O_comp_O O hO3 x]
    abel
  rw [hnil, map_zero]
  abel

/-- The core projection annihilates the nilpotent sector. -/
theorem P_core_P_nil
    (O : E →ₗ[ℚ] E)
    (hO3 : O.comp (O.comp O) = O) :
    (P_core O).comp (P_nil O) = 0 := by
  ext x
  change O (O (x - O (O x))) = 0
  rw [map_sub, O_comp_O_comp_O O hO3 x]
  rw [sub_self, map_zero]

/-- The nilpotent projection annihilates the core sector. -/
theorem P_nil_P_core
    (O : E →ₗ[ℚ] E)
    (hO3 : O.comp (O.comp O) = O) :
    (P_nil O).comp (P_core O) = 0 := by
  ext x
  change O (O x) - O (O (O (O x))) = 0
  rw [O_comp_O_comp_O O hO3 (O x), sub_self]

/-- The nilpotent sector is contained in the kernel of `O`. -/
theorem O_nilpotent_on_P_nil
    (O : E →ₗ[ℚ] E)
    (hO3 : O.comp (O.comp O) = O)
    (x : E) :
    O (P_nil O x) = 0 := by
  change O (x - O (O x)) = 0
  rw [map_sub, O_comp_O_comp_O O hO3 x]
  abel

end HodgeKreinSuperLaplacian
