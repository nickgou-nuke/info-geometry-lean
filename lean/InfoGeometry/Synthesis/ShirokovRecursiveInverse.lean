/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import InfoGeometry.Synthesis.ShirokovCliffordTraceDetInverseBridge

/-!
# Basis-free Shirokov inverse: recursive Faddeev–LeVerrier construction

This module adds the **recursive** (Faddeev–LeVerrier / Shirokov) construction of the
coordinate-free determinant and inverse.  It is complementary to the closed-form
involution formulas in `ShirokovCliffordTraceDetInverseBridge`.

Scope of what is proved here, stated explicitly:

* **Proved, representation-free:** the step sequence `shirokovSequence` and its two
  projections `shirokovU`, `shirokovC` are defined over an arbitrary `R`-algebra `A`
  using only the geometric product, the algebra map of scalars, and an arbitrary
  grade-0 readout `φ : A → R`.  No basis, matrix representation, or grading is used.
* **Proved, concrete:** for the concrete `Cl(1,1) ≅ M₂(ℝ)` owner with
  `N = 2` and `φ = cl11ShirokovTrace = ⟨·⟩₀`, the recursion is proved to produce
  `c₁ = tr`, `U₂ = -det · 1`, `c₂ = -det`, the determinant readout
  `(-1)^(N-1) c_N = det`, the adjugate `U₁ - c₁ = -adj`, and hence a genuine
  two-sided inverse `(U₁ - c₁) / c_N` whenever `det ≠ 0`.
* **Not asserted here:** closed forms for `n = 3, 4, 5, 7` or the general-`n`
  convergence/correctness of the recursion.  Those require a Cayley–Hamilton
  hypothesis for the ambient algebra and are left to separate owners.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Synthesis.ShirokovRecursiveInverse

variable {R A : Type*} [Field R] [Ring A] [Algebra R A]

/--
The Shirokov step sequence. Index `k` corresponds to the `(k+1)`-st pair
`(U_{k+1}, c_{k+1})` of the Faddeev–LeVerrier recursion:

```
U₁ = a,                    c₁ = N φ(a)
U_{k+1} = a (U_k - c_k),   c_{k+1} = (N / (k+2)) φ(U_{k+1})
```

Only the algebra product, the scalar embedding and the grade-0 readout `φ` occur.
-/
def shirokovSequence (φ : A → R) (N : ℕ) (a : A) : ℕ → A × R
  | 0 => (a, (N : R) * φ a)
  | k + 1 =>
      let p := shirokovSequence φ N a k
      let u := a * (p.1 - algebraMap R A p.2)
      (u, ((N : R) / (k + 2 : R)) * φ u)

/-- The `U` (multivector) component of the Shirokov sequence. -/
def shirokovU (φ : A → R) (N : ℕ) (a : A) (k : ℕ) : A :=
  (shirokovSequence φ N a k).1

/-- The `c` (scalar) component of the Shirokov sequence. -/
def shirokovC (φ : A → R) (N : ℕ) (a : A) (k : ℕ) : R :=
  (shirokovSequence φ N a k).2

@[simp] theorem shirokovU_zero (φ : A → R) (N : ℕ) (a : A) :
    shirokovU φ N a 0 = a := rfl

@[simp] theorem shirokovC_zero (φ : A → R) (N : ℕ) (a : A) :
    shirokovC φ N a 0 = (N : R) * φ a := rfl

theorem shirokovU_succ (φ : A → R) (N : ℕ) (a : A) (k : ℕ) :
    shirokovU φ N a (k + 1) =
      a * (shirokovU φ N a k - algebraMap R A (shirokovC φ N a k)) := by
  rfl

theorem shirokovC_succ (φ : A → R) (N : ℕ) (a : A) (k : ℕ) :
    shirokovC φ N a (k + 1) =
      ((N : R) / (k + 2 : R)) *
        φ (a * (shirokovU φ N a k - algebraMap R A (shirokovC φ N a k))) := by
  rfl

/-!
## Concrete correctness in `Cl(1,1) ≅ M₂(ℝ)` with `N = 2`
-/

open InfoGeometry.Synthesis.ShirokovCliffordTraceDetInverseBridge

abbrev Cl11Matrix := Matrix (Fin 2) (Fin 2) ℝ

/-- The first Shirokov scalar is the ordinary matrix trace: `c₁ = N⟨U₁⟩₀ = tr`. -/
theorem cl11_shirokov_c_one (U : Cl11Matrix) :
    shirokovC cl11ShirokovTrace 2 U 0 = Matrix.trace U := by
  simp [shirokovC, shirokovSequence, cl11ShirokovTrace]

/-- Cayley–Hamilton for a concrete `2 × 2` real matrix, proved entrywise. -/
theorem cl11_cayley_hamilton (U : Cl11Matrix) :
    U * U - (Matrix.trace U) • U + (Matrix.det U) • (1 : Cl11Matrix) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.trace, Matrix.det_fin_two, Fin.sum_univ_two] <;>
    ring

/-- The second Shirokov multivector is the scalar `U₂ = -det(U) · 1`. -/
theorem cl11_shirokov_u_two (U : Cl11Matrix) :
    shirokovU cl11ShirokovTrace 2 U 1 = -(Matrix.det U) • (1 : Cl11Matrix) := by
  rw [shirokovU_succ, cl11_shirokov_c_one, Algebra.algebraMap_eq_smul_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.trace, Matrix.det_fin_two, Fin.sum_univ_two] <;>
    ring

/-- The second Shirokov scalar is `c₂ = -det(U)`. -/
theorem cl11_shirokov_c_two (U : Cl11Matrix) :
    shirokovC cl11ShirokovTrace 2 U 1 = -(Matrix.det U) := by
  rw [shirokovC_succ]
  rw [← shirokovU_succ]
  rw [cl11_shirokov_u_two]
  simp [cl11ShirokovTrace, Matrix.trace]

/-- Shirokov's determinant readout at `k = N`: `(-1)^(N-1) c_N = det` for `N = 2`. -/
theorem cl11_shirokov_det_from_final_coeff (U : Cl11Matrix) :
    (-1 : ℝ) ^ (2 - 1) * shirokovC cl11ShirokovTrace 2 U 1 = Matrix.det U := by
  rw [cl11_shirokov_c_two]
  norm_num

/-- The recursive adjugate `U₁ - c₁` equals the negative concrete adjugate matrix. -/
theorem cl11_shirokov_adjugate (U : Cl11Matrix) :
    shirokovU cl11ShirokovTrace 2 U 0 -
        algebraMap ℝ Cl11Matrix (shirokovC cl11ShirokovTrace 2 U 0) =
      -Matrix.adjugate U := by
  rw [cl11_shirokov_c_one, Algebra.algebraMap_eq_smul_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_fin_two, Matrix.trace, Fin.sum_univ_two]

/--
The recursive inverse `A⁻¹ = (U_{N-1} - c_{N-1}) / c_N` at `N = 2` agrees with the
concrete adjugate/determinant inverse and is a genuine two-sided inverse whenever
`det A ≠ 0`.  This is the coordinate-free Shirokov recursion specialized to the
`Cl(1,1)` owner; the zero-divisor case `det A = 0` is excluded.
-/
theorem cl11_shirokov_recursive_inverse (U : Cl11Matrix) (hdet : Matrix.det U ≠ 0) :
    let invA : Cl11Matrix :=
      (shirokovC cl11ShirokovTrace 2 U 1)⁻¹ •
        (shirokovU cl11ShirokovTrace 2 U 0 -
          algebraMap ℝ Cl11Matrix (shirokovC cl11ShirokovTrace 2 U 0))
    U * invA = 1 ∧ invA * U = 1 := by
  dsimp only
  rw [cl11_shirokov_adjugate, cl11_shirokov_c_two]
  constructor
  · simp [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, hdet]
  · simp [Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, hdet]

end InfoGeometry.Synthesis.ShirokovRecursiveInverse
