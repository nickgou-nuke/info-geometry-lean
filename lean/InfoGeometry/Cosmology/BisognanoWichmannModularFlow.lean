/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.SolderingIsomorphism
import InfoGeometry.Projective.SplitQuaternionRankOneProjective
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# Bisognano–Wichmann Modular Flow, Twistor Dyadics, and Lorentz Boosts

This module formalizes the algebraic and geometric core of the Bisognano–Wichmann theorem
and twistor dyadic incidence on the finite (2,2) spacetime carrier:

### Mathematical Invariants Proved:
1. **The 1-Parameter Lorentz Boost Group**:
   The hyperbolic group $B(s) = \operatorname{diag}(e^s, e^{-s}) \in SL(2, \mathbb{R})$ satisfies:
   - $\det(B(s)) = 1$
   - $B(s_1 + s_2) = B(s_1) B(s_2)$
   - $B(0) = \mathbf{1}$
2. **Geometric Spacetime Boost**:
   The transformation $M \mapsto B(s) M B(s)$ pulls back under `solderingInv` to the exact
   Lorentz boost in the $(t, z)$ plane of `Vec22`:
   $$(t, z, x, y) \mapsto (t \cosh(2s) + z \sinh(2s), \quad t \sinh(2s) + z \cosh(2s), \quad x, \quad y)$$
   leaving the transverse coordinates $(x, y)$ invariant.
3. **Exact Metric Preservation (Lorentz Invariance)**:
   $$q_{22}(\operatorname{boostSpacetime}(s, v)) = q_{22}(v)$$
4. **Thermal / Modular Automorphism on CAR Roots**:
   The modular automorphism $\sigma_s(A) = B(s) A B(-s)$ acts on the Cartan root basis as:
   - $\sigma_s(\operatorname{rootPlus}) = e^{2s} \operatorname{rootPlus}$
   - $\sigma_s(\operatorname{rootMinus}) = e^{-2s} \operatorname{rootMinus}$
   - $\sigma_s(\operatorname{axis}) = \operatorname{axis}$
5. **Twistor Dyadics and Incidence via Nilpotency**:
   For any two 2-spinors $u, v \in \mathbb{R}^2$, the dyadic matrix $D(u, v) = u v^T$ satisfies:
   - $\det(D(u, v)) = 0$, so every dyadic spinor pair defines an exact null vector in spacetime.
   - $D(u, v)^2 = (v \cdot u) D(u, v)$.
   - $D(u, v)$ is nilpotent ($D(u, v)^2 = 0$) if and only if the spinors are incident ($v \cdot u = 0$).

All theorems are fully proved with zero `sorry`, zero `admit`, and core Mathlib axioms.
-/

namespace InfoGeometry.Cosmology.BisognanoWichmann

open Matrix
open InfoGeometry.Clifford.Soldering
open InfoGeometry.Clifford.SolderingIsomorphism
open InfoGeometry.Projective.SplitQuaternionRankOneProjective

/-! ### I. The 1-Parameter Hyperbolic Boost Group in SL(2, ℝ) -/

/-- The 1-parameter hyperbolic boost matrix in $M_2(\mathbb{R})$. -/
noncomputable def boostMatrix (s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.exp s, 0;
     0, Real.exp (-s)]

/-- The boost matrix has determinant 1 for all rapidities $s$. -/
@[simp]
theorem boostMatrix_det (s : ℝ) : (boostMatrix s).det = 1 := by
  simp [boostMatrix, Matrix.det_fin_two]
  have h : Real.exp s * Real.exp (-s) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  exact h

/-- Group identity of the boost family. -/
@[simp]
theorem boostMatrix_zero : boostMatrix 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [boostMatrix, Matrix.one_apply]

/-- Additive group homomorphism law: $B(s_1 + s_2) = B(s_1) B(s_2)$. -/
theorem boostMatrix_add (s1 s2 : ℝ) :
    boostMatrix (s1 + s2) = boostMatrix s1 * boostMatrix s2 := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [boostMatrix, Matrix.mul_apply, Fin.sum_univ_two, Real.exp_add]
  · simp [boostMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [boostMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [boostMatrix, Matrix.mul_apply, Fin.sum_univ_two]
    have h : Real.exp (-s1) * Real.exp (-s2) = Real.exp (-s1 + -s2) := (Real.exp_add (-s1) (-s2)).symm
    rw [h]
    congr 1
    ring

/-- Inverse boost matrix is the negative parameter: $B(s)^{-1} = B(-s)$. -/
theorem boostMatrix_inv (s : ℝ) :
    boostMatrix s * boostMatrix (-s) = 1 := by
  rw [← boostMatrix_add, add_neg_cancel, boostMatrix_zero]

/-! ### II. Geometric Lorentz Boost Action on Spacetime -/

/-- Congruence action of the boost on soldered matrices: $M \mapsto B(s) M B(s)$. -/
noncomputable def boostMatrixAction (s : ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  boostMatrix s * M * boostMatrix s

/-- Spacetime vector transformation under the Lorentz boost. -/
noncomputable def boostSpacetime (s : ℝ) (v : Vec22) : Vec22 :=
  solderingInv (boostMatrixAction s (soldering v))

/-- Explicit matrix entries of the boosted soldered matrix. -/
theorem boostMatrixAction_soldering (s : ℝ) (t z x y : ℝ) :
    boostMatrixAction s (soldering (t, z, x, y)) =
      !![Real.exp (2 * s) * (t + z), x + y;
         x - y, Real.exp (-2 * s) * (t - z)] := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp only [boostMatrixAction, boostMatrix, soldering_entry_00, Matrix.mul_apply, Fin.sum_univ_two]
    have h : Real.exp s * (t + z) * Real.exp s = Real.exp (2 * s) * (t + z) := by
      calc Real.exp s * (t + z) * Real.exp s
        _ = (t + z) * (Real.exp s * Real.exp s) := by ring
        _ = (t + z) * Real.exp (s + s) := by rw [← Real.exp_add]
        _ = Real.exp (2 * s) * (t + z) := by ring_nf
    simp [h]
  · simp only [boostMatrixAction, boostMatrix, soldering_entry_01, Matrix.mul_apply, Fin.sum_univ_two]
    have h : Real.exp s * (x + y) * Real.exp (-s) = x + y := by
      calc Real.exp s * (x + y) * Real.exp (-s)
        _ = (x + y) * (Real.exp s * Real.exp (-s)) := by ring
        _ = (x + y) * Real.exp (s + -s) := by rw [← Real.exp_add]
        _ = (x + y) * Real.exp 0 := by ring_nf
        _ = x + y := by simp
    simp [h]
  · simp only [boostMatrixAction, boostMatrix, soldering_entry_10, Matrix.mul_apply, Fin.sum_univ_two]
    have h : Real.exp (-s) * (x - y) * Real.exp s = x - y := by
      calc Real.exp (-s) * (x - y) * Real.exp s
        _ = (x - y) * (Real.exp (-s) * Real.exp s) := by ring
        _ = (x - y) * Real.exp (-s + s) := by rw [← Real.exp_add]
        _ = (x - y) * Real.exp 0 := by ring_nf
        _ = x - y := by simp
    simp [h]
  · simp only [boostMatrixAction, boostMatrix, soldering_entry_11, Matrix.mul_apply, Fin.sum_univ_two]
    have h : Real.exp (-s) * (t - z) * Real.exp (-s) = Real.exp (-2 * s) * (t - z) := by
      calc Real.exp (-s) * (t - z) * Real.exp (-s)
        _ = (t - z) * (Real.exp (-s) * Real.exp (-s)) := by ring
        _ = (t - z) * Real.exp (-s + -s) := by rw [← Real.exp_add]
        _ = Real.exp (-2 * s) * (t - z) := by ring_nf
    simp [h]

/-- Explicit coordinates of the boosted spacetime vector. -/
theorem boostSpacetime_coords (s : ℝ) (t z x y : ℝ) :
    boostSpacetime s (t, z, x, y) =
      ((Real.exp (2 * s) * (t + z) + Real.exp (-2 * s) * (t - z)) / 2,
       (Real.exp (2 * s) * (t + z) - Real.exp (-2 * s) * (t - z)) / 2,
       x,
       y) := by
  unfold boostSpacetime
  rw [boostMatrixAction_soldering]
  dsimp [solderingInv_apply]
  ext <;> ring

/-- Exact Lorentz Invariance: The quadratic form $q_{22}$ is invariant under boosts. -/
theorem boostSpacetime_preserves_q22 (s : ℝ) (v : Vec22) :
    q22 (boostSpacetime s v) = q22 v := by
  unfold boostSpacetime
  rw [← det_soldering_inv_eq_q22]
  have h_det : (boostMatrixAction s (soldering v)).det = (soldering v).det := by
    simp [boostMatrixAction, Matrix.det_mul]
  rw [h_det]
  exact det_soldering_eq_q22 v

/-! ### III. The Modular Automorphism on CAR Roots (Bisognano–Wichmann Action) -/

/-- The modular automorphism action on matrices: $\sigma_s(A) = B(s) A B(-s)$. -/
noncomputable def modularAutomorphism (s : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  boostMatrix s * A * boostMatrix (-s)

/-- Modular action preserves the identity. -/
@[simp]
theorem modularAutomorphism_one (s : ℝ) :
    modularAutomorphism s 1 = 1 := by
  simp [modularAutomorphism, boostMatrix_inv]

/-- Modular action leaves the Cartan generator `axis` invariant. -/
theorem modularAutomorphism_axis (s : ℝ) :
    modularAutomorphism s axis = axis := by
  rw [axis_eq_diagonal]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [modularAutomorphism, boostMatrix, Matrix.mul_apply, Fin.sum_univ_two]
    have h : Real.exp s * Real.exp (-s) = Real.exp (s + -s) := (Real.exp_add s (-s)).symm
    rw [h]
    have h0 : s + -s = 0 := add_neg_cancel s
    rw [h0, Real.exp_zero]
  · simp [modularAutomorphism, boostMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [modularAutomorphism, boostMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [modularAutomorphism, boostMatrix, Matrix.mul_apply, Fin.sum_univ_two]
    have h : Real.exp (-s) * Real.exp s = Real.exp (-s + s) := (Real.exp_add (-s) s).symm
    rw [h]
    have h0 : -s + s = 0 := neg_add_cancel s
    rw [h0, Real.exp_zero]

/-- Modular action dilates the raising operator `rootPlus` by $e^{2s}$. -/
theorem modularAutomorphism_rootPlus (s : ℝ) :
    modularAutomorphism s rootPlus = Real.exp (2 * s) • rootPlus := by
  rw [rootPlus_eq_matrix]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [modularAutomorphism, boostMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [modularAutomorphism, boostMatrix, Matrix.mul_apply, Fin.sum_univ_two]
    have h : Real.exp s * Real.exp s = Real.exp (s + s) := (Real.exp_add s s).symm
    rw [h]
    congr 1
    ring
  · simp [modularAutomorphism, boostMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [modularAutomorphism, boostMatrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- Modular action contracts the lowering operator `rootMinus` by $e^{-2s}$. -/
theorem modularAutomorphism_rootMinus (s : ℝ) :
    modularAutomorphism s rootMinus = Real.exp (-2 * s) • rootMinus := by
  rw [rootMinus_eq_matrix]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [modularAutomorphism, boostMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [modularAutomorphism, boostMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [modularAutomorphism, boostMatrix, Matrix.mul_apply, Fin.sum_univ_two]
    have h : Real.exp (-s) * Real.exp (-s) = Real.exp (-s + -s) := (Real.exp_add (-s) (-s)).symm
    rw [h]
    congr 1
    ring
  · simp [modularAutomorphism, boostMatrix, Matrix.mul_apply, Fin.sum_univ_two]

/-! ### IV. Twistor Dyadics and Incidence via Nilpotency -/

/-- Dyadic outer product matrix of two 2-spinors: $D(u, v) = u v^T$. -/
def dyadicMatrix (u v : ℝ × ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![u.1 * v.1, u.1 * v.2;
     u.2 * v.1, u.2 * v.2]

/-- Every dyadic matrix has vanishing determinant. -/
theorem dyadicMatrix_det (u v : ℝ × ℝ) : (dyadicMatrix u v).det = 0 := by
  simp [dyadicMatrix, Matrix.det_fin_two]
  ring

/-- The spacetime vector corresponding to any dyadic spinor product is null. -/
theorem dyadic_spacetime_vector_is_null (u v : ℝ × ℝ) :
    q22 (solderingInv (dyadicMatrix u v)) = 0 := by
  rw [← det_soldering_inv_eq_q22]
  exact dyadicMatrix_det u v

/-- Dyadic squaring identity: $D(u, v)^2 = (v \cdot u) D(u, v)$. -/
theorem dyadicMatrix_sq (u v : ℝ × ℝ) :
    dyadicMatrix u v * dyadicMatrix u v = (v.1 * u.1 + v.2 * u.2) • dyadicMatrix u v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [dyadicMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]; ring)

/-- Twistor Incidence Equivalence:
A non-zero dyadic matrix is nilpotent if and only if the spinors are orthogonal (incident):
$v_1 u_1 + v_2 u_2 = 0$. -/
theorem dyadicMatrix_nilpotent_iff (u v : ℝ × ℝ) (h_non_zero : dyadicMatrix u v ≠ 0) :
    dyadicMatrix u v * dyadicMatrix u v = 0 ↔ (v.1 * u.1 + v.2 * u.2 = 0) := by
  rw [dyadicMatrix_sq]
  constructor
  · intro h_sq
    by_contra h_dot
    have h_zero : dyadicMatrix u v = 0 := by
      have h_scale : (v.1 * u.1 + v.2 * u.2)⁻¹ • ((v.1 * u.1 + v.2 * u.2) • dyadicMatrix u v) =
                     (v.1 * u.1 + v.2 * u.2)⁻¹ • (0 : Matrix (Fin 2) (Fin 2) ℝ) := by rw [h_sq]
      rw [inv_smul_smul₀ h_dot, smul_zero] at h_scale
      exact h_scale
    exact h_non_zero h_zero
  · intro h_dot
    rw [h_dot, zero_smul]

end InfoGeometry.Cosmology.BisognanoWichmann
