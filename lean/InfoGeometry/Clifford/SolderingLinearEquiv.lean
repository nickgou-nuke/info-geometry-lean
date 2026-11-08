/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.Soldering
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# Elementary real soldering equivalence

This is the original elementary inverse/equivalence section of
`SolderingIsomorphism`, extracted without changing declaration names or proof
bodies. The larger owner imports this module and retains its split-quaternion
and projective bridges. Real incidence users need only the elementary owner.
-/

namespace InfoGeometry.Clifford.SolderingIsomorphism

open Matrix
open InfoGeometry.Clifford.Soldering

/-! ### I. Explicit Linear Inverse of the Soldering Map -/

theorem soldering_entry_00 (t z x y : ℝ) : soldering (t, z, x, y) 0 0 = t + z := by
  simp [soldering, sigma0, sigma1, sigma3, epsilon]

theorem soldering_entry_11 (t z x y : ℝ) : soldering (t, z, x, y) 1 1 = t - z := by
  simp [soldering, sigma0, sigma1, sigma3, epsilon]; ring

theorem soldering_entry_01 (t z x y : ℝ) : soldering (t, z, x, y) 0 1 = x + y := by
  simp [soldering, sigma0, sigma1, sigma3, epsilon]

theorem soldering_entry_10 (t z x y : ℝ) : soldering (t, z, x, y) 1 0 = x - y := by
  simp [soldering, sigma0, sigma1, sigma3, epsilon]; ring

/-- Inverse soldering map reconstructing the 4-vector from a 2x2 real matrix. -/
noncomputable def solderingInv : Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] Vec22 where
  toFun M :=
    let t := (M 0 0 + M 1 1) / 2
    let z := (M 0 0 - M 1 1) / 2
    let x := (M 0 1 + M 1 0) / 2
    let y := (M 0 1 - M 1 0) / 2
    (t, z, x, y)
  map_add' M N := by
    dsimp
    ext <;> (dsimp; ring)
  map_smul' c M := by
    dsimp
    ext <;> (dsimp; ring)

@[simp]
theorem solderingInv_apply (M : Matrix (Fin 2) (Fin 2) ℝ) :
    solderingInv M =
      ((M 0 0 + M 1 1) / 2,
       (M 0 0 - M 1 1) / 2,
       (M 0 1 + M 1 0) / 2,
       (M 0 1 - M 1 0) / 2) :=
  rfl

/-- Left inverse property: `solderingInv (soldering v) = v`. -/
@[simp]
theorem solderingInv_soldering (v : Vec22) :
    solderingInv (soldering v) = v := by
  rcases v with ⟨t, z, x, y⟩
  simp only [solderingInv_apply, soldering_entry_00, soldering_entry_11, soldering_entry_01, soldering_entry_10]
  ext <;> ring

/-- Right inverse property: `soldering (solderingInv M) = M`. -/
@[simp]
theorem soldering_solderingInv (M : Matrix (Fin 2) (Fin 2) ℝ) :
    soldering (solderingInv M) = M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [soldering, solderingInv, sigma0, sigma1, sigma3, epsilon]; ring)

/-- The canonical linear equivalence between spacetime `Vec22` and `M₂(ℝ)`. -/
noncomputable def solderingEquiv : Vec22 ≃ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℝ where
  toFun := soldering
  invFun := solderingInv
  left_inv := solderingInv_soldering
  right_inv := soldering_solderingInv
  map_add' := soldering.map_add
  map_smul' := soldering.map_smul

end InfoGeometry.Clifford.SolderingIsomorphism
