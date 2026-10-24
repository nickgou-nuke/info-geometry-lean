/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FiniteMatrixGibbsParity
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi

/-! Native CFC diagonal Gibbs densities and a concrete nontracial witness.
Uncompiled scratch proposal. The witness requires beta * h nonzero.
-/

noncomputable section
namespace InfoGeometry.Canonical.FiniteMatrixGibbsFunctional

open InfoGeometry.Physics.KleinBottleSewingExact

/-- The native Gibbs density of a real diagonal Hamiltonian is entrywise exponential.
The Hermitian proof is the proof argument of the existing Gibbs definition. -/
theorem gibbsDensity_diagonal {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (d : n → ℝ)
    (hD : (Matrix.diagonal (fun i => (d i : ℂ))).IsHermitian) (β : ℝ) :
    gibbsDensity (Matrix.diagonal (fun i => (d i : ℂ))) hD β =
      Matrix.diagonal (fun i => (Real.exp (-β * d i) : ℂ)) := by
  let φ : (n → ℂ) →⋆ₐ[ℂ] Matrix n n ℂ :=
    { Matrix.diagonalAlgHom (n := n) (α := ℂ) ℂ with
      map_star' := by
        intro v
        change Matrix.diagonal (star v) = (Matrix.diagonal v).conjTranspose
        rw [Matrix.diagonal_conjTranspose] }
  have hd : IsSelfAdjoint (fun i => (d i : ℂ)) := by
    change star (fun i => (d i : ℂ)) = (fun i => (d i : ℂ))
    ext i
    simp
  have hdi (i : n) : IsSelfAdjoint (d i : ℂ) := by
    change star (d i : ℂ) = (d i : ℂ)
    simp
  have hpi : cfc (expWeight β) (fun i => (d i : ℂ)) =
      (fun i => (Real.exp (-β * d i) : ℂ)) := by
    rw [cfc_map_pi (S := ℂ) (ha := hd) (ha' := hdi)
      (hf := (by unfold expWeight; fun_prop))]
    funext i
    exact cfc_algebraMap (R := ℝ) (A := ℂ) (d i) (expWeight β)
  have hmap := StarAlgHom.map_cfc φ (expWeight β) (fun i => (d i : ℂ))
    (by unfold expWeight; fun_prop)
    (φ.toAlgHom.toLinearMap.continuous_of_finiteDimensional) hd hD
  rw [hpi] at hmap
  rw [gibbsDensity, ← hD.cfc_eq]
  exact hmap.symm

/-- Explicit CFC density for the existing Pauli tilt Hamiltonian. -/
theorem tiltHamiltonian_gibbsDensity (h β : ℝ) :
    gibbsDensity (h • tilt2) (tiltHamiltonian_isHermitian h) β =
      !![(Real.exp (-β * h) : ℂ), 0; 0, (Real.exp (β * h) : ℂ)] := by
  have ht : h • tilt2 =
      Matrix.diagonal (fun i : Fin 2 => ((if i = 0 then h else -h : ℝ) : ℂ)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [tilt2, Matrix.diagonal, RCLike.real_smul_eq_coe_mul]
  have hd : (Matrix.diagonal
      (fun i : Fin 2 => ((if i = 0 then h else -h : ℝ) : ℂ))).IsHermitian :=
    ht ▸ tiltHamiltonian_isHermitian h
  have hdiag := gibbsDensity_diagonal
    (fun i : Fin 2 => if i = 0 then h else -h) hd β
  rw [gibbsDensity, ← hd.cfc_eq] at hdiag
  rw [gibbsDensity, ← (tiltHamiltonian_isHermitian h).cfc_eq, ht, hdiag]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal]

/-- Explicit ordered-product expectation difference on the existing matrix carrier. -/
theorem tiltHamiltonian_gibbs_matrixUnits_difference (h β : ℝ) :
    gibbsFunctional (h • tilt2) (tiltHamiltonian_isHermitian h) β
        (Matrix.single 0 1 (1 : ℂ) * Matrix.single 1 0 (1 : ℂ)) -
      gibbsFunctional (h • tilt2) (tiltHamiltonian_isHermitian h) β
        (Matrix.single 1 0 (1 : ℂ) * Matrix.single 0 1 (1 : ℂ)) =
      ((Real.exp (-β * h) : ℂ) + (Real.exp (β * h) : ℂ))⁻¹ *
        ((Real.exp (-β * h) : ℂ) - (Real.exp (β * h) : ℂ)) := by
  simp [gibbsFunctional_apply, tiltHamiltonian_gibbsDensity,
    Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.single, Fin.sum_univ_two]
  ring

/-- The two Boltzmann weights differ when the beta-gap product is nonzero. -/
theorem tiltBoltzmann_weights_ne (h β : ℝ) (hβh : β * h ≠ 0) :
    (Real.exp (-β * h) : ℂ) ≠ (Real.exp (β * h) : ℂ) := by
  intro heq
  have hr : Real.exp (-β * h) = Real.exp (β * h) := by
    exact_mod_cast heq
  have he := Real.exp_injective hr
  apply hβh
  nlinarith

/-- A concrete failure of traciality; no desired output equality is assumed. -/
theorem tiltHamiltonian_gibbs_matrixUnits_ne (h β : ℝ) (hβh : β * h ≠ 0) :
    gibbsFunctional (h • tilt2) (tiltHamiltonian_isHermitian h) β
        (Matrix.single 0 1 (1 : ℂ) * Matrix.single 1 0 (1 : ℂ)) ≠
      gibbsFunctional (h • tilt2) (tiltHamiltonian_isHermitian h) β
        (Matrix.single 1 0 (1 : ℂ) * Matrix.single 0 1 (1 : ℂ)) := by
  have hden : (Real.exp (-β * h) : ℂ) + (Real.exp (β * h) : ℂ) ≠ 0 := by
    have hp : 0 < Real.exp (-β * h) + Real.exp (β * h) :=
      add_pos (Real.exp_pos _) (Real.exp_pos _)
    exact_mod_cast (ne_of_gt hp)
  apply sub_ne_zero.mp
  rw [tiltHamiltonian_gibbs_matrixUnits_difference]
  exact mul_ne_zero (inv_ne_zero hden)
    (sub_ne_zero.mpr (tiltBoltzmann_weights_ne h β hβh))

end InfoGeometry.Canonical.FiniteMatrixGibbsFunctional
