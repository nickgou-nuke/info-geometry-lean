/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.CARMajoranaFiniteBridge
import InfoGeometry.Canonical.KitaevDiracBoundaryProjector

/-! Explicit complex intertwiner from the native real skew chain coefficient
matrix to the native BdG matrix. Its real image is fixed by charge conjugation.
-/
noncomputable section
namespace InfoGeometry.Canonical.KitaevMajoranaNambu
open Matrix CARMajoranaFiniteBridge ConcreteKitaevBdGMatrix
open MajoranaPfaffian4 KitaevChainMajoranaZeroModes

def nambuMatrix : Mat4C :=
  !![Complex.I, 1, 0, 0; 0, 0, -Complex.I, 1;
     -Complex.I, 1, 0, 0; 0, 0, Complex.I, 1]

def nambuInverse : Mat4C :=
  !![-Complex.I/2, 0, Complex.I/2, 0; 1/2, 0, 1/2, 0;
     0, Complex.I/2, 0, -Complex.I/2; 0, 1/2, 0, 1/2]

theorem nambuInverse_mul : nambuInverse * nambuMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [nambuInverse, nambuMatrix, mul_apply, Fin.sum_univ_four,
      Complex.I_sq, Matrix.one_apply]

theorem nambuMatrix_mul_inverse : nambuMatrix * nambuInverse = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [nambuInverse, nambuMatrix, mul_apply, Fin.sum_univ_four,
      Complex.I_sq, Matrix.one_apply]

theorem sweetSpot_nambu_intertwiner (t : ℝ) :
    kitaevSweetSpot4 t * nambuMatrix = Complex.I •
      (nambuMatrix * (sweetSpotKernel t).omega.map (algebraMap ℝ ℂ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kitaevSweetSpot4, nambuMatrix, sweetSpotKernel, matchingKernel,
      skewMatrix4, mul_apply, Fin.sum_univ_four] <;> ring

def nambuSpinor (v : Fin 4 → ℝ) : Vec4C := nambuMatrix *ᵥ (fun i => (v i : ℂ))

theorem nambuSpinor_charge_fixed (v : Fin 4 → ℝ) :
    particleHole4 *ᵥ star (nambuSpinor v) = nambuSpinor v := by
  ext i
  fin_cases i <;>
    simp [nambuSpinor, nambuMatrix, particleHole4, mulVec, dotProduct,
      Fin.sum_univ_four] <;> ring

theorem sweetSpot_nambu_action (t : ℝ) (v : Fin 4 → ℝ) :
    kitaevSweetSpot4 t *ᵥ nambuSpinor v =
      Complex.I • nambuSpinor ((sweetSpotKernel t).omega *ᵥ v) := by
  unfold nambuSpinor
  rw [mulVec_mulVec, sweetSpot_nambu_intertwiner, smul_mulVec,
    ← mulVec_mulVec]
  congr 1
  congr 1
  exact (Matrix.map_mulVec (algebraMap ℝ ℂ) (sweetSpotKernel t).omega v).symm

theorem nambuSpinor_eq_zero_iff (v : Fin 4 → ℝ) : nambuSpinor v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have hv := congrArg (fun w => nambuInverse *ᵥ w) h
    simp only [nambuSpinor, mulVec_mulVec, nambuInverse_mul, one_mulVec,
      mulVec_zero] at hv
    ext i
    have hi := congrFun hv i
    exact_mod_cast hi
  · intro h
    subst v
    simp [nambuSpinor]

theorem sweetSpot_nambu_kernel_iff (t : ℝ) (v : Fin 4 → ℝ) :
    kitaevSweetSpot4 t *ᵥ nambuSpinor v = 0 ↔ (sweetSpotKernel t).omega *ᵥ v = 0 := by
  rw [sweetSpot_nambu_action, smul_eq_zero]
  simp only [Complex.I_ne_zero, false_or, nambuSpinor_eq_zero_iff]

/-- The boundary Dirac projector retains precisely the endpoint coefficients. -/
theorem boundary_projector_nambu (v : Vec4C) :
    boundaryDiracProjector *ᵥ (nambuMatrix *ᵥ v) =
      nambuMatrix *ᵥ ![v 0, 0, 0, v 3] := by
  rw [boundaryDiracProjector_explicit]
  ext i
  fin_cases i <;>
    simp [nambuMatrix, mulVec, dotProduct, Fin.sum_univ_four] <;> ring

theorem conserved_chain_iff_nambu_kernel (t : ℝ) (v : Fin 4 → ℝ) :
    let H := kitaevSweetSpotHamiltonian 2 (t • (1 : ChainOp)) twoSiteMajorana
    H * Fintype.linearCombination ℝ twoSiteMajorana v -
      Fintype.linearCombination ℝ twoSiteMajorana v * H = 0 ↔
        kitaevSweetSpot4 t *ᵥ nambuSpinor v = 0 := by
  rw [sweetSpot_chain_commutator_eq_zero_iff, sweetSpot_nambu_kernel_iff]

end InfoGeometry.Canonical.KitaevMajoranaNambu
