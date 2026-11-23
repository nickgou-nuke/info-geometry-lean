/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.PolarizedShearSpinSolution
import InfoGeometry.OperatorAlgebra.RealMatrixSplit

/-!
# Real Clifford midline symmetry and bounded off-midline evolution

The existing native linear map `Cl11Matrix.gen` represents
`W = δ Eplus + γ Eminus = !![δ, γ; -γ, -δ]`.
Its already owned square is `(δ² - γ²) I`; the determinant below is the
opposite quadratic expression. No second generator family is introduced.

Reflection invariance and Euclidean skew-adjointness hold exactly at `δ=0`.
The Euclidean quadratic drift vanishes for every vector exactly there, but
can vanish for an individual vector away from that locus.

The scaled orthogonal coordinate change `(x,y) ↦ (x-y,x+y)` intertwines
this generator with the existing polarized shear/spin generator. Its
constructed bounded ODE solutions therefore transport to this carrier.
In particular, `δ=3/16`, `γ=5/16` gives bounded dynamics at strip coordinate
`σ=11/16`, strictly away from `1/2`. Boundedness here does not assert
Euclidean orthogonality, positive Onsager dissipation, an analytic KMS
condition, or a theorem about zeros of an L-function.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealCl11MidlineStability

open scoped Matrix
open Matrix
open InfoGeometry.Clifford.Cl11Matrix (Mat2 gen Eplus Eminus J1)
open InfoGeometry.Canonical.PolarizedShearSpinFrame (Vec2)
open InfoGeometry.OperatorAlgebra.RealMatrixSplit

/-- The native real determinant is the negative of the owned Clifford square. -/
theorem gen_det (δ γ : ℝ) : (gen (δ, γ)).det = γ ^ 2 - δ ^ 2 := by
  simp [gen, Eplus, Eminus, Matrix.det_fin_two] <;> ring

/-- Conjugation by the square-minus-one generator reverses the cut coordinate. -/
theorem gen_phase_reflection (δ γ : ℝ) :
    (-Eminus) * gen (δ, γ) * Eminus = gen (-δ, γ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gen, Eplus, Eminus, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem gen_phase_reflection_fixed_iff (δ γ : ℝ) :
    (-Eminus) * gen (δ, γ) * Eminus = gen (δ, γ) ↔ δ = 0 := by
  rw [gen_phase_reflection]
  constructor
  · intro h
    have h00 := congrArg (fun M : Mat2 => M 0 0) h
    simp [gen, Eplus, Eminus] at h00
    linarith
  · intro h
    simp [h]

/-- The symmetric part is an indefinite cut term when its coefficient is nonzero. -/
theorem gen_selfAdjointPart (δ γ : ℝ) :
    (selfAdjointPart ℝ (gen (δ, γ)) : Mat2) = δ • Eplus := by
  rw [selfAdjointPart_eq_half]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gen, Eplus, Eminus] <;> ring

theorem gen_skewAdjointPart (δ γ : ℝ) :
    (skewAdjointPart ℝ (gen (δ, γ)) : Mat2) = γ • Eminus := by
  rw [skewAdjointPart_eq_half]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gen, Eplus, Eminus] <;> ring

/-- Full skew-adjointness is a condition on the generator, not on one test vector. -/
theorem gen_mem_skewAdjoint_iff (δ γ : ℝ) :
    gen (δ, γ) ∈ skewAdjoint Mat2 ↔ δ = 0 := by
  rw [skewAdjoint.mem_iff, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial]
  constructor
  · intro h
    have h00 := congrArg (fun M : Mat2 => M 0 0) h
    simp [gen, Eplus, Eminus] at h00
    linarith
  · intro h
    subst δ
    ext i j
    fin_cases i <;> fin_cases j <;> simp [gen, Eplus, Eminus]

/-- Half the instantaneous Euclidean square-norm derivative along `v' = W v`. -/
theorem gen_quadratic_drift (δ γ : ℝ) (v : Vec2) :
    dotProduct v ((gen (δ, γ)).mulVec v) = δ * (v 0 ^ 2 - v 1 ^ 2) := by
  simp [gen, Eplus, Eminus, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

theorem gen_quadratic_drift_all_zero_iff (δ γ : ℝ) :
    (∀ v : Vec2, dotProduct v ((gen (δ, γ)).mulVec v) = 0) ↔ δ = 0 := by
  constructor
  · intro h
    simpa [gen_quadratic_drift] using h ![1, 0]
  · intro h v
    simp [gen_quadratic_drift, h]

/-- Both ordered mixed products matter; the cut and phase do not commute. -/
theorem gen_commutator (δ γ δ' γ' : ℝ) :
    gen (δ, γ) * gen (δ', γ') - gen (δ', γ') * gen (δ, γ) =
      (2 * (δ * γ' - γ * δ')) • J1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gen, Eplus, Eminus, J1, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- A scaled orthogonal coordinate equivalence into the owned shear/spin frame. -/
def shearCoordinates : Vec2 ≃ₗ[ℝ] Vec2 where
  toFun v := ![v 0 - v 1, v 0 + v 1]
  invFun v := ![(v 0 + v 1) / 2, (v 1 - v 0) / 2]
  left_inv v := by
    ext i
    fin_cases i <;> simp <;> ring
  right_inv v := by
    ext i
    fin_cases i <;> simp <;> ring
  map_add' v w := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' c v := by
    ext i
    fin_cases i <;> simp <;> ring

theorem shearCoordinates_square_sum (v : Vec2) :
    shearCoordinates v 0 ^ 2 + shearCoordinates v 1 ^ 2 =
      2 * (v 0 ^ 2 + v 1 ^ 2) := by
  simp [shearCoordinates]
  ring

/-- The inverse coordinate map intertwines the actual two matrix generators. -/
theorem shearCoordinates_symm_intertwines (δ γ : ℝ) (v : Vec2) :
    shearCoordinates.symm
        ((PolarizedShearSpinFrame.generator δ γ).mulVec v) =
      (gen (δ, γ)).mulVec (shearCoordinates.symm v) := by
  ext i
  fin_cases i <;>
    simp [shearCoordinates, PolarizedShearSpinFrame.generator_eq, gen,
      Eplus, Eminus, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- Transport the existing constructed global ODE solution and its bound.
The hypothesis allows a nonzero symmetric part in the elliptic regime. -/
theorem exists_bounded_gen_solution {δ γ : ℝ} (h : |δ| < γ) (v0 : Vec2) :
    ∃ v : ℝ → Vec2, v 0 = v0 ∧
      (∀ t : ℝ, ∀ i : Fin 2, HasDerivAt (fun r => v r i)
        ((gen (δ, γ)).mulVec (v t) i) t) ∧
      (∀ t : ℝ, 0 ≤ t → v t 0 ^ 2 + v t 1 ^ 2 ≤
        ((γ + |δ|) / (γ - |δ|)) * (v0 0 ^ 2 + v0 1 ^ 2)) := by
  obtain ⟨y, hy0, hyderiv, hybound⟩ :=
    PolarizedShearSpinFrame.exists_bounded_solution (nu := 0) h (le_refl 0)
      (shearCoordinates v0)
  let v : ℝ → Vec2 := fun t => shearCoordinates.symm (y t)
  refine ⟨v, ?_, ?_, ?_⟩
  · simp [v, hy0]
  · intro t i
    have h0 := hyderiv t 0
    have h1 := hyderiv t 1
    simp only [PolarizedShearSpinFrame.velocity, zero_smul, sub_zero] at h0 h1
    change HasDerivAt (fun r => shearCoordinates.symm (y r) i)
      ((gen (δ, γ)).mulVec (shearCoordinates.symm (y t)) i) t
    rw [← shearCoordinates_symm_intertwines]
    fin_cases i
    · change HasDerivAt (fun r => (y r 0 + y r 1) / 2)
        (((PolarizedShearSpinFrame.generator δ γ).mulVec (y t) 0 +
          (PolarizedShearSpinFrame.generator δ γ).mulVec (y t) 1) / 2) t
      exact (h0.add h1).div_const 2
    · change HasDerivAt (fun r => (y r 1 - y r 0) / 2)
        (((PolarizedShearSpinFrame.generator δ γ).mulVec (y t) 1 -
          (PolarizedShearSpinFrame.generator δ γ).mulVec (y t) 0) / 2) t
      exact (h1.sub h0).div_const 2
  · intro t ht
    have hb := hybound t ht
    rw [shearCoordinates_square_sum] at hb
    have hscale := shearCoordinates_square_sum (shearCoordinates.symm (y t))
    simp only [LinearEquiv.apply_symm_apply] at hscale
    change (shearCoordinates.symm (y t)) 0 ^ 2 +
      (shearCoordinates.symm (y t)) 1 ^ 2 ≤ _
    nlinarith

/-- At `σ=11/16`, hence `δ=3/16 ≠ 0`, every initial vector has a bounded
trajectory. This directly refutes growth forced only by leaving the midline. -/
theorem off_midline_bounded_solution (v0 : Vec2) :
    ∃ v : ℝ → Vec2, v 0 = v0 ∧
      (∀ t : ℝ, ∀ i : Fin 2, HasDerivAt (fun r => v r i)
        ((gen (3 / 16, 5 / 16)).mulVec (v t) i) t) ∧
      (∀ t : ℝ, 0 ≤ t → v t 0 ^ 2 + v t 1 ^ 2 ≤
        4 * (v0 0 ^ 2 + v0 1 ^ 2)) := by
  have h : |(3 / 16 : ℝ)| < 5 / 16 := by norm_num
  have hfactor :
      ((5 / 16 : ℝ) + |3 / 16|) / (5 / 16 - |3 / 16|) = 4 := by norm_num
  simpa only [hfactor] using exists_bounded_gen_solution h v0

end InfoGeometry.Canonical.RealCl11MidlineStability

end
