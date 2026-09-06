import Mathlib
import InfoGeometry.Algebra.ZornVectorMatrix

namespace InfoGeometry.Canonical

open InfoGeometry.Algebra
open scoped LinearAlgebra.Projectivization

abbrev RealProjectiveBoundary := Projectivization ℝ (Fin 2 → ℝ)
abbrev SL2R := Matrix.SpecialLinearGroup (Fin 2) ℝ

/--
The projective boundary point represented by the affine coordinate `x`.
This is the Mathlib `Projectivization` model of the real projective line.
-/
noncomputable def affineBoundaryPoint (x : ℝ) : RealProjectiveBoundary :=
  Projectivization.mk ℝ ![x, 1] (by
    intro h
    have h1 := congrArg (fun v : Fin 2 → ℝ => v 1) h
    simp at h1)

/-- The point at infinity on the real projective line. -/
noncomputable def infinityBoundaryPoint : RealProjectiveBoundary :=
  Projectivization.mk ℝ ![1, 0] (by
    intro h
    have h0 := congrArg (fun v : Fin 2 → ℝ => v 0) h
    simp at h0)

/--
The local associative `SL₂(ℝ)` slice acting on the projective boundary.
This is the projective-line avatar of the `Cl(1,1) ≅ M₂(ℝ)` sector.
-/
noncomputable def localSL2ProjectiveAction (g : SL2R) :
    RealProjectiveBoundary → RealProjectiveBoundary :=
  Projectivization.map (g.toLin'.toLinearMap) g.toLin'.injective

/-- The explicit hyperbolic boost matrix in the local `SL₂(ℝ)` slice. -/
noncomputable def modularBoostSL2 (s : ℝ) : SL2R :=
  ⟨![![Real.exp s, 0], ![0, Real.exp (-s)]], by
    simp [Matrix.det_fin_two, Real.exp_neg]⟩

/-- The induced projective action of the hyperbolic boost. -/
noncomputable def modularBoostProjectiveAction (s : ℝ) :
    RealProjectiveBoundary → RealProjectiveBoundary :=
  localSL2ProjectiveAction (modularBoostSL2 s)

noncomputable def modularBoostMatrix (s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![Real.exp s, 0], ![0, Real.exp (-s)]]

noncomputable def mobiusAffine (g : Matrix (Fin 2) (Fin 2) ℝ) (x : ℝ) : ℝ :=
  (g 0 0 * x + g 0 1) / (g 1 0 * x + g 1 1)

theorem modularBoost_det (s : ℝ) :
    Matrix.det (modularBoostMatrix s) = 1 := by
  simp [modularBoostMatrix, Matrix.det_fin_two, Real.exp_neg,
    Real.exp_ne_zero]

theorem modularBoost_mobius_affine (s x : ℝ) :
    mobiusAffine (modularBoostMatrix s) x = Real.exp (2 * s) * x := by
  simp [mobiusAffine, modularBoostMatrix]
  field_simp [Real.exp_ne_zero]
  have h : Real.exp (-s) * Real.exp (s * 2) = Real.exp s := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    Real.exp s * x = x * Real.exp s := by ring
    _ = x * (Real.exp (-s) * Real.exp (s * 2)) := by rw [h]
    _ = x * Real.exp (-s) * Real.exp (s * 2) := by ring

theorem modularBoostMatrix_add (s t : ℝ) :
    modularBoostMatrix (s + t) =
      modularBoostMatrix s * modularBoostMatrix t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, modularBoostMatrix, Real.exp_add] <;>
    ring_nf

theorem modularBoost_fixes_zero (s : ℝ) :
    mobiusAffine (modularBoostMatrix s) 0 = 0 := by
  simp [modularBoost_mobius_affine]

theorem modularBoostSL2_zero :
    modularBoostSL2 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [modularBoostSL2]

theorem modularBoostSL2_add (s t : ℝ) :
    modularBoostSL2 (s + t) = modularBoostSL2 s * modularBoostSL2 t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [modularBoostSL2, Matrix.mul_apply, Fin.sum_univ_two, Real.exp_add] <;>
    ring_nf

noncomputable def diskBoostParameter (s : ℝ) : ℝ :=
  (Real.exp (2 * s) - 1) / (Real.exp (2 * s) + 1)

noncomputable def cayleyBoundary (x : ℝ) : ℂ :=
  ((x : ℂ) - Complex.I) / ((x : ℂ) + Complex.I)

noncomputable def diskBoundaryBoost (s : ℝ) (z : ℂ) : ℂ :=
  (z + (diskBoostParameter s : ℂ)) /
    ((diskBoostParameter s : ℂ) * z + 1)

theorem cayleyBoundary_zero : cayleyBoundary 0 = -1 := by
  apply Complex.ext <;> norm_num [cayleyBoundary]

theorem diskBoundaryBoost_fixed_minus_one_of_den_ne_zero
    (s : ℝ)
    (hden : -(1 : ℂ) * (diskBoostParameter s : ℂ) + 1 ≠ 0) :
    diskBoundaryBoost s (-1) = (-1 : ℂ) := by
  unfold diskBoundaryBoost
  have hden' : (diskBoostParameter s : ℂ) * (-1 : ℂ) + 1 ≠ 0 := by
    simpa [mul_comm] using hden
  have hcancel : ((diskBoostParameter s : ℂ) * (-1 : ℂ) + 1) *
      ((diskBoostParameter s : ℂ) * (-1 : ℂ) + 1)⁻¹ = 1 := by
    simpa using mul_inv_cancel₀ hden'
  calc
    (-1 + (diskBoostParameter s : ℂ)) /
        ((diskBoostParameter s : ℂ) * (-1 : ℂ) + 1) =
      -(((diskBoostParameter s : ℂ) * (-1 : ℂ) + 1) *
          ((diskBoostParameter s : ℂ) * (-1 : ℂ) + 1)⁻¹) := by
      simp [div_eq_mul_inv]
      ring
    _ = -1 := by rw [hcancel]

theorem diskBoundaryBoost_fixed_one_of_den_ne_zero
    (s : ℝ)
    (hden : (diskBoostParameter s : ℂ) + 1 ≠ 0) :
    diskBoundaryBoost s 1 = (1 : ℂ) := by
  unfold diskBoundaryBoost
  simpa [div_eq_mul_inv, add_comm] using (mul_inv_cancel₀ hden)

end InfoGeometry.Canonical
