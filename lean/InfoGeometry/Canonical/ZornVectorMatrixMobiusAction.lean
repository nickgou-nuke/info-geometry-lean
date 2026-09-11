import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.ZornVectorMatrix

namespace InfoGeometry.Canonical

open scoped LinearAlgebra.Projectivization

abbrev RealProjectiveBoundary := Projectivization ℝ (Fin 2 → ℝ)
abbrev SL2R := Matrix.SpecialLinearGroup (Fin 2) ℝ

noncomputable def affineBoundaryPoint (x : ℝ) : RealProjectiveBoundary :=
  Projectivization.mk ℝ ![x, 1] (by
    intro h
    have h1 := congrArg (fun v : Fin 2 → ℝ => v 1) h
    simp at h1)

noncomputable def infinityBoundaryPoint : RealProjectiveBoundary :=
  Projectivization.mk ℝ ![1, 0] (by
    intro h
    have h0 := congrArg (fun v : Fin 2 → ℝ => v 0) h
    simp at h0)

noncomputable def localSL2ProjectiveAction (g : SL2R) :
    RealProjectiveBoundary → RealProjectiveBoundary :=
  Projectivization.map (g.toLin'.toLinearMap) g.toLin'.injective

noncomputable def modularBoostSL2 (s : ℝ) : SL2R :=
  ⟨![![Real.exp s, 0], ![0, Real.exp (-s)]], by
    simp [Matrix.det_fin_two, Real.exp_neg]⟩

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
    modularBoostMatrix (s + t) = modularBoostMatrix s * modularBoostMatrix t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, modularBoostMatrix, Real.exp_add] <;>
    ring_nf

theorem modularBoost_fixes_zero (s : ℝ) :
    mobiusAffine (modularBoostMatrix s) 0 = 0 := by
  simp [modularBoost_mobius_affine]

theorem modularBoostSL2_zero : modularBoostSL2 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [modularBoostSL2]

theorem modularBoostSL2_add (s t : ℝ) :
    modularBoostSL2 (s + t) = modularBoostSL2 s * modularBoostSL2 t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [modularBoostSL2, Matrix.mul_apply, Fin.sum_univ_two, Real.exp_add] <;>
    ring_nf

end InfoGeometry.Canonical
