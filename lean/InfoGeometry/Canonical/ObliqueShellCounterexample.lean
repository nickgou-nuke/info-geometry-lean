/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.DrazinInterShellHodge
import InfoGeometry.Singular.MoorePenroseCanonicalBridge
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Native oblique inter-shell counterexample

Source matrices: upstream/feat/peirce-square-zero-mp at
5e4435976cc4ffb1b75dd46460dc7ec2c8a7a375,
Canonical/DrazinShellMatrixAction.lean and PeirceSquareZeroExamples.lean.

Contract: in Matrix (Fin 3) (Fin 3) ℝ, with its standard ordered coordinate
basis (0,1,2), ordinary matrix multiplication and conjugate-transpose star,
construct the native PowerMPFamily for fittingNilpotentPart A D. Evaluate
the actual drazinShellProj at 0 and 1, and prove that the native corner (1,0)
equals N and has MP inverse M, but S₀ * M * S₁ ≠ M.

The shells are E_N * (N^r * M_r - N^(r+1) * M_(r+1)) * E_N,
using the owner's definitions, not supplied replacement projectors.
No assertion of minimal Drazin index or reverse-corner MP rule is made.
Native owner infrastructure is imported and reused without redefining it.
-/

namespace InfoGeometry.Canonical.ObliqueShellCounterexample

open Matrix
open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.Drazin.IsDrazinInverse
open InfoGeometry.Canonical.DrazinNilpotentShell

noncomputable section

def obliqueA : Matrix (Fin 3) (Fin 3) ℝ := !![1, 1, 0; 0, 0, 1; 0, 0, 0]
def obliqueD : Matrix (Fin 3) (Fin 3) ℝ := !![1, 1, 1; 0, 0, 0; 0, 0, 0]
def obliqueN : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, -1; 0, 0, 1; 0, 0, 0]
def obliqueM : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 0; 0, 0, 0; -1/2, 1/2, 0]

/-- The forward operator and its MP inverse genuinely fail to commute. -/
theorem oblique_pair_not_commute : obliqueN * obliqueM ≠ obliqueM * obliqueN := by
  intro h
  have he := congrArg (fun C : Matrix (Fin 3) (Fin 3) ℝ => C 0 0) h
  norm_num [obliqueN, obliqueM, Matrix.mul_apply, Fin.sum_univ_succ] at he

def obliquePowers : ℕ → Matrix (Fin 3) (Fin 3) ℝ
  | 0 => 1
  | 1 => obliqueM
  | _ + 2 => 0

theorem oblique_drazin : IsDrazinInverse obliqueA obliqueD 2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [obliqueA, obliqueD, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]

theorem oblique_fitting_nilpotent :
    fittingNilpotentPart obliqueA obliqueD = obliqueN := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fittingNilpotentPart, complementaryProjection, projection,
      obliqueA, obliqueD, obliqueN, Matrix.mul_apply, Matrix.one_apply,
      Fin.sum_univ_succ]; decide

theorem obliqueN_sq : obliqueN ^ 2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [obliqueN, pow_two, Matrix.mul_apply, Fin.sum_univ_succ]

theorem oblique_mp_singular :
    InfoGeometry.Singular.MoorePenrose.IsMoorePenroseInverse obliqueN obliqueM := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [obliqueN, obliqueM, Matrix.mul_apply, Fin.sum_univ_succ]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [obliqueN, obliqueM, Matrix.mul_apply, Fin.sum_univ_succ]
  · change (obliqueN * obliqueM).conjTranspose = _
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [obliqueN, obliqueM, Matrix.conjTranspose_apply,
        Matrix.mul_apply, Fin.sum_univ_succ]
  · change (obliqueM * obliqueN).conjTranspose = _
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [obliqueN, obliqueM, Matrix.conjTranspose_apply,
        Matrix.mul_apply, Fin.sum_univ_succ]

/-- Native canonical witnesses obtained through the existing MP bridge. -/
theorem oblique_mp_family :
    PowerMPFamily (fittingNilpotentPart obliqueA obliqueD) obliquePowers := by
  intro m
  rw [oblique_fitting_nilpotent]
  cases m with
  | zero =>
    simp [obliquePowers, InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse]
  | succ m =>
    cases m with
    | zero =>
      simpa [obliquePowers] using oblique_mp_singular.toCanonical
    | succ m =>
      have hp : obliqueN ^ (m + 1 + 1) = 0 := by
        rw [show m + 1 + 1 = 2 + m by omega, pow_add, obliqueN_sq, zero_mul]
      rw [hp]
      simp [obliquePowers, InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse]

/-- Actual oblique dressed shell at index zero. -/
theorem oblique_shell_zero :
    drazinShellProj obliqueA obliqueD obliquePowers 0 =
      !![0, 0, -1/2; 0, 0, -1/2; 0, 0, 1] := by
  unfold drazinShellProj shellProj rangeProj
  simp only [oblique_fitting_nilpotent]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [complementaryProjection, projection, obliqueA, obliqueD,
      obliqueN, obliqueM, obliquePowers, Matrix.mul_apply, Matrix.one_apply,
      Fin.sum_univ_succ]

/-- Actual oblique dressed shell at index one. -/
theorem oblique_shell_one :
    drazinShellProj obliqueA obliqueD obliquePowers 1 =
      !![0, -1, -1/2; 0, 1, 1/2; 0, 0, 0] := by
  unfold drazinShellProj shellProj rangeProj
  simp only [oblique_fitting_nilpotent]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [complementaryProjection, projection, obliqueA, obliqueD,
      obliqueN, obliqueM, obliquePowers, pow_succ, Matrix.mul_apply,
      Matrix.one_apply, Fin.sum_univ_succ]

theorem oblique_corner_eq :
    interShellPeirceCorner obliqueA obliqueD obliquePowers 1 0 = obliqueN := by
  unfold interShellPeirceCorner
  rw [oblique_shell_one, oblique_shell_zero]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [obliqueA, obliqueN, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Canonical MP witness, ready for the native inter-shell Hodge theorem. -/
theorem oblique_corner_mp :
    InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse
      (interShellPeirceCorner obliqueA obliqueD obliquePowers 1 0) obliqueM := by
  rw [oblique_corner_eq]
  exact oblique_mp_singular.toCanonical

/-- The reverse-corner product has entry zero at (2,0), whereas M has -1/2. -/
theorem oblique_reverse_corner_entry :
    (drazinShellProj obliqueA obliqueD obliquePowers 0 * obliqueM *
      drazinShellProj obliqueA obliqueD obliquePowers 1) 2 0 = 0 := by
  rw [oblique_shell_zero, oblique_shell_one]
  norm_num [obliqueM, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Oblique shell localization does not put the MP inverse in the reverse corner. -/
theorem oblique_inverse_not_reverse_corner :
    drazinShellProj obliqueA obliqueD obliquePowers 0 * obliqueM *
      drazinShellProj obliqueA obliqueD obliquePowers 1 ≠ obliqueM := by
  intro h
  have he := congrArg (fun B : Matrix (Fin 3) (Fin 3) ℝ => B 2 0) h
  rw [oblique_reverse_corner_entry] at he
  norm_num [obliqueM] at he

end
end InfoGeometry.Canonical.ObliqueShellCounterexample
