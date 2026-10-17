/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.SplitOctonionClifford33Soldering
import InfoGeometry.Canonical.MajoranaEightByEightJW

/-!
# Zorn left-action and Jordan–Wigner basis change

The canonical `Fin 8` Zorn chart and the literal Jordan–Wigner matrices use the same
occupation ordering, but the two Clifford actions do not have identical matrices in that
chart. The intertwiner swaps the vacuum and top coordinates (`0` and `7`) and fixes the
six middle coordinates. This module proves the six generator identities for that basis
change. It does not assert a universal Clifford-algebra isomorphism.

The corresponding exact integer calculation and carrier-alignment record are in
`scripts/derive_zorn_jw_intertwiner.sage` and `scripts/zorn_jw_intertwiner.json`.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitOctonionJordanWignerIntertwiner

open InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge
open InfoGeometry.Canonical.SplitOctonionParaKahlerNullCone
open InfoGeometry.Canonical.SplitOctonionClifford33Soldering
open InfoGeometry.Canonical.MajoranaEightByEightJW

open scoped Matrix

set_option maxHeartbeats 0

/-- Permutation matrix swapping the vacuum and top coordinates, fixing all others. -/
def zornJWConjugator : Matrix (Fin 8) (Fin 8) ℝ :=
  !![0, 0, 0, 0, 0, 0, 0, 1;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 1, 0;
     1, 0, 0, 0, 0, 0, 0, 0]

/-- The coordinate change is an involution. -/
theorem zornJWConjugator_sq :
    zornJWConjugator * zornJWConjugator = (1 : Matrix (Fin 8) (Fin 8) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [zornJWConjugator, Matrix.mul_apply, Fin.sum_univ_succ, Pi.single_apply]

/-- The vacuum/top coordinate transposition reverses orientation. -/
theorem zornJWConjugator_det : Matrix.det zornJWConjugator = -1 := by
  let σ : Equiv.Perm (Fin 8) := Equiv.swap 0 7
  have hmatrix : zornJWConjugator = (1 : Matrix (Fin 8) (Fin 8) ℝ).submatrix σ id := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [zornJWConjugator, σ, Equiv.swap_apply_def, Matrix.one_apply]
  rw [hmatrix, Matrix.det_permute]
  simp [σ]

/-- The phase-space vector whose Zorn left action corresponds to a positive Majorana mode. -/
def zornMajoranaPlusVector (k : Fin 3) : ParaKahlerVec ℝ where
  u := fun j => if j = k then 1 else 0
  v := fun j => if j = k then 1 else 0

/-- The phase-space vector whose Zorn left action corresponds to a negative Majorana mode. -/
def zornMajoranaMinusVector (k : Fin 3) : ParaKahlerVec ℝ where
  u := fun j => if j = k then 1 else 0
  v := fun j => if j = k then -1 else 0

/-- Positive-mode intertwining: `L_{(eₖ,eₖ)} S = S Γₖ⁺`. -/
theorem zornLeftActMatrix_majoranaPlus_intertwines (k : Fin 3) :
    zornLeftActMatrix (embedVec (zornMajoranaPlusVector k)) * zornJWConjugator =
      zornJWConjugator * majoranaGenR (modeEvenIdx k) := by
  ext i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [zornLeftActMatrix, zornLeftActFin8, zornJWConjugator,
      zornMajoranaPlusVector, embedVec, fin8ToZorn, zornToFin8, zornMul,
      InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge.vec3Dot,
      InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge.vec3Cross,
      majoranaGenR, majoranaGenZ, modeEvenIdx, gamma1PlusZ, gamma2PlusZ,
      gamma3PlusZ, LinearMap.toMatrix_apply, Pi.basisFun_apply,
      Pi.basisFun_repr, Pi.single_apply, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Negative-mode intertwining: `L_{(eₖ,-eₖ)} S = S Γₖ⁻`. -/
theorem zornLeftActMatrix_majoranaMinus_intertwines (k : Fin 3) :
    zornLeftActMatrix (embedVec (zornMajoranaMinusVector k)) * zornJWConjugator =
      zornJWConjugator * majoranaGenR (modeOddIdx k) := by
  ext i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [zornLeftActMatrix, zornLeftActFin8, zornJWConjugator,
      zornMajoranaMinusVector, embedVec, fin8ToZorn, zornToFin8, zornMul,
      InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge.vec3Dot,
      InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge.vec3Cross,
      majoranaGenR, majoranaGenZ, modeOddIdx, gamma1MinusZ, gamma2MinusZ,
      gamma3MinusZ, LinearMap.toMatrix_apply, Pi.basisFun_apply,
      Pi.basisFun_repr, Pi.single_apply, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Matrix-form positive generator identity `Lₖ⁺ = S Γₖ⁺ S`. -/
theorem zornLeftActMatrix_majoranaPlus_eq_conjugate (k : Fin 3) :
    zornLeftActMatrix (embedVec (zornMajoranaPlusVector k)) =
      zornJWConjugator * majoranaGenR (modeEvenIdx k) * zornJWConjugator := by
  calc
    zornLeftActMatrix (embedVec (zornMajoranaPlusVector k)) =
        zornLeftActMatrix (embedVec (zornMajoranaPlusVector k)) *
          zornJWConjugator * zornJWConjugator := by
            calc
              _ = zornLeftActMatrix (embedVec (zornMajoranaPlusVector k)) *
                    (zornJWConjugator * zornJWConjugator) := by
                      rw [zornJWConjugator_sq, Matrix.mul_one]
              _ = _ := by rw [Matrix.mul_assoc]
    _ = zornJWConjugator * majoranaGenR (modeEvenIdx k) * zornJWConjugator := by
      rw [zornLeftActMatrix_majoranaPlus_intertwines]

/-- Matrix-form negative generator identity `Lₖ⁻ = S Γₖ⁻ S`. -/
theorem zornLeftActMatrix_majoranaMinus_eq_conjugate (k : Fin 3) :
    zornLeftActMatrix (embedVec (zornMajoranaMinusVector k)) =
      zornJWConjugator * majoranaGenR (modeOddIdx k) * zornJWConjugator := by
  calc
    zornLeftActMatrix (embedVec (zornMajoranaMinusVector k)) =
        zornLeftActMatrix (embedVec (zornMajoranaMinusVector k)) *
          zornJWConjugator * zornJWConjugator := by
            calc
              _ = zornLeftActMatrix (embedVec (zornMajoranaMinusVector k)) *
                    (zornJWConjugator * zornJWConjugator) := by
                      rw [zornJWConjugator_sq, Matrix.mul_one]
              _ = _ := by rw [Matrix.mul_assoc]
    _ = zornJWConjugator * majoranaGenR (modeOddIdx k) * zornJWConjugator := by
      rw [zornLeftActMatrix_majoranaMinus_intertwines]

end InfoGeometry.Canonical.SplitOctonionJordanWignerIntertwiner
