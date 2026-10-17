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

/-- The vacuum/top coordinate transposition is symmetric, hence orthogonal by
`zornJWConjugator_sq`. -/
theorem zornJWConjugator_transpose :
    zornJWConjugatorᵀ = zornJWConjugator := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [zornJWConjugator, Matrix.transpose_apply]

/-- The basis-change matrix is orthogonal for the standard Euclidean form. -/
theorem zornJWConjugator_is_orthogonal :
    zornJWConjugatorᵀ * zornJWConjugator = (1 : Matrix (Fin 8) (Fin 8) ℝ) := by
  rw [zornJWConjugator_transpose, zornJWConjugator_sq]

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


/-!
### Section 2 — The Six-Generator Cl(3,3) Anticommutator, Signature Match and Square Law

`zornMajoranaVec` indexes the six phase-space vectors by the same `Fin 6` used by
`majoranaGenR`, so the Zorn left actions and the Jordan–Wigner generators can be compared
index by index. The results below close the loop between
`SplitOctonionClifford33Soldering`'s anticommutator law and the literal Jordan–Wigner
matrices: the `8 × 8` matrices of the Zorn left multiplications by `ι(zornMajoranaVec a)`
obey `{Mₐ, M_b} = δ_{ab} · 2η_a · I₈`, where `η = majoranaSignatureR` is exactly the
Jordan–Wigner split signature.

Note the normalisation: on these six vectors the para-Kähler metric is `g = 2η`, not `η`.
That is why the anticommutator carries the factor `2η_a` while the square carries only `η_a`.
Also note these vectors are **not** on the `Cl(3,3)` null cone: `⟨u, v⟩ = η_a ≠ 0`, which is
precisely what allows a generator to square to `±I₈`.
-/

/-- The six non-pure phase-space vectors whose Zorn left actions **satisfy the `Cl(3,3)`
relations** (surjectivity onto `Cl(3,3)` is not asserted here), indexed so
`zornMajoranaVec (modeEvenIdx k) = zornMajoranaPlusVector k` and
`zornMajoranaVec (modeOddIdx k) = zornMajoranaMinusVector k`. -/
def zornMajoranaVec : Fin 6 → ParaKahlerVec ℝ
  | ⟨0, _⟩ => zornMajoranaPlusVector 0
  | ⟨1, _⟩ => zornMajoranaMinusVector 0
  | ⟨2, _⟩ => zornMajoranaPlusVector 1
  | ⟨3, _⟩ => zornMajoranaMinusVector 1
  | ⟨4, _⟩ => zornMajoranaPlusVector 2
  | ⟨5, _⟩ => zornMajoranaMinusVector 2

theorem zornMajoranaVec_modeEvenIdx (k : Fin 3) :
    zornMajoranaVec (modeEvenIdx k) = zornMajoranaPlusVector k := by
  fin_cases k <;> rfl

theorem zornMajoranaVec_modeOddIdx (k : Fin 3) :
    zornMajoranaVec (modeOddIdx k) = zornMajoranaMinusVector k := by
  fin_cases k <;> rfl

/-- **The six Zorn Majorana vectors are not on the `Cl(3,3)` null cone.**
`q(zₐ) = ⟨u, v⟩ = majoranaSignatureR a ≠ 0`, which is exactly what allows a generator
to square to `±I₈` rather than to be nilpotent. This formalizes the null-cone remark in
the docstring of `paraKahlerMetric_zornMajoranaVec` below. -/
theorem zornMajoranaVec_not_isOnNullCone (a : Fin 6) :
    ¬ IsOnNullCone (zornMajoranaVec a) := by
  rw [isOnNullCone_iff_vec3Dot_zero]
  fin_cases a <;>
    simp [zornMajoranaVec, zornMajoranaPlusVector, zornMajoranaMinusVector, vec3Dot]

/-- **Signature match.** The para-Kähler metric restricted to the six Zorn Majorana vectors is
`2η`, where `η` is the Jordan–Wigner split signature:
`g(zₐ, z_b) = δ_{ab} · 2 · η_a`. In particular these vectors are **not** on the `Cl(3,3)`
null cone: `q(zₐ) = ⟨u, v⟩ = η_a ≠ 0`. -/
theorem paraKahlerMetric_zornMajoranaVec (a b : Fin 6) :
    paraKahlerMetric (zornMajoranaVec a) (zornMajoranaVec b)
      = if a = b then 2 * majoranaSignatureR a else 0 := by
  fin_cases a <;> fin_cases b <;>
    (simp [zornMajoranaVec, zornMajoranaPlusVector, zornMajoranaMinusVector,
      paraKahlerMetric, vec3Dot, majoranaSignatureR, majoranaSignatureZ] <;> ring)

theorem paraKahlerMetric_zornMajoranaVec_self (a : Fin 6) :
    paraKahlerMetric (zornMajoranaVec a) (zornMajoranaVec a) = 2 * majoranaSignatureR a := by
  fin_cases a <;>
    (norm_num [zornMajoranaVec, zornMajoranaPlusVector, zornMajoranaMinusVector,
      paraKahlerMetric, vec3Dot, majoranaSignatureR, majoranaSignatureZ])

theorem paraKahlerMetric_zornMajoranaVec_offdiag {a b : Fin 6} (hab : a ≠ b) :
    paraKahlerMetric (zornMajoranaVec a) (zornMajoranaVec b) = 0 := by
  rw [paraKahlerMetric_zornMajoranaVec, ite_eq_right hab]

/-- **Cl(3,3) anticommutator for the six Zorn Majorana generators, in `8 × 8` matrix-product
form.** The genuine real matrices `Mₐ` of the Zorn left multiplications by `ι(zornMajoranaVec a)`
satisfy `{Mₐ, M_b} = δ_{ab} · 2η_a · I₈`. This is the `M_8(ℝ)`-level statement that closes the
loop with `zorn_leftActMatrix_clifford33`, now instantiated on the six generators. -/
theorem zornLeftActMatrix_majorana_clifford33 (a b : Fin 6) :
    zornLeftActMatrix (embedVec (zornMajoranaVec a))
        * zornLeftActMatrix (embedVec (zornMajoranaVec b))
      + zornLeftActMatrix (embedVec (zornMajoranaVec b))
        * zornLeftActMatrix (embedVec (zornMajoranaVec a))
      = (if a = b then 2 * majoranaSignatureR a else 0) • (1 : Matrix (Fin 8) (Fin 8) ℝ) := by
  rw [zorn_leftActMatrix_clifford33, paraKahlerMetric_zornMajoranaVec]

/-- Distinct Zorn Majorana generators anticommute as `8 × 8` matrices, exactly as the literal
Jordan–Wigner generators do. -/
theorem zornLeftActMatrix_majorana_anticomm {a b : Fin 6} (hab : a ≠ b) :
    zornLeftActMatrix (embedVec (zornMajoranaVec a))
        * zornLeftActMatrix (embedVec (zornMajoranaVec b))
      + zornLeftActMatrix (embedVec (zornMajoranaVec b))
        * zornLeftActMatrix (embedVec (zornMajoranaVec a))
      = 0 := by
  rw [zornLeftActMatrix_majorana_clifford33, ite_eq_right hab]
  simp

/-- Index-uniform version of the two mode-indexed conjugacy theorems. -/
theorem zornLeftActMatrix_majorana_eq_conjugate (a : Fin 6) :
    zornLeftActMatrix (embedVec (zornMajoranaVec a))
      = zornJWConjugator * majoranaGenR a * zornJWConjugator := by
  fin_cases a
  · simpa [zornMajoranaVec, modeEvenIdx] using zornLeftActMatrix_majoranaPlus_eq_conjugate 0
  · simpa [zornMajoranaVec, modeOddIdx] using zornLeftActMatrix_majoranaMinus_eq_conjugate 0
  · simpa [zornMajoranaVec, modeEvenIdx] using zornLeftActMatrix_majoranaPlus_eq_conjugate 1
  · simpa [zornMajoranaVec, modeOddIdx] using zornLeftActMatrix_majoranaMinus_eq_conjugate 1
  · simpa [zornMajoranaVec, modeEvenIdx] using zornLeftActMatrix_majoranaPlus_eq_conjugate 2
  · simpa [zornMajoranaVec, modeOddIdx] using zornLeftActMatrix_majoranaMinus_eq_conjugate 2

/-- **Square law.** `Mₐ² = η_a I₈`, i.e. the Zorn left actions square exactly like the
Jordan–Wigner generators. In the para-Kähler metric normalisation this reads
`Mₐ² = (g(zₐ,zₐ)/2) I₈`: `g` is twice the Jordan–Wigner signature form on these vectors. -/
theorem zornLeftActMatrix_majorana_sq (a : Fin 6) :
    zornLeftActMatrix (embedVec (zornMajoranaVec a)) ^ 2
      = majoranaSignatureR a • (1 : Matrix (Fin 8) (Fin 8) ℝ) := by
  have h : zornLeftActMatrix (embedVec (zornMajoranaVec a))
        * zornLeftActMatrix (embedVec (zornMajoranaVec a))
      + zornLeftActMatrix (embedVec (zornMajoranaVec a))
        * zornLeftActMatrix (embedVec (zornMajoranaVec a))
      = (2 * majoranaSignatureR a) • (1 : Matrix (Fin 8) (Fin 8) ℝ) := by
    rw [zornLeftActMatrix_majorana_clifford33]
    simp
  rw [pow_two]
  funext i j
  have hh := congrFun (congrFun h i) j
  change (zornLeftActMatrix (embedVec (zornMajoranaVec a))
        * zornLeftActMatrix (embedVec (zornMajoranaVec a))) i j
      + (zornLeftActMatrix (embedVec (zornMajoranaVec a))
        * zornLeftActMatrix (embedVec (zornMajoranaVec a))) i j
      = (2 * majoranaSignatureR a) * ((1 : Matrix (Fin 8) (Fin 8) ℝ) i j) at hh
  change (zornLeftActMatrix (embedVec (zornMajoranaVec a))
        * zornLeftActMatrix (embedVec (zornMajoranaVec a))) i j
      = majoranaSignatureR a * ((1 : Matrix (Fin 8) (Fin 8) ℝ) i j)
  nlinarith [hh]

/-- The para-Kähler metric normalisation on the Majorana vectors is twice the Jordan–Wigner
signature form. -/
theorem zornLeftActMatrix_majorana_sq_eq_metric (a : Fin 6) :
    zornLeftActMatrix (embedVec (zornMajoranaVec a)) ^ 2
      = (paraKahlerMetric (zornMajoranaVec a) (zornMajoranaVec a) / 2)
          • (1 : Matrix (Fin 8) (Fin 8) ℝ) := by
  rw [zornLeftActMatrix_majorana_sq, paraKahlerMetric_zornMajoranaVec_self]
  have h : ((2 * majoranaSignatureR a) / 2 : ℝ) = majoranaSignatureR a := by ring
  rw [h]

/-- The Zorn Majorana square agrees with the Jordan–Wigner square. -/
theorem zornLeftActMatrix_majorana_sq_eq_majoranaGenR (a : Fin 6) :
    zornLeftActMatrix (embedVec (zornMajoranaVec a)) ^ 2 = majoranaGenR a ^ 2 := by
  rw [zornLeftActMatrix_majorana_sq, pow_two, majoranaGenR_sq]

end InfoGeometry.Canonical.SplitOctonionJordanWignerIntertwiner
