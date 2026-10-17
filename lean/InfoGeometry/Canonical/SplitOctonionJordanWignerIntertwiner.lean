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


/-!
### Section 3 — The Basis Change Is a `Cl(3,3)` Intertwiner

The Zorn `8 × 8` real Clifford action and the 3-qubit Jordan–Wigner action are conjugate
representations, with matching generator relations. This section records that relation by
matching the Zorn odd-superbracket against `majoranaGenR_clifford_superBracket`.
-/

/-- **The six Zorn Majorana left actions and the six literal Jordan–Wigner generators have the
*same* `Cl(3,3)` odd-superbracket.** Together with
`zornLeftActMatrix_majorana_eq_conjugate`, this states that the two $8\times 8$ actions are
conjugate representations with matching generator relations.

The para-Kähler normalisation factor `2η` shows up in both sides with the same sign and the
same factor `2`, so it cancels; see `paraKahlerMetric_zornMajoranaVec_self` for the statement
that `g(zₐ, zₐ) = 2ηₐ` on these six vectors. -/
theorem zornLeftActMatrix_majorana_superBracket_eq (a b : Fin 6) :
    ChakravalaGA.superBracket (R := ℝ) .odd .odd
        (zornLeftActMatrix (embedVec (zornMajoranaVec a)))
        (zornLeftActMatrix (embedVec (zornMajoranaVec b)))
      = ChakravalaGA.superBracket (R := ℝ) .odd .odd (majoranaGenR a) (majoranaGenR b) := by
  rw [majoranaGenR_clifford_superBracket,
    ChakravalaGA.superBracket_fermionic]
  exact zornLeftActMatrix_majorana_clifford33 a b

/-- The same statement in explicit matrix-anticommutator form:
`MₐM_b + M_bMₐ = ΓₐΓ_b + Γ_bΓₐ`. -/
theorem zornLeftActMatrix_majorana_anticomm_eq_majoranaGenR (a b : Fin 6) :
    zornLeftActMatrix (embedVec (zornMajoranaVec a))
        * zornLeftActMatrix (embedVec (zornMajoranaVec b))
      + zornLeftActMatrix (embedVec (zornMajoranaVec b))
        * zornLeftActMatrix (embedVec (zornMajoranaVec a))
      = majoranaGenR a * majoranaGenR b + majoranaGenR b * majoranaGenR a := by
  rw [← ChakravalaGA.superBracket_fermionic (R := ℝ),
    ← ChakravalaGA.superBracket_fermionic (R := ℝ)]
  exact zornLeftActMatrix_majorana_superBracket_eq a b


/-!
### Section 4 — Coordinate-Level Description of the Fock-Basis Change

`zornJWConjugator` is defined as a literal `!![]` array. The theorems in this section give its
meaning: it is the permutation matrix of `zornJWFockSwap`, which exchanges the vacuum ket
`|000⟩` (coordinate `0`, the `Λ⁰` scalar `a`) with the top-state ket `|111⟩` (coordinate `7`,
the `Λ³` scalar `b`) and fixes the six fermionic kets `1 … 6` carrying the `Λ¹ ⊕ Λ²` sheets.
Note that the Levi-Civita / Hodge orientation signs do **not** live in `zornJWConjugator`; they
are already built into the chart `fin8ToZorn` (whose `v` block is `![ψ 3, -ψ 5, ψ 6]`), as
certified by `fin8ToZorn_left_inv` / `fin8ToZorn_right_inv` in
`ZornSplitOctonionFin8Bridge`.
-/

/-- The permutation of the eight Fock basis coordinates induced by `zornJWConjugator`: the
vacuum ket `|000⟩` (coordinate `0`, carrying the `Λ⁰` scalar `a`) is exchanged with the
top-state ket `|111⟩` (coordinate `7`, carrying the `Λ³` scalar `b`), and all six fermionic
kets are fixed. This is the coordinate-level content of the basis change. -/
def zornJWFockSwap (j : Fin 8) : Fin 8 :=
  if j = 0 then 7 else if j = 7 then 0 else j

@[simp] theorem zornJWFockSwap_zero : zornJWFockSwap 0 = 7 := by
  simp [zornJWFockSwap]

@[simp] theorem zornJWFockSwap_seven : zornJWFockSwap 7 = 0 := by
  simp [zornJWFockSwap]

/-- The six fermionic kets — coordinates `1 … 6`, carrying the `Λ¹ ⊕ Λ²` sheets — are fixed. -/
theorem zornJWFockSwap_middle {j : Fin 8} (hj0 : j ≠ 0) (hj7 : j ≠ 7) :
    zornJWFockSwap j = j := by
  simp [zornJWFockSwap, hj0, hj7]

/-- `zornJWFockSwap` is an involution: the basis change is its own inverse. -/
theorem zornJWFockSwap_involutive (j : Fin 8) : zornJWFockSwap (zornJWFockSwap j) = j := by
  fin_cases j <;> simp [zornJWFockSwap]

/-- `zornJWFockSwap` is injective, hence a genuine permutation of the Fock basis. -/
theorem zornJWFockSwap_injective : Function.Injective zornJWFockSwap :=
  fun i j hij => by
    rw [← zornJWFockSwap_involutive i, ← zornJWFockSwap_involutive j, hij]

/-- **Coherence with `zornJWConjugator_det`.** The `zornJWConjugator_det` proof builds the
same permutation as the local `σ : Equiv.Perm (Fin 8) := Equiv.swap 0 7`; this lemma identifies
that object with `zornJWFockSwap`, so the two descriptions of the basis change are provably the
same permutation rather than two unrelated declarations. -/
theorem zornJWFockSwap_eq_equivSwap : zornJWFockSwap = (Equiv.swap 0 7) := by
  funext j
  fin_cases j <;> simp [zornJWFockSwap, Equiv.swap_apply_def]

/-- **Entrywise description of the conjugator.** `zornJWConjugator` is exactly the permutation
matrix of `zornJWFockSwap`: row `i` carries a single `1`, in column `zornJWFockSwap i`. -/
theorem zornJWConjugator_entries (i j : Fin 8) :
    zornJWConjugator i j = if j = zornJWFockSwap i then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> norm_num [zornJWConjugator, zornJWFockSwap]

/-- **Action of the basis change on the Fock basis.** The `k`-th basis ket is sent to the
`zornJWFockSwap k`-th basis ket. This is the general form of the three `mulVec` computations
that `Cl11ChiralVolumeNilpotentQuotientSynthesis` previously brute-forced case by case. -/
theorem zornJWConjugator_mulVec_single (k i : Fin 8) :
    zornJWConjugator.mulVec (Pi.single k (1 : ℝ)) i
      = if i = zornJWFockSwap k then (1 : ℝ) else 0 := by
  have hid : ∀ j : Fin 8, k = zornJWFockSwap j ↔ j = zornJWFockSwap k := by
    intro j
    constructor
    · intro h
      exact (calc zornJWFockSwap k = zornJWFockSwap (zornJWFockSwap j) := by rw [h]
        _ = j := zornJWFockSwap_involutive j).symm
    · intro h
      exact (calc zornJWFockSwap j = zornJWFockSwap (zornJWFockSwap k) := by rw [h]
        _ = k := zornJWFockSwap_involutive k).symm
  have h : zornJWConjugator.mulVec (Pi.single k (1 : ℝ)) i = zornJWConjugator i k := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [h, zornJWConjugator_entries]
  by_cases hi : i = zornJWFockSwap k <;> simp [hi, hid i, zornJWFockSwap_involutive]

/-!
### Section 5 — The Vacuum/Top Swap Is Forced

`zornJWConjugator` is *not* the identity on the Fock basis, and Section 4 pinned down exactly
what it does. This section proves the uniqueness statement that is actually reachable: any
permutation of the Fock basis that intertwines all six Zorn Majorana left actions with the six
Jordan–Wigner generators **and** preserves the fermionic sector must exchange the vacuum ket
`|000⟩` with the top-state ket `|111⟩`. The intertwiner is therefore completely determined
inside the assumption that the six fermionic kets are preserved.

**Scope note (honest boundary).** Unrestricted uniqueness over all `8! = 40320` permutations of
`Fin 8` is *not* claimed here; `hmiddle` is a genuine hypothesis, not a hidden assumption.
This theorem only establishes the vacuum/top swap after the six middle basis states are assumed
fixed; it makes no assertion about how many permutations satisfy the intertwining condition
without that hypothesis.
-/

/-- **The vacuum/top swap is forced.** Let `p` be a permutation of the Fock basis that
intertwines all six Zorn Majorana left actions with the six Jordan–Wigner generators, and that
preserves the fermionic sector (the six coordinates `1 … 6` carrying `Λ¹ ⊕ Λ²`). Then `p`
exchanges the vacuum ket and the top-state ket: `p 0 = 7` and `p 7 = 0`.

Read together with `zornJWFockSwap`, this says the basis change `zornJWConjugator` is not the
identity and — once the six fermionic kets are known to be preserved — has only one possible
non-trivial action left: the `|000⟩ ↔ |111⟩` swap.

Scope: this is *not* full uniqueness among all `8! = 40320` permutations of the Fock basis.
The `hmiddle` hypothesis is what collapses the search space, and the conjuacy hypothesis `h` is
used only to refute the single remaining candidate `p = id` via one matrix entry
(`zornLeftActMatrix … ⟨0⟩ 0 3 = 1` while `majoranaGenR ⟨0⟩ 0 3 = 0`). Downstream users should
therefore not read this as certifying six-generator intertwining rigidity: the proof consumes
far less of `h` than `h` states. Unrestricted uniqueness is **not** asserted here. -/
theorem zornJWConjugator_swap_forced (p : Fin 8 ≃ Fin 8)
    (hmiddle : ∀ j : Fin 8, j ≠ 0 → j ≠ 7 → p j = j)
    (h : ∀ (a : Fin 6) (i j : Fin 8),
      zornLeftActMatrix (embedVec (zornMajoranaVec a)) i j
        = majoranaGenR a (p i) (p.symm j)) :
    p 0 = 7 ∧ p 7 = 0 := by
  have key : zornLeftActMatrix (embedVec (zornMajoranaVec ⟨0, by decide⟩)) 0 3 = 1 := by
    rw [zornLeftActMatrix_majorana_eq_conjugate ⟨0, by decide⟩]
    rw [Matrix.mul_assoc]
    norm_num [zornJWConjugator, majoranaGenR, majoranaGenZ, gamma1PlusZ,
      Matrix.mul_apply, Fin.sum_univ_succ]
  -- A coordinate in the scalar pair can only be sent to the scalar pair.
  have honly : ∀ (c : Fin 8) (hc : c = 0 ∨ c = 7), p c = 0 ∨ p c = 7 := by
    intro c hc
    obtain ⟨k, hk⟩ : ∃ k : Fin 8, p c = k := ⟨p c, rfl⟩
    have hnm : ∀ j : Fin 8, j ≠ 0 → j ≠ 7 → p j ≠ p c := by
      intro j hj0 hj7 heq
      rcases hc with hc0 | hc7
      · exact absurd (p.injective heq) (fun e => hj0 (e.trans hc0))
      · exact absurd (p.injective heq) (fun e => hj7 (e.trans hc7))
    fin_cases k
    · exact Or.inl hk
    · exact absurd ((hmiddle 1 (by decide) (by decide)).trans hk.symm)
        (hnm 1 (by decide) (by decide))
    · exact absurd ((hmiddle 2 (by decide) (by decide)).trans hk.symm)
        (hnm 2 (by decide) (by decide))
    · exact absurd ((hmiddle 3 (by decide) (by decide)).trans hk.symm)
        (hnm 3 (by decide) (by decide))
    · exact absurd ((hmiddle 4 (by decide) (by decide)).trans hk.symm)
        (hnm 4 (by decide) (by decide))
    · exact absurd ((hmiddle 5 (by decide) (by decide)).trans hk.symm)
        (hnm 5 (by decide) (by decide))
    · exact absurd ((hmiddle 6 (by decide) (by decide)).trans hk.symm)
        (hnm 6 (by decide) (by decide))
    · exact Or.inr hk
  rcases honly 0 (Or.inl rfl) with h0 | h0 <;> rcases honly 7 (Or.inr rfl) with h7 | h7
  · exact absurd (p.injective (h0.trans h7.symm)) (by decide)
  · exfalso
    have hid : ∀ j : Fin 8, p j = j := by
      intro j
      fin_cases j
      · exact h0
      · exact hmiddle 1 (by decide) (by decide)
      · exact hmiddle 2 (by decide) (by decide)
      · exact hmiddle 3 (by decide) (by decide)
      · exact hmiddle 4 (by decide) (by decide)
      · exact hmiddle 5 (by decide) (by decide)
      · exact hmiddle 6 (by decide) (by decide)
      · exact h7
    have h03 := h ⟨0, by decide⟩ 0 3
    have hpe : p = Equiv.refl (Fin 8) :=
      Equiv.ext (f := p) (g := Equiv.refl (Fin 8)) (fun j => hid j)
    rw [hpe] at h03
    rw [key] at h03
    norm_num [majoranaGenR, majoranaGenZ, gamma1PlusZ] at h03
  · exact ⟨h0, h7⟩
  · exact absurd (p.injective (h0.trans h7.symm)) (by decide)

/-- **Corollary: the intertwiner is the Fock-basis swap.** Under the hypotheses of
`zornJWConjugator_swap_forced`, `p` agrees with `zornJWFockSwap` on all eight coordinates,
i.e. `p` is exactly the permutation that `zornJWConjugator` realises. -/
theorem zornJWConjugator_eq_of_intertwiner (p : Fin 8 ≃ Fin 8)
    (hmiddle : ∀ j : Fin 8, j ≠ 0 → j ≠ 7 → p j = j)
    (h : ∀ (a : Fin 6) (i j : Fin 8),
      zornLeftActMatrix (embedVec (zornMajoranaVec a)) i j
        = majoranaGenR a (p i) (p.symm j)) :
    ∀ j : Fin 8, p j = zornJWFockSwap j := by
  obtain ⟨h0, h7⟩ := zornJWConjugator_swap_forced p hmiddle h
  intro j
  fin_cases j
  · simpa [zornJWFockSwap] using h0
  · exact hmiddle 1 (by decide) (by decide)
  · exact hmiddle 2 (by decide) (by decide)
  · exact hmiddle 3 (by decide) (by decide)
  · exact hmiddle 4 (by decide) (by decide)
  · exact hmiddle 5 (by decide) (by decide)
  · exact hmiddle 6 (by decide) (by decide)
  · simpa [zornJWFockSwap] using h7

end InfoGeometry.Canonical.SplitOctonionJordanWignerIntertwiner
