/-
Phase 2: Normalized Gell-Mann basis for 𝔰𝔲(3)
- 8 generators gellMann1…8 with Tr(λₐλ_b) = 2δ_{ab}
- Computable data for Lie algebra generators
-/

import Mathlib
import Mathlib.Algebra.Lie.Classical
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Complex.Basic
import InfoGeometry.Algebra.SpecialUnitary

open Matrix
open Fin
open Complex
open LieAlgebra

namespace InfoGeometry.Algebra.GellMann

set_option maxHeartbeats 400000

/-- Helper proof for anti-Hermitian & trace zero matrix membership in 𝔰𝔲(3) -/
private lemma su_mem_proof (M : Matrix (Fin 3) (Fin 3) ℂ)
    (h_dag : Mᴴ = -M) (h_tr : M.trace = 0) : M ∈ su (Fin 3) :=
  ⟨h_dag, h_tr⟩

/-- Gell-Mann matrix 1: λ₁ = [[0, 1, 0], [1, 0, 0], [0, 0, 0]] (anti-Hermitian i λ₁) -/
noncomputable def gellMann1 : su (Fin 3) :=
  ⟨!![0, I, 0; I, 0, 0; 0, 0, 0], by
    constructor
    · ext i j; fin_cases i <;> fin_cases j <;> simp [conjTranspose, Complex.conj_I]
    · simp [Matrix.trace, Fin.sum_univ_three]⟩

/-- Gell-Mann matrix 2: λ₂ = [[0, -i, 0], [i, 0, 0], [0, 0, 0]] (anti-Hermitian i λ₂) -/
noncomputable def gellMann2 : su (Fin 3) :=
  ⟨!![0, -1, 0; 1, 0, 0; 0, 0, 0], by
    constructor
    · ext i j; fin_cases i <;> fin_cases j <;> simp [conjTranspose]
    · simp [Matrix.trace, Fin.sum_univ_three]⟩

/-- Gell-Mann matrix 3: λ₃ = [[1, 0, 0], [0, -1, 0], [0, 0, 0]] (anti-Hermitian i λ₃) -/
noncomputable def gellMann3 : su (Fin 3) :=
  ⟨!![I, 0, 0; 0, -I, 0; 0, 0, 0], by
    constructor
    · ext i j; fin_cases i <;> fin_cases j <;> simp [conjTranspose, Complex.conj_I]
    · simp [Matrix.trace, Fin.sum_univ_three]⟩

/-- Gell-Mann matrix 4: λ₄ = [[0, 0, 1], [0, 0, 0], [1, 0, 0]] (anti-Hermitian i λ₄) -/
noncomputable def gellMann4 : su (Fin 3) :=
  ⟨!![0, 0, I; 0, 0, 0; I, 0, 0], by
    constructor
    · ext i j; fin_cases i <;> fin_cases j <;> simp [conjTranspose, Complex.conj_I]
    · simp [Matrix.trace, Fin.sum_univ_three]⟩

/-- Gell-Mann matrix 5: λ₅ = [[0, 0, -i], [0, 0, 0], [i, 0, 0]] (anti-Hermitian i λ₅) -/
noncomputable def gellMann5 : su (Fin 3) :=
  ⟨!![0, 0, -1; 0, 0, 0; 1, 0, 0], by
    constructor
    · ext i j; fin_cases i <;> fin_cases j <;> simp [conjTranspose]
    · simp [Matrix.trace, Fin.sum_univ_three]⟩

/-- Gell-Mann matrix 6: λ₆ = [[0, 0, 0], [0, 0, 1], [0, 1, 0]] (anti-Hermitian i λ₆) -/
noncomputable def gellMann6 : su (Fin 3) :=
  ⟨!![0, 0, 0; 0, 0, I; 0, I, 0], by
    constructor
    · ext i j; fin_cases i <;> fin_cases j <;> simp [conjTranspose, Complex.conj_I]
    · simp [Matrix.trace, Fin.sum_univ_three]⟩

/-- Gell-Mann matrix 7: λ₇ = [[0, 0, 0], [0, 0, -i], [0, i, 0]] (anti-Hermitian i λ₇) -/
noncomputable def gellMann7 : su (Fin 3) :=
  ⟨!![0, 0, 0; 0, 0, -1; 0, 1, 0], by
    constructor
    · ext i j; fin_cases i <;> fin_cases j <;> simp [conjTranspose]
    · simp [Matrix.trace, Fin.sum_univ_three]⟩

/-- Gell-Mann matrix 8: λ₈ = (1/√3) [[1, 0, 0], [0, 1, 0], [0, 0, -2]] (anti-Hermitian i λ₈) -/
noncomputable def gellMann8 : su (Fin 3) :=
  ⟨!![I / (Real.sqrt 3 : ℂ), 0, 0; 0, I / (Real.sqrt 3 : ℂ), 0; 0, 0, -2 * I / (Real.sqrt 3 : ℂ)], by
    constructor
    · have h2 : (starRingEnd ℂ) (2 : ℂ) = (2 : ℂ) := Complex.conj_natCast 2
      ext i j; fin_cases i <;> fin_cases j <;> simp [conjTranspose, Complex.conj_I, h2] <;> try ring
    · simp [Matrix.trace, Fin.sum_univ_three]; ring⟩

/-- Array of all 8 Gell-Mann matrices -/
noncomputable def gellMannArray : Array (su (Fin 3)) :=
  #[gellMann1, gellMann2, gellMann3, gellMann4, gellMann5, gellMann6, gellMann7, gellMann8]

/-- Get the a-th Gell-Mann matrix (a : Fin 8) -/
noncomputable def gellMann (a : Fin 8) : su (Fin 3) :=
  gellMannArray.getD a.val gellMann1

end InfoGeometry.Algebra.GellMann