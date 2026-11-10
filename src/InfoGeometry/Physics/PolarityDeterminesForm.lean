/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Physics.VoigtConformalFactor

/-!
# Polarity determines the form

Coordinate-certification layer for the polarity theorem, arbitrated by
`proofs/polarity_determines_form.py` (9/9 strict checks: a ring-general
unit-minor certificate over the four diagonal columns, 𝔽₂/𝔽₃/𝔽₅/𝔽₁₀₁ rank
confirmations, and a one-dimensional nullspace isolation equal to `vec(η)`).

With `eta = diag(1, 1, 1, -1)` (time slot last; reused verbatim from
`VoigtConformalFactor`), a bilinear form on `R^4` is presented by a matrix
`m` through `dotProduct x (m *ᵥ y)`.  The functional-pair hypothesis — every
`eta`-orthogonal pair is also `m`-annihilated — forces `m = (m 0 0) • eta`
over an *arbitrary* `CommRing R`:

* the twelve ordered basis pairs `(e_i, e_j)`, `i ≠ j`, kill the
  off-diagonal entries individually (`ediag`, `eoff`), with no `2`-inversion;
* the three null self-pairs `(1,0,0,1)`, `(0,1,0,1)`, `(0,0,1,1)` — all on
  the `eta`-light cone — force `m 0 0 + m 3 3 = 0`, `m 1 1 + m 3 3 = 0`,
  `m 2 2 + m 3 3 = 0`, hence `m 1 1 = m 2 2 = m 0 0` and `m 3 3 = -m 0 0`.

No `Invertible 2` is used: the certificate is division-free, so the theorem
holds over every commutative base ring (the census's finite-field ranks
rule out characteristic degeneracies of the spike system).
-/

namespace InfoGeometry.Physics.PolarityDeterminesForm

open scoped Matrix
open InfoGeometry.Physics.VoigtConformalFactor

variable {R : Type*} [Ring R]

/-- Matrix units in the same `Fin 4` endomorphism carrier used for the form. -/
def polarityMatrixE01 : Matrix (Fin 4) (Fin 4) R := Matrix.single 0 1 (1 : R)

def polarityMatrixE10 : Matrix (Fin 4) (Fin 4) R := Matrix.single 1 0 (1 : R)

/-- Over a nontrivial coefficient ring, the form's matrix carrier is genuinely
noncommutative: opposite matrix units give distinct diagonal units. -/
theorem polarityMatrix_noncommutative_witness [Nontrivial R] :
    polarityMatrixE01 (R := R) * polarityMatrixE10 (R := R) ≠
      polarityMatrixE10 (R := R) * polarityMatrixE01 (R := R) := by
  intro h
  simp only [polarityMatrixE01, polarityMatrixE10] at h
  rw [Matrix.single_mul_single_same, Matrix.single_mul_single_same] at h
  have h00 := congrArg (fun M : Matrix (Fin 4) (Fin 4) R => M 0 0) h
  have hOne : (1 : R) = 0 := by simpa [Matrix.single] using h00
  exact one_ne_zero hOne

/-- The eta-pairing of the unit vectors: a singleton pair evaluates to the
corresponding entry of `eta` itself. -/
theorem dotProduct_single_mulVec_single (i j : Fin 4) :
    dotProduct (Pi.single i (1 : R)) (eta *ᵥ Pi.single j (1 : R)) = eta i j := by
  simp [dotProduct, Matrix.mulVec, eta, Pi.single_apply]

/-- The eta matrix is diagonal off its main diagonal — the only fact about
`eta` needed beyond its explicit entries. -/
theorem eta_offDiag {i j : Fin 4} (h : i ≠ j) : eta i j = (0 : R) := by
  fin_cases i <;> fin_cases j <;>
    simp [InfoGeometry.Physics.VoigtConformalFactor.eta,
      Matrix.cons_val_zero, Matrix.cons_val_succ] at h ⊢

/-- **Polarity determines the form**: a matrix `m` that annihilates every
`eta`-orthogonal pair is a scalar multiple of `eta`. -/
theorem polarity_determines_form (m : Matrix (Fin 4) (Fin 4) R)
    (hm : ∀ x y : Fin 4 → R, dotProduct x (eta *ᵥ y) = 0 →
        dotProduct x (m *ᵥ y) = 0) :
    m = (m 0 0) • eta := by
  -- the twelve ordered unit pairs kill the off-diagonal entries
  have eoff : ∀ i j : Fin 4, i ≠ j → m i j = 0 := by
    intro i j hij
    have h := hm (Pi.single i (1 : R)) (Pi.single j (1 : R))
      (by rw [dotProduct_single_mulVec_single i j, eta_offDiag hij])
    simpa [dotProduct, Matrix.mulVec, Pi.single_apply] using h
  -- the three null self-pairs force the diagonal relations
  have n0 : m 0 0 + m 3 3 = 0 := by
    have h := hm (![1, 0, 0, 1] : Fin 4 → R) (![1, 0, 0, 1] : Fin 4 → R)
      (by simp [dotProduct, Matrix.mulVec, eta, Matrix.cons_val_zero,
        Matrix.cons_val_succ, Fin.sum_univ_succ])
    simpa [dotProduct, Matrix.mulVec, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.sum_univ_succ, eoff 0 3 (by simp), eoff 3 0 (by simp)]
      using h
  have n1 : m 1 1 + m 3 3 = 0 := by
    have h := hm (![0, 1, 0, 1] : Fin 4 → R) (![0, 1, 0, 1] : Fin 4 → R)
      (by simp [dotProduct, Matrix.mulVec, eta, Matrix.cons_val_zero,
        Matrix.cons_val_succ, Fin.sum_univ_succ])
    simpa [dotProduct, Matrix.mulVec, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.sum_univ_succ, eoff 1 3 (by simp), eoff 3 1 (by simp)]
      using h
  have n2 : m 2 2 + m 3 3 = 0 := by
    have h := hm (![0, 0, 1, 1] : Fin 4 → R) (![0, 0, 1, 1] : Fin 4 → R)
      (by simp [dotProduct, Matrix.mulVec, eta, Matrix.cons_val_zero,
        Matrix.cons_val_succ, Fin.sum_univ_succ])
    simpa [dotProduct, Matrix.mulVec, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.sum_univ_succ, eoff 2 3 (by simp), eoff 3 2 (by simp)]
      using h
  have q11 : m 1 1 = m 0 0 := add_right_cancel (n1.trans n0.symm)
  have q22 : m 2 2 = m 0 0 := add_right_cancel (n2.trans n0.symm)
  have q33 : m 3 3 = -m 0 0 := eq_neg_of_add_eq_zero_right n0
  ext i j
  by_cases h : i = j
  · subst h
    fin_cases i <;> simp [eta, q11, q22, q33]
  · simp [Pi.smul_apply, smul_eq_mul, eta_offDiag h, eoff i j h]

end InfoGeometry.Physics.PolarityDeterminesForm
