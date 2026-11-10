/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.PeirceCompressionDefect
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Target/helper compression and equivariant Gramians

Block ablation here means the algebraic condition `p * m * p = 0`. It is not
identified with deleting observations from a corpus. Nonvanishing and positivity
require the additional adjoint hypotheses stated below. No learning algorithm,
spectral ordering, or preservation of a particular embedding is assumed proved.
-/

namespace InfoGeometry.LLM.LanguageSymmetry

open Matrix
open scoped ComplexOrder

section Ring

variable {R : Type*} [Ring R]

/-- The existing Peirce defect identifies the compressed square after ablation. -/
theorem compressed_square_eq_helper_product (p m : R)
    (hp : p * p = p) (hablate : p * m * p = 0) :
    p * (m * m) * p = (p * m * (1 - p)) * ((1 - p) * m * p) := by
  simpa only [hablate, zero_mul, sub_zero] using
    Core.PeirceCompressionDefect.compression_square_defect p m hp

end Ring

section Rectangular

variable {P H R : Type*} [Fintype P] [Fintype H] [Semiring R]

/-- Two intertwiners between different spaces give an equivariant round trip. -/
theorem helper_product_commutes
    (u : Matrix P P R) (v : Matrix H H R)
    (a : Matrix P H R) (b : Matrix H P R)
    (ha : u * a = a * v) (hb : v * b = b * u) :
    u * (a * b) = (a * b) * u := by
  calc
    u * (a * b) = (u * a) * b := (Matrix.mul_assoc _ _ _).symm
    _ = (a * v) * b := by rw [ha]
    _ = a * (v * b) := Matrix.mul_assoc _ _ _
    _ = a * (b * u) := by rw [hb]
    _ = (a * b) * u := (Matrix.mul_assoc _ _ _).symm

end Rectangular

section Complex

variable {P H : Type*} [Fintype P] [Fintype H]

omit [Fintype P] in
/-- For complex matrices, a helper Gramian vanishes exactly when its coupling does. -/
theorem helper_gram_ne_zero_iff (a : Matrix P H ℂ) :
    a * aᴴ ≠ 0 ↔ a ≠ 0 :=
  not_congr Matrix.self_mul_conjTranspose_eq_zero

variable [DecidableEq P] [DecidableEq H]

/-- Adjoint compatibility derives the return intertwiner from the outward one.
The two displayed identities are precisely the halves of unitarity used. -/
theorem adjoint_helper_intertwines
    (u : Matrix P P ℂ) (v : Matrix H H ℂ) (a : Matrix P H ℂ)
    (hu : uᴴ * u = 1) (hv : v * vᴴ = 1) (ha : u * a = a * v) :
    v * aᴴ = aᴴ * u := by
  have hadj : aᴴ * uᴴ = vᴴ * aᴴ := by
    simpa only [Matrix.conjTranspose_mul] using congrArg Matrix.conjTranspose ha
  calc
    v * aᴴ = (v * aᴴ) * (uᴴ * u) := by rw [hu, Matrix.mul_one]
    _ = v * (aᴴ * uᴴ) * u := by simp only [Matrix.mul_assoc]
    _ = v * (vᴴ * aᴴ) * u := by rw [hadj]
    _ = (v * vᴴ) * aᴴ * u := by simp only [Matrix.mul_assoc]
    _ = aᴴ * u := by rw [hv, Matrix.one_mul]

/-- A unitary-compatible outward helper map gives an equivariant target Gramian. -/
theorem helper_gram_commutes
    (u : Matrix P P ℂ) (v : Matrix H H ℂ) (a : Matrix P H ℂ)
    (hu : uᴴ * u = 1) (hv : v * vᴴ = 1) (ha : u * a = a * v) :
    u * (a * aᴴ) = (a * aᴴ) * u :=
  helper_product_commutes u v a aᴴ ha (adjoint_helper_intertwines u v a hu hv ha)

/-- Hermitian data turn the ablated compressed square into an actual Gramian. -/
theorem compressed_square_eq_helper_gram (p m : Matrix P P ℂ)
    (hp : p * p = p) (hps : pᴴ = p) (hms : mᴴ = m)
    (hablate : p * m * p = 0) :
    p * (m * m) * p = (p * m * (1 - p)) * (p * m * (1 - p))ᴴ := by
  simpa only [hablate, zero_mul, sub_zero, Matrix.star_eq_conjTranspose] using
    Core.PeirceCompressionDefect.compression_square_defect_star p m hp hps hms

/-- Positivity follows from the adjoint Gram factorization, not from ring algebra. -/
theorem compressed_square_posSemidef (p m : Matrix P P ℂ)
    (hp : p * p = p) (hps : pᴴ = p) (hms : mᴴ = m)
    (hablate : p * m * p = 0) :
    (p * (m * m) * p).PosSemidef := by
  rw [compressed_square_eq_helper_gram p m hp hps hms hablate]
  exact Matrix.posSemidef_self_mul_conjTranspose _

/-- The exact extra condition for survival is nonzero target/helper coupling. -/
theorem compressed_square_ne_zero_iff (p m : Matrix P P ℂ)
    (hp : p * p = p) (hps : pᴴ = p) (hms : mᴴ = m)
    (hablate : p * m * p = 0) :
    p * (m * m) * p ≠ 0 ↔ p * m * (1 - p) ≠ 0 := by
  rw [compressed_square_eq_helper_gram p m hp hps hms hablate]
  exact helper_gram_ne_zero_iff _

end Complex

section Witness

/-- A target projection in a two-dimensional real space. -/
def ablationProjection : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]

/-- A Hermitian operator whose only couplings cross the target/helper cut. -/
def ablationExchange : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

theorem ablationProjection_idempotent :
    ablationProjection * ablationProjection = ablationProjection := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ablationProjection, Matrix.mul_apply, Fin.sum_univ_two]

theorem ablationExchange_direct_zero :
    ablationProjection * ablationExchange * ablationProjection = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ablationProjection, ablationExchange, Matrix.mul_apply, Fin.sum_univ_two]

theorem ablationExchange_square_compression :
    ablationProjection * (ablationExchange * ablationExchange) * ablationProjection =
      ablationProjection := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ablationProjection, ablationExchange, Matrix.mul_apply, Fin.sum_univ_two]

theorem ablationExchange_square_compression_ne_zero :
    ablationProjection * (ablationExchange * ablationExchange) * ablationProjection ≠ 0 := by
  rw [ablationExchange_square_compression]
  intro h
  have h00 := congrArg (fun a : Matrix (Fin 2) (Fin 2) ℝ => a 0 0) h
  norm_num [ablationProjection] at h00

/-- This witness genuinely uses noncommuting operators. -/
theorem ablationExchange_not_commuting :
    ablationProjection * ablationExchange ≠ ablationExchange * ablationProjection := by
  intro h
  have h01 := congrArg (fun a : Matrix (Fin 2) (Fin 2) ℝ => a 0 1) h
  norm_num [ablationProjection, ablationExchange, Matrix.mul_apply, Fin.sum_univ_two] at h01

end Witness

end InfoGeometry.LLM.LanguageSymmetry
