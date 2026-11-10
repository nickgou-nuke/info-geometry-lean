/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.BoundaryInstrument
import InfoGeometry.Quantum.MixedBoundaryReadout

/-!
# Noncommuting matrix witnesses for two-boundary normalization and order

The boundaries are dense Hermitian matrices, the effect and its complement
are positive, and the instrument is complete. Both the boundaries and the
Kraus operators fail to commute. Exact rational complex calculations exhibit
the different normalizers and different weights of the two temporal orders.
-/

noncomputable section

namespace InfoGeometry.Quantum.TwoBoundaryOperatorExamples

open Matrix
open BoundaryInstrument MixedBoundaryReadout
open scoped BigOperators ComplexOrder

/-- A trace-one positive matrix with nonzero coherence. -/
def input : Matrix (Fin 2) (Fin 2) ℂ := !![2/3, 1/3; 1/3, 1/3]

/-- A trace-one effect with imaginary off-diagonal coherence. -/
def effect : Matrix (Fin 2) (Fin 2) ℂ := !![1/3, Complex.I/3; -Complex.I/3, 2/3]

def probe : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; 1, -1]

def first : Matrix (Fin 2) (Fin 2) ℂ := !![1/2, 1/2; 1/2, -1/2]

def second : Matrix (Fin 2) (Fin 2) ℂ := !![1/2, Complex.I/2; Complex.I/2, 1/2]

/-- Two recorded outcomes, each with one internal Kraus operator. -/
def instrument (a : Fin 2) (_ : Unit) : Matrix (Fin 2) (Fin 2) ℂ :=
  if a = 0 then first else second

theorem input_posSemidef : input.PosSemidef := by
  let L : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; 0, 1]
  have h : input = (1/3 : ℝ) • (L * star L) := by
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      norm_num [input, L, Matrix.mul_apply, Matrix.vecMul, dotProduct,
        Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
        Fin.sum_univ_two, map_ofNat]
  rw [h]
  exact (Matrix.posSemidef_self_mul_conjTranspose L).smul (by norm_num : (0 : ℝ) ≤ 1/3)

theorem effect_posSemidef : effect.PosSemidef := by
  let L : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; -Complex.I, 1]
  have h : effect = (1/3 : ℝ) • (L * star L) := by
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      norm_num [effect, L, Matrix.mul_apply, Matrix.vecMul, dotProduct,
        Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
        Fin.sum_univ_two, map_ofNat]
  rw [h]
  exact (Matrix.posSemidef_self_mul_conjTranspose L).smul (by norm_num : (0 : ℝ) ≤ 1/3)

theorem effect_complement_posSemidef : (1 - effect).PosSemidef := by
  let L : Matrix (Fin 2) (Fin 2) ℂ := !![1, -Complex.I; 0, 1]
  have h : 1 - effect = (1/3 : ℝ) • (L * star L) := by
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      norm_num [effect, L, Matrix.mul_apply, Matrix.vecMul, dotProduct,
        Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
        Fin.sum_univ_two, map_ofNat]
  rw [h]
  exact (Matrix.posSemidef_self_mul_conjTranspose L).smul (by norm_num : (0 : ℝ) ≤ 1/3)

theorem trace_input : trace input = 1 := by
  norm_num [input, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

theorem trace_effect : trace effect = 1 := by
  norm_num [effect, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

theorem probe_isHermitian : probe.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [probe, Matrix.conjTranspose_apply]

/-- The positive boundaries do not commute. -/
theorem boundaries_noncommute : input * effect ≠ effect * input := by
  intro h
  have h' := congrArg (fun X : Matrix (Fin 2) (Fin 2) ℂ => (X 0 0).im) h
  norm_num [input, effect, Matrix.mul_apply, Fin.sum_univ_two] at h'

/-- The ordered measurement operations do not commute either. -/
theorem kraus_noncommute : first * second ≠ second * first := by
  intro h
  have h' := congrArg (fun X : Matrix (Fin 2) (Fin 2) ℂ => (X 0 1).im) h
  norm_num [first, second, Matrix.mul_apply, Fin.sum_univ_two] at h'

theorem instrument_complete :
    (∑ p : Fin 2 × Unit, star (instrument p.1 p.2) * instrument p.1 p.2) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [Fintype.sum_prod_type, Fin.sum_univ_two, instrument, first, second,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply, map_ofNat]

theorem bare_overlap : overlap input effect = 4/9 := by
  apply Complex.ext <;>
    norm_num [overlap, input, effect, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Fin.sum_univ_two]

/-- A Hermitian probe can have a non-real weak readout for positive boundaries. -/
theorem complex_readout : readout input effect probe = (3 - Complex.I)/4 := by
  rw [readout, bare_overlap]
  apply Complex.ext <;>
    norm_num [input, effect, probe, Matrix.trace, Matrix.diag,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      Complex.div_re, Complex.div_im, Complex.normSq_apply]

theorem first_weight : outcomeWeight instrument input effect 0 = 7/36 := by
  norm_num [outcomeWeight, Choi.krausMap, instrument, first, input, effect,
    Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    Fin.sum_univ_two, map_ofNat]

theorem second_weight : outcomeWeight instrument input effect 1 = 7/36 := by
  norm_num [outcomeWeight, Choi.krausMap, instrument, second, input, effect,
    Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    Fin.sum_univ_two, map_ofNat]

theorem instrument_normalizer : normalizer instrument input effect = 7/18 := by
  norm_num [normalizer, Fin.sum_univ_two, first_weight, second_weight]

theorem normalizers_differ : normalizer instrument input effect ≠ (overlap input effect).re := by
  rw [instrument_normalizer, bare_overlap]
  norm_num

/-- First followed by second has a different joint weight from the reverse order. -/
theorem ordered_weight_first_second :
    (trace ((second * first) * input * star (second * first) * effect)).re = 5/72 := by
  norm_num [first, second, input, effect, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply, Fin.sum_univ_two, map_ofNat]

theorem ordered_weight_second_first :
    (trace ((first * second) * input * star (first * second) * effect)).re = 1/8 := by
  norm_num [first, second, input, effect, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply, Fin.sum_univ_two, map_ofNat]

theorem ordered_weights_differ :
    (trace ((second * first) * input * star (second * first) * effect)).re ≠
      (trace ((first * second) * input * star (first * second) * effect)).re := by
  rw [ordered_weight_first_second, ordered_weight_second_first]
  norm_num

end InfoGeometry.Quantum.TwoBoundaryOperatorExamples
