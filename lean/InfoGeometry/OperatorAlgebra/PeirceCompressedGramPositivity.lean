/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceCompressionCurvature
import Mathlib.Analysis.Matrix.Order

/-!
# Positivity of the Peirce compressed Gram tensor in full matrix algebras

These results specialize the associative star-ring identities to arbitrary
finite complex matrices, without commutation or simultaneous diagonalization
assumptions.  The diagonal compressed tensor is positive semidefinite.  Its
trace is strictly positive on every nonzero self-adjoint tangent direction.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceCompressedGramPositivity

open InfoGeometry.OperatorAlgebra.PeirceCompressionCurvature
open InfoGeometry.Core.PeirceTangent
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A compressed self-correlation is a positive semidefinite matrix. -/
theorem compressedGram_self_posSemidef {p x : Matrix n n ℂ}
    (hp : p * p = p) (hps : star p = p) (hxs : star x = x) :
    (compressedGram p x x).PosSemidef := by
  rw [compressedGram_self_eq_star_mul_self hp hps hxs]
  exact Matrix.posSemidef_conjTranspose_mul_self ((1 - p) * x * p)

/-- The trace of a compressed self-correlation is nonnegative. -/
theorem compressedGram_self_trace_re_nonneg {p x : Matrix n n ℂ}
    (hp : p * p = p) (hps : star p = p) (hxs : star x = x) :
    0 ≤ (Matrix.trace (compressedGram p x x)).re := by
  exact (RCLike.nonneg_iff.mp
    (compressedGram_self_posSemidef hp hps hxs).trace_nonneg).1

/-- The compressed Gram trace detects exactly its directed Peirce arrow. -/
theorem compressedGram_self_trace_eq_zero_iff_arrow {p x : Matrix n n ℂ}
    (hp : p * p = p) (hps : star p = p) (hxs : star x = x) :
    Matrix.trace (compressedGram p x x) = 0 ↔ (1 - p) * x * p = 0 := by
  rw [compressedGram_self_eq_star_mul_self hp hps hxs]
  exact Matrix.trace_conjTranspose_mul_self_eq_zero_iff

/-- On self-adjoint tangent directions, vanishing of the compressed trace
forces the entire tangent to vanish, not just one of its matrix entries. -/
theorem compressedGram_self_trace_eq_zero_iff_tangent {p x : Matrix n n ℂ}
    (hp : p * p = p) (hps : star p = p) (hxs : star x = x)
    (hx : p * x + x * p = x) :
    Matrix.trace (compressedGram p x x) = 0 ↔ x = 0 := by
  constructor
  · intro ht
    have hqxp := (compressedGram_self_trace_eq_zero_iff_arrow hp hps hxs).mp ht
    have hpxq : p * x * (1 - p) = 0 := by
      have hs := congrArg star hqxp
      simpa only [star_mul, star_sub, star_one, star_zero, hps, hxs, mul_assoc] using hs
    calc
      x = p * x * (1 - p) + (1 - p) * x * p := tangent_eq_offDiagonal hp hx
      _ = 0 := by rw [hpxq, hqxp]; simp
  · rintro rfl
    simp [compressedGram]

/-- The traced compression is strictly positive on nonzero Hermitian
tangents of the full matrix projection space. -/
theorem compressedGram_self_trace_re_pos {p x : Matrix n n ℂ}
    (hp : p * p = p) (hps : star p = p) (hxs : star x = x)
    (hx : p * x + x * p = x) (hne : x ≠ 0) :
    0 < (Matrix.trace (compressedGram p x x)).re := by
  have hpsd := compressedGram_self_posSemidef hp hps hxs
  have htr : Matrix.trace (compressedGram p x x) ≠ 0 := by
    intro h
    exact hne ((compressedGram_self_trace_eq_zero_iff_tangent hp hps hxs hx).mp h)
  have hre := (RCLike.nonneg_iff.mp hpsd.trace_nonneg).1
  have him := (RCLike.nonneg_iff.mp hpsd.trace_nonneg).2
  have hrne : (Matrix.trace (compressedGram p x x)).re ≠ 0 := by
    intro hr
    apply htr
    apply Complex.ext
    · exact hr
    · exact him
  exact lt_of_le_of_ne hre (Ne.symm hrne)

end InfoGeometry.OperatorAlgebra.PeirceCompressedGramPositivity
