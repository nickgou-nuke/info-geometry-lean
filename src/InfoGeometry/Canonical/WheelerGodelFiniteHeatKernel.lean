/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.WheelerGodelRotatingUniverseChronologyPoset

/-!
# Finite Peirce heat-kernel Taylor identities

This file proves finite-matrix identities for polynomial filters in the even
operator `Σ²`. In particular, every finite Taylor polynomial with constant
term `1` has the same chiral supertrace as the identity, and every finite even
polynomial filter has zero unpolarized odd trace. These are exact algebraic
statements about finite matrices. They do not construct an analytic heat
semigroup, an APS eta invariant, a spectral zeta function, a zeta determinant,
or a Casimir energy.
-/

namespace InfoGeometry.Canonical.WheelerGodelFiniteHeatKernel

open InfoGeometry.Canonical.WheelerGodelRotatingUniverseChronologyPoset

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type*} [CommRing R]

/-- Every positive even moment of the finite Peirce vorticity has zero chiral
supertrace. The proof uses the cyclic equality of the traces of `(A * B)^m`
and `(B * A)^m` on the two equal-size diagonal blocks. -/
theorem block_vorticity_even_power_supertrace_zero
    (A B : Matrix n n R) (k : ℕ) :
    blockSupertrace (blockVorticity A B ^ (2 * k)) = 0 := by
  rw [blockVorticity_eq_fromBlocks, fromBlocks_diag_pow]
  have hneg : (-(B * A)) ^ (2 * k) = (B * A) ^ (2 * k) := by
    rw [neg_pow]
    have he : (-1 : Matrix n n R) ^ (2 * k) = 1 :=
      Even.neg_one_pow ⟨k, by omega⟩
    rw [he, one_mul]
  rw [hneg]
  have htrace : Matrix.trace ((A * B) ^ (2 * k)) =
      Matrix.trace ((B * A) ^ (2 * k)) :=
    trace_mul_pow_comm A B (2 * k)
  change Matrix.trace
    (blockChiralInv * Matrix.fromBlocks ((A * B) ^ (2 * k)) 0 0
      ((B * A) ^ (2 * k))) = 0
  have hmul : blockChiralInv * Matrix.fromBlocks ((A * B) ^ (2 * k)) 0 0
      ((B * A) ^ (2 * k)) =
      Matrix.fromBlocks ((A * B) ^ (2 * k)) 0 0 (-((B * A) ^ (2 * k))) := by
    simp [blockChiralInv, Matrix.fromBlocks_multiply]
  have hdiag (X Y : Matrix n n R) :
      Matrix.trace (Matrix.fromBlocks X 0 0 Y) = Matrix.trace X + Matrix.trace Y := by
    simp [Matrix.trace]
  rw [hmul, hdiag, Matrix.trace_neg, htrace]
  simp

/-- The finite Taylor polynomial `1 + ∑ cₖ Σ^(2(k+1))` has the same chiral
supertrace as the identity. This is the polynomial truncation statement
underlying McKean–Singer-style cancellation; no infinite sum or analytic
continuation is asserted. -/
theorem block_vorticity_finite_even_taylor_supertrace
    (A B : Matrix n n R) (N : ℕ) (c : ℕ → R) :
    blockSupertrace
        (1 + ∑ k ∈ Finset.range N,
          c k • (blockVorticity A B ^ (2 * (k + 1)))) =
      Matrix.trace (blockChiralInv : Matrix (Sum n n) (Sum n n) R) := by
  have hsum :
      blockSupertrace
          (∑ k ∈ Finset.range N,
            c k • (blockVorticity A B ^ (2 * (k + 1)))) = 0 := by
    change Matrix.trace (blockChiralInv *
      ∑ k ∈ Finset.range N,
        c k • (blockVorticity A B ^ (2 * (k + 1)))) = 0
    rw [Matrix.mul_sum, Matrix.trace_sum]
    apply Finset.sum_eq_zero
    intro k hk
    rw [mul_smul_comm, Matrix.trace_smul]
    have hmoment := block_vorticity_even_power_supertrace_zero A B (k + 1)
    change c k • blockSupertrace (blockVorticity A B ^ (2 * (k + 1))) = 0
    rw [hmoment]
    simp
  have hadd (X Y : Matrix (Sum n n) (Sum n n) R) :
      blockSupertrace (X + Y) = blockSupertrace X + blockSupertrace Y := by
    simp [blockSupertrace, Matrix.mul_add, Matrix.trace_add]
  calc
    blockSupertrace
        (1 + ∑ k ∈ Finset.range N,
          c k • (blockVorticity A B ^ (2 * (k + 1))))
      = blockSupertrace (1 : Matrix (Sum n n) (Sum n n) R) +
          blockSupertrace
            (∑ k ∈ Finset.range N,
              c k • (blockVorticity A B ^ (2 * (k + 1)))) := hadd _ _
    _ = Matrix.trace blockChiralInv := by
      rw [hsum]
      simp [blockSupertrace]

/-- The unpolarized trace of `Σ` against any finite even-power polynomial
filter vanishes. This is the exact finite Taylor-polynomial analogue of the
claimed odd heat-trace cancellation. -/
theorem block_vorticity_trace_even_polynomial_filter_zero
    (A B : Matrix n n R) (N : ℕ) (c : ℕ → R) :
    Matrix.trace
        (blockVorticity A B *
          ∑ k ∈ Finset.range N,
            c k • (blockVorticity A B ^ (2 * k))) = 0 := by
  rw [Matrix.mul_sum, Matrix.trace_sum]
  apply Finset.sum_eq_zero
  intro k hk
  rw [mul_smul_comm, Matrix.trace_smul]
  have hpow :
      blockVorticity A B * blockVorticity A B ^ (2 * k) =
        blockVorticity A B ^ (2 * k + 1) := by
    rw [pow_succ']
  rw [hpow]
  have hodd := (hubble_atlas_odd_power_trace_zero A B k).1
  rw [hodd]
  simp

end InfoGeometry.Canonical.WheelerGodelFiniteHeatKernel
