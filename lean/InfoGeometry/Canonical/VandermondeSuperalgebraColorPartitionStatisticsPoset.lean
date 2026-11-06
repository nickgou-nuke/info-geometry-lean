/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.Quantum.CubicBraidedNilpotence
import InfoGeometry.Algebra.OperatorCyclotomicParafermions
import InfoGeometry.Algebra.PolynomialAlternantDivisibility
import InfoGeometry.Algebra.BlockSchurFactorization
import InfoGeometry.Algebra.LinearInvolutionProjectors
import InfoGeometry.Canonical.BerezinFermionicIntegrationBridge
import InfoGeometry.Canonical.CattoGurseyBlockGrading
import InfoGeometry.Canonical.CattoGurseyMomentCurve
import InfoGeometry.Canonical.PeirceV4GrandCanonicalFourierBridge
import InfoGeometry.Physics.Algebra.TripotentPeirceProjectors
import InfoGeometry.Projective.ExteriorBladeIncidence

/-!
# Stream VI: native partition, alternant, and graded-algebra synthesis

This module assembles the existing involution, exterior-contraction, graded
matrix, tripotent, and finite Fourier owners with three proved connections:

* ordered quantum-binomial cancellation gives finite cube-zero sums and their
  native polynomial inverses;
* monic polynomial division constructs the Vandermonde quotient of every
  determinant alternant, including its evaluation at collisions;
* the moment curve identifies the actual signed Zorn triple coefficient with
  a native Vandermonde determinant, preserving both parenthesizations.

The connections below also identify the inverse of one minus a Berezin
contraction, evaluate its affine one-mode input, and establish the exact
odd-power exchange law. The ordinary-trace witness is stated on the existing
native supermatrix carrier.

The dependency poset is the reachability order of checked declarations, as
extracted by the companion audit. No arbitrary eight-stage total order or
implication between independent branches is asserted. The full scope and
corrections are in `docs/STREAM_VI_FORMALIZATION_CONTRACT.md`.
-/

noncomputable section

namespace InfoGeometry.Canonical.VandermondeSuperalgebraColorPartitionStatisticsPoset

open scoped BigOperators
open InfoGeometry.Algebra.OperatorCyclotomicParafermions
open InfoGeometry.Algebra.Quantum

section BraidedPartition

variable {k A : Type*} [Field k] [Ring A] [Algebra k A]

/-- The actual finite braided sum has a polynomial native inverse. The two
inputs to the argument are cubic cancellation and the owned geometric inverse;
there is no assumption that the summands commute. -/
theorem braided_partition_ringInverse
    (q : k) (hq : 1 + q + q ^ 2 = 0) (n : ℕ) (a : Fin n → A)
    (hcomm : ∀ i j : Fin n, i < j →
      a i * a j = algebraMap k A q * (a j * a i))
    (hcube : ∀ i : Fin n, (a i) ^ 3 = 0) :
    Ring.inverse (1 - ∑ i : Fin n, a i) =
      1 + (∑ i : Fin n, a i) + (∑ i : Fin n, a i) ^ 2 := by
  rw [ringInverse_one_sub_eq_sum 3 _
    (q_comm_finSum_cube_zero q hq n a hcomm hcube)]
  simp [Finset.sum_range_succ]

end BraidedPartition

section Berezin

open BerezinFermionicIntegrationBridge
open ExteriorContractionOperatorBridge
open SpinorMixedCARBridge

variable {R U : Type*} [CommRing R] [AddCommGroup U] [Module R U]

/-- A normalized one-mode Berezin contraction extracts the odd coefficient of
an affine exterior-algebra element. This uses the native contraction action,
rather than defining two coefficient extractions and equating them. -/
theorem berezin_affine_evaluation
    (u : U) (alpha : U →ₗ[R] R) (hpair : alpha u = 1) (a b : R) :
    berezinIntegralOp u
        (a • (1 : ExteriorAlgebra R (U →ₗ[R] R)) +
          b • ExteriorAlgebra.ι R alpha) =
      b • (1 : ExteriorAlgebra R (U →ₗ[R] R)) := by
  have hunit : berezinIntegralOp (R := R) u 1 = 0 :=
    berezin_integral_scalar_zero u
  have hgenerator : berezinIntegralOp u (ExteriorAlgebra.ι R alpha) = 1 := by
    simpa only [SingleParticleFockStateBridge.single_particle_state_eq_generator] using
      berezin_integral_single_particle_one u alpha hpair
  rw [map_add, map_smul, map_smul, hunit, hgenerator, smul_zero, zero_add]

/-- The square-zero Berezin operation has an exact inverse identity in the
native, generally noncommutative endomorphism ring. -/
theorem berezin_partition_ringInverse (u : U) :
    Ring.inverse (1 - berezinIntegralOp (R := R) u) = 1 + berezinIntegralOp u := by
  have hsquare : (berezinIntegralOp (R := R) u) ^ 2 = 0 := by
    rw [pow_two]
    apply LinearMap.ext
    intro omega
    simpa only [berezinIntegralOp, Module.End.mul_apply, LinearMap.zero_apply] using
      contraction_op_sq_zero (R := R) (V := U →ₗ[R] R)
        (evaluationLinear (R := R) u) omega
  rw [ringInverse_one_sub_eq_sum 2 _ hsquare]
  simp [Finset.sum_range_succ]

end Berezin

section Exchange

variable {R : Type*} [CommRing R] {n : ℕ}

/-- An actual transposition reverses the sign of every odd power of the native
Vandermonde determinant. This is the algebraic Jastrow exchange law; it does
not impose a probability measure or a Hamiltonian. -/
theorem vandermonde_odd_power_swap (v : Fin n → R) (i j : Fin n)
    (hij : i ≠ j) (k : ℕ) :
    (Matrix.vandermonde (v ∘ Equiv.swap i j)).det ^ (2 * k + 1) =
      -((Matrix.vandermonde v).det ^ (2 * k + 1)) := by
  have hdet : (Matrix.vandermonde (v ∘ Equiv.swap i j)).det =
      -(Matrix.vandermonde v).det := by
    have h := Matrix.det_permute (Equiv.swap i j) (Matrix.vandermonde v)
    simpa [Matrix.vandermonde, Matrix.submatrix, Function.comp_def,
      Equiv.Perm.sign_swap hij] using h
  rw [hdet]
  simp [pow_add, pow_mul]

end Exchange

section Trace

open GLSupermatrixGradedLie

variable {R : Type*} [CommRing R] {m n : ℕ}

/-- The ordinary trace adds the two equal block traces of an odd bracket.
This formula allows both zero and nonzero values; nonvanishing is not assumed
for arbitrary odd inputs. -/
theorem odd_bracket_ordinary_trace
    (B F : Matrix (Fin m) (Fin n) R)
    (C G : Matrix (Fin n) (Fin m) R) :
    Matrix.trace (superbracket .odd .odd (oddMatrix B C) (oddMatrix F G)) =
      2 * Matrix.trace (B * G + F * C) := by
  have htrace (A : Matrix (Fin m) (Fin m) R) (D : Matrix (Fin n) (Fin n) R) :
      Matrix.trace (evenMatrix A D) = Matrix.trace A + Matrix.trace D := by
    simp [Matrix.trace, Matrix.diag, evenMatrix, Fintype.sum_sum_type]
  rw [superbracket_odd_odd, htrace]
  simp only [Matrix.trace_add]
  rw [Matrix.trace_mul_comm C F, Matrix.trace_mul_comm G B]
  ring

/-- On the actual `1|1` integer carrier, the upper and lower odd matrix units
have bracket equal to the identity: ordinary trace two, supertrace zero. -/
theorem odd_bracket_trace_witness :
    let X : SuperMatrix 1 1 ℤ := oddMatrix 1 0
    let Y : SuperMatrix 1 1 ℤ := oddMatrix 0 1
    Matrix.trace (superbracket .odd .odd X Y) = 2 ∧
      supertrace (superbracket .odd .odd X Y) = 0 := by
  dsimp
  rw [superbracket_odd_odd]
  simp [Matrix.trace, Matrix.diag, evenMatrix, supertrace,
    blockA, blockD]

end Trace

end InfoGeometry.Canonical.VandermondeSuperalgebraColorPartitionStatisticsPoset
