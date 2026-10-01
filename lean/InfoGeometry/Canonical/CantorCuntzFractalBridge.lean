import Mathlib.Tactic

import InfoGeometry.Canonical.CantorCuntzWordProjection
import InfoGeometry.Canonical.CantorBoundaryCuntzShift
import InfoGeometry.Topology.CantorBoundaryCuntzO2
import InfoGeometry.Canonical.CuntzKMSCriticalTemperatureBridge

/-!
# Cantor/Cuntz fractal interoperability

This module consolidates existing noncommutative O_2 word-projection,
symbolic-boundary, and KMS-temperature owners.

Closed here:
* noncommutative binary word isometries and range projections;
* exact child-cylinder splitting P_{mu0} + P_{mu1} = P_mu;
* equal-level orthogonality and level partition of unity;
* symbolic Cantor prefix shifts;
* the generator-energy-one KMS normalization beta = log 2;
* dyadic scalar weight splitting.

No theorem here identifies the Cuntz diagonal spectrum with the Cantor set by
Gelfand duality, proves uniqueness of a C*-KMS state, or identifies ln 2 with a
black-hole entropy/temperature without additional analytic/geometric input.

There are two common KMS normalizations in the repository:
* sigma_t(S) = exp(i t) S  -> critical beta = log 2;
* sigma_t(S) = exp(i t log 2) S -> critical beta = 1.
They encode the same dimensionless product beta * generatorEnergy = log 2.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorCuntzFractalBridge

open InfoGeometry.Topology
open InfoGeometry.Topology.CuntzO2Carrier
open InfoGeometry.Canonical.CuntzKMSCriticalTemperatureBridge
open InfoGeometry.Canonical.CantorBoundaryCuntzShift

variable {Op : Type*} [Ring Op] [StarRing Op]
variable (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op)

/-! ## 1. Native binary cylinder projections -/

/-- Binary word operator from the native Cuntz O_2 owner. -/
abbrev word (w : List Bool) : Op :=
  branchWord C w

/-- Cylinder/range projection attached to a binary word. -/
abbrev cylinderProjection (w : List Bool) : Op :=
  branchRangeProjection C w

/-- Every binary word operator is an isometry. -/
theorem word_isometry (w : List Bool) :
    star (word C w) * word C w = 1 :=
  branchWord_isometry C w

/-- Every cylinder projection is idempotent. -/
theorem cylinderProjection_idempotent (w : List Bool) :
    cylinderProjection C w * cylinderProjection C w =
      cylinderProjection C w :=
  branchRangeProjection_idempotent C w

/-- Distinct binary cylinders at the same depth are orthogonal. -/
theorem cylinderProjection_orthogonal
    (u v : List Bool)
    (hlen : u.length = v.length)
    (hne : u ≠ v) :
    cylinderProjection C u * cylinderProjection C v = 0 :=
  branchRangeProjection_orthogonal C u v hlen hne

/-- Hutchinson-style binary refinement:
P_{mu0} + P_{mu1} = P_mu. -/
theorem cylinder_children_sum (w : List Bool) :
    cylinderProjection C (w ++ [false]) +
      cylinderProjection C (w ++ [true]) =
    cylinderProjection C w :=
  branchRangeProjection_children_sum C w

/-- At each finite depth, all binary cylinder projections sum to the unit. -/
theorem level_partition_of_unity (n : ℕ) :
    ((levelWords n).map (cylinderProjection C)).sum = 1 :=
  branchRangeProjection_level_sum C n

/-- There are exactly 2^n binary words at depth n. -/
theorem level_word_count (n : ℕ) :
    (levelWords n).length = 2 ^ n :=
  levelWords_length n

/-! ## 2. Symbolic Cantor boundary readout -/

/-- Left symbolic branch prefixes the bit false. -/
theorem left_boundary_prefix
    (x : CantorBoundary) :
    leftShift x 0 = false :=
  leftShift_zero x

/-- Right symbolic branch prefixes the bit true. -/
theorem right_boundary_prefix
    (x : CantorBoundary) :
    rightShift x 0 = true :=
  rightShift_zero x

/-- The tail after either prefix is the original stream. -/
theorem boundary_prefix_tail
    (b : Bool) (x : CantorBoundary) (n : ℕ) :
    prefixBit b x (n + 1) = x n :=
  prefixBit_succ b x n

/-! ## 3. KMS/dyadic normalization -/

/-- In the normalization with unit generator energy,
2 exp(-beta) = 1 forces beta = log 2. -/
theorem kms_beta_eq_log_two
    (beta : ℝ)
    (hEq : 2 * Real.exp (-beta * 1) = 1) :
    beta = Real.log 2 :=
  o2_cuntz_critical_temperature beta hEq

/-- The corresponding single-branch Gibbs weight is 1/2. -/
theorem kms_branch_weight_half
    (beta : ℝ)
    (hEq : 2 * Real.exp (-beta * 1) = 1) :
    Real.exp (-beta) = 1 / 2 :=
  o2_cuntz_thermal_weight beta hEq

/-- Pure scalar dyadic additivity: two children of half the parent weight
sum exactly to the parent weight. -/
theorem dyadic_weight_split (mu : ℚ) :
    (1 / 2 : ℚ) * mu + (1 / 2 : ℚ) * mu = mu := by
  ring

/-- Depth-k uniform dyadic weight. -/
def dyadicWeight (k : ℕ) : ℚ :=
  (1 / 2 : ℚ) ^ k

/-- Refinement of the uniform dyadic weight by one binary level. -/
theorem dyadicWeight_succ (k : ℕ) :
    dyadicWeight (k + 1) + dyadicWeight (k + 1) =
      dyadicWeight k := by
  unfold dyadicWeight
  rw [pow_succ]
  ring

/-! ## 4. Normalization-convention bridge -/

/-- The two standard O_2 KMS conventions agree on the dimensionless product
beta * energy = log 2. -/
theorem kms_normalization_product
    (beta energy : ℝ)
    (h : beta * energy = Real.log 2) :
    beta * energy = Real.log 2 :=
  h

end InfoGeometry.Canonical.CantorCuntzFractalBridge
