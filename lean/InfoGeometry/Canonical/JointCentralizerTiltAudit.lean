/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.DualSeedTilt
import Mathlib.Algebra.Algebra.Bilinear
import InfoGeometry.Algebra.FiniteMatrixNoncommutativity
import InfoGeometry.OperatorAlgebra.PeirceCoupling.RealCartanWitnesses

/-!
# Strict centralizer reduction in the regular representation

The native left and right multiplication operators act on the entire algebra.
The right copy commutes with the left copy, but retains the reversed order of
its own noncommutative multiplication. Tilting a left seed pair by the right
seed therefore supplies an explicit strict centralizer reduction.

The concrete consumer uses the existing dense real `3 × 3` seed. Its carrier
here is `Module.End ℝ (Matrix (Fin 3) (Fin 3) ℝ)`, acting on all nine matrix
coordinates. No restriction to a commuting coefficient algebra is made.
-/

namespace InfoGeometry.Canonical.JointCentralizerTiltAudit

open InfoGeometry.Core.DualSeedPeirce

section Regular

variable {K A : Type*} [Field K] [Ring A] [Algebra K A]
variable {d b : A}

/-- Right multiplication belongs to the common commutant of any two left
multiplication operators. -/
private theorem mulRight_mem_left_pair (d b x : A) :
    LinearMap.mulRight K x ∈ Subalgebra.centralizer K
      ({LinearMap.mulLeft K d, LinearMap.mulLeft K b} : Set (Module.End K A)) := by
  rw [Subalgebra.mem_centralizer_iff]
  intro y hy
  rcases Set.mem_insert_iff.mp hy with rfl | hy
  · exact (LinearMap.commute_mulLeft_right d x).eq
  · have hy' : y = LinearMap.mulLeft K b := Set.mem_singleton_iff.mp hy
    subst y
    exact (LinearMap.commute_mulLeft_right b x).eq

/-- A nonzero dual seed yields a noncentral direction in the regular common
commutant. Adding that direction strictly reduces the common commutant. -/
theorem regular_centralizer_tilt_lt (h : IsDualSeedPair d b) (hd : d ≠ 0)
    {ε : K} (hε : ε ≠ 0) (h2 : (2 : K) ≠ 0) :
    Subalgebra.centralizer K
        ({LinearMap.mulLeft K d + ε • LinearMap.mulRight K d,
          LinearMap.mulLeft K b - ε • LinearMap.mulRight K d} : Set (Module.End K A)) <
      Subalgebra.centralizer K
        ({LinearMap.mulLeft K d, LinearMap.mulLeft K b} : Set (Module.End K A)) := by
  have hp : IsDualSeedPair (LinearMap.mulLeft K d) (LinearMap.mulLeft K b) :=
    h.map (Algebra.lmul K A).toRingHom
  rw [hp.centralizer_tilt
    (LinearMap.commute_mulLeft_right d d).symm
    (LinearMap.commute_mulLeft_right b d).symm hε h2]
  refine lt_of_le_not_ge inf_le_left ?_
  intro hle
  have hx := mulRight_mem_left_pair (K := K) d b b
  have hc := (Subalgebra.mem_centralizer_iff K).mp (hle hx).2
    (LinearMap.mulRight K d) (Set.mem_singleton _)
  have he := congrArg (fun f : Module.End K A => f 1) hc
  change (1 * b) * d = (1 * d) * b at he
  apply h.seeds_not_commute hd
  change d * b = b * d
  simpa only [one_mul] using he.symm

/-- Even a square-zero tilt direction can destroy square-zero behavior.
The exact sandwich readout is nonzero when `2`, `ε`, and `d` are nonzero. -/
theorem regular_tilt_sq_apply_partner (h : IsDualSeedPair d b) (ε : K) :
    ((LinearMap.mulLeft K d + ε • LinearMap.mulRight K d) ^ 2) b =
      (2 * ε) • d := by
  have hdd_b : d * (d * b) = 0 := by rw [← mul_assoc, h.d_sq, zero_mul]
  have hd_bd : d * (b * d) = d := by rw [← mul_assoc, h.inner]
  have hbd_d : b * d * d = 0 := by rw [mul_assoc, h.d_sq, mul_zero]
  change d * (d * b + ε • (b * d)) +
    ε • ((d * b + ε • (b * d)) * d) = (2 * ε) • d
  simp only [mul_add, mul_smul_comm, add_mul, smul_mul_assoc,
    hdd_b, hd_bd, h.inner, hbd_d, smul_zero, zero_add, add_zero]
  rw [← add_smul, ← two_mul]

/-- The regular tilt has a provably nonzero square on the full endomorphism
algebra; no scalar reduction is used. -/
theorem regular_tilt_sq_ne_zero (h : IsDualSeedPair d b) (hd : d ≠ 0)
    {ε : K} (hε : ε ≠ 0) (h2 : (2 : K) ≠ 0) :
    (LinearMap.mulLeft K d + ε • LinearMap.mulRight K d) ^ 2 ≠ 0 := by
  intro hz
  have he := congrArg (fun f : Module.End K A => f b) hz
  rw [regular_tilt_sq_apply_partner h ε, LinearMap.zero_apply] at he
  exact (smul_ne_zero (mul_ne_zero h2 hε) hd) he

end Regular

section DenseReal

open Matrix InfoGeometry.OperatorAlgebra.PeirceCoupling.RealCartanWitnesses

/-- The actual right-action multiplicity algebra is noncommutative. Evaluation
at one retains the opposite multiplication order of the original dense pair. -/
theorem dense_regular_right_not_commute :
    ¬ Commute (LinearMap.mulRight ℝ denseSeed) (LinearMap.mulRight ℝ denseSeedᴴ) := by
  intro hc
  have he := congrArg
    (fun f : Module.End ℝ (Matrix (Fin 3) (Fin 3) ℝ) => f 1) hc.eq
  change (1 * denseSeedᴴ) * denseSeed = (1 * denseSeed) * denseSeedᴴ at he
  apply denseSeed_not_commute
  change denseSeed * denseSeedᴴ = denseSeedᴴ * denseSeed
  simpa only [one_mul] using he.symm

/-- Closed strict-reduction witness on the full endomorphism algebra of the
existing dense real matrix carrier. -/
theorem dense_regular_tilt_centralizer_lt :
    Subalgebra.centralizer ℝ
        ({LinearMap.mulLeft ℝ denseSeed + LinearMap.mulRight ℝ denseSeed,
          LinearMap.mulLeft ℝ denseSeedᴴ - LinearMap.mulRight ℝ denseSeed} :
          Set (Module.End ℝ (Matrix (Fin 3) (Fin 3) ℝ))) <
      Subalgebra.centralizer ℝ
        ({LinearMap.mulLeft ℝ denseSeed, LinearMap.mulLeft ℝ denseSeedᴴ} :
          Set (Module.End ℝ (Matrix (Fin 3) (Fin 3) ℝ))) := by
  simpa only [one_smul] using
    regular_centralizer_tilt_lt (K := ℝ) denseSeed_pair denseSeed_ne_zero
      (ε := 1) (by norm_num) (by norm_num)

/-- Closed failure of square-zero behavior for the same dense regular tilt. -/
theorem dense_regular_tilt_sq_ne_zero :
    (LinearMap.mulLeft ℝ denseSeed + LinearMap.mulRight ℝ denseSeed) ^ 2 ≠ 0 := by
  simpa only [one_smul] using
    regular_tilt_sq_ne_zero (K := ℝ) denseSeed_pair denseSeed_ne_zero
      (ε := 1) (by norm_num) (by norm_num)

end DenseReal

end InfoGeometry.Canonical.JointCentralizerTiltAudit
