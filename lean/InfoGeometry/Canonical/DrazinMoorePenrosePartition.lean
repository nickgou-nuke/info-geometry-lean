/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.DrazinRegularization
import InfoGeometry.Singular.MoorePenroseSectors
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Drazin and Moore-Penrose partition interface

The spectral and metric partitions have different hypotheses. This module
joins their existing owners without identifying oblique and orthogonal
projectors. Scalar transport is constant global homogeneity, not a local
Weyl connection. DMP products are not inverses on the nilpotent summand.
-/

namespace InfoGeometry.Canonical.DrazinMoorePenrosePartition

open InfoGeometry.Canonical.Drazin
open InfoGeometry.Singular.MoorePenrose
open InfoGeometry.Singular.MoorePenroseSectors

variable {R : Type*} [Ring R] [StarRing R] {a d m : R} {k : ℕ}

/-- The ordered Drazin--Moore--Penrose product. -/
def dmpInverse (a d m : R) : R := d * a * m

/-- The dual ordered product. -/
def dualDmpInverse (a d m : R) : R := m * a * d

theorem dmp_eq_projection_mul (h : IsDrazinInverse a d k) :
    dmpInverse a d m = Drazin.IsDrazinInverse.projection a d * m := by
  unfold dmpInverse Drazin.IsDrazinInverse.projection
  rw [h.comm]

/-- The DMP product satisfies an outer-inverse equation; it is not asserted
here to be the Moore-Penrose or Drazin inverse. -/
theorem dmp_outer_inverse (hd : IsDrazinInverse a d k)
    (hm : IsMoorePenroseInverse a m) :
    dmpInverse a d m * a * dmpInverse a d m = dmpInverse a d m := by
  unfold dmpInverse
  calc
    (d * a * m) * a * (d * a * m) = d * (a * m * a) * d * a * m := by
      simp only [mul_assoc]
    _ = d * a * m := by rw [hm.aba_eq_a, hd.idempotent]

theorem dualDmp_outer_inverse (hd : IsDrazinInverse a d k)
    (hm : IsMoorePenroseInverse a m) :
    dualDmpInverse a d m * a * dualDmpInverse a d m = dualDmpInverse a d m := by
  unfold dualDmpInverse
  calc
    (m * a * d) * a * (m * a * d) = m * a * d * (a * m * a) * d := by
      simp only [mul_assoc]
    _ = m * a * (d * a * d) := by rw [hm.aba_eq_a]; simp only [mul_assoc]
    _ = m * a * d := by rw [hd.idempotent]

/-- Zero trace is the cyclic trace identity, with no chain complex assumed. -/
theorem trace_commutator {ι : Type*} [Fintype ι]
    (x y : Matrix ι ι ℝ) : Matrix.trace (x * y - y * x) = 0 := by
  rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]

section Scaling
variable [Algebra ℝ R]

theorem mp_smul (hm : IsMoorePenroseInverse a m) {c : ℝ} (hc : c ≠ 0) :
    IsMoorePenroseInverse (c • a) (c⁻¹ • m) := by
  have hprod (x y : R) : (c • x) * (c⁻¹ • y) = x * y := by
    simp [smul_mul_assoc, mul_smul_comm, smul_smul, hc]
  have hprod' (x y : R) : (c⁻¹ • x) * (c • y) = x * y := by
    simp [smul_mul_assoc, mul_smul_comm, smul_smul, hc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hprod, mul_smul_comm, hm.aba_eq_a]
  · rw [hprod', mul_smul_comm, hm.bab_eq_b]
  · rw [hprod, hm.ab_adj_eq]
  · rw [hprod', hm.ba_adj_eq]

/-- All four support-sector operators are scale-invariant even before
commutation is supplied to make them projections. -/
theorem sector_scale_invariance (a m : R) {c : ℝ} (hc : c ≠ 0) (i : Bool × Bool) :
    sector ((c • a) * (c⁻¹ • m)) ((c⁻¹ • m) * (c • a)) i =
      sector (a * m) (m * a) i := by
  simp [smul_mul_assoc, mul_smul_comm, smul_smul, hc]

theorem dmp_smul (a d m : R) {c : ℝ} (hc : c ≠ 0) :
    dmpInverse (c • a) (c⁻¹ • d) (c⁻¹ • m) = c⁻¹ • dmpInverse a d m := by
  simp [dmpInverse, smul_mul_assoc, mul_smul_comm, smul_smul, hc]

end Scaling
end InfoGeometry.Canonical.DrazinMoorePenrosePartition
