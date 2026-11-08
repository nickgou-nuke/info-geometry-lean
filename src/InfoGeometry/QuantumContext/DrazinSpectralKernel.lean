/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Abel

set_option linter.deprecated false
set_option linter.unusedVariables false

/-!
# The Drazin Generalized Inverse and the Nilpotent Spectral Kernel

While the Moore–Penrose pseudoinverse $\rho^+$ is metric-dependent and designed for
Hermitian density matrices, the **Drazin inverse** $A^D$ is purely algebraic, metric-free,
and strictly commutes with the operator:
$$A A^D = A^D A$$

For a finite row-stochastic transition matrix $P$, one may study the Markov generator
$L = \mathbf{1} - P$. This file does not establish that such an $L$ has Drazin index
one, nor does it construct its group inverse. It proves algebraic consequences conditional
on the three Drazin equations below:

1. **The Three Drazin Axioms for Index $k$**:
   - $D A D = D$
   - $A D = D A$
   - $A^{k+1} D = A^k$
2. **The Spectral Projectors**:
   - Active core projector: $P_{\text{core}} = A D = D A$, with $P^2 = P$ and $P A = A P$.
   - Generalized kernel projector: $Q_{\text{kernel}} = \mathbf{1} - A D$, with $Q^2 = Q$.
   - Completeness & orthogonality: $P + Q = \mathbf{1}$ and $P \cdot Q = 0$.
3. **Fundamental Kernel Annihilation Law**:
   $$A^k \cdot (\mathbf{1} - A D) = 0$$
   The operator $A^k$ is identically annihilated on the complementary subspace.
4. **Conditional Group Inverse Specialization (Index $k = 1$)**:
   - $A \cdot (\mathbf{1} - P) = 0$ (the transient nilpotent error vanishes identically).
   - Clean algebraic reconstruction: $A \cdot P = A$.

All proofs are 100% native Mathlib 4, strictly constructive, in an arbitrary associative ring,
with zero `sorry`s, zero `admit`s, and zero custom axioms.
-/

namespace InfoGeometry.QuantumContext.Drazin

variable {R : Type*} [Ring R]

/-! --------------------------------------------------------------------------
    Section 1: The Drazin Axioms and Spectral Projectors
    -------------------------------------------------------------------------- -/

/-- Predicate stating that D is the Drazin inverse of A with index k. -/
structure IsDrazinInverse (A D : R) (k : ℕ) : Prop where
  drazin_one   : D * A * D = D
  comm         : A * D = D * A
  index_eq     : A ^ (k + 1) * D = A ^ k

variable {A D : R} {k : ℕ}

/-- The Drazin Spectral Projector P = A · D = D · A. -/
def spectralProj (A D : R) : R := A * D

/-- The Generalized Kernel Projector Q = 1 - P. -/
def kernelProj (A D : R) : R := 1 - spectralProj A D

/-! --------------------------------------------------------------------------
    Section 2: Idempotency and Commutation of the Spectral Projector
    -------------------------------------------------------------------------- -/

/-- P strictly commutes with A: P · A = A · P. -/
theorem spectralProj_comm (hD : IsDrazinInverse A D k) :
    spectralProj A D * A = A * spectralProj A D := by
  dsimp [spectralProj]
  rw [mul_assoc, ← hD.comm, ← mul_assoc]

/-- P is an idempotent projector: P² = P. -/
theorem spectralProj_idempotent (hD : IsDrazinInverse A D k) :
    spectralProj A D * spectralProj A D = spectralProj A D := by
  dsimp [spectralProj]
  calc
    (A * D) * (A * D) = A * (D * A * D) := by
      rw [mul_assoc, mul_assoc, ← mul_assoc D A D]
    _ = A * D := by rw [hD.drazin_one]

/-- Q = 1 - P is an idempotent projector: Q² = Q. -/
theorem kernelProj_idempotent (hD : IsDrazinInverse A D k) :
    kernelProj A D * kernelProj A D = kernelProj A D := by
  dsimp [kernelProj]
  have hP := spectralProj_idempotent hD
  rw [mul_sub, mul_one, sub_mul, one_mul, hP, sub_self, sub_zero]

/-- Completeness: P + Q = 1. -/
theorem spectral_add_kernel :
    spectralProj A D + kernelProj A D = 1 := by
  dsimp [kernelProj]
  abel

/-- Orthogonality: P · Q = 0. -/
theorem spectral_mul_kernel (hD : IsDrazinInverse A D k) :
    spectralProj A D * kernelProj A D = 0 := by
  dsimp [kernelProj]
  have hP := spectralProj_idempotent hD
  rw [mul_sub, mul_one, hP, sub_self]

/-- Orthogonality in the opposite order: the kernel projector also vanishes
when composed on the left with the active spectral projector. -/
theorem kernel_mul_spectral (hD : IsDrazinInverse A D k) :
    kernelProj A D * spectralProj A D = 0 := by
  dsimp [kernelProj, spectralProj]
  have hP := spectralProj_idempotent hD
  rw [sub_mul, one_mul]
  change spectralProj A D - spectralProj A D * spectralProj A D = 0
  rw [hP, sub_self]

/-! --------------------------------------------------------------------------
    Section 3: Kernel Annihilation Theorems
    -------------------------------------------------------------------------- -/

/--
The Fundamental Kernel Annihilation Law:
A^k · (1 - P) = 0.
The operator A^k is identically annihilated by the complementary Drazin projector.
-/
theorem index_annihilates_kernel_proj (hD : IsDrazinInverse A D k) :
    A ^ k * kernelProj A D = 0 := by
  dsimp [kernelProj, spectralProj]
  have h_idx := hD.index_eq
  calc
    A ^ k * (1 - A * D) = A ^ k * 1 - A ^ k * (A * D) := by rw [mul_sub]
    _ = A ^ k - (A ^ k * A) * D := by rw [mul_one, mul_assoc]
    _ = A ^ k - A ^ (k + 1) * D := by rw [← pow_succ A k]
    _ = A ^ k - A ^ k := by rw [h_idx]
    _ = 0 := sub_self (A ^ k)

/-- The complementary projector is also annihilated on the left by the active
power.  This follows from the Drazin commutation relation. -/
theorem kernel_proj_mul_index_power (hD : IsDrazinInverse A D k) :
    kernelProj A D * A ^ k = 0 := by
  have hQ : kernelProj A D * A = A * kernelProj A D := by
    dsimp [kernelProj, spectralProj]
    calc
      (1 - A * D) * A = A - (A * D) * A := by
        rw [sub_mul, one_mul]
      _ = A - A * (A * D) := by
        rw [mul_assoc, ← hD.comm]
      _ = A * (1 - A * D) := by
        rw [mul_sub, mul_one]
  have hcomm : Commute (kernelProj A D) A := hQ
  calc
    kernelProj A D * A ^ k = A ^ k * kernelProj A D :=
      (hcomm.pow_right k).eq
    _ = 0 := index_annihilates_kernel_proj hD

/-! --------------------------------------------------------------------------
    Section 4: Group Inverse Specialization (Index k = 1 for Markov Chains)
    -------------------------------------------------------------------------- -/

/-- For Markov chains and index-1 operators, the nilpotent part is strictly ZERO. -/
theorem group_inverse_nilpotent_zero (h1 : IsDrazinInverse A D 1) :
    A * kernelProj A D = 0 := by
  have h := index_annihilates_kernel_proj h1
  rw [pow_one] at h
  exact h

/- The index-one kernel projector is also annihilated on the left.  This is
   a consequence of the Drazin commutation law, not an additional hypothesis. -/
theorem group_inverse_kernel_proj_zero_left (h1 : IsDrazinInverse A D 1) :
    kernelProj A D * A = 0 := by
  simpa [pow_one] using kernel_proj_mul_index_power h1

/- The active projector reconstructs A from either side in the index-one case. -/
theorem group_inverse_reconstruction_left (h1 : IsDrazinInverse A D 1) :
    spectralProj A D * A = A := by
  have h := group_inverse_kernel_proj_zero_left h1
  calc
    spectralProj A D * A = spectralProj A D * A + 0 := by rw [add_zero]
    _ = spectralProj A D * A + kernelProj A D * A := by rw [h]
    _ = (spectralProj A D + kernelProj A D) * A := by rw [add_mul]
    _ = 1 * A := by rw [spectral_add_kernel]
    _ = A := one_mul A

/-- For index 1, A decomposes cleanly into A = A · P. -/
theorem group_inverse_reconstruction (h1 : IsDrazinInverse A D 1) :
    A * spectralProj A D = A := by
  have h := group_inverse_nilpotent_zero h1
  calc
    A * spectralProj A D = A * spectralProj A D + 0 := by rw [add_zero]
    _ = A * spectralProj A D + A * kernelProj A D := by rw [h]
    _ = A * (spectralProj A D + kernelProj A D) := by rw [← mul_add]
    _ = A * 1 := by rw [spectral_add_kernel]
    _ = A := mul_one A

/-- Constructive model witness for `IsDrazinInverse`: the multiplicative unit `1 : ℤ`
    is its own Drazin (and group) inverse of index `1`. -/
theorem isDrazinInverse_one : IsDrazinInverse (1 : ℤ) (1 : ℤ) 1 :=
  ⟨rfl, rfl, rfl⟩

end InfoGeometry.QuantumContext.Drazin





