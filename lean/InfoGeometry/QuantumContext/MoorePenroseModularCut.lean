/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Moore–Penrose Support Cut for Diagonal Profiles

For a finite real diagonal profile, this module defines the coordinatewise
Moore–Penrose inverse by assigning zero to zero entries and the reciprocal to
nonzero entries. It proves the resulting support identities and a matrix trace
identity. No positivity, trace-one condition, or operator-algebraic GNS
construction is assumed here.

1. **The Moore–Penrose Pseudoinverse $\rho^+$**:
   Surgically maps zero eigenvalues strictly to zero: $\lambda_i = 0 \implies \lambda_i^+ = 0$.
2. **The 4 Penrose Identities**:
   - $\rho \rho^+ \rho = \rho$
   - $\rho^+ \rho \rho^+ = \rho^+$
   - $\rho \rho^+ = P_{\text{supp}}$
   - $\rho^+ \rho = P_{\text{supp}}$
3. **Idempotency & Support Annihilation**:
   - $P_{\text{supp}}^2 = P_{\text{supp}}$
   - Eviction/Mask Projector $Q = \mathbf{1} - P_{\text{supp}}$ satisfies $Q^2 = Q$.
   - $P_{\text{supp}} + Q = \mathbf{1}$ and $P_{\text{supp}} \cdot Q = 0$.
   - Coordinatewise annihilation: $\rho^+ \cdot Q = 0$ and $Q \cdot \rho = 0$.
4. **Scalar Identity on the Active Support**:
   On the active support ($P_{\text{supp}}(i) = 1$), the scalar supportwise inverse satisfies
   the identity:
   $$\rho_i A (\rho_i B \rho_i^+) = \rho_i B A$$
5. **Positive Support Coordinate**:
   If $\rho(i_{\text{anchor}}) > 0$, then
   $P_{\text{supp}}(i_{\text{anchor}}) = 1$, so the support is nonempty.
6. **Matrix Moore–Penrose Cut & Reduced Trace Identity**:
   Lifts the Moore–Penrose identities and reduced trace-cycling formula to the
   non-commutative matrix algebra $\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{R}$:
   $$\operatorname{Tr}(\rho A (\rho B \rho^+)) = \operatorname{Tr}(\rho B P_{\text{supp}} A)$$

The declarations are kernel-checked using Mathlib, with no `sorry`, `admit`, or
repository-authored axioms in this module.
-/

namespace InfoGeometry.QuantumContext.MoorePenrose

noncomputable section

variable {n : ℕ}

/-! --------------------------------------------------------------------------
    Section 1: The Moore–Penrose Pseudoinverse and Support Projectors
    -------------------------------------------------------------------------- -/

/-- The Moore–Penrose pseudoinverse of a diagonal density vector:
    sends zero eigenvalues strictly to 0, avoiding 1/0 singularity. -/
def moorePenrose (ρ : Fin n → ℝ) : Fin n → ℝ :=
  fun i => if ρ i = 0 then 0 else (ρ i)⁻¹

/-- The Support Projector P = ρ · ρ⁺. -/
def supportProj (ρ : Fin n → ℝ) : Fin n → ℝ :=
  fun i => if ρ i = 0 then 0 else 1

/-- The Eviction/Mask Projector Q = 1 - P. -/
def evictionProj (ρ : Fin n → ℝ) : Fin n → ℝ :=
  fun i => 1 - supportProj ρ i

/-! --------------------------------------------------------------------------
    Section 2: Proof of the Four Moore–Penrose Identities
    -------------------------------------------------------------------------- -/

/-- Penrose Identity 1: ρ · ρ⁺ · ρ = ρ. -/
theorem penrose_one (ρ : Fin n → ℝ) :
    (fun i => ρ i * moorePenrose ρ i * ρ i) = ρ := by
  ext i
  dsimp [moorePenrose]
  split_ifs with h
  · rw [h, zero_mul, zero_mul]
  · rw [mul_inv_cancel₀ h, one_mul]

/-- Penrose Identity 2: ρ⁺ · ρ · ρ⁺ = ρ⁺. -/
theorem penrose_two (ρ : Fin n → ℝ) :
    (fun i => moorePenrose ρ i * ρ i * moorePenrose ρ i) = moorePenrose ρ := by
  ext i
  dsimp [moorePenrose]
  split_ifs with h
  · ring
  · rw [inv_mul_cancel₀ h, one_mul]

/-- Identification of ρ · ρ⁺ with the Support Projector. -/
theorem mul_pinv_eq_support (ρ : Fin n → ℝ) :
    (fun i => ρ i * moorePenrose ρ i) = supportProj ρ := by
  ext i
  dsimp [moorePenrose, supportProj]
  split_ifs with h
  · rw [h, zero_mul]
  · exact mul_inv_cancel₀ h

/-- Identification of ρ⁺ · ρ with the Support Projector. -/
theorem pinv_mul_eq_support (ρ : Fin n → ℝ) :
    (fun i => moorePenrose ρ i * ρ i) = supportProj ρ := by
  ext i
  dsimp [moorePenrose, supportProj]
  split_ifs with h
  · rw [zero_mul]
  · exact inv_mul_cancel₀ h

/-! --------------------------------------------------------------------------
    Section 3: Projector Orthogonality, Idempotency and Support Annihilation
    -------------------------------------------------------------------------- -/

/-- P_supp is an idempotent orthogonal projector: P² = P. -/
theorem support_idempotent (ρ : Fin n → ℝ) :
    (fun i => supportProj ρ i * supportProj ρ i) = supportProj ρ := by
  ext i
  dsimp [supportProj]
  split_ifs <;> ring

/-- Q is an idempotent orthogonal projector: Q² = Q. -/
theorem eviction_idempotent (ρ : Fin n → ℝ) :
    (fun i => evictionProj ρ i * evictionProj ρ i) = evictionProj ρ := by
  ext i
  dsimp [evictionProj, supportProj]
  split_ifs <;> ring

/-- Completeness: P + Q = 1. -/
theorem support_add_eviction (ρ : Fin n → ℝ) :
    (fun i => supportProj ρ i + evictionProj ρ i) = (fun _ => 1) := by
  ext i
  dsimp [evictionProj]
  ring

/-- Orthogonality: P · Q = 0. -/
theorem support_mul_eviction (ρ : Fin n → ℝ) :
    (fun i => supportProj ρ i * evictionProj ρ i) = (fun _ => 0) := by
  ext i
  dsimp [evictionProj, supportProj]
  split_ifs <;> ring

/-- Coordinatewise annihilation of the complementary support: ρ⁺ · Q = 0. -/
theorem pinv_annihilates_eviction (ρ : Fin n → ℝ) :
    (fun i => moorePenrose ρ i * evictionProj ρ i) = (fun _ => 0) := by
  ext i
  dsimp [moorePenrose, evictionProj, supportProj]
  split_ifs <;> ring

/-- Coordinatewise annihilation of the density profile by the complement: Q · ρ = 0. -/
theorem eviction_annihilates_density (ρ : Fin n → ℝ) :
    (fun i => evictionProj ρ i * ρ i) = (fun _ => 0) := by
  ext i
  dsimp [evictionProj, supportProj]
  split_ifs with h
  · rw [h, mul_zero]
  · ring

/-! --------------------------------------------------------------------------
    Section 4: Scalar Supportwise Inverse Identity
    -------------------------------------------------------------------------- -/

/-- On the active support (where `supportProj ρ i = 1`), the scalar supportwise
inverse gives `ρ i * A * (ρ i * B * ρ⁺ i) = ρ i * B * A`. This scalar identity
does not assert an automorphism or a noncommutative KMS condition. -/
theorem supportwise_scalar_inverse_identity (ρ : Fin n → ℝ) (i : Fin n)
    (h_active : supportProj ρ i = 1) (A B : ℝ) :
    ρ i * A * (ρ i * B * moorePenrose ρ i) = ρ i * B * A := by
  dsimp [supportProj] at h_active
  split_ifs at h_active with h_zero
  · revert h_active; norm_num
  · dsimp [moorePenrose]
    simp only [h_zero, ↓reduceIte]
    calc
      ρ i * A * (ρ i * B * (ρ i)⁻¹)
        = (ρ i * A) * (B * (ρ i * (ρ i)⁻¹)) := by ring
      _ = (ρ i * A) * (B * 1) := by rw [mul_inv_cancel₀ h_zero]
      _ = ρ i * B * A := by ring

/-! --------------------------------------------------------------------------
    Section 5: Positive Support Coordinate
    -------------------------------------------------------------------------- -/

/--
If a coordinate has strictly positive weight, it is retained by the active
support projector. In particular, the support is nonempty.
-/
theorem active_support_anchor (ρ : Fin n → ℝ) (i_anchor : Fin n)
    (h_pos : ρ i_anchor > 0) :
    supportProj ρ i_anchor = 1 := by
  dsimp [supportProj]
  have h_ne : ρ i_anchor ≠ 0 := ne_of_gt h_pos
  simp [h_ne]

/-! --------------------------------------------------------------------------
    Section 6: Matrix Moore–Penrose Cut & Reduced Trace Identity
    -------------------------------------------------------------------------- -/

/-- Diagonal density matrix $\rho = \operatorname{diag}(\rho_i)$. -/
def densityMatrix (ρ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal ρ

/-- Diagonal Moore–Penrose pseudoinverse matrix $\rho^+ = \operatorname{diag}(\rho_i^+)$. -/
def pinvMatrix (ρ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (moorePenrose ρ)

/-- Diagonal active-support orthogonal projector matrix $P_{\text{supp}} = \operatorname{diag}(P_i)$. -/
def supportMatrix (ρ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (supportProj ρ)

/-- Diagonal complementary eviction projector matrix $Q_{\text{evict}} = \operatorname{diag}(Q_i)$. -/
def evictionMatrix (ρ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (evictionProj ρ)

/-- Matrix Penrose Identity 1: $\rho \rho^+ \rho = \rho$. -/
theorem densityMatrix_penrose_one (ρ : Fin n → ℝ) :
    densityMatrix ρ * pinvMatrix ρ * densityMatrix ρ = densityMatrix ρ := by
  dsimp [densityMatrix, pinvMatrix]
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, penrose_one]

/-- Matrix Penrose Identity 2: $\rho^+ \rho \rho^+ = \rho^+$. -/
theorem pinvMatrix_penrose_two (ρ : Fin n → ℝ) :
    pinvMatrix ρ * densityMatrix ρ * pinvMatrix ρ = pinvMatrix ρ := by
  dsimp [densityMatrix, pinvMatrix]
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, penrose_two]

/-- Matrix Penrose Identity 3: $\rho^+ \rho = P_{\text{supp}}$. -/
theorem pinvMatrix_mul_densityMatrix (ρ : Fin n → ℝ) :
    pinvMatrix ρ * densityMatrix ρ = supportMatrix ρ := by
  dsimp [densityMatrix, pinvMatrix, supportMatrix]
  rw [Matrix.diagonal_mul_diagonal, pinv_mul_eq_support]

/-- Matrix Penrose Identity 4: $\rho \rho^+ = P_{\text{supp}}$. -/
theorem densityMatrix_mul_pinvMatrix (ρ : Fin n → ℝ) :
    densityMatrix ρ * pinvMatrix ρ = supportMatrix ρ := by
  dsimp [densityMatrix, pinvMatrix, supportMatrix]
  rw [Matrix.diagonal_mul_diagonal, mul_pinv_eq_support]

/-- Matrix projector completeness: $P_{\text{supp}} + Q_{\text{evict}} = I_n$. -/
theorem supportMatrix_add_evictionMatrix (ρ : Fin n → ℝ) :
    supportMatrix ρ + evictionMatrix ρ = 1 := by
  ext i j
  dsimp [supportMatrix, evictionMatrix]
  by_cases hij : i = j
  · subst hij
    simp [evictionProj]
  · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]

/-- Matrix projector orthogonality: $P_{\text{supp}} Q_{\text{evict}} = 0$. -/
theorem supportMatrix_mul_evictionMatrix (ρ : Fin n → ℝ) :
    supportMatrix ρ * evictionMatrix ρ = 0 := by
  dsimp [supportMatrix, evictionMatrix]
  rw [Matrix.diagonal_mul_diagonal, support_mul_eviction, Matrix.diagonal_zero]

/-- **Non-Commutative Matrix Reduced Trace Identity**:
For any diagonal density profile $\rho : \operatorname{Fin} n \to \mathbb{R}$ and arbitrary
non-commutative observables $A, B : \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{R}$,
the supportwise inverse formula satisfies
$\operatorname{Tr}(\rho A (\rho B \rho^+)) = \operatorname{Tr}(\rho B P_{\text{supp}} A)$. -/
theorem matrix_reduced_trace_identity
    (ρ : Fin n → ℝ) (A B : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.trace (densityMatrix ρ * A * (densityMatrix ρ * B * pinvMatrix ρ)) =
      Matrix.trace (densityMatrix ρ * B * supportMatrix ρ * A) := by
  calc
    Matrix.trace (densityMatrix ρ * A * (densityMatrix ρ * B * pinvMatrix ρ))
      = Matrix.trace ((densityMatrix ρ * A * densityMatrix ρ * B) * pinvMatrix ρ) := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.trace (pinvMatrix ρ * (densityMatrix ρ * A * densityMatrix ρ * B)) := by
        rw [Matrix.trace_mul_comm]
    _ = Matrix.trace (((pinvMatrix ρ * densityMatrix ρ) * A) * (densityMatrix ρ * B)) := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((supportMatrix ρ * A) * (densityMatrix ρ * B)) := by
        rw [pinvMatrix_mul_densityMatrix]
    _ = Matrix.trace ((densityMatrix ρ * B) * (supportMatrix ρ * A)) := by
        rw [Matrix.trace_mul_comm]
    _ = Matrix.trace (densityMatrix ρ * B * supportMatrix ρ * A) := by
        simp only [Matrix.mul_assoc]

/-- If $B$ satisfies the right-support condition $B P_{\text{supp}} = B$, the reduced trace
identity specializes to
$\operatorname{Tr}(\rho A (\rho B \rho^+)) = \operatorname{Tr}(\rho B A)$. -/
theorem matrix_reduced_trace_identity_of_right_supported
    (ρ : Fin n → ℝ) (A B : Matrix (Fin n) (Fin n) ℝ)
    (hB : B * supportMatrix ρ = B) :
    Matrix.trace (densityMatrix ρ * A * (densityMatrix ρ * B * pinvMatrix ρ)) =
      Matrix.trace (densityMatrix ρ * B * A) := by
  rw [matrix_reduced_trace_identity, Matrix.mul_assoc (densityMatrix ρ) B (supportMatrix ρ), hB]

end

end InfoGeometry.QuantumContext.MoorePenrose
