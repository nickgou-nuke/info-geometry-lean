import Mathlib.Tactic
import InfoGeometry.Canonical.MatrixStageInductiveLimit
import InfoGeometry.SuperGrassmannian.SatoColimitTriality

/-!
# Sato-GNS Pre-Hilbert Subfactor Bridge

This module formalizes the connection between the algebraic matrix-stage direct-limit trace
(`MatrixStageInductiveLimit.lean`, `SatoColimitTriality.lean`) and the GNS pre-Hilbert space
inner product and finite subfactor dimension ratios.

## Key Theorems & Constructions:
1. `gnsInner`: GNS pre-Hilbert inner product $\langle X, Y \rangle = \tau_\infty(X^* Y)$.
2. `gnsInner_conj_symm`: Conjugate symmetry $\langle Y, X \rangle = \overline{\langle X, Y \rangle}$.
3. Additivity and scalar scaling in both arguments:
   - `gnsInner_add_right`, `gnsInner_smul_right`
   - `gnsInner_add_left`, `gnsInner_smul_left`
4. `gns_adjoint_left`: GNS adjoint relation for left regular multiplication:
   $\langle A X, Y \rangle = \langle X, A^* Y \rangle$.
5. `gnsInner_comm`: Trace cyclicity on inner product $\langle X, Y \rangle = \tau_\infty(Y X^*)$.
6. `subfactor_stage_dimension_ratio`: Subfactor dimension ratio $4^{2n} / 4^n = 2^{2n}$.
7. `matrix_stage_limit_noncommutative`: Strict non-commutativity witness for $\mathrm{MatrixStageLimit}$.
-/

namespace InfoGeometry.Canonical.SatoGNSPreHilbertSubfactorBridge

open InfoGeometry.Canonical.MatrixStageInductiveLimit
open InfoGeometry.Canonical.ComplexMatrixStage
open InfoGeometry.Canonical.UHFInductiveColimitBoundary

noncomputable section

/-! ### 1. GNS Pre-Hilbert Inner Product -/

/-- The canonical GNS pre-Hilbert space inner product on the algebraic matrix-stage direct limit. -/
noncomputable def gnsInner (X Y : MatrixStageLimit) : ℂ :=
  limitTrace (star X * Y)

/-- Conjugate symmetry of the GNS inner product. -/
theorem gnsInner_conj_symm (X Y : MatrixStageLimit) :
    gnsInner Y X = starRingEnd ℂ (gnsInner X Y) := by
  dsimp [gnsInner]
  rw [← limitTrace_star, star_mul, star_star, limitTrace_mul_comm]

/-- Right additivity of the GNS inner product. -/
theorem gnsInner_add_right (X Y Z : MatrixStageLimit) :
    gnsInner X (Y + Z) = gnsInner X Y + gnsInner X Z := by
  dsimp [gnsInner]
  rw [mul_add, limitTrace_add]

/-- Right scalar multiplication scaling of the GNS inner product. -/
theorem gnsInner_smul_right (c : ℂ) (X Y : MatrixStageLimit) :
    gnsInner X (c • Y) = c * gnsInner X Y := by
  dsimp [gnsInner]
  rw [mul_smul_comm, limitTrace_smul]

/-- Left additivity of the GNS inner product. -/
theorem gnsInner_add_left (X Y Z : MatrixStageLimit) :
    gnsInner (X + Y) Z = gnsInner X Z + gnsInner Y Z := by
  dsimp [gnsInner]
  rw [star_add, add_mul, limitTrace_add]

/-- Left scalar multiplication scaling of the GNS inner product (conjugate linear). -/
theorem gnsInner_smul_left (c : ℂ) (X Y : MatrixStageLimit) :
    gnsInner (c • X) Y = starRingEnd ℂ c * gnsInner X Y := by
  dsimp [gnsInner]
  rw [star_smul, smul_mul_assoc, limitTrace_smul]
  rfl

/-- GNS adjoint relation for the left multiplication representation:
    $\langle A X, Y \rangle = \langle X, A^* Y \rangle$. -/
theorem gns_adjoint_left (A X Y : MatrixStageLimit) :
    gnsInner (A * X) Y = gnsInner X (star A * Y) := by
  dsimp [gnsInner]
  rw [star_mul, mul_assoc]

/-- Trace cyclicity on the inner product: $\langle X, Y \rangle = \tau_\infty(Y X^*)$. -/
theorem gnsInner_comm (X Y : MatrixStageLimit) :
    gnsInner X Y = limitTrace (Y * star X) := by
  dsimp [gnsInner]
  rw [limitTrace_mul_comm (star X) Y]

/-! ### 2. Finite Subfactor Dimension Ratio -/

/-- The finite subfactor dimension ratio theorem for the stage matrix towers:
    $(4)^{2n} / 4^n = 2^{2n}$. -/
theorem subfactor_stage_dimension_ratio (n : ℕ) :
    (4 : ℕ) ^ (2 * n) / (4 : ℕ) ^ n = (2 : ℕ) ^ (2 * n) := by
  have h4 : (4 : ℕ) ^ (2 * n) = (4 : ℕ) ^ n * (4 : ℕ) ^ n := by
    rw [← pow_add, ← two_mul]
  have hpos : 0 < (4 : ℕ) ^ n := Nat.pow_pos (by decide)
  rw [h4, Nat.mul_div_cancel_left _ hpos]
  calc (4 : ℕ) ^ n = ((2 : ℕ) ^ 2) ^ n := rfl
  _ = (2 : ℕ) ^ (2 * n) := by rw [← pow_mul]

/-! ### 3. Strict Non-Commutativity Witness for MatrixStageLimit -/

def w0 : BitWord 1 := fun _ => false
def w1 : BitWord 1 := fun _ => true

theorem w0_ne_w1 : w0 ≠ w1 := by
  intro h
  have h0 : w0 ⟨0, by decide⟩ = w1 ⟨0, by decide⟩ := by rw [h]
  revert h0
  decide

/-- First matrix unit $E_{01}$ at Stage 1. -/
def A1 : Stage 1 := fun i j => if i = w0 ∧ j = w1 then (1 : ℂ) else 0

/-- Second matrix unit $E_{10}$ at Stage 1. -/
def B1 : Stage 1 := fun i j => if i = w1 ∧ j = w0 then (1 : ℂ) else 0

theorem bitword1_eq (w : BitWord 1) : w = w0 ∨ w = w1 := by
  cases h' : w ⟨0, by decide⟩
  · left; ext i; fin_cases i; exact h'
  · right; ext i; fin_cases i; exact h'

theorem univ_bitword1 : (Finset.univ : Finset (BitWord 1)) = {w0, w1} := by
  ext w
  simp only [Finset.mem_univ, true_iff, Finset.mem_insert, Finset.mem_singleton]
  exact bitword1_eq w

theorem not_mem_singleton_w1 : w0 ∉ ({w1} : Finset (BitWord 1)) := by
  simp only [Finset.mem_singleton]
  exact w0_ne_w1

theorem A1_mul_B1_w0_w0 : (A1 * B1) w0 w0 = 1 := by
  rw [Matrix.mul_apply, univ_bitword1, Finset.sum_insert not_mem_singleton_w1, Finset.sum_singleton]
  dsimp [A1, B1]
  simp [w0_ne_w1]

theorem B1_mul_A1_w0_w0 : (B1 * A1) w0 w0 = 0 := by
  rw [Matrix.mul_apply, univ_bitword1, Finset.sum_insert not_mem_singleton_w1, Finset.sum_singleton]
  dsimp [A1, B1]
  simp [w0_ne_w1]

theorem A1_mul_B1_ne : A1 * B1 ≠ B1 * A1 := by
  intro h
  have h_entry : (A1 * B1) w0 w0 = (B1 * A1) w0 w0 := by rw [h]
  rw [A1_mul_B1_w0_w0, B1_mul_A1_w0_w0] at h_entry
  exact one_ne_zero h_entry

/-- Non-commutativity witness: the inductive direct limit algebra `MatrixStageLimit`
    is strictly non-commutative. -/
theorem matrix_stage_limit_noncommutative : ∃ X Y : MatrixStageLimit, X * Y ≠ Y * X := by
  use canonicalStageHom 1 A1, canonicalStageHom 1 B1
  intro h
  have h_mul : canonicalStageHom 1 (A1 * B1) = canonicalStageHom 1 (B1 * A1) := by
    rw [map_mul, map_mul, h]
  have h_eq := canonicalStageHom_injective 1 h_mul
  exact A1_mul_B1_ne h_eq

end

end InfoGeometry.Canonical.SatoGNSPreHilbertSubfactorBridge
