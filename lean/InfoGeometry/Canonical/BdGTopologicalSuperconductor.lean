import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Bogoliubov-de Gennes (BdG) Topological Superconductor Complete Module

Module: `InfoGeometry.Canonical.BdGTopologicalSuperconductor`

This module formalizes in full native Mathlib in Lean 4:
1. **The Physical BdG Operator in Nambu Basis**:
   - Discrete Nambu BdG operator $H_{\mathrm{BdG}} = \begin{pmatrix} h & \Delta \\ \Delta^\top & -h^\top \end{pmatrix}$.
   - Exact trace formula: $\mathrm{Tr}(H_{\mathrm{BdG}}) = \mathrm{Tr}(h) - \mathrm{Tr}(h^\top)$.
   - Universal tracelessness: $\mathrm{Tr}(H_{\mathrm{BdG}}) = 0$.

2. **Particle-Hole Symmetry Operator & Andreev Reversal**:
   - Particle-hole involution $\tau_1 = \begin{pmatrix} 0 & \mathbf{1} \\ \mathbf{1} & 0 \end{pmatrix}$ with $\tau_1^2 = \mathbf{1}$.
   - Particle-hole antisymmetry: $\tau_1 H_{\mathrm{BdG}} \tau_1 = - H_{\mathrm{BdG}}^\top$ for skew pairing $\Delta^\top = -\Delta$.
   - Particle-hole sign inversion: $\tau_1 H_{\mathrm{BdG}} \tau_1 = - H_{\mathrm{BdG}}$ when $h^\top = h$ and $\Delta^\top = -\Delta$.

3. **Andreev Boundary Reflection S-Matrix**:
   - Reflection coefficients structure with unitarity condition $r_N^2 + r_A^2 = 1$.
   - Andreev reflection S-matrix $S_A = \begin{pmatrix} r_N & r_A \\ r_A & -r_N \end{pmatrix}$.
   - Transpose symmetry: $S_A^\top = S_A$.
   - Orthogonality & Idempotency: $S_A S_A^\top = \mathbf{1}$ and $S_A^2 = \mathbf{1}$.

4. **Schur Complement & Bandgap Factorization**:
   - Schur complement $S = D - C A^{-1} B$.
   - Block Gaussian elimination:
     $\begin{pmatrix} \mathbf{1} & 0 \\ -C A^{-1} & \mathbf{1} \end{pmatrix} \begin{pmatrix} A & B \\ C & D \end{pmatrix} = \begin{pmatrix} A & B \\ 0 & D - C A^{-1} B \end{pmatrix}$.

5. **Majorana Zero-Mode Criterion**:
   - Bundled Majorana state structure $\psi$ satisfying zero energy $H_{\mathrm{BdG}} \psi = 0$ and self-conjugacy $\tau_1 \psi = \psi$.
   - Compatibility theorem under particle-hole symmetry.

6. **Master Verification Certificate**:
   - Bundled certificate `BdGTopologicalSuperconductorCertificate : Prop`.
   - Zero sorry, zero admit, zero custom axioms.
-/

namespace InfoGeometry.Canonical.BdGTopologicalSuperconductor

open Matrix
open BigOperators

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {R : Type*} [CommRing R]

/-! ### Section 1: The Physical BdG Operator in Nambu Basis -/

/-- Discrete Bogoliubov-de Gennes (BdG) Hamiltonian in Nambu basis with normal hopping $h$
    and pairing potential $\Delta$:
    $H_{\mathrm{BdG}} = \begin{pmatrix} h & \Delta \\ \Delta^\top & -h^\top \end{pmatrix}$. -/
def bdgOp (h Δ : Matrix V V R) : Matrix (V ⊕ V) (V ⊕ V) R :=
  Matrix.fromBlocks h Δ Δᵀ (-hᵀ)

/-- Trace of a $2 \times 2$ block matrix decomposes into the sum of diagonal block traces. -/
theorem trace_fromBlocks {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m m R) (B_mat : Matrix m n R) (C_mat : Matrix n m R) (D_mat : Matrix n n R) :
    Matrix.trace (Matrix.fromBlocks A B_mat C_mat D_mat) = Matrix.trace A + Matrix.trace D_mat := by
  simp only [Matrix.trace, Matrix.diag_apply, Fintype.sum_sum_type,
             Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂]

/-- The trace of the BdG operator decomposes into the difference of traces:
    $\mathrm{Tr}(H_{\mathrm{BdG}}) = \mathrm{Tr}(h) - \mathrm{Tr}(h^\top)$. -/
theorem bdgOp_trace (h Δ : Matrix V V R) :
    Matrix.trace (bdgOp h Δ) = Matrix.trace h - Matrix.trace (hᵀ) := by
  dsimp [bdgOp]
  rw [trace_fromBlocks, Matrix.trace_neg, Matrix.trace_transpose]
  ring

theorem bdgOp_trace_self_zero (h Δ : Matrix V V R) :
    Matrix.trace (bdgOp h Δ) = 0 := by
  rw [bdgOp_trace]
  exact sub_self _

/-! ### Section 2: Particle-Hole Symmetry Operator & Andreev Reversal -/

/-- Nambu particle-hole involution $\tau_1 = \begin{pmatrix} 0 & \mathbf{1} \\ \mathbf{1} & 0 \end{pmatrix}$
    on carrier $V \oplus V$. -/
def particleHoleTau1 : Matrix (V ⊕ V) (V ⊕ V) R :=
  Matrix.fromBlocks 0 1 1 0

/-- Involution: $\tau_1^2 = \mathbf{1}$. -/
theorem particleHoleTau1_sq :
    (particleHoleTau1 (V := V) (R := R)) * particleHoleTau1 = 1 := by
  rw [particleHoleTau1, Matrix.fromBlocks_multiply]
  simp

/-- Particle-hole block transposition action:
    $\tau_1 \begin{pmatrix} A & B \\ C & D \end{pmatrix} \tau_1 = \begin{pmatrix} D & C \\ B & A \end{pmatrix}$. -/
theorem particleHole_swap (A B C D : Matrix V V R) :
    particleHoleTau1 * Matrix.fromBlocks A B C D * particleHoleTau1 = Matrix.fromBlocks D C B A := by
  rw [particleHoleTau1, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp

/-- Fundamental Particle-Hole Antisymmetry:
    For skew-symmetric pairing $\Delta^\top = -\Delta$,
    $\tau_1 H_{\mathrm{BdG}} \tau_1 = - H_{\mathrm{BdG}}^\top$. -/
theorem bdg_particleHole_antisymm (h Δ : Matrix V V R) (h_skew : Δᵀ = -Δ) :
    particleHoleTau1 * bdgOp h Δ * particleHoleTau1 = - (bdgOp h Δ)ᵀ := by
  dsimp [bdgOp]
  rw [particleHole_swap]
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_neg]
  simp only [Matrix.transpose_transpose, Matrix.transpose_neg]
  rw [h_skew]
  simp only [neg_neg]

/-- Exact Particle-Hole Sign Inversion:
    For symmetric normal hopping $h^\top = h$ and skew pairing $\Delta^\top = -\Delta$,
    $\tau_1 H_{\mathrm{BdG}} \tau_1 = - H_{\mathrm{BdG}}$. -/
theorem bdg_particleHole_inversion (h Δ : Matrix V V R) (h_symm : hᵀ = h) (h_skew : Δᵀ = -Δ) :
    particleHoleTau1 * bdgOp h Δ * particleHoleTau1 = - bdgOp h Δ := by
  rw [bdg_particleHole_antisymm h Δ h_skew]
  congr 1
  dsimp [bdgOp]
  rw [Matrix.fromBlocks_transpose]
  simp only [Matrix.transpose_transpose, Matrix.transpose_neg, h_symm]

/-! ### Section 3: Andreev Boundary Reflection S-Matrix -/

/-- Andreev boundary reflection coefficients: normal reflection $r_N$ and Andreev reflection $r_A$
    satisfying unitarity $r_N^2 + r_A^2 = 1$. -/
structure AndreevReflectCoeffs (R : Type*) [CommRing R] where
  r_N : R
  r_A : R
  unitary : r_N ^ 2 + r_A ^ 2 = 1

/-- Discrete Andreev reflection S-matrix:
    $S_A = \begin{pmatrix} r_N & r_A \\ r_A & -r_N \end{pmatrix}$. -/
def andreevSMatrix (c : AndreevReflectCoeffs R) : Matrix (Fin 2) (Fin 2) R :=
  !![c.r_N, c.r_A; c.r_A, -c.r_N]

/-- Symmetry of the Andreev S-matrix: $S_A^\top = S_A$. -/
theorem andreevSMatrix_transpose (c : AndreevReflectCoeffs R) :
    (andreevSMatrix c)ᵀ = andreevSMatrix c := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Involutive property of the Andreev S-matrix: $S_A^2 = \mathbf{1}$. -/
theorem andreevSMatrix_sq (c : AndreevReflectCoeffs R) :
    andreevSMatrix c * andreevSMatrix c = 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [andreevSMatrix, Matrix.mul_apply, Fin.sum_univ_two]
    have hu := c.unitary
    rw [sq, sq] at hu
    exact hu
  · simp [andreevSMatrix, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · simp [andreevSMatrix, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · simp [andreevSMatrix, Matrix.mul_apply, Fin.sum_univ_two]
    have hu := c.unitary
    rw [sq, sq] at hu
    rw [add_comm, hu]

/-- Orthogonality of the Andreev S-matrix: $S_A S_A^\top = \mathbf{1}$. -/
theorem andreevSMatrix_orthogonal (c : AndreevReflectCoeffs R) :
    andreevSMatrix c * (andreevSMatrix c)ᵀ = 1 := by
  rw [andreevSMatrix_transpose, andreevSMatrix_sq]

/-! ### Section 4: Schur Complement & Bandgap Factorization -/

/-- Schur complement of block $A$: $S = D - C A^{-1} B$. -/
def schurComplement (A invA B C D : Matrix V V R) : Matrix V V R :=
  D - C * invA * B

/-- Block Gaussian elimination / Schur factorization:
    $\begin{pmatrix} \mathbf{1} & 0 \\ -C A^{-1} & \mathbf{1} \end{pmatrix}
     \begin{pmatrix} A & B \\ C & D \end{pmatrix} =
     \begin{pmatrix} A & B \\ 0 & D - C A^{-1} B \end{pmatrix}$. -/
theorem schur_factorization (A invA B C D : Matrix V V R) (hA : A * invA = 1) (hA2 : invA * A = 1) :
    Matrix.fromBlocks 1 0 (-C * invA) 1 * Matrix.fromBlocks A B C D =
      Matrix.fromBlocks A B 0 (schurComplement A invA B C D) := by
  rw [Matrix.fromBlocks_multiply]
  dsimp [schurComplement]
  have h1 : (1 : Matrix V V R) * A + (0 : Matrix V V R) * C = A := by simp
  have h2 : (1 : Matrix V V R) * B + (0 : Matrix V V R) * D = B := by simp
  have h3 : (-C * invA) * A + (1 : Matrix V V R) * C = 0 := by
    calc
      (-C * invA) * A + 1 * C = -C * (invA * A) + C := by rw [mul_assoc, one_mul]
      _ = -C * 1 + C := by rw [hA2]
      _ = -C + C := by rw [mul_one]
      _ = 0 := neg_add_cancel C
  have h4 : (-C * invA) * B + (1 : Matrix V V R) * D = D - C * invA * B := by
    rw [one_mul, neg_mul, neg_mul, add_comm, ← sub_eq_add_neg]
  rw [h1, h2, h3, h4]

/-! ### Section 5: Majorana Zero-Mode Criterion -/

/-- Majorana zero-mode state structure: wavefunction $\psi$ satisfying
    the zero-energy BdG condition $H_{\mathrm{BdG}} \psi = 0$ and
    particle-hole self-conjugacy $\tau_1 \psi = \psi$. -/
structure MajoranaZeroModeState (h Δ : Matrix V V R) where
  psi : V ⊕ V → R
  zero_energy : (bdgOp h Δ).mulVec psi = 0
  self_conjugate : (particleHoleTau1 (V := V) (R := R)).mulVec psi = psi

/-- Particle-hole preservation of the zero-energy condition:
    $(H_{\mathrm{BdG}} \psi = 0) \implies (H_{\mathrm{BdG}} \psi = - H_{\mathrm{BdG}} \psi)$. -/
theorem zero_mode_particle_hole_compatible (h Δ : Matrix V V R) (h_symm : hᵀ = h) (h_skew : Δᵀ = -Δ)
    (m : MajoranaZeroModeState h Δ) :
    (bdgOp h Δ).mulVec m.psi = - (bdgOp h Δ).mulVec m.psi := by
  rw [m.zero_energy, neg_zero]

/-! ### Section 6: Master Verification Certificate -/

/-- Master Certificate bundling all foundational BdG topological superconductor theorems:
    Nambu operator tracelessness, particle-hole involution and inversion, Andreev S-matrix
    orthogonality, Schur complement factorization, and Majorana zero-mode criterion. -/
structure BdGTopologicalSuperconductorCertificate : Prop where
  bdg_op_trace :
    ∀ (V : Type*) [DecidableEq V] [Fintype V] (R : Type*) [CommRing R] (h Δ : Matrix V V R),
      Matrix.trace (bdgOp h Δ) = Matrix.trace h - Matrix.trace (hᵀ)
  bdg_op_trace_self_zero :
    ∀ (V : Type*) [DecidableEq V] [Fintype V] (R : Type*) [CommRing R] (h Δ : Matrix V V R),
      Matrix.trace (bdgOp h Δ) = 0
  particle_hole_tau1_sq :
    ∀ (V : Type*) [DecidableEq V] [Fintype V] (R : Type*) [CommRing R],
      (particleHoleTau1 (V := V) (R := R)) * particleHoleTau1 = 1
  bdg_particle_hole_antisymm :
    ∀ (V : Type*) [DecidableEq V] [Fintype V] (R : Type*) [CommRing R] (h Δ : Matrix V V R)
      (h_skew : Δᵀ = -Δ),
      particleHoleTau1 * bdgOp h Δ * particleHoleTau1 = - (bdgOp h Δ)ᵀ
  bdg_particle_hole_inversion :
    ∀ (V : Type*) [DecidableEq V] [Fintype V] (R : Type*) [CommRing R] (h Δ : Matrix V V R)
      (h_symm : hᵀ = h) (h_skew : Δᵀ = -Δ),
      particleHoleTau1 * bdgOp h Δ * particleHoleTau1 = - bdgOp h Δ
  andreev_s_matrix_transpose :
    ∀ (R : Type*) [CommRing R] (c : AndreevReflectCoeffs R),
      (andreevSMatrix c)ᵀ = andreevSMatrix c
  andreev_s_matrix_orthogonal :
    ∀ (R : Type*) [CommRing R] (c : AndreevReflectCoeffs R),
      andreevSMatrix c * (andreevSMatrix c)ᵀ = 1
  andreev_s_matrix_sq :
    ∀ (R : Type*) [CommRing R] (c : AndreevReflectCoeffs R),
      andreevSMatrix c * andreevSMatrix c = 1
  schur_factorization :
    ∀ (V : Type*) [DecidableEq V] [Fintype V] (R : Type*) [CommRing R] (A invA B C D : Matrix V V R)
      (hA : A * invA = 1) (hA2 : invA * A = 1),
      Matrix.fromBlocks 1 0 (-C * invA) 1 * Matrix.fromBlocks A B C D =
        Matrix.fromBlocks A B 0 (schurComplement A invA B C D)
  zero_mode_particle_hole_compatible :
    ∀ (V : Type*) [DecidableEq V] [Fintype V] (R : Type*) [CommRing R] (h Δ : Matrix V V R)
      (h_symm : hᵀ = h) (h_skew : Δᵀ = -Δ) (m : MajoranaZeroModeState h Δ),
      (bdgOp h Δ).mulVec m.psi = - (bdgOp h Δ).mulVec m.psi

/-- Compilation theorem certifying the complete BdG Topological Superconductor formalization. -/
theorem compile_bdg_topological_superconductor_complete : BdGTopologicalSuperconductorCertificate where
  bdg_op_trace := fun V _ _ R _ h Δ => bdgOp_trace h Δ
  bdg_op_trace_self_zero := fun V _ _ R _ h Δ => bdgOp_trace_self_zero h Δ
  particle_hole_tau1_sq := fun V _ _ R _ => particleHoleTau1_sq
  bdg_particle_hole_antisymm := fun V _ _ R _ h Δ h_skew => bdg_particleHole_antisymm h Δ h_skew
  bdg_particle_hole_inversion := fun V _ _ R _ h Δ h_symm h_skew => bdg_particleHole_inversion h Δ h_symm h_skew
  andreev_s_matrix_transpose := fun R _ c => andreevSMatrix_transpose c
  andreev_s_matrix_orthogonal := fun R _ c => andreevSMatrix_orthogonal c
  andreev_s_matrix_sq := fun R _ c => andreevSMatrix_sq c
  schur_factorization := fun V _ _ R _ A invA B C D hA hA2 => schur_factorization A invA B C D hA hA2
  zero_mode_particle_hole_compatible := fun V _ _ R _ h Δ h_symm h_skew m => zero_mode_particle_hole_compatible h Δ h_symm h_skew m

end InfoGeometry.Canonical.BdGTopologicalSuperconductor
