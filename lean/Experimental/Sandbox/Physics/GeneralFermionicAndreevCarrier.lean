import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sum
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases

open Matrix
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

/-!
# General Fermionic Andreev Carrier & Horizon S-Matrix Conservation
Target: `lean/Experimental/Sandbox/Physics/GeneralFermionicAndreevCarrier.lean`

Generalizes the historical 1D / 2-coordinate toy models of Fermionic Andreev Reflection
into an arbitrary-dimensional Hilbert/graph carrier module:
1. The General Andreev 90-Degree Rotation Operator:
   - On doubled electron-hole space `V ⊕ V`:
     $R_A = \begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix}$.
   - Exact almost-complex / fermionic phase rotation: $R_A^2 = -1$.
   - 4-step Andreev boundary loop: $R_A^4 = 1$.
   - Tracelessness of the general Andreev rotation: $\operatorname{Tr}(R_A) = 0$.
2. Quadratic Form & Norm Conservation:
   - Generalized quadratic form on `V ⊕ V → R`: $\lVert v \rVert^2 = \sum_i (v_i)^2$.
   - Exact entrywise action on electron and hole sectors:
     $(R_A v)_e = -v_h$, $(R_A v)_h = v_e$.
   - Invariance of the quadratic norm: $\lVert R_A v \rVert^2 = \lVert v \rVert^2$.
3. Horizon 2-Channel Scattering S-Matrix & Conservation:
   - Unitary scattering structure with normal/Andreev reflections and transmissions.
   - S-matrix representation in `Matrix (Fin 2) (Fin 2) R`.
   - Exact unitarity and flux conservation: $S S^\top = 1$.
4. Master Verification Certificate:
   - Structure `GeneralFermionicAndreevCertificate : Prop`.
   - Complete zero-sorry compilation theorem `compile_general_fermionic_andreev`.
-/

namespace Experimental.Sandbox.Physics.GeneralFermionicAndreevCarrier

universe u_V u_R

variable {V : Type u_V} [DecidableEq V] [Fintype V]
variable {R : Type u_R} [CommRing R]

/-! ### Section 1: The General Andreev 90-Degree Rotation Operator -/

/-- General Andreev 90-degree particle-hole rotation operator on doubled space `V ⊕ V`:
    $R_A = \begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix}$. -/
def andreevRotation : Matrix (V ⊕ V) (V ⊕ V) R :=
  Matrix.fromBlocks 0 (-1) 1 0

/-- Fundamental almost-complex / fermionic phase rotation law:
    $R_A^2 = -1$. -/
theorem andreevRotation_sq :
    (andreevRotation (V := V) (R := R)) * andreevRotation = -1 := by
  dsimp [andreevRotation]
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one,
    add_zero, zero_add, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks, Matrix.one_apply, Matrix.neg_apply]

/-- 4-step Andreev loop closure:
    $R_A^4 = 1$. -/
theorem andreevRotation_pow4 :
    (andreevRotation (V := V) (R := R)) * andreevRotation *
      (andreevRotation * andreevRotation) = 1 := by
  rw [andreevRotation_sq]
  rw [mul_neg, mul_one, neg_neg]

/-- Trace of block $2 \times 2$ matrix decomposes into the sum of diagonal block traces. -/
theorem trace_fromBlocks {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m m R) (B_mat : Matrix m n R) (C_mat : Matrix n m R) (D_mat : Matrix n n R) :
    Matrix.trace (Matrix.fromBlocks A B_mat C_mat D_mat) = Matrix.trace A + Matrix.trace D_mat := by
  simp only [Matrix.trace, Matrix.diag_apply, Fintype.sum_sum_type,
             Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂]

/-- Tracelessness of the general Andreev rotation operator:
    $\operatorname{Tr}(R_A) = 0$. -/
theorem andreevRotation_traceless :
    Matrix.trace (andreevRotation (V := V) (R := R)) = 0 := by
  dsimp [andreevRotation]
  rw [trace_fromBlocks, Matrix.trace_zero, add_zero]

/-! ### Section 2: Quadratic Form & Norm Conservation -/

/-- Generalized quadratic norm on the total particle-hole carrier $V \oplus V \to R$:
    $\lVert v \rVert^2 = \sum_x (v(x))^2$. -/
def vectorNormSq (v : V ⊕ V → R) : R :=
  ∑ i, (v i)^2

/-- Entrywise action of the Andreev rotation on the electron sector:
    $(R_A v)(\mathrm{inl}\ i) = - v(\mathrm{inr}\ i)$. -/
theorem andreevRotation_mulVec_inl (v : V ⊕ V → R) (i : V) :
    (andreevRotation.mulVec v) (Sum.inl i) = - v (Sum.inr i) := by
  have hv : v = Sum.elim (fun j => v (Sum.inl j)) (fun j => v (Sum.inr j)) := by
    ext (j | j) <;> rfl
  conv_lhs => rw [hv]
  rw [andreevRotation, Matrix.fromBlocks_mulVec]
  simp only [Sum.elim_inl, Matrix.zero_mulVec, zero_add, Matrix.neg_mulVec, Matrix.one_mulVec, Pi.neg_apply]
  rfl

/-- Entrywise action of the Andreev rotation on the hole sector:
    $(R_A v)(\mathrm{inr}\ i) = v(\mathrm{inl}\ i)$. -/
theorem andreevRotation_mulVec_inr (v : V ⊕ V → R) (i : V) :
    (andreevRotation.mulVec v) (Sum.inr i) = v (Sum.inl i) := by
  have hv : v = Sum.elim (fun j => v (Sum.inl j)) (fun j => v (Sum.inr j)) := by
    ext (j | j) <;> rfl
  conv_lhs => rw [hv]
  rw [andreevRotation, Matrix.fromBlocks_mulVec]
  simp only [Sum.elim_inr, Matrix.zero_mulVec, add_zero, Matrix.one_mulVec]
  rfl

/-- Exact quadratic norm conservation under the general Andreev rotation:
    $\lVert R_A v \rVert^2 = \lVert v \rVert^2$. -/
theorem andreevRotation_preserves_norm (v : V ⊕ V → R) :
    vectorNormSq (andreevRotation.mulVec v) = vectorNormSq v := by
  dsimp [vectorNormSq]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [andreevRotation_mulVec_inl, andreevRotation_mulVec_inr, neg_sq]
  rw [add_comm]

/-! ### Section 3: Horizon 2-Channel Scattering S-Matrix & Conservation -/

/-- 2-channel scattering structure at an Andreev superconducting horizon,
    specifying normal reflection $r_N$, Andreev reflection $r_A$,
    normal transmission $t_N$, and Andreev transmission $t_A$. -/
structure ScatteringSMatrix2 (R : Type*) [CommRing R] where
  rN : R
  rA : R
  tN : R
  tA : R
  unitary_row1 : rN^2 + rA^2 = 1
  unitary_row2 : tN^2 + tA^2 = 1
  orthogonal : rN * tN + rA * tA = 0

/-- Matrix representation of the 2-channel scattering S-matrix:
    $S = \begin{pmatrix} r_N & r_A \\ t_N & t_A \end{pmatrix}$. -/
def toSMatrix (S : ScatteringSMatrix2 R) : Matrix (Fin 2) (Fin 2) R :=
  !![S.rN, S.rA; S.tN, S.tA]

/-- Exact unitarity and flux conservation of the 2-channel horizon S-matrix:
    $S S^\top = 1$. -/
theorem sMatrix_mul_transpose_one (S : ScatteringSMatrix2 R) :
    toSMatrix S * (toSMatrix S)ᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp only [toSMatrix, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.one_apply_eq]
    calc
      S.rN * S.rN + S.rA * S.rA = S.rN^2 + S.rA^2 := by ring
      _ = 1 := S.unitary_row1
  · simp only [toSMatrix, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide)]
    exact S.orthogonal
  · simp only [toSMatrix, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)]
    calc
      S.tN * S.rN + S.tA * S.rA = S.rN * S.tN + S.rA * S.tA := by ring
      _ = 0 := S.orthogonal
  · simp only [toSMatrix, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.one_apply_eq]
    calc
      S.tN * S.tN + S.tA * S.tA = S.tN^2 + S.tA^2 := by ring
      _ = 1 := S.unitary_row2

/-! ### Section 4: Master Verification Certificate -/

/-- Master Verification Certificate bundling the general Andreev rotation algebra,
    quadratic norm conservation, and horizon 2-channel S-matrix unitarity. -/
structure GeneralFermionicAndreevCertificate : Prop where
  andreev_rotation_sq :
    ∀ {V : Type u_V} [DecidableEq V] [Fintype V] {R : Type u_R} [CommRing R],
      andreevRotation (V := V) (R := R) * andreevRotation = -1
  andreev_rotation_pow4 :
    ∀ {V : Type u_V} [DecidableEq V] [Fintype V] {R : Type u_R} [CommRing R],
      andreevRotation (V := V) (R := R) * andreevRotation *
        (andreevRotation * andreevRotation) = 1
  andreev_rotation_traceless :
    ∀ {V : Type u_V} [DecidableEq V] [Fintype V] {R : Type u_R} [CommRing R],
      Matrix.trace (andreevRotation (V := V) (R := R)) = 0
  andreev_mulvec_inl :
    ∀ {V : Type u_V} [DecidableEq V] [Fintype V] {R : Type u_R} [CommRing R]
      (v : V ⊕ V → R) (i : V),
      (andreevRotation.mulVec v) (Sum.inl i) = - v (Sum.inr i)
  andreev_mulvec_inr :
    ∀ {V : Type u_V} [DecidableEq V] [Fintype V] {R : Type u_R} [CommRing R]
      (v : V ⊕ V → R) (i : V),
      (andreevRotation.mulVec v) (Sum.inr i) = v (Sum.inl i)
  andreev_preserves_norm :
    ∀ {V : Type u_V} [DecidableEq V] [Fintype V] {R : Type u_R} [CommRing R]
      (v : V ⊕ V → R),
      vectorNormSq (andreevRotation.mulVec v) = vectorNormSq v
  smatrix_unitary :
    ∀ {R : Type u_R} [CommRing R] (S : ScatteringSMatrix2 R),
      toSMatrix S * (toSMatrix S)ᵀ = 1

/-- Compilation of the master General Fermionic Andreev Carrier certificate with zero sorry. -/
theorem compile_general_fermionic_andreev :
    GeneralFermionicAndreevCertificate where
  andreev_rotation_sq := andreevRotation_sq
  andreev_rotation_pow4 := andreevRotation_pow4
  andreev_rotation_traceless := andreevRotation_traceless
  andreev_mulvec_inl := andreevRotation_mulVec_inl
  andreev_mulvec_inr := andreevRotation_mulVec_inr
  andreev_preserves_norm := andreevRotation_preserves_norm
  smatrix_unitary := sMatrix_mul_transpose_one

end Experimental.Sandbox.Physics.GeneralFermionicAndreevCarrier
