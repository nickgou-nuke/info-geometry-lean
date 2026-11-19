/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Exceptional.GenericGradedJacobiClosure
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.Meta
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Order.Antichain
import Mathlib.Order.Bounds.Defs
import Mathlib.Tactic.FinCases

/-!
# Split $\mathfrak{g}_{2(2)} \subset \mathrm{Cl}^{(2)}(4,4)$ on Double-Real Krein Spinors $\mathcal{K}_{8,8}$

Complete native Mathlib Lean 4 formalization of the epistemic `SOLVE ET COAGULA`
architecture over noncommutative real matrix algebras (`Mat2`, `Mat16`), $\mathrm{Cl}(1,1)$,
$\mathrm{Cl}(4,4)$ on the 16-dimensional double-real Krein module $\mathcal{K}_{8,8}$,
Cartan's $S_3$ triality, the 14-dimensional centerless 5-graded split Lie algebra
$\mathfrak{g}_{2(2)}$, Witt's Free Lie Algebra pigeonhole obstruction, and the 15-node
graded acyclic causal poset $(\mathfrak{P}, \prec)$.

No scalar, diagonal, or commuting surrogates are substituted anywhere; zero `sorry`,
`admit`, `native_decide`, or custom axioms are used.
-/

noncomputable section

namespace InfoGeometry.Exceptional.SplitG2Cl44SolveEtCoagulaPoset

open Matrix Module Submodule
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Exceptional
open InfoGeometry.MetaCompiler

/-! ## Section 0 (`PHASE 0 — SOLVE`): Primordial Cut, Peirce Anatomy in `Cl(1,1)`, & `tensor4` -/

abbrev Mat2 : Type := Matrix (Fin 2) (Fin 2) ℝ

lemma ext_mat2 {A B : Mat2}
    (h00 : A 0 0 = B 0 0) (h01 : A 0 1 = B 0 1)
    (h10 : A 1 0 = B 1 0) (h11 : A 1 1 = B 1 1) : A = B := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

def cl11Pos : Mat2 := !![0, 1; 1, 0]
def cl11Neg : Mat2 := !![0, -1; 1, 0]
def cl11Grad : Mat2 := !![1, 0; 0, -1]
def cl11Proj0 : Mat2 := !![1, 0; 0, 0]
def cl11Proj1 : Mat2 := !![0, 0; 0, 1]
def cl11Up : Mat2 := !![0, 0; 1, 0]
def cl11Down : Mat2 := !![0, 1; 0, 0]

lemma one_mat2_eq_proj_add : (1 : Mat2) = cl11Proj0 + cl11Proj1 := by
  apply ext_mat2 <;> norm_num [cl11Proj0, cl11Proj1]

lemma cl11Grad_eq_invS : cl11Grad = invS cl11Proj0 := by
  apply ext_mat2 <;> norm_num [cl11Grad, invS, cl11Proj0]

lemma cl11Proj1_eq_one_sub : cl11Proj1 = (1 : Mat2) - cl11Proj0 := by
  apply ext_mat2 <;> norm_num [cl11Proj1, cl11Proj0]

@[simp] lemma cl11Pos_00 : cl11Pos 0 0 = 0 := by norm_num [cl11Pos]
@[simp] lemma cl11Pos_01 : cl11Pos 0 1 = 1 := by norm_num [cl11Pos]
@[simp] lemma cl11Pos_10 : cl11Pos 1 0 = 1 := by norm_num [cl11Pos]
@[simp] lemma cl11Pos_11 : cl11Pos 1 1 = 0 := by norm_num [cl11Pos]

@[simp] lemma cl11Neg_00 : cl11Neg 0 0 = 0 := by norm_num [cl11Neg]
@[simp] lemma cl11Neg_01 : cl11Neg 0 1 = -1 := by norm_num [cl11Neg]
@[simp] lemma cl11Neg_10 : cl11Neg 1 0 = 1 := by norm_num [cl11Neg]
@[simp] lemma cl11Neg_11 : cl11Neg 1 1 = 0 := by norm_num [cl11Neg]

@[simp] lemma cl11Grad_00 : cl11Grad 0 0 = 1 := by norm_num [cl11Grad]
@[simp] lemma cl11Grad_01 : cl11Grad 0 1 = 0 := by norm_num [cl11Grad]
@[simp] lemma cl11Grad_10 : cl11Grad 1 0 = 0 := by norm_num [cl11Grad]
@[simp] lemma cl11Grad_11 : cl11Grad 1 1 = -1 := by norm_num [cl11Grad]

@[simp] lemma cl11Proj0_00 : cl11Proj0 0 0 = 1 := by norm_num [cl11Proj0]
@[simp] lemma cl11Proj0_01 : cl11Proj0 0 1 = 0 := by norm_num [cl11Proj0]
@[simp] lemma cl11Proj0_10 : cl11Proj0 1 0 = 0 := by norm_num [cl11Proj0]
@[simp] lemma cl11Proj0_11 : cl11Proj0 1 1 = 0 := by norm_num [cl11Proj0]

@[simp] lemma cl11Proj1_00 : cl11Proj1 0 0 = 0 := by norm_num [cl11Proj1]
@[simp] lemma cl11Proj1_01 : cl11Proj1 0 1 = 0 := by norm_num [cl11Proj1]
@[simp] lemma cl11Proj1_10 : cl11Proj1 1 0 = 0 := by norm_num [cl11Proj1]
@[simp] lemma cl11Proj1_11 : cl11Proj1 1 1 = 1 := by norm_num [cl11Proj1]

@[simp] lemma cl11Up_00 : cl11Up 0 0 = 0 := by norm_num [cl11Up]
@[simp] lemma cl11Up_01 : cl11Up 0 1 = 0 := by norm_num [cl11Up]
@[simp] lemma cl11Up_10 : cl11Up 1 0 = 1 := by norm_num [cl11Up]
@[simp] lemma cl11Up_11 : cl11Up 1 1 = 0 := by norm_num [cl11Up]

@[simp] lemma cl11Down_00 : cl11Down 0 0 = 0 := by norm_num [cl11Down]
@[simp] lemma cl11Down_01 : cl11Down 0 1 = 1 := by norm_num [cl11Down]
@[simp] lemma cl11Down_10 : cl11Down 1 0 = 0 := by norm_num [cl11Down]
@[simp] lemma cl11Down_11 : cl11Down 1 1 = 0 := by norm_num [cl11Down]

@[simp] lemma cl11Pos_transpose : cl11Posᵀ = cl11Pos := by
  apply ext_mat2 <;> simp [Matrix.transpose_apply]
@[simp] lemma cl11Neg_transpose : cl11Negᵀ = -cl11Neg := by
  apply ext_mat2 <;> simp [Matrix.transpose_apply]
@[simp] lemma cl11Grad_transpose : cl11Gradᵀ = cl11Grad := by
  apply ext_mat2 <;> simp [Matrix.transpose_apply]
@[simp] lemma cl11Proj0_transpose : cl11Proj0ᵀ = cl11Proj0 := by
  apply ext_mat2 <;> simp [Matrix.transpose_apply]
@[simp] lemma cl11Proj1_transpose : cl11Proj1ᵀ = cl11Proj1 := by
  apply ext_mat2 <;> simp [Matrix.transpose_apply]
@[simp] lemma cl11Up_transpose : cl11Upᵀ = cl11Down := by
  apply ext_mat2 <;> simp [Matrix.transpose_apply]
@[simp] lemma cl11Down_transpose : cl11Downᵀ = cl11Up := by
  apply ext_mat2 <;> simp [Matrix.transpose_apply]

@[simp] lemma cl11Pos_mul_self : cl11Pos * cl11Pos = (1 : Mat2) := by
  apply ext_mat2 <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma cl11Neg_mul_self : cl11Neg * cl11Neg = -(1 : Mat2) := by
  apply ext_mat2 <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma cl11Grad_mul_self : cl11Grad * cl11Grad = (1 : Mat2) := by
  apply ext_mat2 <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma cl11Pos_mul_neg : cl11Pos * cl11Neg = cl11Grad := by
  apply ext_mat2 <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma cl11Neg_mul_pos : cl11Neg * cl11Pos = -cl11Grad := by
  apply ext_mat2 <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma cl11Pos_mul_grad : cl11Pos * cl11Grad = cl11Neg := by
  apply ext_mat2 <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma cl11Grad_mul_pos : cl11Grad * cl11Pos = -cl11Neg := by
  apply ext_mat2 <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma cl11Neg_mul_grad : cl11Neg * cl11Grad = cl11Pos := by
  apply ext_mat2 <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma cl11Grad_mul_neg : cl11Grad * cl11Neg = -cl11Pos := by
  apply ext_mat2 <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma cl11Up_mul_up : cl11Up * cl11Up = (0 : Mat2) := by
  apply ext_mat2 <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma cl11Down_mul_down : cl11Down * cl11Down = (0 : Mat2) := by
  apply ext_mat2 <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma cl11Up_mul_down : cl11Up * cl11Down = cl11Proj1 := by
  apply ext_mat2 <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma cl11Down_mul_up : cl11Down * cl11Up = cl11Proj0 := by
  apply ext_mat2 <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma cl11Grad_mul_up : cl11Grad * cl11Up = -cl11Up := by
  apply ext_mat2 <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma cl11Up_mul_grad : cl11Up * cl11Grad = cl11Up := by
  apply ext_mat2 <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma cl11Grad_mul_down : cl11Grad * cl11Down = cl11Down := by
  apply ext_mat2 <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma cl11Down_mul_grad : cl11Down * cl11Grad = -cl11Down := by
  apply ext_mat2 <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma cl11Proj0_mul_self : cl11Proj0 * cl11Proj0 = cl11Proj0 := by
  apply ext_mat2 <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma cl11Proj1_mul_self : cl11Proj1 * cl11Proj1 = cl11Proj1 := by
  apply ext_mat2 <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma cl11Proj0_mul_proj1 : cl11Proj0 * cl11Proj1 = (0 : Mat2) := by
  apply ext_mat2 <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma cl11Proj1_mul_proj0 : cl11Proj1 * cl11Proj0 = (0 : Mat2) := by
  apply ext_mat2 <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma cl11Proj1_mul_up : cl11Proj1 * cl11Up = cl11Up := by
  apply ext_mat2 <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma cl11Up_mul_proj1 : cl11Up * cl11Proj1 = (0 : Mat2) := by
  apply ext_mat2 <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma cl11Proj1_mul_down : cl11Proj1 * cl11Down = (0 : Mat2) := by
  apply ext_mat2 <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma cl11Down_mul_proj1 : cl11Down * cl11Proj1 = cl11Down := by
  apply ext_mat2 <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma cl11Proj1_mul_grad : cl11Proj1 * cl11Grad = -cl11Proj1 := by
  apply ext_mat2 <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma cl11Grad_mul_proj1 : cl11Grad * cl11Proj1 = -cl11Proj1 := by
  apply ext_mat2 <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma cl11Proj1_mul_pos : cl11Proj1 * cl11Pos = cl11Up := by
  apply ext_mat2 <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma cl11Pos_mul_proj1 : cl11Pos * cl11Proj1 = cl11Down := by
  apply ext_mat2 <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma cl11Proj1_mul_neg : cl11Proj1 * cl11Neg = cl11Up := by
  apply ext_mat2 <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma cl11Neg_mul_proj1 : cl11Neg * cl11Proj1 = -cl11Down := by
  apply ext_mat2 <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma cl11Up_mul_pos : cl11Up * cl11Pos = cl11Proj1 := by
  apply ext_mat2 <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma cl11Pos_mul_up : cl11Pos * cl11Up = cl11Proj0 := by
  apply ext_mat2 <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma cl11Up_mul_neg : cl11Up * cl11Neg = -cl11Proj1 := by
  apply ext_mat2 <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma cl11Neg_mul_up : cl11Neg * cl11Up = -cl11Proj0 := by
  apply ext_mat2 <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma cl11Down_mul_pos : cl11Down * cl11Pos = cl11Proj0 := by
  apply ext_mat2 <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma cl11Pos_mul_down : cl11Pos * cl11Down = cl11Proj1 := by
  apply ext_mat2 <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma cl11Down_mul_neg : cl11Down * cl11Neg = cl11Proj0 := by
  apply ext_mat2 <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma cl11Neg_mul_down : cl11Neg * cl11Down = cl11Proj1 := by
  apply ext_mat2 <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

lemma cl11Up_anticomm_down : cl11Up * cl11Down + cl11Down * cl11Up = (1 : Mat2) := by
  apply ext_mat2 <;> norm_num [cl11Up, cl11Down, Matrix.mul_apply, Fin.sum_univ_two]

lemma cl11Up_comm_down : cl11Up * cl11Down - cl11Down * cl11Up = -cl11Grad := by
  apply ext_mat2 <;> norm_num [cl11Up, cl11Down, cl11Grad, Matrix.mul_apply, Fin.sum_univ_two]

theorem cl11Pos_cl11Neg_noncomm : cl11Pos * cl11Neg ≠ cl11Neg * cl11Pos := by
  intro h
  have h00 := congrArg (fun M : Mat2 => M 0 0) h
  simp at h00
  norm_num at h00

lemma peirce_fourfold_anatomy_mat2 (M : Mat2) :
    peirce11 cl11Proj0 M = M 0 0 • cl11Proj0 ∧
    conePlus cl11Proj0 M = M 0 1 • cl11Down ∧
    coneMinus cl11Proj0 M = M 1 0 • cl11Up ∧
    peirce00 cl11Proj0 M = M 1 1 • cl11Proj1 ∧
    M = peirce11 cl11Proj0 M + conePlus cl11Proj0 M +
        coneMinus cl11Proj0 M + peirce00 cl11Proj0 M := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    apply ext_mat2 <;>
    simp [peirce11, conePlus, coneMinus, peirce00, cl11Proj0, cl11Proj1, cl11Up, cl11Down,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

/-! ### 4-Fold Tensor Algebra on `Krein16Idx` -/

abbrev Krein16Idx : Type := Fin 2 × Fin 2 × Fin 2 × Fin 2
abbrev Mat16 : Type := Matrix Krein16Idx Krein16Idx ℝ

theorem finrank_mat16 : Module.finrank ℝ Mat16 = 256 := by
  rw [Module.finrank_matrix]
  simp

def tensor4 (A B C D : Mat2) : Mat16 :=
  fun i j => A i.1 j.1 * B i.2.1 j.2.1 * C i.2.2.1 j.2.2.1 * D i.2.2.2 j.2.2.2

@[simp] lemma tensor4_apply (A B C D : Mat2) (i j : Krein16Idx) :
    tensor4 A B C D i j = A i.1 j.1 * B i.2.1 j.2.1 * C i.2.2.1 j.2.2.1 * D i.2.2.2 j.2.2.2 :=
  rfl

@[simp] theorem tensor4_one : tensor4 1 1 1 1 = (1 : Mat16) := by
  ext i j
  rcases i with ⟨i0, i1, i2, i3⟩
  rcases j with ⟨j0, j1, j2, j3⟩
  simp only [tensor4, Matrix.one_apply, Prod.mk.injEq]
  by_cases h0 : i0 = j0 <;> by_cases h1 : i1 = j1 <;>
    by_cases h2 : i2 = j2 <;> by_cases h3 : i3 = j3 <;>
    simp [h0, h1, h2, h3]

@[simp] theorem tensor4_mul (A₁ B₁ C₁ D₁ A₂ B₂ C₂ D₂ : Mat2) :
    tensor4 A₁ B₁ C₁ D₁ * tensor4 A₂ B₂ C₂ D₂ =
      tensor4 (A₁ * A₂) (B₁ * B₂) (C₁ * C₂) (D₁ * D₂) := by
  ext i k
  rcases i with ⟨i0, i1, i2, i3⟩
  rcases k with ⟨k0, k1, k2, k3⟩
  dsimp [Matrix.mul_apply, tensor4]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

@[simp] theorem tensor4_transpose (A B C D : Mat2) :
    (tensor4 A B C D)ᵀ = tensor4 Aᵀ Bᵀ Cᵀ Dᵀ := by
  ext i j
  rfl

@[simp] lemma tensor4_zero_left (B C D : Mat2) : tensor4 0 B C D = 0 := by
  ext i j; simp [tensor4]
@[simp] lemma tensor4_zero_2 (A C D : Mat2) : tensor4 A 0 C D = 0 := by
  ext i j; simp [tensor4]
@[simp] lemma tensor4_zero_3 (A B D : Mat2) : tensor4 A B 0 D = 0 := by
  ext i j; simp [tensor4]
@[simp] lemma tensor4_zero_right (A B C : Mat2) : tensor4 A B C 0 = 0 := by
  ext i j; simp [tensor4]

@[simp] lemma tensor4_neg_left (A B C D : Mat2) : tensor4 (-A) B C D = -tensor4 A B C D := by
  ext i j; simp [tensor4]
@[simp] lemma tensor4_neg_2 (A B C D : Mat2) : tensor4 A (-B) C D = -tensor4 A B C D := by
  ext i j; simp [tensor4]
@[simp] lemma tensor4_neg_3 (A B C D : Mat2) : tensor4 A B (-C) D = -tensor4 A B C D := by
  ext i j; simp [tensor4]
@[simp] lemma tensor4_neg_right (A B C D : Mat2) : tensor4 A B C (-D) = -tensor4 A B C D := by
  ext i j; simp [tensor4]

lemma tensor4_add_left (A₁ A₂ B C D : Mat2) :
    tensor4 (A₁ + A₂) B C D = tensor4 A₁ B C D + tensor4 A₂ B C D := by
  ext i j; simp [tensor4]; ring
lemma tensor4_add_2 (A B₁ B₂ C D : Mat2) :
    tensor4 A (B₁ + B₂) C D = tensor4 A B₁ C D + tensor4 A B₂ C D := by
  ext i j; simp [tensor4]; ring
lemma tensor4_add_3 (A B C₁ C₂ D : Mat2) :
    tensor4 A B (C₁ + C₂) D = tensor4 A B C₁ D + tensor4 A B C₂ D := by
  ext i j; simp [tensor4]; ring
lemma tensor4_add_right (A B C D₁ D₂ : Mat2) :
    tensor4 A B C (D₁ + D₂) = tensor4 A B C D₁ + tensor4 A B C D₂ := by
  ext i j; simp [tensor4]; ring

lemma tensor4_sub_left (A₁ A₂ B C D : Mat2) :
    tensor4 (A₁ - A₂) B C D = tensor4 A₁ B C D - tensor4 A₂ B C D := by
  ext i j; simp [tensor4]; ring
lemma tensor4_sub_2 (A B₁ B₂ C D : Mat2) :
    tensor4 A (B₁ - B₂) C D = tensor4 A B₁ C D - tensor4 A B₂ C D := by
  ext i j; simp [tensor4]; ring
lemma tensor4_sub_3 (A B C₁ C₂ D : Mat2) :
    tensor4 A B (C₁ - C₂) D = tensor4 A B C₁ D - tensor4 A B C₂ D := by
  ext i j; simp [tensor4]; ring
lemma tensor4_sub_right (A B C D₁ D₂ : Mat2) :
    tensor4 A B C (D₁ - D₂) = tensor4 A B C D₁ - tensor4 A B C D₂ := by
  ext i j; simp [tensor4]; ring

@[simp] lemma tensor4_smul_left (r : ℝ) (A B C D : Mat2) :
    tensor4 (r • A) B C D = r • tensor4 A B C D := by
  ext i j; simp [tensor4]; ring
@[simp] lemma tensor4_smul_2 (r : ℝ) (A B C D : Mat2) :
    tensor4 A (r • B) C D = r • tensor4 A B C D := by
  ext i j; simp [tensor4]; ring
@[simp] lemma tensor4_smul_3 (r : ℝ) (A B C D : Mat2) :
    tensor4 A B (r • C) D = r • tensor4 A B C D := by
  ext i j; simp [tensor4]; ring
@[simp] lemma tensor4_smul_right (r : ℝ) (A B C D : Mat2) :
    tensor4 A B C (r • D) = r • tensor4 A B C D := by
  ext i j; simp [tensor4]; ring

def ket0 : Fin 2 → ℝ := ![1, 0]
def ket1 : Fin 2 → ℝ := ![0, 1]

@[simp] lemma ket0_0 : ket0 0 = 1 := by norm_num [ket0]
@[simp] lemma ket0_1 : ket0 1 = 0 := by norm_num [ket0]
@[simp] lemma ket1_0 : ket1 0 = 0 := by norm_num [ket1]
@[simp] lemma ket1_1 : ket1 1 = 1 := by norm_num [ket1]

@[simp] lemma cl11Pos_mulVec_ket0 : cl11Pos.mulVec ket0 = ket1 := by
  ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
@[simp] lemma cl11Pos_mulVec_ket1 : cl11Pos.mulVec ket1 = ket0 := by
  ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
@[simp] lemma cl11Neg_mulVec_ket0 : cl11Neg.mulVec ket0 = ket1 := by
  ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
@[simp] lemma cl11Neg_mulVec_ket1 : cl11Neg.mulVec ket1 = -ket0 := by
  ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
@[simp] lemma cl11Grad_mulVec_ket0 : cl11Grad.mulVec ket0 = ket0 := by
  ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
@[simp] lemma cl11Grad_mulVec_ket1 : cl11Grad.mulVec ket1 = -ket1 := by
  ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
@[simp] lemma cl11Up_mulVec_ket0 : cl11Up.mulVec ket0 = ket1 := by
  ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
@[simp] lemma cl11Up_mulVec_ket1 : cl11Up.mulVec ket1 = 0 := by
  ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
@[simp] lemma cl11Down_mulVec_ket0 : cl11Down.mulVec ket0 = 0 := by
  ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
@[simp] lemma cl11Down_mulVec_ket1 : cl11Down.mulVec ket1 = ket0 := by
  ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
@[simp] lemma cl11Proj1_mulVec_ket0 : cl11Proj1.mulVec ket0 = 0 := by
  ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
@[simp] lemma cl11Proj1_mulVec_ket1 : cl11Proj1.mulVec ket1 = ket1 := by
  ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

def vec4 (v0 v1 v2 v3 : Fin 2 → ℝ) : Krein16Idx → ℝ :=
  fun i => v0 i.1 * v1 i.2.1 * v2 i.2.2.1 * v3 i.2.2.2

@[simp] lemma vec4_apply (v0 v1 v2 v3 : Fin 2 → ℝ) (i : Krein16Idx) :
    vec4 v0 v1 v2 v3 i = v0 i.1 * v1 i.2.1 * v2 i.2.2.1 * v3 i.2.2.2 :=
  rfl

@[simp] lemma vec4_zero_1 (v1 v2 v3 : Fin 2 → ℝ) : vec4 0 v1 v2 v3 = 0 := by ext i; simp
@[simp] lemma vec4_zero_2 (v0 v2 v3 : Fin 2 → ℝ) : vec4 v0 0 v2 v3 = 0 := by ext i; simp
@[simp] lemma vec4_zero_3 (v0 v1 v3 : Fin 2 → ℝ) : vec4 v0 v1 0 v3 = 0 := by ext i; simp
@[simp] lemma vec4_zero_4 (v0 v1 v2 : Fin 2 → ℝ) : vec4 v0 v1 v2 0 = 0 := by ext i; simp

@[simp] lemma vec4_neg_1 (v0 v1 v2 v3 : Fin 2 → ℝ) : vec4 (-v0) v1 v2 v3 = -vec4 v0 v1 v2 v3 := by
  ext i; simp
@[simp] lemma vec4_neg_2 (v0 v1 v2 v3 : Fin 2 → ℝ) : vec4 v0 (-v1) v2 v3 = -vec4 v0 v1 v2 v3 := by
  ext i; simp
@[simp] lemma vec4_neg_3 (v0 v1 v2 v3 : Fin 2 → ℝ) : vec4 v0 v1 (-v2) v3 = -vec4 v0 v1 v2 v3 := by
  ext i; simp
@[simp] lemma vec4_neg_4 (v0 v1 v2 v3 : Fin 2 → ℝ) : vec4 v0 v1 v2 (-v3) = -vec4 v0 v1 v2 v3 := by
  ext i; simp

@[simp] theorem tensor4_mulVec (A B C D : Mat2) (v0 v1 v2 v3 : Fin 2 → ℝ) :
    (tensor4 A B C D).mulVec (vec4 v0 v1 v2 v3) =
      vec4 (A.mulVec v0) (B.mulVec v1) (C.mulVec v2) (D.mulVec v3) := by
  ext i
  rcases i with ⟨i0, i1, i2, i3⟩
  dsimp [Matrix.mulVec, dotProduct, tensor4, vec4]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

/-! ## Section I: Derivations, Socratic Leibniz Aporia, & Associative Jacobi Ceiling -/

def endomorphismLeibnizDefect {A : Type*} [Ring A] [Algebra ℝ A]
    (D : Module.End ℝ A) (x y : A) : A :=
  D (x * y) - (D x * y + x * D y)

theorem ax4_associative_jacobi_ceiling {R : Type*} [Ring R] (x y z : R) :
    (fun a b : R => a * b - b * a) x ((fun a b : R => a * b - b * a) y z) -
    (fun a b : R => a * b - b * a) ((fun a b : R => a * b - b * a) x y) z -
    (fun a b : R => a * b - b * a) y ((fun a b : R => a * b - b * a) x z) = 0 := by
  dsimp
  noncomm_ring

theorem associative_jacobi_leibnizDefect_zero :
    ∀ x y z : Mat2,
      let bracket : Mat2 →ₗ[ℝ] Mat2 →ₗ[ℝ] Mat2 :=
        { toFun := fun a =>
            { toFun := fun b => a * b - b * a
              map_add' := fun b₁ b₂ => by noncomm_ring
              map_smul' := fun r b => by
                simp only [RingHom.id_apply, mul_smul_comm, smul_mul_assoc, smul_sub] }
          map_add' := fun a₁ a₂ => by
            ext b i j
            simp [Matrix.add_apply, mul_add, add_mul]
            ring
          map_smul' := fun r a => by
            ext b i j
            simp [Matrix.smul_apply]
            ring }
      leibnizDefect bracket x y z = 0 := by
  intro x y z
  dsimp [leibnizDefect]
  noncomm_ring

def gradInnerDeriv : Module.End ℝ Mat2 where
  toFun Y := cl11Grad * Y - Y * cl11Grad
  map_add' X Y := by noncomm_ring
  map_smul' r X := by simp [smul_sub]

theorem gradInnerDeriv_is_derivation (X Y : Mat2) :
    endomorphismLeibnizDefect gradInnerDeriv X Y = 0 := by
  dsimp [endomorphismLeibnizDefect, gradInnerDeriv]
  noncomm_ring

theorem innerDerivationWitness_sq_not_derivation :
    endomorphismLeibnizDefect (gradInnerDeriv.comp gradInnerDeriv) cl11Up cl11Down ≠ 0 := by
  intro h
  have h11 := congrArg (fun M : Mat2 => M 1 1) h
  have h_val :
      endomorphismLeibnizDefect (gradInnerDeriv.comp gradInnerDeriv) cl11Up cl11Down =
        -((8 : ℝ) • cl11Proj1) := by
    dsimp [endomorphismLeibnizDefect, gradInnerDeriv]
    apply ext_mat2 <;> norm_num [cl11Up, cl11Down, cl11Grad, cl11Proj1,
      Matrix.mul_apply, Fin.sum_univ_two]
  rw [h_val] at h11
  simp at h11

/-! ## Section II: `Cl(4,4)` on `Krein16Idx`, `gamma44`, `kreinMetric88`, & 28 Krein-Skew Bivectors -/

def cl44Gen : Fin 8 → Mat16
  | 0 => tensor4 cl11Pos 1 1 1
  | 1 => tensor4 cl11Grad cl11Pos 1 1
  | 2 => tensor4 cl11Grad cl11Grad cl11Pos 1
  | 3 => tensor4 cl11Grad cl11Grad cl11Grad cl11Pos
  | 4 => tensor4 cl11Neg 1 1 1
  | 5 => tensor4 cl11Grad cl11Neg 1 1
  | 6 => tensor4 cl11Grad cl11Grad cl11Neg 1
  | 7 => tensor4 cl11Grad cl11Grad cl11Grad cl11Neg

theorem cl44Gen_sq_pos (i : Fin 8) (hi : i.1 < 4) :
    cl44Gen i * cl44Gen i = (1 : Mat16) := by
  fin_cases i <;> first | exact absurd hi (by decide) | simp [cl44Gen]

theorem cl44Gen_sq_neg (i : Fin 8) (hi : 4 ≤ i.1) :
    cl44Gen i * cl44Gen i = -(1 : Mat16) := by
  fin_cases i <;> first | exact absurd hi (by decide) | simp [cl44Gen]

theorem cl44Gen_anticomm (a b : Fin 8) (hab : a ≠ b) :
    cl44Gen a * cl44Gen b + cl44Gen b * cl44Gen a = 0 := by
  fin_cases a <;> fin_cases b <;>
    first
    | exact absurd rfl hab
    | simp [cl44Gen]

def gamma44 : Mat16 := tensor4 cl11Grad cl11Grad cl11Grad cl11Grad
def kreinMetric88 : Mat16 := tensor4 cl11Pos cl11Neg cl11Pos cl11Neg

theorem cl44_volume_product :
    cl44Gen 0 * cl44Gen 4 * cl44Gen 1 * cl44Gen 5 *
      cl44Gen 2 * cl44Gen 6 * cl44Gen 3 * cl44Gen 7 = gamma44 := by
  simp [cl44Gen, gamma44]

theorem gamma44_sq : gamma44 * gamma44 = (1 : Mat16) := by
  simp [gamma44]

theorem gamma44_trace_zero : Matrix.trace gamma44 = 0 := by
  dsimp [Matrix.trace, Matrix.diag, gamma44, tensor4]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, cl11Grad_00, cl11Grad_11]
  ring

theorem gamma44_anticomm_gen (a : Fin 8) :
    gamma44 * cl44Gen a + cl44Gen a * gamma44 = 0 := by
  fin_cases a <;> simp [gamma44, cl44Gen]

theorem kreinMetric88_product :
    cl44Gen 4 * cl44Gen 5 * cl44Gen 6 * cl44Gen 7 = kreinMetric88 := by
  simp [cl44Gen, kreinMetric88]

@[simp] theorem kreinMetric88_transpose : kreinMetric88ᵀ = kreinMetric88 := by
  dsimp [kreinMetric88]
  rw [tensor4_transpose, cl11Pos_transpose, cl11Neg_transpose]
  simp [tensor4_neg_2, tensor4_neg_right]

@[simp] theorem kreinMetric88_sq : kreinMetric88 * kreinMetric88 = (1 : Mat16) := by
  simp [kreinMetric88]

theorem kreinMetric88_comm_gamma44 :
    kreinMetric88 * gamma44 = gamma44 * kreinMetric88 := by
  simp [kreinMetric88, gamma44]

def kreinInner16 (u v : Krein16Idx → ℝ) : ℝ :=
  dotProduct u (kreinMetric88.mulVec v)

theorem kreinInner16_nondegenerate (u : Krein16Idx → ℝ) :
    (∀ v : Krein16Idx → ℝ, kreinInner16 u v = 0) ↔ u = 0 := by
  constructor
  · intro h
    have hmul : u ᵥ* kreinMetric88 = 0 := by
      ext i
      have hi := h (Pi.single i (1 : ℝ))
      dsimp [kreinInner16] at hi
      rw [Matrix.dotProduct_mulVec, dotProduct_single, mul_one] at hi
      exact hi
    have h1 := congrArg (fun w => w ᵥ* kreinMetric88) hmul
    rw [Matrix.vecMul_vecMul, kreinMetric88_sq, Matrix.vecMul_one, Matrix.zero_vecMul] at h1
    exact h1
  · rintro rfl v
    simp [kreinInner16]

theorem cl44Gen_transpose (a : Fin 8) :
    (cl44Gen a)ᵀ = if a.1 < 4 then cl44Gen a else -cl44Gen a := by
  fin_cases a <;> simp [cl44Gen, Matrix.transpose_one]

theorem cl44Gen_krein_conj (a : Fin 8) :
    (cl44Gen a)ᵀ * kreinMetric88 = kreinMetric88 * cl44Gen a := by
  fin_cases a <;> simp [cl44Gen, kreinMetric88, Matrix.transpose_one]

def cl44Bivector (a b : Fin 8) : Mat16 := cl44Gen a * cl44Gen b

theorem cl44Bivector_swap (a b : Fin 8) (hab : a ≠ b) :
    cl44Bivector b a = -cl44Bivector a b := by
  have h := cl44Gen_anticomm a b hab
  dsimp [cl44Bivector]
  exact eq_neg_of_add_eq_zero_right h

theorem cl44Bivector_chiral_even (a b : Fin 8) :
    cl44Bivector a b * gamma44 = gamma44 * cl44Bivector a b := by
  dsimp [cl44Bivector]
  have ha := eq_neg_of_add_eq_zero_right (gamma44_anticomm_gen a)
  have hb := eq_neg_of_add_eq_zero_right (gamma44_anticomm_gen b)
  calc
    (cl44Gen a * cl44Gen b) * gamma44
        = cl44Gen a * (cl44Gen b * gamma44) := mul_assoc _ _ _
    _ = cl44Gen a * -(gamma44 * cl44Gen b) := by rw [hb]
    _ = -(cl44Gen a * gamma44) * cl44Gen b := by noncomm_ring
    _ = -(-(gamma44 * cl44Gen a)) * cl44Gen b := by rw [ha]
    _ = gamma44 * (cl44Gen a * cl44Gen b) := by noncomm_ring

theorem cl44Bivector_krein_skew (a b : Fin 8) (hab : a ≠ b) :
    (cl44Bivector a b)ᵀ * kreinMetric88 + kreinMetric88 * cl44Bivector a b = 0 := by
  dsimp [cl44Bivector]
  rw [Matrix.transpose_mul, mul_assoc, cl44Gen_krein_conj a, ← mul_assoc,
    cl44Gen_krein_conj b, mul_assoc kreinMetric88 (cl44Gen b) (cl44Gen a),
    ← mul_add, cl44Gen_anticomm b a hab.symm, mul_zero]

def cl44BivectorSubmodule : Submodule ℝ Mat16 :=
  Submodule.span ℝ { M : Mat16 | ∃ a b : Fin 8, a < b ∧ M = cl44Bivector a b }

lemma mem_cl44BivectorSubmodule_of_ne (a b : Fin 8) (hab : a ≠ b) :
    cl44Bivector a b ∈ cl44BivectorSubmodule := by
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · exact Submodule.subset_span ⟨a, b, hlt, rfl⟩
  · rw [cl44Bivector_swap b a hab.symm]
    exact neg_mem (Submodule.subset_span ⟨b, a, hgt, rfl⟩)

lemma mem_cl44BivectorSubmodule_scale (c : ℝ) (a b : Fin 8) (hab : a ≠ b) :
    c • cl44Bivector a b ∈ cl44BivectorSubmodule :=
  Submodule.smul_mem _ c (mem_cl44BivectorSubmodule_of_ne a b hab)

theorem cl44BivectorSubmodule_chiral_even {G : Mat16} (hG : G ∈ cl44BivectorSubmodule) :
    G * gamma44 = gamma44 * G := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hG
  · rintro _ ⟨a, b, _, rfl⟩
    exact cl44Bivector_chiral_even a b
  · simp
  · intro x y _ _ hx hy
    rw [add_mul, mul_add, hx, hy]
  · intro c x _ hx
    rw [smul_mul_assoc, mul_smul_comm, hx]

theorem cl44BivectorSubmodule_krein_skew {G : Mat16} (hG : G ∈ cl44BivectorSubmodule) :
    Gᵀ * kreinMetric88 + kreinMetric88 * G = 0 := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hG
  · rintro _ ⟨a, b, hab, rfl⟩
    exact cl44Bivector_krein_skew a b (ne_of_lt hab)
  · simp
  · intro x y _ _ hx hy
    rw [Matrix.transpose_add, add_mul, mul_add]
    calc
      (xᵀ * kreinMetric88 + yᵀ * kreinMetric88) + (kreinMetric88 * x + kreinMetric88 * y)
          = (xᵀ * kreinMetric88 + kreinMetric88 * x) +
              (yᵀ * kreinMetric88 + kreinMetric88 * y) := by abel
      _ = 0 := by rw [hx, hy, add_zero]
  · intro c x _ hx
    rw [Matrix.transpose_smul, smul_mul_assoc, mul_smul_comm, ← smul_add, hx, smul_zero]

private lemma cl44Gen_sq_scalar (x : Fin 8) :
    cl44Gen x * cl44Gen x = (if x.1 < 4 then (1 : ℝ) else -1) • (1 : Mat16) := by
  split_ifs with h
  · rw [one_smul]; exact cl44Gen_sq_pos x h
  · rw [neg_one_smul]; exact cl44Gen_sq_neg x (Nat.le_of_not_lt h)

private lemma cl44Gen_swap {x y : Fin 8} (hxy : x ≠ y) :
    cl44Gen x * cl44Gen y = -(cl44Gen y * cl44Gen x) :=
  eq_neg_of_add_eq_zero_right (cl44Gen_anticomm y x hxy.symm)

private lemma cl44Bivector_comm_disjoint {a b c d : Fin 8}
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    cl44Bivector a b * cl44Bivector c d - cl44Bivector c d * cl44Bivector a b = 0 := by
  have h1 := cl44Gen_swap hac
  have h2 := cl44Gen_swap had.symm
  have h3 := cl44Gen_swap hbc
  have h4 := cl44Gen_swap hbd
  dsimp [cl44Bivector]
  calc
    (cl44Gen a * cl44Gen b) * (cl44Gen c * cl44Gen d) -
        (cl44Gen c * cl44Gen d) * (cl44Gen a * cl44Gen b)
        = cl44Gen a * ((cl44Gen b * cl44Gen c) * cl44Gen d) -
            (cl44Gen c * (cl44Gen d * cl44Gen a)) * cl44Gen b := by noncomm_ring
    _ = cl44Gen a * ((-(cl44Gen c * cl44Gen b)) * cl44Gen d) -
            (cl44Gen c * (-(cl44Gen a * cl44Gen d))) * cl44Gen b := by rw [h3, h2]
    _ = -((cl44Gen a * cl44Gen c) * (cl44Gen b * cl44Gen d)) +
            (cl44Gen c * cl44Gen a) * (cl44Gen d * cl44Gen b) := by noncomm_ring
    _ = -((-(cl44Gen c * cl44Gen a)) * (-(cl44Gen d * cl44Gen b))) +
            (cl44Gen c * cl44Gen a) * (cl44Gen d * cl44Gen b) := by rw [h1, h4]
    _ = 0 := by noncomm_ring

private lemma cl44Bivector_comm_bridge {a b d : Fin 8}
    (hab : a ≠ b) (hbd : b ≠ d) (had : a ≠ d) :
    cl44Bivector a b * cl44Bivector b d - cl44Bivector b d * cl44Bivector a b =
      (2 * (if b.1 < 4 then (1 : ℝ) else -1)) • cl44Bivector a d := by
  have hda := cl44Gen_swap had.symm
  have hdb := cl44Gen_swap hbd.symm
  have hba := cl44Gen_swap hab.symm
  have hb := cl44Gen_sq_scalar b
  dsimp [cl44Bivector]
  have hL : (cl44Gen a * cl44Gen b) * (cl44Gen b * cl44Gen d) =
      (if b.1 < 4 then (1 : ℝ) else -1) • (cl44Gen a * cl44Gen d) := by
    calc
      (cl44Gen a * cl44Gen b) * (cl44Gen b * cl44Gen d)
          = cl44Gen a * ((cl44Gen b * cl44Gen b) * cl44Gen d) := by noncomm_ring
      _ = cl44Gen a * (((if b.1 < 4 then (1 : ℝ) else -1) • (1 : Mat16)) * cl44Gen d) := by rw [hb]
      _ = (if b.1 < 4 then (1 : ℝ) else -1) • (cl44Gen a * cl44Gen d) := by simp
  have hR : (cl44Gen b * cl44Gen d) * (cl44Gen a * cl44Gen b) =
      -((if b.1 < 4 then (1 : ℝ) else -1) • (cl44Gen a * cl44Gen d)) := by
    calc
      (cl44Gen b * cl44Gen d) * (cl44Gen a * cl44Gen b)
          = cl44Gen b * (cl44Gen d * cl44Gen a) * cl44Gen b := by noncomm_ring
      _ = cl44Gen b * (-(cl44Gen a * cl44Gen d)) * cl44Gen b := by rw [hda]
      _ = -(cl44Gen b * cl44Gen a * (cl44Gen d * cl44Gen b)) := by noncomm_ring
      _ = -(cl44Gen b * cl44Gen a * (-(cl44Gen b * cl44Gen d))) := by rw [hdb]
      _ = ((cl44Gen b * cl44Gen a) * cl44Gen b) * cl44Gen d := by noncomm_ring
      _ = ((-(cl44Gen a * cl44Gen b)) * cl44Gen b) * cl44Gen d := by rw [hba]
      _ = -(cl44Gen a * ((cl44Gen b * cl44Gen b) * cl44Gen d)) := by noncomm_ring
      _ = -((if b.1 < 4 then (1 : ℝ) else -1) • (cl44Gen a * cl44Gen d)) := by
            rw [hb]; simp
  rw [hL, hR, sub_neg_eq_add, ← two_smul ℝ, smul_smul, mul_comm (2 : ℝ)]

private lemma cl44Bivector_comm_mem_basis {a b c d : Fin 8} (hab : a < b) (hcd : c < d) :
    cl44Bivector a b * cl44Bivector c d - cl44Bivector c d * cl44Bivector a b ∈
      cl44BivectorSubmodule := by
  by_cases hac : a = c
  · subst hac
    by_cases hbd : b = d
    · subst hbd; rw [sub_self]; exact zero_mem _
    · have hbr := cl44Bivector_comm_bridge (ne_of_gt hab) (ne_of_lt hcd) hbd
      have h_eq : cl44Bivector a b * cl44Bivector a d - cl44Bivector a d * cl44Bivector a b =
          -((2 * (if a.1 < 4 then (1 : ℝ) else -1)) • cl44Bivector b d) := by
        calc
          cl44Bivector a b * cl44Bivector a d - cl44Bivector a d * cl44Bivector a b
              = (-cl44Bivector b a) * cl44Bivector a d - cl44Bivector a d * (-cl44Bivector b a) := by
                  rw [cl44Bivector_swap b a (ne_of_gt hab)]
          _ = -(cl44Bivector b a * cl44Bivector a d - cl44Bivector a d * cl44Bivector b a) := by noncomm_ring
          _ = -((2 * (if a.1 < 4 then (1 : ℝ) else -1)) • cl44Bivector b d) := by rw [hbr]
      rw [h_eq]
      exact neg_mem (mem_cl44BivectorSubmodule_scale _ b d hbd)
  · by_cases had : a = d
    · subst had
      have hbc : b ≠ c := ne_of_gt (lt_trans hcd hab)
      have h_eq : cl44Bivector a b * cl44Bivector c a - cl44Bivector c a * cl44Bivector a b =
          (2 * (if a.1 < 4 then (1 : ℝ) else -1)) • cl44Bivector b c := by
        calc
          cl44Bivector a b * cl44Bivector c a - cl44Bivector c a * cl44Bivector a b
              = (-cl44Bivector b a) * (-cl44Bivector a c) - (-cl44Bivector a c) * (-cl44Bivector b a) := by
                  rw [cl44Bivector_swap b a (ne_of_gt hab), cl44Bivector_swap a c (ne_of_gt hcd)]
          _ = cl44Bivector b a * cl44Bivector a c - cl44Bivector a c * cl44Bivector b a := by noncomm_ring
          _ = (2 * (if a.1 < 4 then (1 : ℝ) else -1)) • cl44Bivector b c :=
                cl44Bivector_comm_bridge (ne_of_gt hab) (ne_of_gt hcd) hbc
      rw [h_eq]
      exact mem_cl44BivectorSubmodule_scale _ b c hbc
    · by_cases hbc : b = c
      · subst hbc
        have had' : a ≠ d := ne_of_lt (lt_trans hab hcd)
        rw [cl44Bivector_comm_bridge (ne_of_lt hab) (ne_of_lt hcd) had']
        exact mem_cl44BivectorSubmodule_scale _ a d had'
      · by_cases hbd : b = d
        · subst hbd
          have h_eq : cl44Bivector a b * cl44Bivector c b - cl44Bivector c b * cl44Bivector a b =
              -((2 * (if b.1 < 4 then (1 : ℝ) else -1)) • cl44Bivector a c) := by
            calc
              cl44Bivector a b * cl44Bivector c b - cl44Bivector c b * cl44Bivector a b
                  = cl44Bivector a b * (-cl44Bivector b c) - (-cl44Bivector b c) * cl44Bivector a b := by
                      rw [cl44Bivector_swap b c (ne_of_gt hcd)]
              _ = -(cl44Bivector a b * cl44Bivector b c - cl44Bivector b c * cl44Bivector a b) := by noncomm_ring
              _ = -((2 * (if b.1 < 4 then (1 : ℝ) else -1)) • cl44Bivector a c) := by
                    rw [cl44Bivector_comm_bridge (ne_of_lt hab) (ne_of_gt hcd) hac]
          rw [h_eq]
          exact neg_mem (mem_cl44BivectorSubmodule_scale _ a c hac)
        · rw [cl44Bivector_comm_disjoint hac had hbc hbd]
          exact zero_mem _

theorem cl44BivectorSubmodule_comm_mem {A B : Mat16}
    (hA : A ∈ cl44BivectorSubmodule) (hB : B ∈ cl44BivectorSubmodule) :
    A * B - B * A ∈ cl44BivectorSubmodule := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hA
  · rintro _ ⟨a, b, hab, rfl⟩
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hB
    · rintro _ ⟨c, d, hcd, rfl⟩
      exact cl44Bivector_comm_mem_basis hab hcd
    · simp
    · intro x y _ _ hx hy
      have h_eq : cl44Bivector a b * (x + y) - (x + y) * cl44Bivector a b =
          (cl44Bivector a b * x - x * cl44Bivector a b) +
          (cl44Bivector a b * y - y * cl44Bivector a b) := by noncomm_ring
      rw [h_eq]; exact add_mem hx hy
    · intro r x _ hx
      have h_eq : cl44Bivector a b * (r • x) - (r • x) * cl44Bivector a b =
          r • (cl44Bivector a b * x - x * cl44Bivector a b) := by
        simp [smul_sub]
      rw [h_eq]; exact Submodule.smul_mem _ r hx
  · simp
  · intro x y _ _ hx hy
    have h_eq : (x + y) * B - B * (x + y) =
        (x * B - B * x) + (y * B - B * y) := by noncomm_ring
    rw [h_eq]; exact add_mem hx hy
  · intro r x _ hx
    have h_eq : (r • x) * B - B * (r • x) =
        r • (x * B - B * x) := by
      simp [smul_sub]
    rw [h_eq]; exact Submodule.smul_mem _ r hx

/-! ## Section III: Cartan $S_3$ Triality, Extremal Spinor $\psi_+$, & 14D 5-Graded Split $\mathfrak{g}_{2(2)}$ -/

abbrev Mat4 : Type := Matrix (Fin 4) (Fin 4) ℝ

lemma ext_mat4 {A B : Mat4}
    (h : ∀ i j : Fin 4, A i j = B i j) : A = B := by
  ext i j; exact h i j

def trialityHadamardFn : Fin 4 → Fin 4 → ℝ
  | 0, _ => (1 / 2 : ℝ)
  | 1, 0 => (1 / 2 : ℝ)
  | 1, 1 => (1 / 2 : ℝ)
  | 1, 2 => -(1 / 2 : ℝ)
  | 1, 3 => -(1 / 2 : ℝ)
  | 2, 0 => (1 / 2 : ℝ)
  | 2, 1 => -(1 / 2 : ℝ)
  | 2, 2 => (1 / 2 : ℝ)
  | 2, 3 => -(1 / 2 : ℝ)
  | 3, 0 => (1 / 2 : ℝ)
  | 3, 1 => -(1 / 2 : ℝ)
  | 3, 2 => -(1 / 2 : ℝ)
  | 3, 3 => (1 / 2 : ℝ)

def trialityHadamard : Mat4 := Matrix.of trialityHadamardFn

def trialitySpinSwapFn : Fin 4 → Fin 4 → ℝ
  | 0, 0 => -1
  | 1, 1 => 1
  | 2, 2 => 1
  | 3, 3 => 1
  | _, _ => 0

def trialitySpinSwap : Mat4 := Matrix.of trialitySpinSwapFn

def trialityCycle : Mat4 :=
  trialityHadamard * trialitySpinSwap

lemma trialityHadamard_apply (i j : Fin 4) :
    trialityHadamard i j = trialityHadamardFn i j := rfl

lemma trialitySpinSwap_apply (i j : Fin 4) :
    trialitySpinSwap i j = trialitySpinSwapFn i j := rfl

theorem trialityHadamard_sq : trialityHadamard * trialityHadamard = (1 : Mat4) := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;>
    simp [trialityHadamard_apply, trialityHadamardFn] <;> norm_num

theorem trialitySpinSwap_sq : trialitySpinSwap * trialitySpinSwap = (1 : Mat4) := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;>
    simp [trialitySpinSwap_apply, trialitySpinSwapFn]

lemma trialityCycle_apply (i j : Fin 4) :
    trialityCycle i j = if j = 0 then -trialityHadamardFn i 0 else trialityHadamardFn i j := by
  rw [trialityCycle, Matrix.mul_apply, Fin.sum_univ_four]
  fin_cases j <;> simp [trialityHadamard_apply, trialitySpinSwap_apply, trialitySpinSwapFn]

lemma trialityCycle_sq_apply (i j : Fin 4) :
    (trialityCycle * trialityCycle) i j = trialityCycle j i := by
  rw [Matrix.mul_apply, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;>
    simp [trialityCycle_apply, trialityHadamardFn] <;> norm_num

theorem trialityCycle_cube :
    trialityCycle * trialityCycle * trialityCycle = (1 : Mat4) := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_four]
  simp only [trialityCycle_sq_apply]
  fin_cases i <;> fin_cases j <;>
    simp [trialityCycle_apply, trialityHadamardFn] <;> norm_num

theorem triality_s3_relation :
    trialitySpinSwap * trialityCycle * trialitySpinSwap =
      trialityCycle * trialityCycle := by
  have hL : trialitySpinSwap * trialityCycle * trialitySpinSwap =
      trialitySpinSwap * trialityHadamard := by
    rw [trialityCycle]
    simp only [mul_assoc, trialitySpinSwap_sq, mul_one]
  rw [hL]
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_four, trialityCycle_sq_apply]
  fin_cases i <;> fin_cases j <;>
    simp [trialitySpinSwap_apply, trialitySpinSwapFn, trialityHadamard_apply,
      trialityHadamardFn, trialityCycle_apply]

theorem trialityHadamard_trialitySpinSwap_noncomm :
    trialityHadamard * trialitySpinSwap ≠ trialitySpinSwap * trialityHadamard := by
  intro h
  have h01 := congrArg (fun M : Mat4 => M 0 1) h
  rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_four] at h01
  norm_num [trialityHadamard_apply, trialityHadamardFn,
    trialitySpinSwap_apply, trialitySpinSwapFn] at h01

def trialityFixedCartan : Submodule ℝ (Fin 4 → ℝ) where
  carrier := { w : Fin 4 → ℝ | trialityHadamard.mulVec w = w ∧ trialitySpinSwap.mulVec w = w }
  add_mem' {u v} hu hv := ⟨by rw [Matrix.mulVec_add, hu.1, hv.1],
    by rw [Matrix.mulVec_add, hu.2, hv.2]⟩
  zero_mem' := ⟨by simp, by simp⟩
  smul_mem' r {u} hu := ⟨by rw [Matrix.mulVec_smul, hu.1],
    by rw [Matrix.mulVec_smul, hu.2]⟩

lemma mem_trialityFixedCartan_iff (w : Fin 4 → ℝ) :
    w ∈ trialityFixedCartan ↔ w 0 = 0 ∧ w 1 + w 2 + w 3 = 0 := by
  change (trialityHadamard.mulVec w = w ∧ trialitySpinSwap.mulVec w = w) ↔ _
  constructor
  · rintro ⟨hH, hS⟩
    have hS0 := congrFun hS 0
    simp [trialitySpinSwap, trialitySpinSwapFn, Matrix.mulVec, dotProduct, Fin.sum_univ_four] at hS0
    have hw0 : w 0 = 0 := by linarith
    have hH0 := congrFun hH 0
    simp [trialityHadamard, trialityHadamardFn, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four, hw0] at hH0
    exact ⟨hw0, by linarith⟩
  · rintro ⟨hw0, hsum⟩
    refine ⟨?_, ?_⟩
    · ext i
      fin_cases i <;>
        simp [trialityHadamard, trialityHadamardFn, Matrix.mulVec, dotProduct,
          Fin.sum_univ_four, hw0] <;>
        linarith
    · ext i
      fin_cases i <;>
        simp [trialitySpinSwap, trialitySpinSwapFn, Matrix.mulVec, dotProduct,
          Fin.sum_univ_four, hw0]

def vecHTheta : Fin 4 → ℝ
  | 0 => 0
  | 1 => 1
  | 2 => 0
  | 3 => -1

def vecHAlpha : Fin 4 → ℝ
  | 0 => 0
  | 1 => 1
  | 2 => -2
  | 3 => 1

lemma vecHTheta_mem_trialityFixedCartan : vecHTheta ∈ trialityFixedCartan :=
  (mem_trialityFixedCartan_iff vecHTheta).mpr ⟨rfl, by norm_num [vecHTheta]⟩

lemma vecHAlpha_mem_trialityFixedCartan : vecHAlpha ∈ trialityFixedCartan :=
  (mem_trialityFixedCartan_iff vecHAlpha).mpr ⟨rfl, by norm_num [vecHAlpha]⟩

theorem trialityFixedCartan_finrank : Module.finrank ℝ trialityFixedCartan = 2 := by
  let b : Fin 2 → trialityFixedCartan :=
    ![⟨vecHTheta, vecHTheta_mem_trialityFixedCartan⟩,
      ⟨vecHAlpha, vecHAlpha_mem_trialityFixedCartan⟩]
  have h_indep : LinearIndependent ℝ b := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have h1 := congrArg (fun x : trialityFixedCartan => x.1 1) hc
    have h2 := congrArg (fun x : trialityFixedCartan => x.1 2) hc
    simp only [Fin.sum_univ_two, ZeroMemClass.coe_zero, Pi.zero_apply,
      b, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue] at h1 h2
    have h1' : c 0 * 1 + c 1 * 1 = 0 := h1
    have h2' : c 0 * 0 + c 1 * (-2) = 0 := h2
    have hc1 : c 1 = 0 := by linarith
    have hc0 : c 0 = 0 := by linarith
    intro i; fin_cases i <;> assumption
  have h_span : Submodule.span ℝ (Set.range b) = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨w, hw⟩ _
    obtain ⟨hw0, hsum⟩ := (mem_trialityFixedCartan_iff w).mp hw
    have h_eq : (⟨w, hw⟩ : trialityFixedCartan) =
        ((w 1 - w 3) / 2) • b 0 + (-w 2 / 2) • b 1 := by
      apply Subtype.ext
      ext i
      fin_cases i <;>
        simp [b, vecHTheta, vecHAlpha, hw0] <;>
        linarith
    rw [h_eq]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  have hfr := finrank_span_eq_card h_indep
  rw [h_span, finrank_top] at hfr
  simpa using hfr

/-! ### Extremal Spinor `psiPlus ∈ S_+` and Pure-Integer Generators `uVec`, `dVec` -/

def ket0000 : Krein16Idx → ℝ := vec4 ket0 ket0 ket0 ket0
def ket1111 : Krein16Idx → ℝ := vec4 ket1 ket1 ket1 ket1
def psiPlus : Krein16Idx → ℝ := ket0000 + ket1111
def psiMinus : Krein16Idx → ℝ := ket0000 - ket1111

theorem psiPlus_chiral_even : gamma44.mulVec psiPlus = psiPlus := by
  simp only [psiPlus, ket0000, ket1111, gamma44, Matrix.mulVec_add, tensor4_mulVec,
    cl11Grad_mulVec_ket0, cl11Grad_mulVec_ket1, vec4_neg_1, vec4_neg_2, vec4_neg_3,
    vec4_neg_4, neg_neg]

theorem psiPlus_krein_norm : kreinInner16 psiPlus psiPlus = 2 := by
  dsimp [kreinInner16, psiPlus, ket0000, ket1111, kreinMetric88]
  rw [Matrix.mulVec_add, tensor4_mulVec, tensor4_mulVec]
  simp only [cl11Pos_mulVec_ket0, cl11Neg_mulVec_ket0, cl11Pos_mulVec_ket1, cl11Neg_mulVec_ket1,
    vec4_neg_2, vec4_neg_4, neg_neg]
  dsimp [dotProduct]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, ket0_0, ket0_1, ket1_0, ket1_1]
  ring

theorem psiMinus_krein_norm : kreinInner16 psiMinus psiMinus = -2 := by
  dsimp [kreinInner16, psiMinus, ket0000, ket1111, kreinMetric88]
  rw [Matrix.mulVec_sub, tensor4_mulVec, tensor4_mulVec]
  simp only [cl11Pos_mulVec_ket0, cl11Neg_mulVec_ket0, cl11Pos_mulVec_ket1, cl11Neg_mulVec_ket1,
    vec4_neg_2, vec4_neg_4, neg_neg]
  dsimp [dotProduct]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, ket0_0, ket0_1, ket1_0, ket1_1]
  ring

def eTilde0 : Mat16 := cl44Gen 4
def uVec1 : Mat16 := tensor4 cl11Grad cl11Up 1 1
def uVec2 : Mat16 := tensor4 cl11Grad cl11Grad cl11Up 1
def uVec3 : Mat16 := tensor4 cl11Grad cl11Grad cl11Grad cl11Up
def dVec1 : Mat16 := tensor4 cl11Grad cl11Down 1 1
def dVec2 : Mat16 := tensor4 cl11Grad cl11Grad cl11Down 1
def dVec3 : Mat16 := tensor4 cl11Grad cl11Grad cl11Grad cl11Down

lemma uVec1_eq : uVec1 = (1 / 2 : ℝ) • (cl44Gen 1 + cl44Gen 5) := by
  ext i j
  dsimp [uVec1, cl44Gen, tensor4]
  have h : ∀ a b, cl11Up a b = (1 / 2 : ℝ) * (cl11Pos a b + cl11Neg a b) := by
    intro a b; fin_cases a <;> fin_cases b <;> norm_num [cl11Up, cl11Pos, cl11Neg]
  rw [h]; ring

lemma uVec2_eq : uVec2 = (1 / 2 : ℝ) • (cl44Gen 2 + cl44Gen 6) := by
  ext i j
  dsimp [uVec2, cl44Gen, tensor4]
  have h : ∀ a b, cl11Up a b = (1 / 2 : ℝ) * (cl11Pos a b + cl11Neg a b) := by
    intro a b; fin_cases a <;> fin_cases b <;> norm_num [cl11Up, cl11Pos, cl11Neg]
  rw [h]; ring

lemma uVec3_eq : uVec3 = (1 / 2 : ℝ) • (cl44Gen 3 + cl44Gen 7) := by
  ext i j
  dsimp [uVec3, cl44Gen, tensor4]
  have h : ∀ a b, cl11Up a b = (1 / 2 : ℝ) * (cl11Pos a b + cl11Neg a b) := by
    intro a b; fin_cases a <;> fin_cases b <;> norm_num [cl11Up, cl11Pos, cl11Neg]
  rw [h]; ring

lemma dVec1_eq : dVec1 = (1 / 2 : ℝ) • (cl44Gen 1 - cl44Gen 5) := by
  ext i j
  dsimp [dVec1, cl44Gen, tensor4]
  have h : ∀ a b, cl11Down a b = (1 / 2 : ℝ) * (cl11Pos a b - cl11Neg a b) := by
    intro a b; fin_cases a <;> fin_cases b <;> norm_num [cl11Down, cl11Pos, cl11Neg]
  rw [h]; ring

lemma dVec2_eq : dVec2 = (1 / 2 : ℝ) • (cl44Gen 2 - cl44Gen 6) := by
  ext i j
  dsimp [dVec2, cl44Gen, tensor4]
  have h : ∀ a b, cl11Down a b = (1 / 2 : ℝ) * (cl11Pos a b - cl11Neg a b) := by
    intro a b; fin_cases a <;> fin_cases b <;> norm_num [cl11Down, cl11Pos, cl11Neg]
  rw [h]; ring

lemma dVec3_eq : dVec3 = (1 / 2 : ℝ) • (cl44Gen 3 - cl44Gen 7) := by
  ext i j
  dsimp [dVec3, cl44Gen, tensor4]
  have h : ∀ a b, cl11Down a b = (1 / 2 : ℝ) * (cl11Pos a b - cl11Neg a b) := by
    intro a b; fin_cases a <;> fin_cases b <;> norm_num [cl11Down, cl11Pos, cl11Neg]
  rw [h]; ring

/-! ### Explicit 14-Element Integer-Entry Basis of Split $\mathfrak{g}_{2(2)} \subset \mathrm{Cl}^{(2)}(4,4)$ -/

def HThetaMat : Mat16 := tensor4 1 cl11Proj1 1 1 - tensor4 1 1 1 cl11Proj1
def HAlphaMat : Mat16 :=
  tensor4 1 cl11Proj1 1 1 + tensor4 1 1 1 cl11Proj1 - (2 : ℝ) • tensor4 1 1 cl11Proj1 1

def ZPlus2Mat : Mat16 := uVec1 * dVec3
def X1Mat : Mat16 := uVec1 * dVec2
def X2Mat : Mat16 := uVec2 * dVec3
def X3Mat : Mat16 := uVec1 * uVec2 - eTilde0 * dVec3
def X4Mat : Mat16 := -(dVec2 * dVec3 + eTilde0 * uVec1)
def E0Mat : Mat16 := uVec3 * uVec1 - eTilde0 * dVec2
def F0Mat : Mat16 := -(dVec3 * dVec1 + eTilde0 * uVec2)
def Y1Mat : Mat16 := uVec2 * dVec1
def Y2Mat : Mat16 := uVec3 * dVec2
def Y3Mat : Mat16 := dVec1 * dVec2 + eTilde0 * uVec3
def Y4Mat : Mat16 := -(uVec2 * uVec3 - eTilde0 * dVec1)
def ZMinus2Mat : Mat16 := uVec3 * dVec1

def g2Basis : Fin 14 → Mat16
  | 0 => ZPlus2Mat
  | 1 => X1Mat
  | 2 => X2Mat
  | 3 => X3Mat
  | 4 => X4Mat
  | 5 => HThetaMat
  | 6 => HAlphaMat
  | 7 => E0Mat
  | 8 => F0Mat
  | 9 => Y1Mat
  | 10 => Y2Mat
  | 11 => Y3Mat
  | 12 => Y4Mat
  | 13 => ZMinus2Mat

def g2Submodule : Submodule ℝ Mat16 :=
  Submodule.span ℝ (Set.range g2Basis)

def so34Submodule : Submodule ℝ Mat16 :=
  Submodule.span ℝ { M : Mat16 | ∃ a b : Fin 8, 1 ≤ a.1 ∧ a < b ∧ M = cl44Bivector a b }

private lemma so34Submodule_le_bivector : so34Submodule ≤ cl44BivectorSubmodule := by
  refine Submodule.span_le.mpr ?_
  rintro M ⟨a, b, _, hab, rfl⟩
  exact Submodule.subset_span ⟨a, b, hab, rfl⟩

private lemma bivector_mem_so34 {a b : Fin 8} (ha : 1 ≤ a.1) (hb : 1 ≤ b.1) (hab : a ≠ b) :
    cl44Bivector a b ∈ so34Submodule := by
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · exact Submodule.subset_span ⟨a, b, ha, hlt, rfl⟩
  · rw [cl44Bivector_swap b a hab.symm]
    exact neg_mem (Submodule.subset_span ⟨b, a, hb, hgt, rfl⟩)

private lemma comb_mem_so34 {a₁ a₂ b₁ b₂ : Fin 8}
    (ha₁ : 1 ≤ a₁.1) (ha₂ : 1 ≤ a₂.1) (hb₁ : 1 ≤ b₁.1) (hb₂ : 1 ≤ b₂.1)
    (h11 : a₁ ≠ b₁) (h12 : a₁ ≠ b₂) (h21 : a₂ ≠ b₁) (h22 : a₂ ≠ b₂)
    (s₁ s₂ : ℝ) :
    ((1 / 2 : ℝ) • (cl44Gen a₁ + s₁ • cl44Gen a₂)) *
      ((1 / 2 : ℝ) • (cl44Gen b₁ + s₂ • cl44Gen b₂)) ∈ so34Submodule := by
  have hexp :
      ((1 / 2 : ℝ) • (cl44Gen a₁ + s₁ • cl44Gen a₂)) *
        ((1 / 2 : ℝ) • (cl44Gen b₁ + s₂ • cl44Gen b₂)) =
        (1 / 4 : ℝ) • (cl44Bivector a₁ b₁ + s₂ • cl44Bivector a₁ b₂ +
          s₁ • cl44Bivector a₂ b₁ + (s₁ * s₂) • cl44Bivector a₂ b₂) := by
    dsimp [cl44Bivector]
    simp only [smul_mul_assoc, mul_smul_comm, mul_add, add_mul, smul_add, smul_smul]
    rw [show (1 / 2 : ℝ) * (1 / 2) = 1 / 4 by norm_num,
      show (1 / 2 : ℝ) * (1 / 2 * s₁) = (1 / 4 : ℝ) * s₁ by rw [← mul_assoc]; norm_num,
      show (1 / 2 : ℝ) * s₂ * (1 / 2) = (1 / 4 : ℝ) * s₂ by rw [mul_right_comm]; norm_num,
      show (1 / 2 : ℝ) * s₂ * (1 / 2 * s₁) = (1 / 4 : ℝ) * (s₁ * s₂) by
        rw [mul_mul_mul_comm (1 / 2 : ℝ) s₂ (1 / 2 : ℝ) s₁,
          show (1 / 2 : ℝ) * (1 / 2) = 1 / 4 by norm_num, mul_comm s₂ s₁]]
    abel_nf
  rw [hexp]
  refine Submodule.smul_mem _ _ ?_
  exact add_mem (add_mem (add_mem
    (bivector_mem_so34 ha₁ hb₁ h11)
    (Submodule.smul_mem _ _ (bivector_mem_so34 ha₁ hb₂ h12)))
    (Submodule.smul_mem _ _ (bivector_mem_so34 ha₂ hb₁ h21)))
    (Submodule.smul_mem _ _ (bivector_mem_so34 ha₂ hb₂ h22))

lemma HThetaMat_eq_bivector :
    HThetaMat = (1 / 2 : ℝ) • (cl44Bivector 3 7 - cl44Bivector 1 5) := by
  have h15 : cl44Bivector 1 5 = tensor4 1 cl11Grad 1 1 := by simp [cl44Bivector, cl44Gen]
  have h37 : cl44Bivector 3 7 = tensor4 1 1 1 cl11Grad := by simp [cl44Bivector, cl44Gen]
  have hg : cl11Grad = (1 : Mat2) - (2 : ℝ) • cl11Proj1 := by
    apply ext_mat2 <;> norm_num [cl11Grad, cl11Proj1]
  rw [h15, h37, hg]
  dsimp [HThetaMat]
  ext i j
  simp [tensor4]
  ring

lemma HAlphaMat_eq_bivector :
    HAlphaMat = (1 / 2 : ℝ) • ((2 : ℝ) • cl44Bivector 2 6 - cl44Bivector 1 5 - cl44Bivector 3 7) := by
  have h15 : cl44Bivector 1 5 = tensor4 1 cl11Grad 1 1 := by simp [cl44Bivector, cl44Gen]
  have h26 : cl44Bivector 2 6 = tensor4 1 1 cl11Grad 1 := by simp [cl44Bivector, cl44Gen]
  have h37 : cl44Bivector 3 7 = tensor4 1 1 1 cl11Grad := by simp [cl44Bivector, cl44Gen]
  have hg : cl11Grad = (1 : Mat2) - (2 : ℝ) • cl11Proj1 := by
    apply ext_mat2 <;> norm_num [cl11Grad, cl11Proj1]
  rw [h15, h26, h37, hg]
  dsimp [HAlphaMat]
  ext i j
  simp [tensor4]
  ring

lemma g2Basis_mem_so34 (i : Fin 14) : g2Basis i ∈ so34Submodule := by
  have h15 : cl44Bivector 1 5 ∈ so34Submodule := bivector_mem_so34 (by decide) (by decide) (by decide)
  have h26 : cl44Bivector 2 6 ∈ so34Submodule := bivector_mem_so34 (by decide) (by decide) (by decide)
  have h37 : cl44Bivector 3 7 ∈ so34Submodule := bivector_mem_so34 (by decide) (by decide) (by decide)
  have h_e0_u1 : eTilde0 * uVec1 ∈ so34Submodule := by
    rw [show eTilde0 = cl44Gen 4 from rfl, uVec1_eq]
    rw [mul_smul_comm, mul_add]
    exact Submodule.smul_mem _ _ (add_mem
      (bivector_mem_so34 (by decide) (by decide) (by decide))
      (bivector_mem_so34 (by decide) (by decide) (by decide)))
  have h_e0_u2 : eTilde0 * uVec2 ∈ so34Submodule := by
    rw [show eTilde0 = cl44Gen 4 from rfl, uVec2_eq]
    rw [mul_smul_comm, mul_add]
    exact Submodule.smul_mem _ _ (add_mem
      (bivector_mem_so34 (by decide) (by decide) (by decide))
      (bivector_mem_so34 (by decide) (by decide) (by decide)))
  have h_e0_u3 : eTilde0 * uVec3 ∈ so34Submodule := by
    rw [show eTilde0 = cl44Gen 4 from rfl, uVec3_eq]
    rw [mul_smul_comm, mul_add]
    exact Submodule.smul_mem _ _ (add_mem
      (bivector_mem_so34 (by decide) (by decide) (by decide))
      (bivector_mem_so34 (by decide) (by decide) (by decide)))
  have h_e0_d1 : eTilde0 * dVec1 ∈ so34Submodule := by
    rw [show eTilde0 = cl44Gen 4 from rfl, dVec1_eq]
    rw [mul_smul_comm, mul_sub]
    exact Submodule.smul_mem _ _ (sub_mem
      (bivector_mem_so34 (by decide) (by decide) (by decide))
      (bivector_mem_so34 (by decide) (by decide) (by decide)))
  have h_e0_d2 : eTilde0 * dVec2 ∈ so34Submodule := by
    rw [show eTilde0 = cl44Gen 4 from rfl, dVec2_eq]
    rw [mul_smul_comm, mul_sub]
    exact Submodule.smul_mem _ _ (sub_mem
      (bivector_mem_so34 (by decide) (by decide) (by decide))
      (bivector_mem_so34 (by decide) (by decide) (by decide)))
  have h_e0_d3 : eTilde0 * dVec3 ∈ so34Submodule := by
    rw [show eTilde0 = cl44Gen 4 from rfl, dVec3_eq]
    rw [mul_smul_comm, mul_sub]
    exact Submodule.smul_mem _ _ (sub_mem
      (bivector_mem_so34 (by decide) (by decide) (by decide))
      (bivector_mem_so34 (by decide) (by decide) (by decide)))
  fin_cases i
  · -- 0: ZPlus2Mat = uVec1 * dVec3
    dsimp [g2Basis, ZPlus2Mat]
    rw [uVec1_eq, dVec3_eq]
    simpa [one_smul, neg_one_smul, sub_eq_add_neg] using
      comb_mem_so34 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (1 : ℝ) (-1 : ℝ)
  · -- 1: X1Mat = uVec1 * dVec2
    dsimp [g2Basis, X1Mat]
    rw [uVec1_eq, dVec2_eq]
    simpa [one_smul, neg_one_smul, sub_eq_add_neg] using
      comb_mem_so34 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (1 : ℝ) (-1 : ℝ)
  · -- 2: X2Mat = uVec2 * dVec3
    dsimp [g2Basis, X2Mat]
    rw [uVec2_eq, dVec3_eq]
    simpa [one_smul, neg_one_smul, sub_eq_add_neg] using
      comb_mem_so34 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (1 : ℝ) (-1 : ℝ)
  · -- 3: X3Mat = uVec1 * uVec2 - eTilde0 * dVec3
    dsimp [g2Basis, X3Mat]
    refine sub_mem ?_ h_e0_d3
    rw [uVec1_eq, uVec2_eq]
    simpa [one_smul] using
      comb_mem_so34 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (1 : ℝ) (1 : ℝ)
  · -- 4: X4Mat = -(dVec2 * dVec3 + eTilde0 * uVec1)
    dsimp [g2Basis, X4Mat]
    refine neg_mem (add_mem ?_ h_e0_u1)
    rw [dVec2_eq, dVec3_eq]
    simpa [neg_one_smul, sub_eq_add_neg] using
      comb_mem_so34 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (-1 : ℝ) (-1 : ℝ)
  · -- 5: HThetaMat
    dsimp [g2Basis]
    rw [HThetaMat_eq_bivector]
    exact Submodule.smul_mem _ _ (sub_mem h37 h15)
  · -- 6: HAlphaMat
    dsimp [g2Basis]
    rw [HAlphaMat_eq_bivector]
    exact Submodule.smul_mem _ _ (sub_mem (sub_mem (Submodule.smul_mem _ _ h26) h15) h37)
  · -- 7: E0Mat = uVec3 * uVec1 - eTilde0 * dVec2
    dsimp [g2Basis, E0Mat]
    refine sub_mem ?_ h_e0_d2
    rw [uVec3_eq, uVec1_eq]
    simpa [one_smul] using
      comb_mem_so34 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (1 : ℝ) (1 : ℝ)
  · -- 8: F0Mat = -(dVec3 * dVec1 + eTilde0 * uVec2)
    dsimp [g2Basis, F0Mat]
    refine neg_mem (add_mem ?_ h_e0_u2)
    rw [dVec3_eq, dVec1_eq]
    simpa [neg_one_smul, sub_eq_add_neg] using
      comb_mem_so34 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (-1 : ℝ) (-1 : ℝ)
  · -- 9: Y1Mat = uVec2 * dVec1
    dsimp [g2Basis, Y1Mat]
    rw [uVec2_eq, dVec1_eq]
    simpa [one_smul, neg_one_smul, sub_eq_add_neg] using
      comb_mem_so34 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (1 : ℝ) (-1 : ℝ)
  · -- 10: Y2Mat = uVec3 * dVec2
    dsimp [g2Basis, Y2Mat]
    rw [uVec3_eq, dVec2_eq]
    simpa [one_smul, neg_one_smul, sub_eq_add_neg] using
      comb_mem_so34 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (1 : ℝ) (-1 : ℝ)
  · -- 11: Y3Mat = dVec1 * dVec2 + eTilde0 * uVec3
    dsimp [g2Basis, Y3Mat]
    refine add_mem ?_ h_e0_u3
    rw [dVec1_eq, dVec2_eq]
    simpa [neg_one_smul, sub_eq_add_neg] using
      comb_mem_so34 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (-1 : ℝ) (-1 : ℝ)
  · -- 12: Y4Mat = -(uVec2 * uVec3 - eTilde0 * dVec1)
    dsimp [g2Basis, Y4Mat]
    refine neg_mem (sub_mem ?_ h_e0_d1)
    rw [uVec2_eq, uVec3_eq]
    simpa [one_smul] using
      comb_mem_so34 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (1 : ℝ) (1 : ℝ)
  · -- 13: ZMinus2Mat = uVec3 * dVec1
    dsimp [g2Basis, ZMinus2Mat]
    rw [uVec3_eq, dVec1_eq]
    simpa [one_smul, neg_one_smul, sub_eq_add_neg] using
      comb_mem_so34 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (1 : ℝ) (-1 : ℝ)

theorem g2Basis_mem_bivector (i : Fin 14) : g2Basis i ∈ cl44BivectorSubmodule :=
  so34Submodule_le_bivector (g2Basis_mem_so34 i)

theorem g2Basis_comm_e0 (i : Fin 14) :
    g2Basis i * cl44Gen 0 = cl44Gen 0 * g2Basis i := by
  have h := g2Basis_mem_so34 i
  refine Submodule.span_induction ?_ ?_ ?_ ?_ h
  · rintro _ ⟨a, b, ha, hab, rfl⟩
    have ha0 : a ≠ 0 := fun h0 => by omega
    have hb0 : b ≠ 0 := fun h0 => by
      have : a.1 < b.1 := hab
      omega
    have hca := cl44Gen_swap ha0
    have hcb := cl44Gen_swap hb0
    dsimp [cl44Bivector]
    calc
      (cl44Gen a * cl44Gen b) * cl44Gen 0
          = cl44Gen a * (cl44Gen b * cl44Gen 0) := mul_assoc _ _ _
      _ = cl44Gen a * -(cl44Gen 0 * cl44Gen b) := by rw [hcb]
      _ = -(cl44Gen a * cl44Gen 0) * cl44Gen b := by noncomm_ring
      _ = -(-(cl44Gen 0 * cl44Gen a)) * cl44Gen b := by rw [hca]
      _ = cl44Gen 0 * (cl44Gen a * cl44Gen b) := by noncomm_ring
  · simp
  · intro x y _ _ hx hy; rw [add_mul, mul_add, hx, hy]
  · intro c x _ hx; rw [smul_mul_assoc, mul_smul_comm, hx]

lemma ZPlus2Mat_norm : ZPlus2Mat = tensor4 1 cl11Up cl11Grad cl11Down := by
  simp [ZPlus2Mat, uVec1, dVec3]
lemma X1Mat_norm : X1Mat = tensor4 1 cl11Up cl11Down 1 := by
  simp [X1Mat, uVec1, dVec2]
lemma X2Mat_norm : X2Mat = tensor4 1 1 cl11Up cl11Down := by
  simp [X2Mat, uVec2, dVec3]
lemma X3Mat_norm :
    X3Mat = tensor4 1 cl11Up cl11Up 1 - tensor4 cl11Pos cl11Grad cl11Grad cl11Down := by
  simp [X3Mat, uVec1, uVec2, eTilde0, dVec3, cl44Gen]
lemma X4Mat_norm :
    X4Mat = tensor4 1 1 cl11Down cl11Down - tensor4 cl11Pos cl11Up 1 1 := by
  simp [X4Mat, dVec2, dVec3, eTilde0, uVec1, cl44Gen]; abel
lemma E0Mat_norm :
    E0Mat = -(tensor4 1 cl11Up cl11Grad cl11Up + tensor4 cl11Pos cl11Grad cl11Down 1) := by
  simp [E0Mat, uVec3, uVec1, eTilde0, dVec2, cl44Gen]; abel
lemma F0Mat_norm :
    F0Mat = -(tensor4 1 cl11Down cl11Grad cl11Down + tensor4 cl11Pos cl11Grad cl11Up 1) := by
  simp [F0Mat, dVec3, dVec1, eTilde0, uVec2, cl44Gen]
lemma Y1Mat_norm : Y1Mat = tensor4 1 cl11Down cl11Up 1 := by
  simp [Y1Mat, uVec2, dVec1]
lemma Y2Mat_norm : Y2Mat = tensor4 1 1 cl11Down cl11Up := by
  simp [Y2Mat, uVec3, dVec2]
lemma Y3Mat_norm :
    Y3Mat = -tensor4 1 cl11Down cl11Down 1 + tensor4 cl11Pos cl11Grad cl11Grad cl11Up := by
  simp [Y3Mat, dVec1, dVec2, eTilde0, uVec3, cl44Gen]
lemma Y4Mat_norm :
    Y4Mat = -tensor4 1 1 cl11Up cl11Up + tensor4 cl11Pos cl11Down 1 1 := by
  simp [Y4Mat, uVec2, uVec3, eTilde0, dVec1, cl44Gen]; abel
lemma ZMinus2Mat_norm : ZMinus2Mat = tensor4 1 cl11Down cl11Grad cl11Up := by
  simp [ZMinus2Mat, uVec3, dVec1]

theorem g2Basis_ann_psiPlus (i : Fin 14) : (g2Basis i).mulVec psiPlus = 0 := by
  fin_cases i <;>
    simp only [g2Basis, ZPlus2Mat_norm, X1Mat_norm, X2Mat_norm, X3Mat_norm, X4Mat_norm,
      HThetaMat, HAlphaMat, E0Mat_norm, F0Mat_norm, Y1Mat_norm, Y2Mat_norm, Y3Mat_norm,
      Y4Mat_norm, ZMinus2Mat_norm, psiPlus, ket0000, ket1111,
      Matrix.mulVec_add, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.neg_mulVec,
      Matrix.smul_mulVec, tensor4_mulVec, Matrix.one_mulVec,
      cl11Pos_mulVec_ket0, cl11Pos_mulVec_ket1, cl11Grad_mulVec_ket0, cl11Grad_mulVec_ket1,
      cl11Up_mulVec_ket0, cl11Up_mulVec_ket1, cl11Down_mulVec_ket0, cl11Down_mulVec_ket1,
      cl11Proj1_mulVec_ket0, cl11Proj1_mulVec_ket1,
      vec4_zero_2, vec4_zero_3, vec4_zero_4,
      vec4_neg_2, vec4_neg_3] <;>
    module

/-! ### Linear Independence of the 14 Basis Matrices (`finrank = 14`) & Stabilizer Exactness -/

private def idx4 (b0 b1 b2 b3 : Fin 2) : Krein16Idx := (b0, b1, b2, b3)

theorem g2Basis_linearIndependent : LinearIndependent ℝ g2Basis := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have eval_at (r c_idx : Krein16Idx) :
      ∑ i : Fin 14, c i * g2Basis i r c_idx = 0 := by
    have h0 := congrArg (fun M : Mat16 => M r c_idx) hc
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at h0
    exact h0
  have h14_sum (f : Fin 14 → ℝ) :
      ∑ i : Fin 14, f i =
        f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 +
        f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 +
      (f 7 + (f 8 + (f 9 + (f 10 + (f 11 + (f 12 + f 13)))))))))))) = _
    ring
  have kill_root (r c_idx : Krein16Idx) :
      c 0 * ZPlus2Mat r c_idx + c 1 * X1Mat r c_idx + c 2 * X2Mat r c_idx +
      c 3 * X3Mat r c_idx + c 4 * X4Mat r c_idx + c 5 * HThetaMat r c_idx +
      c 6 * HAlphaMat r c_idx + c 7 * E0Mat r c_idx + c 8 * F0Mat r c_idx +
      c 9 * Y1Mat r c_idx + c 10 * Y2Mat r c_idx + c 11 * Y3Mat r c_idx +
      c 12 * Y4Mat r c_idx + c 13 * ZMinus2Mat r c_idx = 0 := by
    have h := eval_at r c_idx
    rw [h14_sum] at h
    simpa only [g2Basis, Fin.isValue] using h
  have hc0 : c 0 = 0 := by
    have h := kill_root (idx4 0 1 0 0) (idx4 0 0 0 1)
    simp only [ZPlus2Mat_norm, X1Mat_norm, X2Mat_norm, X3Mat_norm, X4Mat_norm,
      HThetaMat, HAlphaMat, E0Mat_norm, F0Mat_norm, Y1Mat_norm, Y2Mat_norm, Y3Mat_norm,
      Y4Mat_norm, ZMinus2Mat_norm, idx4, tensor4_apply, Matrix.sub_apply, Matrix.add_apply,
      Matrix.neg_apply, Matrix.smul_apply, Matrix.one_apply, Fin.isValue] at h
    norm_num [cl11Pos, cl11Grad, cl11Up, cl11Down, cl11Proj1] at h
    linarith
  have hc1 : c 1 = 0 := by
    have h := kill_root (idx4 0 1 0 0) (idx4 0 0 1 0)
    simp only [ZPlus2Mat_norm, X1Mat_norm, X2Mat_norm, X3Mat_norm, X4Mat_norm,
      HThetaMat, HAlphaMat, E0Mat_norm, F0Mat_norm, Y1Mat_norm, Y2Mat_norm, Y3Mat_norm,
      Y4Mat_norm, ZMinus2Mat_norm, idx4, tensor4_apply, Matrix.sub_apply, Matrix.add_apply,
      Matrix.neg_apply, Matrix.smul_apply, Matrix.one_apply, Fin.isValue] at h
    norm_num [cl11Pos, cl11Grad, cl11Up, cl11Down, cl11Proj1] at h
    linarith
  have hc2 : c 2 = 0 := by
    have h := kill_root (idx4 0 0 1 0) (idx4 0 0 0 1)
    simp only [ZPlus2Mat_norm, X1Mat_norm, X2Mat_norm, X3Mat_norm, X4Mat_norm,
      HThetaMat, HAlphaMat, E0Mat_norm, F0Mat_norm, Y1Mat_norm, Y2Mat_norm, Y3Mat_norm,
      Y4Mat_norm, ZMinus2Mat_norm, idx4, tensor4_apply, Matrix.sub_apply, Matrix.add_apply,
      Matrix.neg_apply, Matrix.smul_apply, Matrix.one_apply, Fin.isValue] at h
    norm_num [cl11Pos, cl11Grad, cl11Up, cl11Down, cl11Proj1] at h
    linarith
  have hc3 : c 3 = 0 := by
    have h := kill_root (idx4 0 1 1 0) (idx4 0 0 0 0)
    simp only [ZPlus2Mat_norm, X1Mat_norm, X2Mat_norm, X3Mat_norm, X4Mat_norm,
      HThetaMat, HAlphaMat, E0Mat_norm, F0Mat_norm, Y1Mat_norm, Y2Mat_norm, Y3Mat_norm,
      Y4Mat_norm, ZMinus2Mat_norm, idx4, tensor4_apply, Matrix.sub_apply, Matrix.add_apply,
      Matrix.neg_apply, Matrix.smul_apply, Matrix.one_apply, Fin.isValue] at h
    norm_num [cl11Pos, cl11Grad, cl11Up, cl11Down, cl11Proj1] at h
    linarith
  have hc4 : c 4 = 0 := by
    have h := kill_root (idx4 0 0 0 0) (idx4 0 0 1 1)
    simp only [ZPlus2Mat_norm, X1Mat_norm, X2Mat_norm, X3Mat_norm, X4Mat_norm,
      HThetaMat, HAlphaMat, E0Mat_norm, F0Mat_norm, Y1Mat_norm, Y2Mat_norm, Y3Mat_norm,
      Y4Mat_norm, ZMinus2Mat_norm, idx4, tensor4_apply, Matrix.sub_apply, Matrix.add_apply,
      Matrix.neg_apply, Matrix.smul_apply, Matrix.one_apply, Fin.isValue] at h
    norm_num [cl11Pos, cl11Grad, cl11Up, cl11Down, cl11Proj1] at h
    linarith
  have hc7 : c 7 = 0 := by
    have h := kill_root (idx4 0 1 0 1) (idx4 0 0 0 0)
    simp only [ZPlus2Mat_norm, X1Mat_norm, X2Mat_norm, X3Mat_norm, X4Mat_norm,
      HThetaMat, HAlphaMat, E0Mat_norm, F0Mat_norm, Y1Mat_norm, Y2Mat_norm, Y3Mat_norm,
      Y4Mat_norm, ZMinus2Mat_norm, idx4, tensor4_apply, Matrix.sub_apply, Matrix.add_apply,
      Matrix.neg_apply, Matrix.smul_apply, Matrix.one_apply, Fin.isValue] at h
    norm_num [cl11Pos, cl11Grad, cl11Up, cl11Down, cl11Proj1] at h
    linarith
  have hc8 : c 8 = 0 := by
    have h := kill_root (idx4 0 0 0 0) (idx4 0 1 0 1)
    simp only [ZPlus2Mat_norm, X1Mat_norm, X2Mat_norm, X3Mat_norm, X4Mat_norm,
      HThetaMat, HAlphaMat, E0Mat_norm, F0Mat_norm, Y1Mat_norm, Y2Mat_norm, Y3Mat_norm,
      Y4Mat_norm, ZMinus2Mat_norm, idx4, tensor4_apply, Matrix.sub_apply, Matrix.add_apply,
      Matrix.neg_apply, Matrix.smul_apply, Matrix.one_apply, Fin.isValue] at h
    norm_num [cl11Pos, cl11Grad, cl11Up, cl11Down, cl11Proj1] at h
    linarith
  have hc9 : c 9 = 0 := by
    have h := kill_root (idx4 0 0 1 0) (idx4 0 1 0 0)
    simp only [ZPlus2Mat_norm, X1Mat_norm, X2Mat_norm, X3Mat_norm, X4Mat_norm,
      HThetaMat, HAlphaMat, E0Mat_norm, F0Mat_norm, Y1Mat_norm, Y2Mat_norm, Y3Mat_norm,
      Y4Mat_norm, ZMinus2Mat_norm, idx4, tensor4_apply, Matrix.sub_apply, Matrix.add_apply,
      Matrix.neg_apply, Matrix.smul_apply, Matrix.one_apply, Fin.isValue] at h
    norm_num [cl11Pos, cl11Grad, cl11Up, cl11Down, cl11Proj1] at h
    linarith
  have hc10 : c 10 = 0 := by
    have h := kill_root (idx4 0 0 0 1) (idx4 0 0 1 0)
    simp only [ZPlus2Mat_norm, X1Mat_norm, X2Mat_norm, X3Mat_norm, X4Mat_norm,
      HThetaMat, HAlphaMat, E0Mat_norm, F0Mat_norm, Y1Mat_norm, Y2Mat_norm, Y3Mat_norm,
      Y4Mat_norm, ZMinus2Mat_norm, idx4, tensor4_apply, Matrix.sub_apply, Matrix.add_apply,
      Matrix.neg_apply, Matrix.smul_apply, Matrix.one_apply, Fin.isValue] at h
    norm_num [cl11Pos, cl11Grad, cl11Up, cl11Down, cl11Proj1] at h
    linarith
  have hc11 : c 11 = 0 := by
    have h := kill_root (idx4 0 0 0 0) (idx4 0 1 1 0)
    simp only [ZPlus2Mat_norm, X1Mat_norm, X2Mat_norm, X3Mat_norm, X4Mat_norm,
      HThetaMat, HAlphaMat, E0Mat_norm, F0Mat_norm, Y1Mat_norm, Y2Mat_norm, Y3Mat_norm,
      Y4Mat_norm, ZMinus2Mat_norm, idx4, tensor4_apply, Matrix.sub_apply, Matrix.add_apply,
      Matrix.neg_apply, Matrix.smul_apply, Matrix.one_apply, Fin.isValue] at h
    norm_num [cl11Pos, cl11Grad, cl11Up, cl11Down, cl11Proj1] at h
    linarith
  have hc12 : c 12 = 0 := by
    have h := kill_root (idx4 0 0 1 1) (idx4 0 0 0 0)
    simp only [ZPlus2Mat_norm, X1Mat_norm, X2Mat_norm, X3Mat_norm, X4Mat_norm,
      HThetaMat, HAlphaMat, E0Mat_norm, F0Mat_norm, Y1Mat_norm, Y2Mat_norm, Y3Mat_norm,
      Y4Mat_norm, ZMinus2Mat_norm, idx4, tensor4_apply, Matrix.sub_apply, Matrix.add_apply,
      Matrix.neg_apply, Matrix.smul_apply, Matrix.one_apply, Fin.isValue] at h
    norm_num [cl11Pos, cl11Grad, cl11Up, cl11Down, cl11Proj1] at h
    linarith
  have hc13 : c 13 = 0 := by
    have h := kill_root (idx4 0 0 0 1) (idx4 0 1 0 0)
    simp only [ZPlus2Mat_norm, X1Mat_norm, X2Mat_norm, X3Mat_norm, X4Mat_norm,
      HThetaMat, HAlphaMat, E0Mat_norm, F0Mat_norm, Y1Mat_norm, Y2Mat_norm, Y3Mat_norm,
      Y4Mat_norm, ZMinus2Mat_norm, idx4, tensor4_apply, Matrix.sub_apply, Matrix.add_apply,
      Matrix.neg_apply, Matrix.smul_apply, Matrix.one_apply, Fin.isValue] at h
    norm_num [cl11Pos, cl11Grad, cl11Up, cl11Down, cl11Proj1] at h
    linarith
  have hdiag1 := kill_root (idx4 0 0 1 0) (idx4 0 0 1 0)
  have hdiag2 := kill_root (idx4 0 0 0 1) (idx4 0 0 0 1)
  simp only [hc0, hc1, hc2, hc3, hc4, hc7, hc8, hc9, hc10, hc11, hc12, hc13, zero_mul, zero_add,
    add_zero, HThetaMat, HAlphaMat, idx4, tensor4_apply, Matrix.sub_apply, Matrix.add_apply,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, Fin.isValue] at hdiag1 hdiag2
  norm_num [cl11Proj1] at hdiag1 hdiag2
  have hc6 : c 6 = 0 := by linarith
  have hc5 : c 5 = 0 := by linarith
  intro i
  fin_cases i <;> assumption

theorem finrank_g2Submodule : Module.finrank ℝ g2Submodule = 14 := by
  rw [g2Submodule, finrank_span_eq_card g2Basis_linearIndependent]
  simp

/-! ### Part III(b): Stabilizer Exactness (`g2Submodule = stabilizerSubmodule`), 5-Grading, Serre Syzygies, Jordan Jump & Centerlessness -/

@[simp] lemma cl11Proj0_mul_up : cl11Proj0 * cl11Up = (0 : Mat2) := by
  apply ext_mat2 <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma cl11Up_mul_proj0 : cl11Up * cl11Proj0 = cl11Up := by
  apply ext_mat2 <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma cl11Proj0_mul_down : cl11Proj0 * cl11Down = cl11Down := by
  apply ext_mat2 <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma cl11Down_mul_proj0 : cl11Down * cl11Proj0 = (0 : Mat2) := by
  apply ext_mat2 <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma cl11Proj0_mul_grad : cl11Proj0 * cl11Grad = cl11Proj0 := by
  apply ext_mat2 <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma cl11Grad_mul_proj0 : cl11Grad * cl11Proj0 = cl11Proj0 := by
  apply ext_mat2 <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma cl11Proj0_mul_pos : cl11Proj0 * cl11Pos = cl11Down := by
  apply ext_mat2 <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma cl11Pos_mul_proj0 : cl11Pos * cl11Proj0 = cl11Up := by
  apply ext_mat2 <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private lemma cl11Proj0_eq_one_sub : cl11Proj0 = (1 : Mat2) - cl11Proj1 := by
  apply ext_mat2 <;> norm_num [cl11Proj0, cl11Proj1]

private lemma cl11Proj0_add_proj1 : cl11Proj0 + cl11Proj1 = (1 : Mat2) := by
  apply ext_mat2 <;> norm_num [cl11Proj0, cl11Proj1]

def oddBivectorSubmodule : Submodule ℝ Mat16 :=
  Submodule.span ℝ { M : Mat16 | ∃ b : Fin 8, 0 < b.1 ∧ M = cl44Bivector 0 b }

private lemma oddBivectorSubmodule_le_bivector :
    oddBivectorSubmodule ≤ cl44BivectorSubmodule := by
  refine Submodule.span_le.mpr ?_
  rintro M ⟨b, hb, rfl⟩
  exact Submodule.subset_span ⟨0, b, Fin.mk_lt_mk.mpr hb, rfl⟩

lemma cl44BivectorSubmodule_eq_sup :
    cl44BivectorSubmodule = so34Submodule ⊔ oddBivectorSubmodule := by
  refine le_antisymm ?_ (sup_le so34Submodule_le_bivector oddBivectorSubmodule_le_bivector)
  refine Submodule.span_le.mpr ?_
  rintro M ⟨a, b, hab, rfl⟩
  by_cases ha0 : a = 0
  · subst ha0
    exact Submodule.mem_sup_right (Submodule.subset_span ⟨b, hab, rfl⟩)
  · have ha1 : 1 ≤ a.1 := Nat.pos_of_ne_zero (fun h => ha0 (Fin.ext h))
    exact Submodule.mem_sup_left (Submodule.subset_span ⟨a, b, ha1, hab, rfl⟩)

lemma mem_so34_comm_e0 {G : Mat16} (hG : G ∈ so34Submodule) :
    G * cl44Gen 0 = cl44Gen 0 * G := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hG
  · rintro _ ⟨a, b, ha, hab, rfl⟩
    have ha0 : a ≠ 0 := fun h0 => by omega
    have hb0 : b ≠ 0 := fun h0 => by
      have : a.1 < b.1 := hab
      omega
    have hca := cl44Gen_swap ha0
    have hcb := cl44Gen_swap hb0
    dsimp [cl44Bivector]
    calc
      (cl44Gen a * cl44Gen b) * cl44Gen 0
          = cl44Gen a * (cl44Gen b * cl44Gen 0) := mul_assoc _ _ _
      _ = cl44Gen a * -(cl44Gen 0 * cl44Gen b) := by rw [hcb]
      _ = -(cl44Gen a * cl44Gen 0) * cl44Gen b := by noncomm_ring
      _ = -(-(cl44Gen 0 * cl44Gen a)) * cl44Gen b := by rw [hca]
      _ = cl44Gen 0 * (cl44Gen a * cl44Gen b) := by noncomm_ring
  · simp
  · intro x y _ _ hx hy; rw [add_mul, mul_add, hx, hy]
  · intro c x _ hx; rw [smul_mul_assoc, mul_smul_comm, hx]

lemma mem_oddBivector_anticomm_e0 {K : Mat16} (hK : K ∈ oddBivectorSubmodule) :
    K * cl44Gen 0 = -(cl44Gen 0 * K) := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hK
  · rintro _ ⟨b, hb, rfl⟩
    have hb0 : b ≠ 0 := fun h0 => by
      have : 0 < b.1 := hb
      omega
    have hcb := cl44Gen_swap hb0
    dsimp [cl44Bivector]
    calc
      (cl44Gen 0 * cl44Gen b) * cl44Gen 0
          = cl44Gen 0 * (cl44Gen b * cl44Gen 0) := mul_assoc _ _ _
      _ = cl44Gen 0 * -(cl44Gen 0 * cl44Gen b) := by rw [hcb]
      _ = -((cl44Gen 0 * cl44Gen 0) * cl44Gen b) := by noncomm_ring
      _ = -((1 : Mat16) * cl44Gen b) := by rw [cl44Gen_sq_pos 0 (by decide)]
      _ = -(cl44Gen 0 * (cl44Gen 0 * cl44Gen b)) := by
          rw [← mul_assoc, cl44Gen_sq_pos 0 (by decide)]
  · simp
  · intro x y _ _ hx hy; rw [add_mul, mul_add, hx, hy, neg_add]
  · intro c x _ hx; rw [smul_mul_assoc, mul_smul_comm, hx, smul_neg]

theorem mem_so34_iff_comm_e0 {M : Mat16} (hM : M ∈ cl44BivectorSubmodule) :
    M ∈ so34Submodule ↔ M * cl44Gen 0 = cl44Gen 0 * M := by
  constructor
  · exact mem_so34_comm_e0
  · intro hcomm
    have hsup : M ∈ so34Submodule ⊔ oddBivectorSubmodule :=
      cl44BivectorSubmodule_eq_sup ▸ hM
    rcases Submodule.mem_sup.mp hsup with ⟨G, hG, K, hK, rfl⟩
    have hG0 := mem_so34_comm_e0 hG
    have hK0 := mem_oddBivector_anticomm_e0 hK
    have he0 : cl44Gen 0 * cl44Gen 0 = (1 : Mat16) := cl44Gen_sq_pos 0 (by decide)
    have hconj1 : cl44Gen 0 * (G + K) * cl44Gen 0 = G + K := by
      rw [mul_assoc (cl44Gen 0) (G + K), hcomm, ← mul_assoc, he0, one_mul]
    have hconj2 : cl44Gen 0 * (G + K) * cl44Gen 0 = G - K := by
      calc
        cl44Gen 0 * (G + K) * cl44Gen 0
            = cl44Gen 0 * (G * cl44Gen 0 + K * cl44Gen 0) := by
              rw [mul_assoc (cl44Gen 0) (G + K), add_mul]
        _ = cl44Gen 0 * (cl44Gen 0 * G - cl44Gen 0 * K) := by rw [hG0, hK0, ← sub_eq_add_neg]
        _ = (cl44Gen 0 * cl44Gen 0) * G - (cl44Gen 0 * cl44Gen 0) * K := by noncomm_ring
        _ = G - K := by rw [he0, one_mul, one_mul]
    have h2K : (2 : ℝ) • K = 0 := by
      have hdiff : G + K = G - K := hconj1.symm.trans hconj2
      have hK_neg : K = -K := by
        calc
          K = (G + K) - G := (add_sub_cancel_left G K).symm
          _ = (G - K) - G := by rw [hdiff]
          _ = -K := by abel
      calc
        (2 : ℝ) • K = K + K := two_smul ℝ K
        _ = K + -K := by nth_rw 2 [hK_neg]
        _ = 0 := add_neg_cancel K
    have hK_zero : K = 0 := by
      rcases smul_eq_zero.mp h2K with h2 | hK0'
      · norm_num at h2
      · exact hK0'
    rw [hK_zero, add_zero]
    exact hG

private def so34Pairs (k : Fin 21) : Fin 8 × Fin 8 :=
  match k.1 with
  | 0 => (1, 2) | 1 => (1, 3) | 2 => (1, 4) | 3 => (1, 5) | 4 => (1, 6) | 5 => (1, 7)
  | 6 => (2, 3) | 7 => (2, 4) | 8 => (2, 5) | 9 => (2, 6) | 10 => (2, 7)
  | 11 => (3, 4) | 12 => (3, 5) | 13 => (3, 6) | 14 => (3, 7)
  | 15 => (4, 5) | 16 => (4, 6) | 17 => (4, 7)
  | 18 => (5, 6) | 19 => (5, 7)
  | _ => (6, 7)

private lemma exists_so34Pair :
    ∀ a b : Fin 8, 1 ≤ a.1 → a < b → ∃ k : Fin 21, so34Pairs k = (a, b) := by
  decide

private lemma so34Pairs_valid (k : Fin 21) :
    1 ≤ (so34Pairs k).1.1 ∧ (so34Pairs k).1 < (so34Pairs k).2 := by
  fin_cases k <;> decide

theorem so34Submodule_finrank_le : Module.finrank ℝ so34Submodule ≤ 21 := by
  let Φ : (Fin 21 → ℝ) →ₗ[ℝ] Mat16 :=
    { toFun := fun c => ∑ k : Fin 21, c k • cl44Bivector (so34Pairs k).1 (so34Pairs k).2
      map_add' := fun c₁ c₂ => by
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun r c => by
        simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul] }
  have hrange : LinearMap.range Φ = so34Submodule := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨c, rfl⟩
      dsimp [Φ]
      refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
      obtain ⟨h1, hlt⟩ := so34Pairs_valid k
      exact Submodule.subset_span ⟨(so34Pairs k).1, (so34Pairs k).2, h1, hlt, rfl⟩
    · refine Submodule.span_le.mpr ?_
      rintro M ⟨a, b, ha, hab, rfl⟩
      obtain ⟨k, hk⟩ := exists_so34Pair a b ha hab
      let c : Fin 21 → ℝ := fun j => if j = k then 1 else 0
      refine ⟨c, ?_⟩
      dsimp [Φ, c]
      simp [hk]
  have hrk := LinearMap.finrank_range_add_finrank_ker Φ
  rw [hrange, Module.finrank_pi, Fintype.card_fin] at hrk
  omega

def spinorAct : so34Submodule →ₗ[ℝ] (Krein16Idx → ℝ) where
  toFun G := G.1.mulVec psiPlus
  map_add' G H := Matrix.add_mulVec G.1 H.1 psiPlus
  map_smul' r G := Matrix.smul_mulVec r G.1 psiPlus

private def spinorOrbitGen : Fin 7 → Mat16
  | 0 => cl44Bivector 1 4
  | 1 => cl44Bivector 2 4
  | 2 => cl44Bivector 3 4
  | 3 => cl44Bivector 4 5
  | 4 => cl44Bivector 4 6
  | 5 => cl44Bivector 4 7
  | 6 => cl44Bivector 1 5

private lemma spinorOrbitGen_mem_so34 (k : Fin 7) :
    spinorOrbitGen k ∈ so34Submodule := by
  fin_cases k <;> exact bivector_mem_so34 (by decide) (by decide) (by decide)

private def spinorOrbitVec (k : Fin 7) : Krein16Idx → ℝ :=
  spinorAct ⟨spinorOrbitGen k, spinorOrbitGen_mem_so34 k⟩

private lemma spinorOrbitVec_linearIndependent : LinearIndependent ℝ spinorOrbitVec := by
  have h14 : cl44Bivector 1 4 = -tensor4 cl11Pos cl11Pos 1 1 := by
    simp [cl44Bivector, cl44Gen]
  have h24 : cl44Bivector 2 4 = -tensor4 cl11Pos cl11Grad cl11Pos 1 := by
    simp [cl44Bivector, cl44Gen]
  have h34 : cl44Bivector 3 4 = -tensor4 cl11Pos cl11Grad cl11Grad cl11Pos := by
    simp [cl44Bivector, cl44Gen]
  have h45 : cl44Bivector 4 5 = tensor4 cl11Pos cl11Neg 1 1 := by
    simp [cl44Bivector, cl44Gen]
  have h46 : cl44Bivector 4 6 = tensor4 cl11Pos cl11Grad cl11Neg 1 := by
    simp [cl44Bivector, cl44Gen]
  have h47 : cl44Bivector 4 7 = tensor4 cl11Pos cl11Grad cl11Grad cl11Neg := by
    simp [cl44Bivector, cl44Gen]
  have h15 : cl44Bivector 1 5 = tensor4 1 cl11Grad 1 1 := by
    simp [cl44Bivector, cl44Gen]
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have eval_orb (q : Krein16Idx) : ∑ k : Fin 7, c k * spinorOrbitVec k q = 0 := by
    have hq := congrFun hc q
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using hq
  have expand_orb (q : Krein16Idx) :
      c 0 * spinorOrbitVec 0 q + c 1 * spinorOrbitVec 1 q + c 2 * spinorOrbitVec 2 q +
      c 3 * spinorOrbitVec 3 q + c 4 * spinorOrbitVec 4 q + c 5 * spinorOrbitVec 5 q +
      c 6 * spinorOrbitVec 6 q = 0 := by
    have hsum : ∑ k : Fin 7, c k * spinorOrbitVec k q =
        c 0 * spinorOrbitVec 0 q + c 1 * spinorOrbitVec 1 q + c 2 * spinorOrbitVec 2 q +
        c 3 * spinorOrbitVec 3 q + c 4 * spinorOrbitVec 4 q + c 5 * spinorOrbitVec 5 q +
        c 6 * spinorOrbitVec 6 q := by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
      change c 0 * spinorOrbitVec 0 q + (c 1 * spinorOrbitVec 1 q + (c 2 * spinorOrbitVec 2 q +
        (c 3 * spinorOrbitVec 3 q + (c 4 * spinorOrbitVec 4 q +
          (c 5 * spinorOrbitVec 5 q + c 6 * spinorOrbitVec 6 q))))) = _
      ring
    rw [← hsum]
    exact eval_orb q
  have orb_simp :
      ∀ k : Fin 7, spinorOrbitVec k =
        match k with
        | 0 => -(vec4 ket1 ket1 ket0 ket0 + vec4 ket0 ket0 ket1 ket1)
        | 1 => -vec4 ket1 ket0 ket1 ket0 + vec4 ket0 ket1 ket0 ket1
        | 2 => -(vec4 ket1 ket0 ket0 ket1 + vec4 ket0 ket1 ket1 ket0)
        | 3 => vec4 ket1 ket1 ket0 ket0 - vec4 ket0 ket0 ket1 ket1
        | 4 => vec4 ket1 ket0 ket1 ket0 + vec4 ket0 ket1 ket0 ket1
        | 5 => vec4 ket1 ket0 ket0 ket1 - vec4 ket0 ket1 ket1 ket0
        | 6 => vec4 ket0 ket0 ket0 ket0 - vec4 ket1 ket1 ket1 ket1 := by
    intro k
    fin_cases k <;>
      simp only [spinorOrbitVec, spinorAct, LinearMap.coe_mk, AddHom.coe_mk, spinorOrbitGen,
        h14, h24, h34, h45, h46, h47, h15, psiPlus, ket0000, ket1111,
        Matrix.neg_mulVec, Matrix.mulVec_add, tensor4_mulVec, Matrix.one_mulVec,
        cl11Pos_mulVec_ket0, cl11Pos_mulVec_ket1, cl11Neg_mulVec_ket0, cl11Neg_mulVec_ket1,
        cl11Grad_mulVec_ket0, cl11Grad_mulVec_ket1, vec4_neg_2, vec4_neg_3, vec4_neg_4] <;>
      module
  have h1100 := expand_orb (idx4 1 1 0 0)
  have h0011 := expand_orb (idx4 0 0 1 1)
  have h1010 := expand_orb (idx4 1 0 1 0)
  have h0101 := expand_orb (idx4 0 1 0 1)
  have h1001 := expand_orb (idx4 1 0 0 1)
  have h0110 := expand_orb (idx4 0 1 1 0)
  have h0000 := expand_orb (idx4 0 0 0 0)
  simp only [orb_simp 0, orb_simp 1, orb_simp 2, orb_simp 3, orb_simp 4, orb_simp 5, orb_simp 6,
    idx4, Pi.neg_apply, Pi.add_apply, Pi.sub_apply, vec4,
    ket0_0, ket0_1, ket1_0, ket1_1] at h1100 h0011 h1010 h0101 h1001 h0110 h0000
  norm_num at h1100 h0011 h1010 h0101 h1001 h0110 h0000
  have hc0 : c 0 = 0 := by linarith
  have hc3 : c 3 = 0 := by linarith
  have hc1 : c 1 = 0 := by linarith
  have hc4 : c 4 = 0 := by linarith
  have hc2 : c 2 = 0 := by linarith
  have hc5 : c 5 = 0 := by linarith
  have hc6 : c 6 = 0 := by linarith
  intro k
  fin_cases k <;> assumption

theorem spinorAct_range_finrank_ge :
    7 ≤ Module.finrank ℝ (LinearMap.range spinorAct) := by
  have hle : Submodule.span ℝ (Set.range spinorOrbitVec) ≤ LinearMap.range spinorAct := by
    refine Submodule.span_le.mpr ?_
    rintro v ⟨k, rfl⟩
    exact ⟨⟨spinorOrbitGen k, spinorOrbitGen_mem_so34 k⟩, rfl⟩
  have hfr := Submodule.finrank_mono hle
  rw [finrank_span_eq_card spinorOrbitVec_linearIndependent, Fintype.card_fin] at hfr
  exact hfr

theorem spinorAct_ker_finrank_le :
    Module.finrank ℝ (LinearMap.ker spinorAct) ≤ 14 := by
  have hrk := LinearMap.finrank_range_add_finrank_ker spinorAct
  have h21 := so34Submodule_finrank_le
  have h7 := spinorAct_range_finrank_ge
  omega

def stabilizerSubmodule : Submodule ℝ Mat16 where
  carrier := { G : Mat16 |
    G ∈ cl44BivectorSubmodule ∧ G * cl44Gen 0 = cl44Gen 0 * G ∧ G.mulVec psiPlus = 0 }
  add_mem' {u v} hu hv :=
    ⟨add_mem hu.1 hv.1,
     by rw [add_mul, mul_add, hu.2.1, hv.2.1],
     by rw [Matrix.add_mulVec, hu.2.2, hv.2.2, add_zero]⟩
  zero_mem' := ⟨zero_mem _, by simp, by simp⟩
  smul_mem' r {u} hu :=
    ⟨smul_mem _ r hu.1,
     by rw [smul_mul_assoc, mul_smul_comm, hu.2.1],
     by rw [Matrix.smul_mulVec, hu.2.2, smul_zero]⟩

lemma mem_stabilizerSubmodule_iff_so34 (G : Mat16) :
    G ∈ stabilizerSubmodule ↔ G ∈ so34Submodule ∧ G.mulVec psiPlus = 0 := by
  change (G ∈ cl44BivectorSubmodule ∧ G * cl44Gen 0 = cl44Gen 0 * G ∧ G.mulVec psiPlus = 0) ↔ _
  constructor
  · rintro ⟨hB, hcomm, hpsi⟩
    exact ⟨(mem_so34_iff_comm_e0 hB).mpr hcomm, hpsi⟩
  · rintro ⟨hso, hpsi⟩
    exact ⟨so34Submodule_le_bivector hso, mem_so34_comm_e0 hso, hpsi⟩

theorem g2Submodule_eq_stabilizer : g2Submodule = stabilizerSubmodule := by
  have hle : g2Submodule ≤ stabilizerSubmodule := by
    refine Submodule.span_le.mpr ?_
    rintro G ⟨i, rfl⟩
    exact ⟨g2Basis_mem_bivector i, g2Basis_comm_e0 i, g2Basis_ann_psiPlus i⟩
  let e : LinearMap.ker spinorAct ≃ₗ[ℝ] stabilizerSubmodule :=
    { toFun := fun ⟨⟨G, hso⟩, hker⟩ =>
        ⟨G, (mem_stabilizerSubmodule_iff_so34 G).mpr ⟨hso, by simpa [spinorAct] using hker⟩⟩
      invFun := fun ⟨G, hst⟩ =>
        ⟨⟨G, ((mem_stabilizerSubmodule_iff_so34 G).mp hst).1⟩,
         by simpa [spinorAct] using ((mem_stabilizerSubmodule_iff_so34 G).mp hst).2⟩
      left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
      right_inv := fun ⟨_, _⟩ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hfin : Module.finrank ℝ stabilizerSubmodule ≤ Module.finrank ℝ g2Submodule := by
    rw [← e.finrank_eq, finrank_g2Submodule]
    exact spinorAct_ker_finrank_le
  exact Submodule.eq_of_le_of_finrank_le hle hfin

theorem g2Submodule_comm_mem {X Y : Mat16} (hX : X ∈ g2Submodule) (hY : Y ∈ g2Submodule) :
    X * Y - Y * X ∈ g2Submodule := by
  rw [g2Submodule_eq_stabilizer] at hX hY ⊢
  refine ⟨cl44BivectorSubmodule_comm_mem hX.1 hY.1, ?_, ?_⟩
  · have hx0 := hX.2.1
    have hy0 := hY.2.1
    calc
      (X * Y - Y * X) * cl44Gen 0
          = X * (Y * cl44Gen 0) - Y * (X * cl44Gen 0) := by noncomm_ring
      _ = X * (cl44Gen 0 * Y) - Y * (cl44Gen 0 * X) := by rw [hy0, hx0]
      _ = (X * cl44Gen 0) * Y - (Y * cl44Gen 0) * X := by noncomm_ring
      _ = (cl44Gen 0 * X) * Y - (cl44Gen 0 * Y) * X := by rw [hx0, hy0]
      _ = cl44Gen 0 * (X * Y - Y * X) := by noncomm_ring
  · rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hY.2.2, hX.2.2]
    simp

instance mat16LieRing : LieRing Mat16 := LieRing.ofAssociativeRing

def g2LieSubalgebra : LieSubalgebra ℝ Mat16 where
  toSubmodule := g2Submodule
  lie_mem' hX hY := g2Submodule_comm_mem hX hY

/-! ### Exact 5-Grading, Weights, Heisenberg Contact, Serre Syzygies, Jordan Jump & Centerlessness -/

def adOp (A B : Mat16) : Mat16 := A * B - B * A

lemma adOp_add_right (A B C : Mat16) : adOp A (B + C) = adOp A B + adOp A C := by
  dsimp [adOp]; noncomm_ring

lemma adOp_smul_right (A : Mat16) (r : ℝ) (B : Mat16) :
    adOp A (r • B) = r • adOp A B := by
  dsimp [adOp]; simp only [mul_smul_comm, smul_mul_assoc, smul_sub]

lemma adOp_add_left (A B C : Mat16) : adOp (A + B) C = adOp A C + adOp B C := by
  dsimp [adOp]; noncomm_ring

lemma adOp_smul_left (r : ℝ) (A B : Mat16) : adOp (r • A) B = r • adOp A B := by
  dsimp [adOp]; simp only [smul_mul_assoc, mul_smul_comm, smul_sub]

def g2WeightTheta : Fin 14 → ℝ
  | 0 => 2
  | 1 => 1 | 2 => 1 | 3 => 1 | 4 => 1
  | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0
  | 9 => -1 | 10 => -1 | 11 => -1 | 12 => -1
  | 13 => -2

def g2WeightAlpha : Fin 14 → ℝ
  | 0 => 0
  | 1 => 3 | 2 => -3 | 3 => -1 | 4 => 1
  | 5 => 0 | 6 => 0 | 7 => 2 | 8 => -2
  | 9 => -3 | 10 => 3 | 11 => 1 | 12 => -1
  | 13 => 0

private lemma m_tensor4_zero_1 (B C D : Mat2) : tensor4 0 B C D = 0 := by
  ext i j; simp [tensor4]
private lemma m_tensor4_zero_4 (A B C : Mat2) : tensor4 A B C 0 = 0 := by
  ext i j; simp [tensor4]
private lemma cl11Grad_eq_one_sub_two_proj1 :
    cl11Grad = (1 : Mat2) - (2 : ℝ) • cl11Proj1 := by
  apply ext_mat2 <;> norm_num [cl11Grad, cl11Proj1]

section G2BracketExpand

attribute [local simp] mul_add add_mul mul_sub sub_mul mul_neg neg_mul
  mul_smul_comm smul_mul_assoc smul_add smul_neg smul_smul
  m_tensor4_zero_1 tensor4_zero_2 tensor4_zero_3 m_tensor4_zero_4
  tensor4_neg_left tensor4_neg_2 tensor4_neg_3 tensor4_neg_right
  tensor4_add_left tensor4_add_2 tensor4_add_3 tensor4_add_right
  tensor4_sub_left tensor4_sub_2 tensor4_sub_3 tensor4_sub_right
  cl11Proj0_eq_one_sub

theorem HTheta_HAlpha_comm : adOp HThetaMat HAlphaMat = 0 := by
  dsimp [adOp, HThetaMat, HAlphaMat]
  simp
  module

theorem ad_HTheta_g2Basis (i : Fin 14) :
    adOp HThetaMat (g2Basis i) = g2WeightTheta i • g2Basis i := by
  fin_cases i <;>
    simp [adOp, g2Basis, g2WeightTheta, HThetaMat,
      ZPlus2Mat_norm, X1Mat_norm, X2Mat_norm, X3Mat_norm, X4Mat_norm,
      HAlphaMat, E0Mat_norm, F0Mat_norm, Y1Mat_norm, Y2Mat_norm, Y3Mat_norm,
      Y4Mat_norm, ZMinus2Mat_norm] <;>
    module

theorem ad_HAlpha_g2Basis (i : Fin 14) :
    adOp HAlphaMat (g2Basis i) = g2WeightAlpha i • g2Basis i := by
  fin_cases i <;>
    simp [adOp, g2Basis, g2WeightAlpha, HAlphaMat, HThetaMat,
      ZPlus2Mat_norm, X1Mat_norm, X2Mat_norm, X3Mat_norm, X4Mat_norm,
      E0Mat_norm, F0Mat_norm, Y1Mat_norm, Y2Mat_norm, Y3Mat_norm,
      Y4Mat_norm, ZMinus2Mat_norm] <;>
    module

theorem heisenberg_X1_X2 : adOp X1Mat X2Mat = ZPlus2Mat := by
  dsimp [adOp]
  rw [X1Mat_norm, X2Mat_norm, ZPlus2Mat_norm]
  simp [show cl11Grad = (1 : Mat2) - (2 : ℝ) • cl11Proj1 by
    apply ext_mat2 <;> norm_num [cl11Grad, cl11Proj1]]
  module

theorem heisenberg_X3_X4 : adOp X3Mat X4Mat = -(3 : ℝ) • ZPlus2Mat := by
  dsimp [adOp]
  rw [X3Mat_norm, X4Mat_norm, ZPlus2Mat_norm]
  simp [show cl11Grad = (1 : Mat2) - (2 : ℝ) • cl11Proj1 by
    apply ext_mat2 <;> norm_num [cl11Grad, cl11Proj1]]
  module

theorem heisenberg_X4_X3 : adOp X4Mat X3Mat = (3 : ℝ) • ZPlus2Mat := by
  have hanti : adOp X4Mat X3Mat = -adOp X3Mat X4Mat := by
    dsimp [adOp]; abel
  rw [hanti, heisenberg_X3_X4, neg_smul, neg_neg]

theorem ZPlus2Mat_ne_zero : ZPlus2Mat ≠ 0 := by
  intro h
  have h1001 := congrArg (fun M : Mat16 => M (idx4 0 1 0 0) (idx4 0 0 0 1)) h
  simp only [ZPlus2Mat_norm, idx4, tensor4_apply, Matrix.zero_apply] at h1001
  norm_num [Matrix.one_apply, cl11Grad, cl11Up, cl11Down] at h1001

theorem chevalley_E0_F0 : adOp E0Mat F0Mat = HAlphaMat := by
  dsimp [adOp]
  rw [E0Mat_norm, F0Mat_norm, HAlphaMat]
  simp
  module

theorem chevalley_ZPlus2_ZMinus2 : adOp ZPlus2Mat ZMinus2Mat = HThetaMat := by
  dsimp [adOp]
  rw [ZPlus2Mat_norm, ZMinus2Mat_norm, HThetaMat]
  simp

theorem chevalley_X2_Y2 : adOp X2Mat Y2Mat = (1 / 2 : ℝ) • (HThetaMat - HAlphaMat) := by
  dsimp [adOp]
  rw [X2Mat_norm, Y2Mat_norm, HThetaMat, HAlphaMat]
  simp
  module

theorem ad_E0_Y2_zero : adOp E0Mat Y2Mat = 0 := by
  dsimp [adOp]
  rw [E0Mat_norm, Y2Mat_norm]
  simp

theorem ad_X2_F0_zero : adOp X2Mat F0Mat = 0 := by
  dsimp [adOp]
  rw [X2Mat_norm, F0Mat_norm]
  simp

theorem ad_X2_sq_E0_zero : adOp X2Mat (adOp X2Mat E0Mat) = 0 := by
  have h1 : adOp X2Mat E0Mat = -X3Mat := by
    dsimp [adOp]
    rw [X2Mat_norm, E0Mat_norm, X3Mat_norm]
    simp [cl11Grad_eq_one_sub_two_proj1]
    module
  rw [h1, adOp, X2Mat_norm, X3Mat_norm]
  simp

theorem ad_E0_cube_X2 : adOp E0Mat (adOp E0Mat (adOp E0Mat X2Mat)) = (6 : ℝ) • X1Mat := by
  have h1 : adOp E0Mat X2Mat = X3Mat := by
    dsimp [adOp]
    rw [E0Mat_norm, X2Mat_norm, X3Mat_norm]
    simp [cl11Grad_eq_one_sub_two_proj1]
    module
  have h2 : adOp E0Mat X3Mat = (-2 : ℝ) • X4Mat := by
    dsimp [adOp]
    rw [E0Mat_norm, X3Mat_norm, X4Mat_norm]
    simp
    module
  have h3 : adOp E0Mat X4Mat = (-3 : ℝ) • X1Mat := by
    dsimp [adOp]
    rw [E0Mat_norm, X4Mat_norm, X1Mat_norm]
    simp
    module
  rw [h1, h2, adOp_smul_right, h3, ← smul_assoc]
  norm_num

theorem ad_E0_four_X2_zero :
    adOp E0Mat (adOp E0Mat (adOp E0Mat (adOp E0Mat X2Mat))) = 0 := by
  have h4 : adOp E0Mat X1Mat = 0 := by
    dsimp [adOp]
    rw [E0Mat_norm, X1Mat_norm]
    simp
  rw [ad_E0_cube_X2, adOp_smul_right, h4, smul_zero]

theorem ad_Y2_sq_F0_zero : adOp Y2Mat (adOp Y2Mat F0Mat) = 0 := by
  have h1 : adOp Y2Mat F0Mat = -Y3Mat := by
    dsimp [adOp]
    rw [Y2Mat_norm, F0Mat_norm, Y3Mat_norm]
    simp [cl11Grad_eq_one_sub_two_proj1]
    module
  rw [h1, adOp, Y2Mat_norm, Y3Mat_norm]
  simp

theorem ad_F0_four_Y2_zero :
    adOp F0Mat (adOp F0Mat (adOp F0Mat (adOp F0Mat Y2Mat))) = 0 := by
  have h1 : adOp F0Mat Y2Mat = Y3Mat := by
    dsimp [adOp]
    rw [F0Mat_norm, Y2Mat_norm, Y3Mat_norm]
    simp [cl11Grad_eq_one_sub_two_proj1]
    module
  have h2 : adOp F0Mat Y3Mat = (2 : ℝ) • Y4Mat := by
    dsimp [adOp]
    rw [F0Mat_norm, Y3Mat_norm, Y4Mat_norm]
    simp
    module
  have h3 : adOp F0Mat Y4Mat = (-3 : ℝ) • Y1Mat := by
    dsimp [adOp]
    rw [F0Mat_norm, Y4Mat_norm, Y1Mat_norm]
    simp
    module
  have h4 : adOp F0Mat Y1Mat = 0 := by
    dsimp [adOp]
    rw [F0Mat_norm, Y1Mat_norm]
    simp
  simp only [h1, h2, h3, h4, adOp_smul_right, smul_zero]

end G2BracketExpand

lemma jordanAnticomm_X1_X2 :
    X1Mat * X2Mat + X2Mat * X1Mat = tensor4 1 cl11Up 1 cl11Down := by
  rw [X1Mat_norm, X2Mat_norm]
  simp only [tensor4_mul, mul_one, one_mul, cl11Down_mul_up, cl11Up_mul_down]
  rw [← tensor4_add_3, cl11Proj0_add_proj1]

lemma jordan_X1_X2_krein_symm :
    (X1Mat * X2Mat + X2Mat * X1Mat)ᵀ * kreinMetric88 =
      kreinMetric88 * (X1Mat * X2Mat + X2Mat * X1Mat) := by
  rw [jordanAnticomm_X1_X2]
  dsimp [kreinMetric88]
  rw [tensor4_transpose, Matrix.transpose_one, cl11Up_transpose, cl11Down_transpose]
  simp

lemma jordan_X1_X2_ne_zero : X1Mat * X2Mat + X2Mat * X1Mat ≠ 0 := by
  intro h
  have h01 := congrArg (fun M : Mat16 => M (idx4 0 1 0 0) (idx4 0 0 0 1)) h
  rw [jordanAnticomm_X1_X2] at h01
  simp only [idx4, tensor4_apply, Matrix.one_apply, Matrix.zero_apply] at h01
  norm_num [cl11Up, cl11Down] at h01

theorem jordan_X1_X2_not_mem_bivector :
    X1Mat * X2Mat + X2Mat * X1Mat ∉ cl44BivectorSubmodule := by
  intro hmem
  have hskew := cl44BivectorSubmodule_krein_skew hmem
  have hsymm := jordan_X1_X2_krein_symm
  have h2 : (2 : ℝ) • (kreinMetric88 * (X1Mat * X2Mat + X2Mat * X1Mat)) = 0 := by
    calc
      (2 : ℝ) • (kreinMetric88 * (X1Mat * X2Mat + X2Mat * X1Mat))
          = kreinMetric88 * (X1Mat * X2Mat + X2Mat * X1Mat) +
              kreinMetric88 * (X1Mat * X2Mat + X2Mat * X1Mat) := two_smul ℝ _
      _ = (X1Mat * X2Mat + X2Mat * X1Mat)ᵀ * kreinMetric88 +
              kreinMetric88 * (X1Mat * X2Mat + X2Mat * X1Mat) := by
            nth_rw 1 [← hsymm]
      _ = 0 := hskew
  have hkm : kreinMetric88 * (X1Mat * X2Mat + X2Mat * X1Mat) = 0 := by
    rcases smul_eq_zero.mp h2 with h2z | hkm'
    · norm_num at h2z
    · exact hkm'
  have hzero : X1Mat * X2Mat + X2Mat * X1Mat = 0 := by
    calc
      X1Mat * X2Mat + X2Mat * X1Mat
          = (kreinMetric88 * kreinMetric88) * (X1Mat * X2Mat + X2Mat * X1Mat) := by
            rw [kreinMetric88_sq, one_mul]
      _ = kreinMetric88 * (kreinMetric88 * (X1Mat * X2Mat + X2Mat * X1Mat)) := mul_assoc _ _ _
      _ = 0 := by rw [hkm, mul_zero]
  exact jordan_X1_X2_ne_zero hzero

theorem jordan_X1_X2_not_mem_g2 :
    X1Mat * X2Mat + X2Mat * X1Mat ∉ g2Submodule := by
  intro hmem
  rw [g2Submodule_eq_stabilizer] at hmem
  exact jordan_X1_X2_not_mem_bivector hmem.1

theorem g2_centerless :
    ∀ Z ∈ g2Submodule, (∀ X ∈ g2Submodule, adOp Z X = 0) → Z = 0 := by
  intro Z hZ hcent
  have hsp : Z ∈ Submodule.span ℝ (Set.range g2Basis) := hZ
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hsp
  have hbasis_mem (i : Fin 14) : g2Basis i ∈ g2Submodule := Submodule.subset_span ⟨i, rfl⟩
  have h_sum_eq :
      (c.sum fun i a => a • g2Basis i) = ∑ i : Fin 14, c i • g2Basis i := by
    rw [Finsupp.sum_fintype]
    intro _; simp
  rw [h_sum_eq] at hcent ⊢
  have had_theta : ∑ i : Fin 14, (c i * g2WeightTheta i) • g2Basis i = 0 := by
    have hZ5 : adOp (∑ i : Fin 14, c i • g2Basis i) HThetaMat = 0 :=
      hcent (g2Basis 5) (hbasis_mem 5)
    have hH : adOp HThetaMat (∑ i : Fin 14, c i • g2Basis i) = 0 := by
      have hflip : adOp HThetaMat (∑ i : Fin 14, c i • g2Basis i) =
          -adOp (∑ i : Fin 14, c i • g2Basis i) HThetaMat := by
        dsimp [adOp]; abel
      rw [hflip, hZ5, neg_zero]
    rw [← hH]
    have hlin : ∀ (s : Finset (Fin 14)) (f : Fin 14 → Mat16),
        adOp HThetaMat (∑ i ∈ s, f i) = ∑ i ∈ s, adOp HThetaMat (f i) := by
      intro s f
      induction s using Finset.induction with
      | empty => simp [adOp]
      | insert a s ha ih =>
        rw [Finset.sum_insert ha, adOp_add_right, ih, Finset.sum_insert ha]
    rw [hlin]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [adOp_smul_right, ad_HTheta_g2Basis i, smul_smul]
  have hlin_c := (Fintype.linearIndependent_iff.mp g2Basis_linearIndependent)
    (fun i => c i * g2WeightTheta i) had_theta
  have hc0 : c 0 = 0 := by have := hlin_c 0; norm_num [g2WeightTheta] at this; exact this
  have hc1 : c 1 = 0 := by have := hlin_c 1; norm_num [g2WeightTheta] at this; exact this
  have hc2 : c 2 = 0 := by have := hlin_c 2; norm_num [g2WeightTheta] at this; exact this
  have hc3 : c 3 = 0 := by have := hlin_c 3; norm_num [g2WeightTheta] at this; exact this
  have hc4 : c 4 = 0 := by have := hlin_c 4; norm_num [g2WeightTheta] at this; exact this
  have hc9 : c 9 = 0 := by have := hlin_c 9; norm_num [g2WeightTheta] at this; exact this
  have hc10 : c 10 = 0 := by have := hlin_c 10; norm_num [g2WeightTheta] at this; exact this
  have hc11 : c 11 = 0 := by have := hlin_c 11; norm_num [g2WeightTheta] at this; exact this
  have hc12 : c 12 = 0 := by have := hlin_c 12; norm_num [g2WeightTheta] at this; exact this
  have hc13 : c 13 = 0 := by have := hlin_c 13; norm_num [g2WeightTheta] at this; exact this
  have had_alpha : ∑ i : Fin 14, (c i * g2WeightAlpha i) • g2Basis i = 0 := by
    have hZ6 : adOp (∑ i : Fin 14, c i • g2Basis i) HAlphaMat = 0 :=
      hcent (g2Basis 6) (hbasis_mem 6)
    have hH : adOp HAlphaMat (∑ i : Fin 14, c i • g2Basis i) = 0 := by
      have hflip : adOp HAlphaMat (∑ i : Fin 14, c i • g2Basis i) =
          -adOp (∑ i : Fin 14, c i • g2Basis i) HAlphaMat := by
        dsimp [adOp]; abel
      rw [hflip, hZ6, neg_zero]
    rw [← hH]
    have hlin : ∀ (s : Finset (Fin 14)) (f : Fin 14 → Mat16),
        adOp HAlphaMat (∑ i ∈ s, f i) = ∑ i ∈ s, adOp HAlphaMat (f i) := by
      intro s f
      induction s using Finset.induction with
      | empty => simp [adOp]
      | insert a s ha ih =>
        rw [Finset.sum_insert ha, adOp_add_right, ih, Finset.sum_insert ha]
    rw [hlin]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [adOp_smul_right, ad_HAlpha_g2Basis i, smul_smul]
  have hlin_a := (Fintype.linearIndependent_iff.mp g2Basis_linearIndependent)
    (fun i => c i * g2WeightAlpha i) had_alpha
  have hc7 : c 7 = 0 := by have := hlin_a 7; norm_num [g2WeightAlpha] at this; exact this
  have hc8 : c 8 = 0 := by have := hlin_a 8; norm_num [g2WeightAlpha] at this; exact this
  have hcartan : ∑ i : Fin 14, c i • g2Basis i = c 5 • HThetaMat + c 6 • HAlphaMat := by
    have hterm (i : Fin 14) :
        c i • g2Basis i =
          (if i = 5 then c 5 • HThetaMat else 0) +
          (if i = 6 then c 6 • HAlphaMat else 0) := by
      fin_cases i <;>
        simp [g2Basis, hc0, hc1, hc2, hc3, hc4, hc7, hc8, hc9, hc10, hc11, hc12, hc13]
    simp only [hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [hcartan] at hcent ⊢
  have hE0 : adOp (c 5 • HThetaMat + c 6 • HAlphaMat) E0Mat = 0 := hcent (g2Basis 7) (hbasis_mem 7)
  have hX1 : adOp (c 5 • HThetaMat + c 6 • HAlphaMat) X1Mat = 0 := hcent (g2Basis 1) (hbasis_mem 1)
  have hE0_val : adOp (c 5 • HThetaMat + c 6 • HAlphaMat) E0Mat = ((2 : ℝ) * c 6) • E0Mat := by
    rw [adOp_add_left, adOp_smul_left, adOp_smul_left]
    have h5 := ad_HTheta_g2Basis 7
    have h6 := ad_HAlpha_g2Basis 7
    simp only [g2Basis, g2WeightTheta, g2WeightAlpha, zero_smul] at h5 h6
    rw [h5, h6, smul_zero, zero_add, smul_smul, mul_comm (c 6) 2]
  have hE0_nz : E0Mat ≠ 0 := by
    have hi := g2Basis_linearIndependent.ne_zero 7
    simpa [g2Basis] using hi
  have hc6 : c 6 = 0 := by
    rw [hE0_val] at hE0
    rcases smul_eq_zero.mp hE0 with h2c | h0
    · linarith
    · exact absurd h0 hE0_nz
  have hX1_val : adOp (c 5 • HThetaMat + c 6 • HAlphaMat) X1Mat = c 5 • X1Mat := by
    rw [hc6, zero_smul, add_zero, adOp_smul_left]
    have h5 := ad_HTheta_g2Basis 1
    simp only [g2Basis, g2WeightTheta, one_smul] at h5
    rw [h5]
  have hX1_nz : X1Mat ≠ 0 := by
    have hi := g2Basis_linearIndependent.ne_zero 1
    simpa [g2Basis] using hi
  have hc5 : c 5 = 0 := by
    rw [hX1_val] at hX1
    rcases smul_eq_zero.mp hX1 with hc5z | h0
    · exact hc5z
    · exact absurd h0 hX1_nz
  rw [hc5, hc6, zero_smul, zero_smul, add_zero]

/-! ## Section IV (`PHASE IV`): Witt's Free Lie Algebra Formula & Pigeonhole Obstruction -/

def wittNecklaceInt (k d : ℕ) : ℤ :=
  ∑ m ∈ d.divisors, (ArithmeticFunction.moebius (d / m) : ℤ) * (k : ℤ) ^ m

def wittLieDim (k d : ℕ) : ℕ :=
  (wittNecklaceInt k d / (d : ℤ)).toNat

private lemma moebius_one_val : ArithmeticFunction.moebius 1 = 1 :=
  ArithmeticFunction.moebius_apply_one

private lemma moebius_two_val : ArithmeticFunction.moebius 2 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private lemma moebius_three_val : ArithmeticFunction.moebius 3 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private lemma moebius_four_val : ArithmeticFunction.moebius 4 = 0 := by
  refine ArithmeticFunction.moebius_eq_zero_of_not_squarefree ?_
  intro hsq
  have h24 : 2 * 2 ∣ 4 := by norm_num
  have hu := hsq 2 h24
  norm_num [Nat.isUnit_iff] at hu

private lemma moebius_five_val : ArithmeticFunction.moebius 5 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private lemma moebius_six_val : ArithmeticFunction.moebius 6 = 1 := by
  have h6 : (6 : ℕ) = 2 * 3 := by norm_num
  rw [h6, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    moebius_two_val, moebius_three_val]
  norm_num

private lemma divisors_one : Nat.divisors 1 = {1} := by decide
private lemma divisors_two : Nat.divisors 2 = {1, 2} := by decide
private lemma divisors_three : Nat.divisors 3 = {1, 3} := by decide
private lemma divisors_four : Nat.divisors 4 = {1, 2, 4} := by decide
private lemma divisors_five : Nat.divisors 5 = {1, 5} := by decide
private lemma divisors_six : Nat.divisors 6 = {1, 2, 3, 6} := by decide

theorem wittLieDim_2_1 : wittLieDim 2 1 = 2 := by
  dsimp [wittLieDim, wittNecklaceInt]
  rw [divisors_one, Finset.sum_singleton]
  norm_num [moebius_one_val]

theorem wittLieDim_2_2 : wittLieDim 2 2 = 1 := by
  dsimp [wittLieDim, wittNecklaceInt]
  rw [divisors_two, Finset.sum_pair (by decide)]
  norm_num [moebius_two_val, moebius_one_val]

theorem wittLieDim_2_3 : wittLieDim 2 3 = 2 := by
  dsimp [wittLieDim, wittNecklaceInt]
  rw [divisors_three, Finset.sum_pair (by decide)]
  norm_num [moebius_three_val, moebius_one_val]

theorem wittLieDim_2_4 : wittLieDim 2 4 = 3 := by
  dsimp [wittLieDim, wittNecklaceInt]
  rw [divisors_four, Finset.sum_insert (by decide), Finset.sum_pair (by decide)]
  norm_num [moebius_four_val, moebius_two_val, moebius_one_val]

theorem wittLieDim_2_5 : wittLieDim 2 5 = 6 := by
  dsimp [wittLieDim, wittNecklaceInt]
  rw [divisors_five, Finset.sum_pair (by decide)]
  norm_num [moebius_five_val, moebius_one_val]

theorem wittLieDim_2_6 : wittLieDim 2 6 = 9 := by
  dsimp [wittLieDim, wittNecklaceInt]
  rw [divisors_six, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_pair (by decide)]
  norm_num [moebius_six_val, moebius_three_val, moebius_two_val, moebius_one_val]

theorem witt_sum_1_to_5 : ∑ d ∈ Finset.Icc 1 5, wittLieDim 2 d = 14 := by
  have hset : Finset.Icc 1 5 = {1, 2, 3, 4, 5} := by decide
  rw [hset, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    wittLieDim_2_1, wittLieDim_2_2, wittLieDim_2_3, wittLieDim_2_4, wittLieDim_2_5]
  norm_num

theorem witt_sum_1_to_6 : ∑ d ∈ Finset.Icc 1 6, wittLieDim 2 d = 23 := by
  have hset : Finset.Icc 1 6 = insert 6 (Finset.Icc 1 5) := by decide
  rw [hset, Finset.sum_insert (by decide), wittLieDim_2_6, witt_sum_1_to_5]

theorem witt_pigeonhole_no_injective_linearMap
    {L : Type*} [AddCommGroup L] [Module ℝ L]
    (hL : (∑ d ∈ Finset.Icc 1 6, wittLieDim 2 d) ≤ Module.finrank ℝ L) :
    ¬ ∃ f : L →ₗ[ℝ] g2Submodule, Function.Injective f := by
  rintro ⟨f, hf⟩
  have hle := LinearMap.finrank_le_finrank_of_injective hf
  rw [finrank_g2Submodule] at hle
  rw [witt_sum_1_to_6] at hL
  omega

theorem witt_pigeonhole_fin23_no_injective_linearMap :
    ¬ ∃ f : (Fin (∑ d ∈ Finset.Icc 1 6, wittLieDim 2 d) → ℝ) →ₗ[ℝ] g2Submodule,
        Function.Injective f := by
  refine witt_pigeonhole_no_injective_linearMap ?_
  rw [Module.finrank_pi, Fintype.card_fin]

/-! ## Section V (`PHASE V — COAGULA`): 15-Node Graded Acyclic Causal Poset & Epistemic Synthesis -/

inductive CausalArchetype where
  | Delta0
  | A0
  | C8
  | K_TT
  | Tau
  | Gamma_SS
  | G
  | Omega
  | Phi_5
  | Heis
  | J_cl
  | W_23
  | H
  | E
  | Xi_top
  deriving DecidableEq, Repr

private def causalToFin : CausalArchetype → Fin 15
  | .Delta0 => 0 | .A0 => 1 | .C8 => 2 | .K_TT => 3 | .Tau => 4
  | .Gamma_SS => 5 | .G => 6 | .Omega => 7 | .Phi_5 => 8 | .Heis => 9
  | .J_cl => 10 | .W_23 => 11 | .H => 12 | .E => 13 | .Xi_top => 14

private def finToCausal : Fin 15 → CausalArchetype
  | 0 => .Delta0 | 1 => .A0 | 2 => .C8 | 3 => .K_TT | 4 => .Tau
  | 5 => .Gamma_SS | 6 => .G | 7 => .Omega | 8 => .Phi_5 | 9 => .Heis
  | 10 => .J_cl | 11 => .W_23 | 12 => .H | 13 => .E | 14 => .Xi_top

private lemma causal_left_inv (a : CausalArchetype) : finToCausal (causalToFin a) = a := by
  cases a <;> rfl

private lemma causal_right_inv (i : Fin 15) : causalToFin (finToCausal i) = i := by
  fin_cases i <;> rfl

def causalArchetypeEquivFin15 : CausalArchetype ≃ Fin 15 where
  toFun := causalToFin
  invFun := finToCausal
  left_inv := causal_left_inv
  right_inv := causal_right_inv

instance : Fintype CausalArchetype :=
  Fintype.ofEquiv (Fin 15) causalArchetypeEquivFin15.symm

theorem card_causalArchetype : Fintype.card CausalArchetype = 15 := by
  rw [Fintype.card_congr causalArchetypeEquivFin15, Fintype.card_fin]

def archetypeGrade : CausalArchetype → ℕ
  | .Delta0 => 0
  | .A0 | .C8 | .Tau | .Gamma_SS => 1
  | .K_TT | .G => 2
  | .Omega => 3
  | .Phi_5 => 4
  | .Heis | .J_cl | .W_23 => 5
  | .H | .E => 6
  | .Xi_top => 7

def coversBool : CausalArchetype → CausalArchetype → Bool
  | .Delta0, .A0 | .Delta0, .C8 | .Delta0, .Tau | .Delta0, .Gamma_SS => true
  | .C8, .K_TT | .C8, .G | .A0, .G => true
  | .K_TT, .Omega | .G, .Omega | .Tau, .Omega | .Gamma_SS, .Omega => true
  | .Omega, .Phi_5 => true
  | .Phi_5, .Heis | .Phi_5, .J_cl | .Phi_5, .W_23 => true
  | .Heis, .H | .J_cl, .H | .W_23, .H => true
  | .Heis, .E | .J_cl, .E | .W_23, .E => true
  | .H, .Xi_top | .E, .Xi_top => true
  | _, _ => false

def Covers (u v : CausalArchetype) : Prop := coversBool u v = true

def leBool (u v : CausalArchetype) : Bool :=
  (u == v) || (u == .Delta0) || (v == .Xi_top) ||
  (1 ≤ archetypeGrade u && archetypeGrade u ≤ 2 && 3 ≤ archetypeGrade v) ||
  (3 ≤ archetypeGrade u && archetypeGrade u < archetypeGrade v) ||
  (u == .C8 && (v == .K_TT || v == .G)) ||
  (u == .A0 && v == .G)

private lemma leBool_refl (a : CausalArchetype) : leBool a a = true := by
  cases a <;> rfl

private lemma leBool_eq_or_grade_lt {a b : CausalArchetype} (h : leBool a b = true) :
    a = b ∨ archetypeGrade a < archetypeGrade b := by
  by_cases heq : a = b
  · exact Or.inl heq
  · right
    have hneq : (a == b) = false := beq_false_of_ne heq
    simp only [leBool, hneq, Bool.false_or] at h
    cases a <;> cases b <;> simp_all [archetypeGrade]

private lemma leBool_antisymm {a b : CausalArchetype}
    (hab : leBool a b = true) (hba : leBool b a = true) : a = b := by
  rcases leBool_eq_or_grade_lt hab with rfl | hlt1
  · rfl
  · rcases leBool_eq_or_grade_lt hba with rfl | hlt2
    · rfl
    · omega

private lemma leBool_grade_le {a b : CausalArchetype} (h : leBool a b = true) :
    archetypeGrade a ≤ archetypeGrade b := by
  rcases leBool_eq_or_grade_lt h with rfl | hlt
  · exact le_rfl
  · exact Nat.le_of_lt hlt

private lemma grade_zero_eq_delta0 {a : CausalArchetype} (h : archetypeGrade a = 0) :
    a = .Delta0 := by
  cases a <;> first | rfl | (simp [archetypeGrade] at h)

private lemma leBool_of_delta0 (c : CausalArchetype) : leBool .Delta0 c = true := by
  cases c <;> rfl

private lemma leBool_of_xi_top (a : CausalArchetype) : leBool a .Xi_top = true := by
  cases a <;> rfl

private lemma leBool_trans {a b c : CausalArchetype}
    (hab : leBool a b = true) (hbc : leBool b c = true) : leBool a c = true := by
  by_cases ha0 : a = .Delta0
  · subst ha0; exact leBool_of_delta0 c
  by_cases hc7 : c = .Xi_top
  · subst hc7; exact leBool_of_xi_top a
  by_cases hab_eq : a = b
  · subst hab_eq; exact hbc
  by_cases hbc_eq : b = c
  · subst hbc_eq; exact hab
  have ha_pos : 1 ≤ archetypeGrade a := by
    rcases Nat.eq_zero_or_pos (archetypeGrade a) with h0 | hp
    · exact absurd (grade_zero_eq_delta0 h0) ha0
    · exact hp
  have hga : archetypeGrade a < archetypeGrade b := by
    rcases leBool_eq_or_grade_lt hab with rfl | hlt
    · exact absurd rfl hab_eq
    · exact hlt
  have hgb : archetypeGrade b < archetypeGrade c := by
    rcases leBool_eq_or_grade_lt hbc with rfl | hlt
    · exact absurd rfl hbc_eq
    · exact hlt
  have hgc_le : archetypeGrade c ≤ 7 := by
    cases c <;> simp [archetypeGrade]
  have hga_lt_c : archetypeGrade a < archetypeGrade c := lt_trans hga hgb
  by_cases hc3 : 3 ≤ archetypeGrade c
  · by_cases ha2 : archetypeGrade a ≤ 2
    · simp [leBool, ha_pos, ha2, hc3]
    · have ha3 : 3 ≤ archetypeGrade a := by omega
      simp [leBool, ha3, hga_lt_c]
  · have hgb2 : archetypeGrade b = 2 := by omega
    have hga1 : archetypeGrade a = 1 := by omega
    have hgc2 : archetypeGrade c = 2 := by omega
    omega

instance : PartialOrder CausalArchetype where
  le u v := leBool u v = true
  lt u v := leBool u v = true ∧ u ≠ v
  le_refl u := leBool_refl u
  le_trans _ _ _ h1 h2 := leBool_trans h1 h2
  le_antisymm _ _ h1 h2 := leBool_antisymm h1 h2
  lt_iff_le_not_ge u v := by
    constructor
    · rintro ⟨hle, hne⟩
      exact ⟨hle, fun hba => hne (leBool_antisymm hle hba)⟩
    · rintro ⟨hle, hnot⟩
      refine ⟨hle, ?_⟩
      rintro rfl
      exact hnot (leBool_refl u)

private lemma le_iff_leBool (u v : CausalArchetype) : u ≤ v ↔ leBool u v = true := Iff.rfl

private lemma lt_iff_leBool_ne (u v : CausalArchetype) : u < v ↔ leBool u v = true ∧ u ≠ v :=
  Iff.rfl

instance : DecidableRel (α := CausalArchetype) (· ≤ ·) := fun u v =>
  inferInstanceAs (Decidable (leBool u v = true))

instance : DecidableRel (α := CausalArchetype) (· < ·) := fun u v =>
  inferInstanceAs (Decidable (leBool u v = true ∧ u ≠ v))

instance : DecidableRel Covers := fun u v =>
  inferInstanceAs (Decidable (coversBool u v = true))

theorem card_causal_covers :
    Fintype.card { p : CausalArchetype × CausalArchetype // Covers p.1 p.2 } = 23 := by
  decide

theorem covers_imp_lt {u v : CausalArchetype} (h : Covers u v) : u < v := by
  revert u v h
  decide

theorem strict_grade_monotonicity {u v : CausalArchetype} (h : Covers u v) :
    archetypeGrade u < archetypeGrade v := by
  revert u v h
  decide

theorem lt_grade_monotonicity {u v : CausalArchetype} (h : u < v) :
    archetypeGrade u < archetypeGrade v := by
  rcases leBool_eq_or_grade_lt h.1 with rfl | hlt
  · exact absurd rfl h.2
  · exact hlt

theorem covers_transitively_reduced {u v : CausalArchetype} (h : Covers u v) (w : CausalArchetype) :
    ¬ (u < w ∧ w < v) := by
  revert u v w h
  decide

theorem bot_le_all (a : CausalArchetype) : CausalArchetype.Delta0 ≤ a :=
  leBool_of_delta0 a

theorem all_le_top (a : CausalArchetype) : a ≤ CausalArchetype.Xi_top :=
  leBool_of_xi_top a

theorem antichain_K_TT_G_Tau_Gamma_SS :
    IsAntichain (· ≤ ·) ({CausalArchetype.K_TT, .G, .Tau, .Gamma_SS} : Set CausalArchetype) := by
  intro x hx y hy hne hle
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl
  all_goals first
    | exact absurd rfl hne
    | exact absurd hle (by decide)

theorem antichain_A0_Tau_Gamma_SS :
    IsAntichain (· ≤ ·) ({CausalArchetype.A0, .Tau, .Gamma_SS} : Set CausalArchetype) := by
  intro x hx y hy hne hle
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  all_goals first
    | exact absurd rfl hne
    | exact absurd hle (by decide)

theorem xi_top_isLUB_H_E :
    IsLUB ({CausalArchetype.H, .E} : Set CausalArchetype) CausalArchetype.Xi_top := by
  refine ⟨?_, ?_⟩
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> exact all_le_top _
  · intro u hu
    have huH : CausalArchetype.H ≤ u := hu (Set.mem_insert _ _)
    have huE : CausalArchetype.E ≤ u := hu (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    cases u with
    | Xi_top => exact le_refl _
    | _ => first | exact absurd huH (by decide) | exact absurd huE (by decide)

def archetypeClaim : CausalArchetype → Prop
  | .Delta0 => cl11Pos * cl11Neg ≠ cl11Neg * cl11Pos
  | .A0 =>
      (∀ x y z : Mat16,
        (x * (y * z - z * y) - (y * z - z * y) * x) -
        ((x * y - y * x) * z - z * (x * y - y * x)) -
        (y * (x * z - z * x) - (x * z - z * x) * y) = 0) ∧
      (∀ X Y : Mat2, endomorphismLeibnizDefect gradInnerDeriv X Y = 0) ∧
      endomorphismLeibnizDefect (gradInnerDeriv.comp gradInnerDeriv) cl11Up cl11Down ≠ 0
  | .C8 =>
      gamma44 * gamma44 = (1 : Mat16) ∧ Matrix.trace gamma44 = 0 ∧
      (∀ a : Fin 8, gamma44 * cl44Gen a + cl44Gen a * gamma44 = 0)
  | .K_TT =>
      kreinMetric88ᵀ = kreinMetric88 ∧ kreinMetric88 * kreinMetric88 = (1 : Mat16) ∧
      (∀ u : Krein16Idx → ℝ, (∀ v : Krein16Idx → ℝ, kreinInner16 u v = 0) ↔ u = 0)
  | .Tau =>
      trialityCycle * trialityCycle * trialityCycle = (1 : Mat4) ∧
      trialitySpinSwap * trialityCycle * trialitySpinSwap = trialityCycle * trialityCycle ∧
      Module.finrank ℝ trialityFixedCartan = 2
  | .Gamma_SS =>
      gamma44.mulVec psiPlus = psiPlus ∧
      kreinInner16 psiPlus psiPlus = 2 ∧
      kreinInner16 psiMinus psiMinus = -2
  | .G =>
      (∀ B ∈ cl44BivectorSubmodule, B * gamma44 = gamma44 * B) ∧
      (∀ B ∈ cl44BivectorSubmodule, Bᵀ * kreinMetric88 + kreinMetric88 * B = 0) ∧
      (∀ X ∈ cl44BivectorSubmodule, ∀ Y ∈ cl44BivectorSubmodule,
        X * Y - Y * X ∈ cl44BivectorSubmodule)
  | .Omega =>
      Module.finrank ℝ so34Submodule ≤ 21 ∧
      7 ≤ Module.finrank ℝ (LinearMap.range spinorAct) ∧
      Module.finrank ℝ (LinearMap.ker spinorAct) ≤ 14
  | .Phi_5 =>
      g2Submodule = stabilizerSubmodule ∧
      Module.finrank ℝ g2Submodule = 14 ∧
      (∀ i : Fin 14, adOp HThetaMat (g2Basis i) = g2WeightTheta i • g2Basis i ∧
        adOp HAlphaMat (g2Basis i) = g2WeightAlpha i • g2Basis i) ∧
      (∀ Z ∈ g2Submodule, (∀ X ∈ g2Submodule, adOp Z X = 0) → Z = 0)
  | .Heis =>
      adOp X1Mat X2Mat = ZPlus2Mat ∧
      adOp X4Mat X3Mat = (3 : ℝ) • ZPlus2Mat ∧
      ZPlus2Mat ≠ 0 ∧
      adOp X2Mat (adOp X2Mat E0Mat) = 0 ∧
      adOp E0Mat (adOp E0Mat (adOp E0Mat (adOp E0Mat X2Mat))) = 0 ∧
      adOp Y2Mat (adOp Y2Mat F0Mat) = 0 ∧
      adOp F0Mat (adOp F0Mat (adOp F0Mat (adOp F0Mat Y2Mat))) = 0
  | .J_cl =>
      (X1Mat * X2Mat + X2Mat * X1Mat)ᵀ * kreinMetric88 =
        kreinMetric88 * (X1Mat * X2Mat + X2Mat * X1Mat) ∧
      (X1Mat * X2Mat + X2Mat * X1Mat) ∉ cl44BivectorSubmodule ∧
      (X1Mat * X2Mat + X2Mat * X1Mat) ∉ g2Submodule
  | .W_23 =>
      (∑ d ∈ Finset.Icc 1 5, wittLieDim 2 d = 14) ∧
      wittLieDim 2 6 = 9 ∧
      (∑ d ∈ Finset.Icc 1 6, wittLieDim 2 d = 23) ∧
      (¬ ∃ f : (Fin (∑ d ∈ Finset.Icc 1 6, wittLieDim 2 d) → ℝ) →ₗ[ℝ] g2Submodule,
        Function.Injective f)
  | .H =>
      (∀ X Y : g2LieSubalgebra, ⁅X, Y⁆.1 ∈ g2Submodule) ∧
      adOp E0Mat F0Mat = HAlphaMat ∧
      adOp ZPlus2Mat ZMinus2Mat = HThetaMat ∧
      adOp X2Mat Y2Mat = (1 / 2 : ℝ) • (HThetaMat - HAlphaMat)
  | .E =>
      (∀ Z ∈ g2Submodule, (∀ X ∈ g2Submodule, adOp Z X = 0) → Z = 0) ∧
      Module.finrank ℝ g2Submodule = ∑ d ∈ Finset.Icc 1 5, wittLieDim 2 d ∧
      Module.finrank ℝ g2Submodule < ∑ d ∈ Finset.Icc 1 6, wittLieDim 2 d
  | .Xi_top =>
      (∀ a : CausalArchetype, CausalArchetype.Delta0 ≤ a ∧ a ≤ CausalArchetype.Xi_top) ∧
      IsLUB ({CausalArchetype.H, .E} : Set CausalArchetype) CausalArchetype.Xi_top ∧
      Fintype.card CausalArchetype = 15 ∧
      Fintype.card { p : CausalArchetype × CausalArchetype // Covers p.1 p.2 } = 23

theorem every_archetype_coagulated (a : CausalArchetype) : archetypeClaim a := by
  cases a with
  | Delta0 => exact cl11Pos_cl11Neg_noncomm
  | A0 =>
    exact ⟨ax4_associative_jacobi_ceiling, gradInnerDeriv_is_derivation,
      innerDerivationWitness_sq_not_derivation⟩
  | C8 => exact ⟨gamma44_sq, gamma44_trace_zero, gamma44_anticomm_gen⟩
  | K_TT => exact ⟨kreinMetric88_transpose, kreinMetric88_sq, kreinInner16_nondegenerate⟩
  | Tau => exact ⟨trialityCycle_cube, triality_s3_relation, trialityFixedCartan_finrank⟩
  | Gamma_SS => exact ⟨psiPlus_chiral_even, psiPlus_krein_norm, psiMinus_krein_norm⟩
  | G =>
    exact ⟨fun _ h => cl44BivectorSubmodule_chiral_even h,
      fun _ h => cl44BivectorSubmodule_krein_skew h,
      fun _ hX _ hY => cl44BivectorSubmodule_comm_mem hX hY⟩
  | Omega => exact ⟨so34Submodule_finrank_le, spinorAct_range_finrank_ge, spinorAct_ker_finrank_le⟩
  | Phi_5 =>
    exact ⟨g2Submodule_eq_stabilizer, finrank_g2Submodule,
      fun i => ⟨ad_HTheta_g2Basis i, ad_HAlpha_g2Basis i⟩, g2_centerless⟩
  | Heis =>
    exact ⟨heisenberg_X1_X2, heisenberg_X4_X3, ZPlus2Mat_ne_zero,
      ad_X2_sq_E0_zero, ad_E0_four_X2_zero, ad_Y2_sq_F0_zero, ad_F0_four_Y2_zero⟩
  | J_cl => exact ⟨jordan_X1_X2_krein_symm, jordan_X1_X2_not_mem_bivector, jordan_X1_X2_not_mem_g2⟩
  | W_23 =>
    exact ⟨witt_sum_1_to_5, wittLieDim_2_6, witt_sum_1_to_6, witt_pigeonhole_fin23_no_injective_linearMap⟩
  | H =>
    exact ⟨fun X Y => ⁅X, Y⁆.2, chevalley_E0_F0, chevalley_ZPlus2_ZMinus2, chevalley_X2_Y2⟩
  | E =>
    refine ⟨g2_centerless, ?_, ?_⟩
    · rw [finrank_g2Submodule, witt_sum_1_to_5]
    · rw [finrank_g2Submodule, witt_sum_1_to_6]; norm_num
  | Xi_top =>
    exact ⟨fun a => ⟨bot_le_all a, all_le_top a⟩, xi_top_isLUB_H_E,
      card_causalArchetype, card_causal_covers⟩

def SplitG2Cl44SolveEtCoagulaSynthesis : Prop :=
  (∀ a : CausalArchetype, archetypeClaim a) ∧
  IsAntichain (· ≤ ·) ({CausalArchetype.K_TT, .G, .Tau, .Gamma_SS} : Set CausalArchetype) ∧
  IsAntichain (· ≤ ·) ({CausalArchetype.A0, .Tau, .Gamma_SS} : Set CausalArchetype) ∧
  (∀ {u v : CausalArchetype}, Covers u v → archetypeGrade u < archetypeGrade v) ∧
  (∀ {u v : CausalArchetype}, Covers u v → ∀ w : CausalArchetype, ¬ (u < w ∧ w < v))

theorem split_g2_cl44_solve_et_coagula_synthesis : SplitG2Cl44SolveEtCoagulaSynthesis :=
  ⟨every_archetype_coagulated, antichain_K_TT_G_Tau_Gamma_SS, antichain_A0_Tau_Gamma_SS,
   fun h => strict_grade_monotonicity h, fun h w => covers_transitively_reduced h w⟩

def splitG2Cl44SolveEtCoagulaArchetype : TypedArchetype Unit .proved where
  name := `InfoGeometry.Exceptional.SplitG2Cl44SolveEtCoagulaPoset.split_g2_cl44_solve_et_coagula_synthesis
  phase := 5
  claim := fun _ => SplitG2Cl44SolveEtCoagulaSynthesis
  evidence := fun _ => split_g2_cl44_solve_et_coagula_synthesis

#register_archetype splitG2Cl44SolveEtCoagulaArchetype
#audit_archetype splitG2Cl44SolveEtCoagulaArchetype

end InfoGeometry.Exceptional.SplitG2Cl44SolveEtCoagulaPoset
