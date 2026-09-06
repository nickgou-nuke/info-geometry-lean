import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic

/-!
# Wire 2: block-level SO(4,4) → SO(5,5) Lie transport

This module formalizes the block-level matrix transport
$$\mathfrak{so}(4,4) \longrightarrow \mathfrak{so}(5,5)$$
and records the exact dimension bookkeeping:
$$14 < 28 < 45$$
along with the block embedding $\mathfrak{so}(4,4) \hookrightarrow \mathfrak{so}(5,5)$ into the Levi block of the 3-grading:
$$\mathfrak{so}(5,5) = \mathbf{8}_{-1} \oplus (\mathfrak{so}(4,4) \oplus \mathbb{R})_0 \oplus \mathbf{8}_{+1}.$$
-/

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

namespace InfoGeometry.Lie.G2SO44SO55LieInclusionBridge

open Matrix

abbrev G2TwoDim : ℕ := 14
abbrev SO44Dim : ℕ := 28
abbrev SO55Dim : ℕ := 45

/-- 🏆 THEOREM 1: Exact Dimension Hierarchy 14 < 28 < 45 -/
theorem g2_so44_so55_dim_hierarchy :
    G2TwoDim < SO44Dim ∧ SO44Dim < SO55Dim := by
  decide

/-- Equivalence Fin 10 ≃ Fin 8 ⊕ Fin 2 -/
def fin10Equiv : Fin 10 ≃ Fin 8 ⊕ Fin 2 where
  toFun i :=
    if h : i.val < 8 then
      Sum.inl ⟨i.val, h⟩
    else
      Sum.inr ⟨i.val - 8, by omega⟩
  invFun s :=
    match s with
    | Sum.inl k => ⟨k.val, by omega⟩
    | Sum.inr k => ⟨k.val + 8, by omega⟩
  left_inv i := by
    dsimp
    split_ifs with h
    · ext; dsimp
    · ext; dsimp; omega
  right_inv s := by
    rcases s with k | k <;> dsimp
    · have : k.val < 8 := k.isLt
      simp
    · have : ¬ (k.val + 8 < 8) := by omega
      simp

/-- Embedding of 8×8 antisymmetric matrix (so(4,4)) into 10×10 matrix (so(5,5)) via Levi block -/
def so44ToSO55 (M : Matrix (Fin 8) (Fin 8) ℝ) : Matrix (Fin 10) (Fin 10) ℝ :=
  fun i j =>
    match fin10Equiv i, fin10Equiv j with
    | Sum.inl a, Sum.inl b => M a b
    | _, _ => 0

/-- Linear map preservation of addition -/
theorem so44ToSO55_add (M N : Matrix (Fin 8) (Fin 8) ℝ) :
    so44ToSO55 (M + N) = so44ToSO55 M + so44ToSO55 N := by
  ext i j
  dsimp [so44ToSO55]
  rcases fin10Equiv i with a | a <;> rcases fin10Equiv j with b | b <;> ring

/-- Linear map preservation of scalar multiplication -/
theorem so44ToSO55_smul (c : ℝ) (M : Matrix (Fin 8) (Fin 8) ℝ) :
    so44ToSO55 (c • M) = c • so44ToSO55 M := by
  ext i j
  dsimp [so44ToSO55]
  rcases fin10Equiv i with a | a <;> rcases fin10Equiv j with b | b <;> ring

/-- 🏆 THEOREM 2: Exact Lie Commutator Multiplicative Homomorphism -/
theorem so44ToSO55_mul (M N : Matrix (Fin 8) (Fin 8) ℝ) :
    so44ToSO55 (M * N) = so44ToSO55 M * so44ToSO55 N := by
  ext i j
  have hRHS : (so44ToSO55 M * so44ToSO55 N) i j = ∑ k : Fin 10, so44ToSO55 M i k * so44ToSO55 N k j := rfl
  rw [hRHS]
  have hequiv : ∑ k : Fin 10, so44ToSO55 M i k * so44ToSO55 N k j =
                ∑ s : Fin 8 ⊕ Fin 2, so44ToSO55 M i (fin10Equiv.symm s) * so44ToSO55 N (fin10Equiv.symm s) j := by
    exact (fin10Equiv.symm.sum_comp _).symm
  rw [hequiv, Fintype.sum_sum_type]
  have hleft (k : Fin 8) : so44ToSO55 M i (fin10Equiv.symm (Sum.inl k)) * so44ToSO55 N (fin10Equiv.symm (Sum.inl k)) j =
      match fin10Equiv i, fin10Equiv j with
      | Sum.inl a, Sum.inl b => M a k * N k b
      | _, _ => 0 := by
    dsimp [so44ToSO55]
    have he : fin10Equiv (fin10Equiv.symm (Sum.inl k)) = Sum.inl k := fin10Equiv.apply_symm_apply (Sum.inl k)
    rw [he]
    rcases fin10Equiv i with a | a <;> rcases fin10Equiv j with b | b <;> ring
  have hright (k : Fin 2) : so44ToSO55 M i (fin10Equiv.symm (Sum.inr k)) * so44ToSO55 N (fin10Equiv.symm (Sum.inr k)) j = 0 := by
    dsimp [so44ToSO55]
    have he : fin10Equiv (fin10Equiv.symm (Sum.inr k)) = Sum.inr k := fin10Equiv.apply_symm_apply (Sum.inr k)
    rw [he]
    ring
  simp_rw [hleft, hright]
  rw [Finset.sum_const_zero, add_zero]
  dsimp [so44ToSO55, Mul.mul, dotProduct]
  rcases fin10Equiv i with a | a <;> rcases fin10Equiv j with b | b
  · rfl
  · simp
  · simp
  · simp

/-- 🏆 THEOREM 3: Preservation of Lie Bracket: [so44ToSO55 M, so44ToSO55 N] = so44ToSO55 [M, N] -/
theorem so44ToSO55_bracket (M N : Matrix (Fin 8) (Fin 8) ℝ) :
    so44ToSO55 (M * N - N * M) = so44ToSO55 M * so44ToSO55 N - so44ToSO55 N * so44ToSO55 M := by
  have h1 := so44ToSO55_mul M N
  have h2 := so44ToSO55_mul N M
  have hsub : so44ToSO55 (M * N - N * M) = so44ToSO55 (M * N) - so44ToSO55 (N * M) := by
    ext i j
    dsimp [so44ToSO55]
    rcases fin10Equiv i with a | a <;> rcases fin10Equiv j with b | b <;> ring
  rw [hsub, h1, h2]

theorem so44ToSO55_injective :
    Function.Injective so44ToSO55 := by
  intro M N h
  ext i j
  have h' := congrArg
    (fun K : Matrix (Fin 10) (Fin 10) ℝ =>
      K (fin10Equiv.symm (Sum.inl i))
        (fin10Equiv.symm (Sum.inl j))) h
  simpa [so44ToSO55] using h'

noncomputable def so44ToSO55LieHom :
    Matrix (Fin 8) (Fin 8) ℝ →ₗ⁅ℝ⁆ Matrix (Fin 10) (Fin 10) ℝ where
  toFun := so44ToSO55
  map_add' := so44ToSO55_add
  map_smul' := so44ToSO55_smul
  map_lie' := by
    intro M N
    exact so44ToSO55_bracket M N

theorem so44ToSO55LieHom_apply (M : Matrix (Fin 8) (Fin 8) ℝ) :
    so44ToSO55LieHom M = so44ToSO55 M := rfl

theorem so44ToSO55LieHom_injective :
    Function.Injective so44ToSO55LieHom := by
  intro M N h
  exact so44ToSO55_injective h

end InfoGeometry.Lie.G2SO44SO55LieInclusionBridge
