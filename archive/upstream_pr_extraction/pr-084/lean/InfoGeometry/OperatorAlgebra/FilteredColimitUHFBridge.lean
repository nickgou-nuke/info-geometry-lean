import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Stage-Compatible UHF Trace Cocone

This module proves finite-stage trace preservation for the standard matrix
embeddings and packages the compatible linear maps in a small local cocone
structure. It is not Mathlib's `IsColimit` and does not construct a categorical
UHF colimit or a descended state.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.FilteredColimitUHFBridge

open CategoryTheory
open Matrix

/-- Finite matrix algebra stage M_{2^n}(ℂ) represented as linear module -/
abbrev MatrixStage (n : ℕ) := Matrix (Fin (2^n)) (Fin (2^n)) ℂ

/-- Canonical normalized trace functional on stage n: τ_n(A) = 2⁻ⁿ Tr(A) -/
def stageTrace (n : ℕ) (A : MatrixStage n) : ℂ :=
  (1 / (2^n : ℂ)) * Matrix.trace A

/-- Block embedding map ι_n : M_{2^n}(ℂ) → M_{2^{n+1}}(ℂ) via A ↦ A ⊗ I₂ -/
def stageEmbedding (n : ℕ) (A : MatrixStage n) : MatrixStage (n + 1) :=
  fun i j =>
    let i_div : Fin (2^n) := ⟨i.val / 2, by omega⟩
    let j_div : Fin (2^n) := ⟨j.val / 2, by omega⟩
    if i.val % 2 = j.val % 2 then A i_div j_div else 0

/-- Equivalence between Fin (2^(n+1)) and Fin (2^n) × Fin 2 -/
def finSuccPowEquiv (n : ℕ) : Fin (2^(n + 1)) ≃ Fin (2^n) × Fin 2 where
  toFun i := (⟨i.val / 2, by omega⟩, ⟨i.val % 2, by omega⟩)
  invFun p := ⟨p.1.val * 2 + p.2.val, by
    rcases p with ⟨⟨m, hm⟩, ⟨b, hb⟩⟩
    dsimp
    have : m * 2 + b < 2^n * 2 := by omega
    simpa [pow_succ] using this⟩
  left_inv i := by
    ext
    dsimp
    omega
  right_inv p := by
    ext
    · dsimp; omega
    · dsimp; omega

/-- 🏆 THEOREM 1: Trace Preservation under Inductive Embedding: τ_{n+1}(ι_n(A)) = τ_n(A) -/
theorem stageTrace_preserving (n : ℕ) (A : MatrixStage n) :
    stageTrace (n + 1) (stageEmbedding n A) = stageTrace n A := by
  dsimp [stageTrace, stageEmbedding, Matrix.trace]
  have hsum : ∑ i : Fin (2^(n + 1)), (if i.val % 2 = i.val % 2 then A ⟨i.val / 2, by omega⟩ ⟨i.val / 2, by omega⟩ else 0) =
              (2 : ℂ) * ∑ m : Fin (2^n), A m m := by
    simp only [ite_true]
    have hequiv := (finSuccPowEquiv n).symm.sum_comp (fun i : Fin (2^(n+1)) => A ⟨i.val / 2, by omega⟩ ⟨i.val / 2, by omega⟩)
    rw [← hequiv]
    rw [Fintype.sum_prod_type]
    have hinner (m : Fin (2^n)) : ∑ b : Fin 2, A ⟨(finSuccPowEquiv n).symm (m, b) / 2, by omega⟩ ⟨(finSuccPowEquiv n).symm (m, b) / 2, by omega⟩ = (2 : ℂ) * A m m := by
      have hval (b : Fin 2) : ((finSuccPowEquiv n).symm (m, b)).val / 2 = m.val := by
        dsimp [finSuccPowEquiv]
        omega
      have hval_eq (b : Fin 2) : (⟨((finSuccPowEquiv n).symm (m, b)).val / 2, by omega⟩ : Fin (2^n)) = m := by
        ext
        exact hval b
      simp_rw [hval_eq]
      simp [two_mul]
    simp_rw [hinner]
    rw [← Finset.mul_sum]
  rw [hsum]
  have hpow : (2^(n + 1) : ℂ) = (2^n : ℂ) * 2 := by ring
  rw [hpow]
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  calc (1 / ((2^n : ℂ) * 2)) * ((2 : ℂ) * ∑ m : Fin (2^n), A m m)
    _ = (1 / (2^n : ℂ)) * ((1 / 2 * 2) * ∑ m : Fin (2^n), A m m) := by ring
    _ = (1 / (2^n : ℂ)) * (1 * ∑ m : Fin (2^n), A m m) := by
      rw [one_div_mul_cancel h2]
    _ = (1 / (2^n : ℂ)) * ∑ m : Fin (2^n), A m m := by ring

/-- Cocone compatibility condition for the inductive filtered colimit -/
structure UHFCocone (X : Type) [AddCommGroup X] [Module ℂ X] where
  map : ∀ n, MatrixStage n →ₗ[ℂ] X
  comm : ∀ n (A : MatrixStage n), map (n + 1) (stageEmbedding n A) = map n A

/- Stage-compatible trace cocone; no universal colimit factorization is claimed. -/
def canonicalStateCocone : UHFCocone ℂ where
  map n := {
    toFun := stageTrace n
    map_add' := by
      intro A B
      dsimp [stageTrace]
      rw [Matrix.trace_add, mul_add]
    map_smul' := by
      intro c A
      dsimp [stageTrace]
      rw [Matrix.trace_smul, smul_eq_mul]
      ring
  }
  comm n A := stageTrace_preserving n A

end InfoGeometry.OperatorAlgebra.FilteredColimitUHFBridge
