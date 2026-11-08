/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.KrausAmplificationCP
import InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleFiniteMarginal
import Mathlib.Analysis.Matrix.Order

/-! # Finite replacement channels

A fixed positive trace-one matrix determines a trace-preserving completely
positive linear map. Its amplifications are the tensor product of the
partial trace of the input with the output state.
-/

noncomputable section

namespace InfoGeometry.Quantum.ReplacementStateChannel

open Matrix InfoGeometry.Quantum.KrausAmplification
open InfoGeometry.Quantum.FiniteAttentionCanonicalBridges
open InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleFiniteMarginal
open scoped ComplexOrder MatrixOrder Kronecker

variable {n : ℕ}
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ

/-- The linear extension of the constant state preparation map. -/
def replacement (σ : Mat) : Mat →ₗ[ℂ] Mat where
  toFun X := Matrix.trace X • σ
  map_add' X Y := by simp [Matrix.trace_add, add_smul]
  map_smul' c X := by simp [Matrix.trace_smul, smul_smul]

theorem replacement_trace (σ X : Mat) (hσ : Matrix.trace σ = 1) :
    Matrix.trace (replacement σ X) = Matrix.trace X := by
  simp [replacement, Matrix.trace_smul, hσ]

theorem replacement_on_density (σ X : Mat) (hX : Matrix.trace X = 1) :
    replacement σ X = σ := by
  simp [replacement, hX]

/-- Each amplification is a tensor product with the true partial trace. -/
theorem amplification_replacement (σ : Mat) {r : ℕ}
    (X : Matrix (Fin r × Fin n) (Fin r × Fin n) ℂ) :
    amplification (r := Fin r) (replacement σ) X = partialTraceSecondOp X ⊗ₖ σ := by
  ext ⟨a, i⟩ ⟨b, j⟩
  simp [amplification_apply, replacement, block, partialTraceSecondOp,
    Matrix.trace, Matrix.diag, Matrix.kronecker_apply]

/-- Positivity holds after tensoring with every finite ancillary matrix space. -/
theorem replacement_completely_positive (σ : Mat) (hσ : σ.PosSemidef) {r : ℕ}
    (X : Matrix (Fin r × Fin n) (Fin r × Fin n) ℂ) (hX : X.PosSemidef) :
    (amplification (r := Fin r) (replacement σ) X).PosSemidef := by
  rw [amplification_replacement]
  exact (partialTraceSecond_posSemidef X hX).kronecker hσ

/-- State preparation with an arbitrary finite output index type. -/
def replacementTo {α : Type*} [Fintype α] [DecidableEq α] {m : ℕ}
    (σ : Matrix α α ℂ) : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix α α ℂ where
  toFun X := Matrix.trace X • σ
  map_add' X Y := by simp [Matrix.trace_add, add_smul]
  map_smul' c X := by simp [Matrix.trace_smul, smul_smul]

/-- Rectangular amplification acts independently on each ancillary block. -/
def amplificationTo {α : Type*} [Fintype α] [DecidableEq α] {m : ℕ}
    {r : Type*} [Fintype r] [DecidableEq r]
    (E : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix α α ℂ) :
    Matrix (r × Fin m) (r × Fin m) ℂ →ₗ[ℂ] Matrix (r × α) (r × α) ℂ where
  toFun X := fun a b => E (block X a.1 b.1) a.2 b.2
  map_add' X Y := by
    ext a b
    rw [show block (X + Y) a.1 b.1 = block X a.1 b.1 + block Y a.1 b.1 by ext i j; rfl,
      E.map_add]
    rfl
  map_smul' c X := by
    ext a b
    rw [show block (c • X) a.1 b.1 = c • block X a.1 b.1 by ext i j; rfl, E.map_smul]
    rfl

theorem replacementTo_trace {α : Type*} [Fintype α] [DecidableEq α] {m : ℕ}
    (σ : Matrix α α ℂ) (hσ : Matrix.trace σ = 1) (X : Matrix (Fin m) (Fin m) ℂ) :
    Matrix.trace (replacementTo σ X) = Matrix.trace X := by
  simp [replacementTo, Matrix.trace_smul, hσ]

theorem replacementTo_on_density {α : Type*} [Fintype α] [DecidableEq α] {m : ℕ}
    (σ : Matrix α α ℂ) (X : Matrix (Fin m) (Fin m) ℂ) (hX : Matrix.trace X = 1) :
    replacementTo σ X = σ := by
  simp [replacementTo, hX]

/-- The partial trace over the finite input factor, for an arbitrary finite
ancillary index type. -/
def partialTraceTo {r : Type*} [Fintype r] [DecidableEq r] {m : ℕ}
    (X : Matrix (r × Fin m) (r × Fin m) ℂ) : Matrix r r ℂ :=
  fun a b => ∑ j, X (a, j) (b, j)

theorem partialTraceTo_posSemidef {r : Type*} [Fintype r] [DecidableEq r] {m : ℕ}
    (X : Matrix (r × Fin m) (r × Fin m) ℂ) (hX : X.PosSemidef) :
    (partialTraceTo X).PosSemidef := by
  let blocks : Fin m → Matrix r r ℂ :=
    fun j => X.submatrix (fun i => (i, j)) (fun i => (i, j))
  have hsum : ∀ s : Finset (Fin m), (∑ j ∈ s, blocks j).PosSemidef := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (Matrix.PosSemidef.zero : (0 : Matrix r r ℂ).PosSemidef)
    | @insert a s ha ih =>
        rw [Finset.sum_insert ha]
        exact (hX.submatrix (fun i => (i, a))).add ih
  have heq : partialTraceTo X = ∑ j, blocks j := by
    ext i k
    simp [partialTraceTo, blocks, Matrix.submatrix, Matrix.sum_apply]
  rw [heq]
  exact hsum Finset.univ

/-- Complete positivity holds for every finite ancillary index type. -/
theorem replacementTo_completely_positive {α : Type*} [Fintype α] [DecidableEq α]
    {m : ℕ} {r : Type*} [Fintype r] [DecidableEq r]
    (σ : Matrix α α ℂ) (hσ : σ.PosSemidef)
    (X : Matrix (r × Fin m) (r × Fin m) ℂ) (hX : X.PosSemidef) :
    (amplificationTo (replacementTo σ) X).PosSemidef := by
  have hEq : amplificationTo (replacementTo σ) X = partialTraceTo X ⊗ₖ σ := by
    ext ⟨a, i⟩ ⟨b, j⟩
    change (Matrix.trace (block X a b)) * σ i j = (partialTraceTo X ⊗ₖ σ) (a, i) (b, j)
    simp [block, partialTraceTo,
      Matrix.trace, Matrix.diag, Matrix.kronecker_apply]
  rw [hEq]
  exact (partialTraceTo_posSemidef X hX).kronecker hσ

/-- On a square carrier, the original amplification and rectangular
amplification agree on every matrix for every finite ancillary index type. -/
theorem square_amplifications_agree {r : Type*} [Fintype r] [DecidableEq r]
    (E : Mat →ₗ[ℂ] Mat) (X : Matrix (r × Fin n) (r × Fin n) ℂ) :
    amplificationTo E X = amplification (r := r) E X := by
  ext ⟨a, i⟩ ⟨b, j⟩
  rfl

/-- The original square replacement map is completely positive on arbitrary
finite ancillary types, using the same amplification as the Kraus API. -/
theorem replacement_completely_positive_all {r : Type*} [Fintype r] [DecidableEq r]
    (σ : Mat) (hσ : σ.PosSemidef)
    (X : Matrix (r × Fin n) (r × Fin n) ℂ) (hX : X.PosSemidef) :
    (amplification (r := r) (replacement σ) X).PosSemidef := by
  rw [← square_amplifications_agree]
  exact replacementTo_completely_positive σ hσ X hX

end InfoGeometry.Quantum.ReplacementStateChannel

end
