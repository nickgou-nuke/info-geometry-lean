/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Canonical.TensorTowerColimit

/-!
# A block-duplication matrix sequence and its conditional cone lemmas

`CliffordStage 𝕜 n` below is the full matrix ring on `Fin (2^n)`. The
successor map duplicates a matrix into two diagonal blocks. This file proves
facts about that matrix sequence and compatible linear maps out of it; it does
not construct a Clifford algebra, identify these stages with a Clifford
representation, or construct a topological/C*-algebraic completion.

The actual growing `Cl(1,1)` operator colimit is owned by
`InfoGeometry.Clifford.Cl11TensorTowerLimit`; its recursive commutator results
are in `InfoGeometry.Clifford.Cl11RecursiveCommutatorColimit`.

## BUCKET 1: Proved
Finite matrix-stage linearity, injectivity, and finite-iterate cone compatibility.

## BUCKET 2: Conditional
Nonvanishing transport is conditional on the explicit target-kernel witness.

## BUCKET 3: Open boundary
No Clifford identification, universal-property theorem for a colimit, topology,
or analytic/C*-completion is established here.
-/

set_option linter.unusedSectionVars false

namespace InfoGeometry.Canonical.CliffordDirectColimit

variable {𝕜 : Type} [Ring 𝕜]

/-- Full square matrix ring used at the finite index `n` of this sequence.
No Clifford-algebra identification is part of this definition. -/
abbrev CliffordStage (𝕜 : Type) [Ring 𝕜] (n : ℕ) : Type :=
  Matrix (Fin (2^n)) (Fin (2^n)) 𝕜

/-- Block-duplication map from the `n`th square-matrix stage to the next one. -/
def cliffordEmbedSucc (n : ℕ) (A : CliffordStage 𝕜 n) : CliffordStage 𝕜 (n + 1) :=
  Matrix.of (fun i j =>
    if h : i.val < 2^n ∧ j.val < 2^n then A ⟨i.val, h.1⟩ ⟨j.val, h.2⟩
    else if h2 : i.val ≥ 2^n ∧ j.val ≥ 2^n then A ⟨i.val - 2^n, by omega⟩ ⟨j.val - 2^n, by omega⟩
    else 0)

/-- Linear-map version of the block-duplication map. -/
def cliffordEmbedSuccLinear (n : ℕ) : CliffordStage 𝕜 n →ₗ[𝕜] CliffordStage 𝕜 (n + 1) where
  toFun := cliffordEmbedSucc n
  map_add' := by
    intro A B
    ext i j
    dsimp [cliffordEmbedSucc]
    split_ifs <;> simp
  map_smul' := by
    intro c A
    ext i j
    dsimp [cliffordEmbedSucc]
    split_ifs <;> simp

/-- The block-duplication map is injective at every finite stage. -/
theorem cliffordEmbedSucc_injective (n : ℕ) :
    Function.Injective (cliffordEmbedSucc (𝕜 := 𝕜) n) := by
  intro A B h
  ext a b
  have h_pow : 2^n < 2^(n + 1) := by
    rw [Nat.pow_succ]
    nlinarith [Nat.two_pow_pos n]
  have h_lt_a : a.val < 2^(n + 1) := Nat.lt_trans a.isLt h_pow
  have h_lt_b : b.val < 2^(n + 1) := Nat.lt_trans b.isLt h_pow
  let i : Fin (2^(n + 1)) := ⟨a.val, h_lt_a⟩
  let j : Fin (2^(n + 1)) := ⟨b.val, h_lt_b⟩
  have happ := congrFun (congrFun h i) j
  have h_cond : a.val < 2^n ∧ b.val < 2^n := ⟨a.isLt, b.isLt⟩
  change (if h : a.val < 2^n ∧ b.val < 2^n then A ⟨a.val, h.1⟩ ⟨b.val, h.2⟩ else if h2 : a.val ≥ 2^n ∧ b.val ≥ 2^n then A ⟨a.val - 2^n, by omega⟩ ⟨b.val - 2^n, by omega⟩ else 0) =
         (if h : a.val < 2^n ∧ b.val < 2^n then B ⟨a.val, h.1⟩ ⟨b.val, h.2⟩ else if h2 : a.val ≥ 2^n ∧ b.val ≥ 2^n then B ⟨a.val - 2^n, by omega⟩ ⟨b.val - 2^n, by omega⟩ else 0) at happ
  simp only [dite_eq_left h_cond] at happ
  exact happ

/-- The `m`-step iterate of the block-duplication maps. -/
def cliffordSeq (n m : ℕ) : CliffordStage 𝕜 n →ₗ[𝕜] CliffordStage 𝕜 (n + m) :=
  iota_seq (fun k => CliffordStage 𝕜 k) (fun k => cliffordEmbedSuccLinear k) n m

/-- The multi-step embedding sequence is injective. -/
theorem cliffordSeq_injective (n m : ℕ) :
    Function.Injective (cliffordSeq (𝕜 := 𝕜) n m) := by
  induction' m with m ih
  · intro X Y h
    dsimp [cliffordSeq, iota_seq] at h
    exact h
  · intro X Y h
    dsimp [cliffordSeq, iota_seq] at h
    have h_inj := cliffordEmbedSucc_injective (n + m) h
    exact ih h_inj

/-- The iterated block-duplication map reflects zero. -/
theorem cliffordSeq_eq_zero (n m : ℕ) (X : CliffordStage 𝕜 n) :
    cliffordSeq (𝕜 := 𝕜) n m X = 0 → X = 0 := by
  induction' m with m ih
  · intro h
    simpa [cliffordSeq, iota_seq] using h
  · intro h
    have h' : cliffordEmbedSuccLinear (𝕜 := 𝕜) (n + m) (cliffordSeq (𝕜 := 𝕜) n m X) = 0 := by
      change cliffordEmbedSucc (𝕜 := 𝕜) (n + m)
        (cliffordSeq (𝕜 := 𝕜) n m X) = 0 at h
      exact h
    have h0 : cliffordEmbedSucc (𝕜 := 𝕜) (n + m) 0 = 0 :=
      (cliffordEmbedSuccLinear (𝕜 := 𝕜) (n + m)).map_zero
    have hstep' : cliffordEmbedSucc (𝕜 := 𝕜) (n + m) (cliffordSeq (𝕜 := 𝕜) n m X) = cliffordEmbedSucc (𝕜 := 𝕜) (n + m) 0 := by
      rw [h0]
      exact h'
    have hstep : cliffordSeq (𝕜 := 𝕜) n m X = 0 :=
      cliffordEmbedSucc_injective (𝕜 := 𝕜) (n + m) hstep'
    exact ih hstep

/-- A nonzero stage matrix stays nonzero under every finite iterate of the
block-duplication maps. This is an algebraic persistence statement. -/
theorem stagewise_nonvanishing_of_nonzero
    (n : ℕ) {X : CliffordStage 𝕜 n} (hX : X ≠ 0) :
    ∀ m, cliffordSeq (𝕜 := 𝕜) n m X ≠ 0 := by
  intro m hzero
  exact hX (cliffordSeq_eq_zero (𝕜 := 𝕜) n m X hzero)

/-- A compatible linear cone has the same readout before and after any finite
iterate of the block-duplication maps. This is a cone-compatibility result;
`A_inf` is not constructed here as a colimit. -/
theorem blockSequence_cone_readout
    (A_inf : Type) [AddCommGroup A_inf] [Module 𝕜 A_inf]
    (psi : ∀ k, CliffordStage 𝕜 k →ₗ[𝕜] A_inf)
    (psi_comm : ∀ k, (psi (k + 1)).comp (cliffordEmbedSuccLinear k) = psi k)
    (psi_trace : A_inf →ₗ[𝕜] 𝕜) (n m : ℕ) (X : CliffordStage 𝕜 n) :
    psi_trace (psi (n + m) (cliffordSeq n m X)) = psi_trace (psi n X) := by
  have hcone := psi_comp_iota_seq (fun k => CliffordStage 𝕜 k)
    (fun k => cliffordEmbedSuccLinear k) A_inf psi psi_comm n m
  exact congrArg (fun f : CliffordStage 𝕜 n →ₗ[𝕜] A_inf => psi_trace (f X)) hcone

/-- The finite matrix-sequence map from stage `1` to stage `1 + n` is injective.
The statement concerns only the explicitly defined matrix sequence above. -/
theorem stageOne_matrixSequence_injective (n : ℕ) :
    Function.Injective (cliffordSeq (𝕜 := 𝕜) 1 n) :=
  by
    induction n with
    | zero =>
        intro X Y hXY
        simpa [cliffordSeq, iota_seq] using hXY
    | succ n ih =>
        intro X Y hXY
        dsimp [cliffordSeq, iota_seq] at hXY
        change cliffordEmbedSucc (1 + n)
          (cliffordSeq (𝕜 := 𝕜) 1 n X) =
          cliffordEmbedSucc (1 + n)
          (cliffordSeq (𝕜 := 𝕜) 1 n Y) at hXY
        exact ih (cliffordEmbedSucc_injective (1 + n) hXY)

/-- Conditional nonvanishing transport for a compatible target map.

The target `A_inf` is arbitrary. The explicit `colimit_kernel` hypothesis
supplies the implication from target vanishing to eventual stage vanishing;
this theorem does not assert that `A_inf` is a colimit or a C*-completion. -/
theorem cone_nonzero_of_sequence_persistence
    (A_inf : Type) [AddCommGroup A_inf] [Module 𝕜 A_inf]
    (psi : ∀ k, CliffordStage 𝕜 k →ₗ[𝕜] A_inf)
    (colimit_kernel : ∀ (k : ℕ) (X : CliffordStage 𝕜 k), psi k X = 0 → ∃ m, cliffordSeq k m X = 0)
    (n : ℕ) (X : CliffordStage 𝕜 n)
    (h_persistent : ∀ m, cliffordSeq (𝕜 := 𝕜) n m X ≠ 0) :
    psi n X ≠ 0 := by
  intro hvanish
  obtain ⟨m, hm⟩ := colimit_kernel n X hvanish
  exact h_persistent m hm

/-- Conditional nonvanishing transport from a nonzero source-stage matrix and
zero-reflection of every finite iterate. -/
theorem cone_nonzero_of_nonzero_source
    (A_inf : Type) [AddCommGroup A_inf] [Module 𝕜 A_inf]
    (psi : ∀ k, CliffordStage 𝕜 k →ₗ[𝕜] A_inf)
    (colimit_kernel : ∀ (k : ℕ) (X : CliffordStage 𝕜 k), psi k X = 0 → ∃ m, cliffordSeq k m X = 0)
    (n : ℕ) (X : CliffordStage 𝕜 n) (hX : X ≠ 0) :
    psi n X ≠ 0 := by
  intro hvanish
  obtain ⟨m, hm⟩ := colimit_kernel n X hvanish
  exact hX (cliffordSeq_eq_zero (𝕜 := 𝕜) n m X hm)

end InfoGeometry.Canonical.CliffordDirectColimit
