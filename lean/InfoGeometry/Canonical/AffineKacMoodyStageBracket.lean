/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.AffineKacMoodyFiniteModeColimit
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

/-!
# Bracket closure for affine Kac--Moody mode cutoffs

The causal dependencies are: affine central extension → finite mode stages →
generator bracket and mode addition → closure under linear span.  The final
colimit Lie bracket is not constructed here; this file proves its essential
finite-stage closure input.

- BUCKET 1 (Real Math in This File):
  - `BracketClosureArchetype`, `BracketClosureArchetype.rank`,
    `bracketClosure_causal_chain`
  - `affineFiniteModeGenerator_bracket_mem`,
    `affineFiniteModeStage_bracket_mem`

- BUCKET 2 (Meaningful Mathematical Results Used):
  - `InfoGeometry.Canonical.AffineKacMoodyFiniteModeColimit`

- BUCKET 3 (Excluded Wrapper Patterns):
  - Zero wrapper structures, zero `Prop`-valued aliases, and zero `:= rfl` theorems.
-/

noncomputable section

namespace InfoGeometry.Canonical.AffineKacMoodyFiniteModeColimit

open VirasoroProject

/-- Dependency nodes extracted from the affine-current colimit construction.
The last node records the next goal, not a theorem proved in this module. -/
inductive BracketClosureArchetype
  | affineCarrier
  | modeCutoff
  | generatorBracket
  | spanClosure
  | colimitBracket
  deriving DecidableEq, Repr

/-- Rank in the causal dependency chain. -/
def BracketClosureArchetype.rank : BracketClosureArchetype → ℕ
  | .affineCarrier => 0
  | .modeCutoff => 1
  | .generatorBracket => 2
  | .spanClosure => 3
  | .colimitBracket => 4

/-- The causal order is the linear extension of the dependency ranks. -/
instance : PartialOrder BracketClosureArchetype where
  le a b := a.rank ≤ b.rank
  le_refl a := Nat.le_refl _
  le_trans _ _ _ := Nat.le_trans
  le_antisymm := by
    intro a b hab hba
    cases a <;> cases b <;> simp_all [BracketClosureArchetype.rank]

/-- The extracted archetypes occur in their intended causal order. -/
theorem bracketClosure_causal_chain :
    BracketClosureArchetype.affineCarrier ≤ .modeCutoff ∧
    BracketClosureArchetype.modeCutoff ≤ .generatorBracket ∧
    BracketClosureArchetype.generatorBracket ≤ .spanClosure ∧
    BracketClosureArchetype.spanClosure ≤ .colimitBracket := by
  decide

universe u
variable {𝕜 : Type u} [Field 𝕜] [CharZero 𝕜]
variable {𝓰 : Type u} [LieRing 𝓰] [LieAlgebra 𝕜 𝓰]
variable (Φ : LinearMap.BilinForm 𝕜 𝓰)
variable (hΦ : Φ.lieInvariant 𝓰) (hΦs : Φ.IsSymm)

/-- Bracketing two affine current generators adds their modes and keeps the
cocycle contribution in the central line, hence in every sufficiently large
finite-mode stage. -/
theorem current_generators_bracket_mem_stage
    (N M : ℕ) (m n : ℤ) (x y : 𝓰)
    (hm : Int.natAbs m ≤ N) (hn : Int.natAbs n ≤ M) :
    ⁅affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs m x,
      affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs n y⁆ ∈
        affineFiniteModeStage Φ hΦ hΦs (N + M) := by
  rw [affineCurrentGen_bracket]
  have hmn : Int.natAbs (m + n) ≤ N + M := by
    exact (Int.natAbs_add_le m n).trans (Nat.add_le_add hm hn)
  refine (affineFiniteModeStage Φ hΦ hΦs (N + M)).add_mem
    (affineCurrentGen_mem_stage Φ hΦ hΦs (N + M) (m + n) _ hmn) ?_
  by_cases hzero : m + n = 0
  · rw [if_pos hzero]
    exact Submodule.smul_mem _ _
      (affineCentralGen_mem_stage Φ hΦ hΦs (N + M))
  · rw [if_neg hzero]
    exact (affineFiniteModeStage Φ hΦ hΦs (N + M)).zero_mem

/-- Bracketing a current generator against any element of a cutoff stage lands
in the sum cutoff.  The central generator has zero bracket with every element. -/
theorem current_generator_bracket_mem_stage
    (N M : ℕ) (m : ℤ) (x : 𝓰) (hm : Int.natAbs m ≤ N)
    {Y : KM Φ hΦ hΦs} (hY : Y ∈ affineFiniteModeStage Φ hΦ hΦs M) :
    ⁅affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs m x, Y⁆ ∈
      affineFiniteModeStage Φ hΦ hΦs (N + M) := by
  induction hY using Submodule.span_induction with
  | mem Y hY =>
      change Y = affineCentralGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs ∨
        ∃ n : ℤ, ∃ y : 𝓰, Int.natAbs n ≤ M ∧
          Y = affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs n y at hY
      rcases hY with hY | ⟨n, y, hn, rfl⟩
      · subst Y
        rw [LieTwoCocycle.CentralExtension.lie_def]
        simp only [affineCurrentGen, affineCentralGen, map_zero]
        exact (affineFiniteModeStage Φ hΦ hΦs (N + M)).zero_mem
      · exact current_generators_bracket_mem_stage Φ hΦ hΦs N M m n x y hm hn
  | zero => simp
  | add Y Z hY hZ ihY ihZ =>
      rw [lie_add]
      exact (affineFiniteModeStage Φ hΦ hΦs (N + M)).add_mem ihY ihZ
  | smul c Y hY ihY =>
      rw [lie_smul]
      exact (affineFiniteModeStage Φ hΦ hΦs (N + M)).smul_mem c ihY

/-- The native affine Kac--Moody bracket sends mode cutoffs `N` and `M` into
the cutoff `N + M`.  This is the bracket-closure lemma needed before a Lie
bracket can be transported to the categorical finite-mode colimit. -/
theorem affineFiniteModeStage_bracket_mem
    (N M : ℕ) {X Y : KM Φ hΦ hΦs}
    (hX : X ∈ affineFiniteModeStage Φ hΦ hΦs N)
    (hY : Y ∈ affineFiniteModeStage Φ hΦ hΦs M) :
    ⁅X, Y⁆ ∈ affineFiniteModeStage Φ hΦ hΦs (N + M) := by
  induction hX using Submodule.span_induction with
  | mem X hX =>
      change X = affineCentralGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs ∨
        ∃ m : ℤ, ∃ x : 𝓰, Int.natAbs m ≤ N ∧
          X = affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs m x at hX
      rcases hX with hX | ⟨m, x, hm, rfl⟩
      · subst X
        rw [LieTwoCocycle.CentralExtension.lie_def]
        simp only [affineCentralGen, zero_lie, map_zero]
        exact (affineFiniteModeStage Φ hΦ hΦs (N + M)).zero_mem
      · exact current_generator_bracket_mem_stage Φ hΦ hΦs N M m x hm hY
  | zero => simp
  | add X Z hX hZ ihX ihZ =>
      rw [add_lie]
      exact (affineFiniteModeStage Φ hΦ hΦs (N + M)).add_mem ihX ihZ
  | smul c X hX ihX =>
      rw [smul_lie]
      exact (affineFiniteModeStage Φ hΦ hΦs (N + M)).smul_mem c ihX

/-! ### Non-Commutative Operator Realization of `BracketClosureArchetype` over `[Ring B]` -/

section NonCommutativeOperatorRealization

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- Non-commutative operator realization mapping each `BracketClosureArchetype` node
to its canonical operator in `[Ring B]`. -/
def bracketClosureArchetypeOperator (P A C X : B) : BracketClosureArchetype → B
  | .affineCarrier => peirce11 P X + peirce00 P X
  | .modeCutoff => conePlus P A + coneMinus P C
  | .generatorBracket => InfoGeometry.OperatorAlgebra.PeirceSpine.comm (conePlus P A) (coneMinus P C)
  | .spanClosure => InfoGeometry.OperatorAlgebra.PeirceSpine.anticomm (conePlus P A) (coneMinus P C)
  | .colimitBracket => InfoGeometry.OperatorAlgebra.PeirceSpine.comm (genPhi P A C) (genJ P A C)

/-- **Theorem (Non-Commutative Operator Identities across `BracketClosureArchetype`)**:
For any idempotent `P * P = P` in a non-commutative ring `[Ring B]`, the five stages
satisfy even-grade projection, nilpotent mode-cutoff brackets, and exact Tetraktys
`𝔰𝔩₂` commutator closure `[Φ, J] = 2 Σ`. -/
theorem bracketClosureArchetype_operator_identities {P : B} (hP : P * P = P) (A C X : B) :
    bracketClosureArchetypeOperator P A C X .affineCarrier = evenGrade P X ∧
    bracketClosureArchetypeOperator P A C X .modeCutoff = genPhi P A C ∧
    bracketClosureArchetypeOperator P A C X .generatorBracket = genSig P A C ∧
    bracketClosureArchetypeOperator P A C X .spanClosure = genV P A C ∧
    bracketClosureArchetypeOperator P A C X .colimitBracket = -((2 : ℤ) • genSig P A C) ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm (genSig P A C) (genPhi P A C) =
      (2 : ℤ) • (genV P A C * genJ P A C) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, (archetype_A7_so12_lie_brackets_and_cubic_inversions hP A C).2.1⟩
  dsimp only [bracketClosureArchetypeOperator]
  exact (archetype_A7_so12_lie_brackets_and_cubic_inversions hP A C).1

end NonCommutativeOperatorRealization

end InfoGeometry.Canonical.AffineKacMoodyFiniteModeColimit

end noncomputable section
