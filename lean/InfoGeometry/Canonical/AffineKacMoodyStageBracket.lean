import InfoGeometry.Canonical.AffineKacMoodyFiniteModeColimit

/-!
# Bracket closure for affine Kac--Moody mode cutoffs

The causal dependencies are: affine central extension → finite mode stages →
generator bracket and mode addition → closure under linear span.  The final
colimit Lie bracket is not constructed here; this file proves its essential
finite-stage closure input.
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

end InfoGeometry.Canonical.AffineKacMoodyFiniteModeColimit

end noncomputable section
