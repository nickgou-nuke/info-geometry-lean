import InfoGeometry.Canonical.AffineKacMoodyStageBracket

/-!
# Categorical Colimit Bracket Archetype

This module fulfills the final `.colimitBracket` archetype in the causal poset.
Rather than engaging in manual bi-colimit bifunctor lifts in `ModuleCat`, we 
use the rigorous mathematical fact that the union of all finite stages (which 
is exactly the colimit image) is a genuine Lie subalgebra of the parent 
Kac--Moody algebra.

The finite-stage closure prerequisite (`affineFiniteModeStage_bracket_mem`) 
guarantees that this infinite colimit supremum is closed under the Kac--Moody 
Lie bracket.
-/

noncomputable section

namespace InfoGeometry.Canonical.AffineKacMoodyFiniteModeColimit

open CategoryTheory CategoryTheory.Limits
open VirasoroProject

universe u
variable {𝕜 : Type u} [Field 𝕜] [CharZero 𝕜]
variable {𝓰 : Type u} [LieRing 𝓰] [LieAlgebra 𝕜 𝓰]
variable (Φ : LinearMap.BilinForm 𝕜 𝓰)
variable (hΦ : Φ.lieInvariant 𝓰) (hΦs : Φ.IsSymm)

/-- The directed union of all finite mode stages. This represents the infinite-dimensional
colimit limit as a native submodule. -/
def affineFiniteModeUnion : Submodule 𝕜 (KM Φ hΦ hΦs) :=
  ⨆ N : ℕ, affineFiniteModeStage Φ hΦ hΦs N

/-- The finite mode stages form a directed system under inclusion. -/
theorem affineFiniteModeStage_directed :
    Directed (· ≤ ·) (affineFiniteModeStage Φ hΦ hΦs) := by
  intro i j
  use max i j
  constructor
  · exact affineFiniteModeStage_mono Φ hΦ hΦs (le_max_left i j)
  · exact affineFiniteModeStage_mono Φ hΦ hΦs (le_max_right i j)

/-- 🏆 THEOREM: The categorical colimit supremum is closed under the Lie bracket.
    This relies directly on the causal prerequisite `affineFiniteModeStage_bracket_mem`. -/
theorem union_bracket_closed {X Y : KM Φ hΦ hΦs}
    (hX : X ∈ affineFiniteModeUnion Φ hΦ hΦs)
    (hY : Y ∈ affineFiniteModeUnion Φ hΦ hΦs) :
    ⁅X, Y⁆ ∈ affineFiniteModeUnion Φ hΦ hΦs := by
  have dir := affineFiniteModeStage_directed Φ hΦ hΦs
  have hX_mem : X ∈ ⨆ N, affineFiniteModeStage Φ hΦ hΦs N := hX
  have hY_mem : Y ∈ ⨆ N, affineFiniteModeStage Φ hΦ hΦs N := hY
  have hX_sup := (Submodule.mem_iSup_of_directed (affineFiniteModeStage Φ hΦ hΦs) dir).mp hX_mem
  have hY_sup := (Submodule.mem_iSup_of_directed (affineFiniteModeStage Φ hΦ hΦs) dir).mp hY_mem
  rcases hX_sup with ⟨N, hX_stage⟩
  rcases hY_sup with ⟨M, hY_stage⟩
  
  -- Use the finite-stage bracket closure prerequisite
  have h_bracket := affineFiniteModeStage_bracket_mem Φ hΦ hΦs N M hX_stage hY_stage
  
  -- The bracket lives in stage N+M, which is part of the supremum
  have h_res : ⁅X, Y⁆ ∈ ⨆ N, affineFiniteModeStage Φ hΦ hΦs N := by
    apply (Submodule.mem_iSup_of_directed (affineFiniteModeStage Φ hΦ hΦs) dir).mpr
    exact ⟨N + M, h_bracket⟩
  exact h_res

/-- The Categorical Colimit Lie Subalgebra.
    We natively endow the infinite colimit limit with its intrinsic Lie algebra
    structure inherited from the Kac-Moody envelope. -/
def affineFiniteModeColimitLieSubalgebra : LieSubalgebra 𝕜 (KM Φ hΦ hΦs) :=
  { affineFiniteModeUnion Φ hΦ hΦs with
    lie_mem' := by
      intro X Y hX hY
      exact union_bracket_closed Φ hΦ hΦs hX hY }

end InfoGeometry.Canonical.AffineKacMoodyFiniteModeColimit
