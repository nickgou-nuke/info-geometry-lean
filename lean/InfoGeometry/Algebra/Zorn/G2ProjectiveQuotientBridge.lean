import InfoGeometry.Algebra.Zorn.G2TwoBasisRigidity
import InfoGeometry.Algebra.Zorn.G2TwoExplicitGenerators
import InfoGeometry.Algebra.Zorn.G2BNBruhatFramework
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2Unipotent
open Equiv
open MulAction

namespace InfoGeometry.Algebra.Zorn.G2ProjectiveQuotientBridge

/-!
# Projective Geometry and Quotient Bridges

This module connects the split-octonion automorphism group to projective
geometry via quotients and covering maps.
-/

/-! ## Step 1: SplitOctF2 cardinality -/

instance : Zero SplitOctF2 := ⟨zero⟩

theorem splitOctF2_card_eq_256 : Fintype.card SplitOctF2 = 256 := splitOctF2_card

/-! ## Step 2: Projective space -/

/-- The set of nonzero vectors in `SplitOctF2`. -/
def projectiveSplitOctF2 :=
  { v : SplitOctF2 // v ≠ 0 }
  deriving Fintype

theorem projective_points_count :
    Fintype.card projectiveSplitOctF2 = 255 := by
  simp [projectiveSplitOctF2, splitOctF2_card_eq_256]

/-! ## Step 3: Faithful action on projective space -/

/-- The automorphism group acts on the projective space by linearity.
Because `SplitOctF2Aut` carries the group structure `f * g = g ∘ f`,
the natural left action is `g • x = g.symm x`. -/
noncomputable instance : MulAction SplitOctF2Aut projectiveSplitOctF2 where
  smul g v := ⟨(g.1).symm v.1, by
    intro h
    have h0 : g.1 0 = 0 := by
      have hadd := g.2.2.1 0 0
      have hself : add (g.1 0) (g.1 0) = 0 := add_self (g.1 0)
      have h00 : add 0 0 = 0 := add_self 0
      rw [h00] at hadd
      exact hadd.trans hself
    have : v.1 = 0 := by
      have h_inv : v.1 = g.1 (g.1.symm v.1) := (g.1.right_inv v.1).symm
      have h₁ : g.1 (g.1.symm v.1) = g.1 0 := by rw [h]
      have h₂ : g.1 0 = 0 := h0
      exact (h_inv.trans h₁).trans h₂
    exact v.2 this
  ⟩
  one_smul v := by
    apply Subtype.ext
    rfl
  mul_smul g h v := by
    apply Subtype.ext
    rfl

/-- The action is faithful on projective space. -/
theorem projective_action_faithful (g : SplitOctF2Aut)
    (h : ∀ v : projectiveSplitOctF2, g • v = v) : g = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro X
  have h0 : g.1 0 = 0 := by
    have hadd := g.2.2.1 0 0
    have hself : add (g.1 0) (g.1 0) = 0 := add_self (g.1 0)
    have h00 : add 0 0 = 0 := add_self 0
    rw [h00] at hadd
    exact hadd.trans hself
  by_cases hX : X = 0
  · rw [hX, h0]
    rfl
  · have hproj := h ⟨X, hX⟩
    dsimp at hproj
    have h' : g.1.symm X = X := Subtype.mk.inj hproj
    have h₁ : g.1 X = g.1 (g.1.symm X) := congrArg g.1 h'.symm
    have h₂ : g.1 (g.1.symm X) = X := g.1.right_inv X
    exact h₁.trans h₂

/-! ## Step 4: Admissible 7-basis torsor as a flag variety -/

/-- The stabilizer of the standard flag is trivial. -/
theorem standard_flag_stabilizer_eq_bot :
    MulAction.stabilizer SplitOctF2Aut standardAdmissibleBasis7 = ⊥ :=
  InfoGeometry.Algebra.Zorn.G2BNBruhatFramework.standardAdmissibleBasis7_stabilizer_eq_bot

/-! ## Step 5: Weyl group action on admissible bases -/

/-- The Weyl subgroup acts on admissible 7-bases. -/
theorem g2weylGroup_smul_admissible (w : InfoGeometry.Algebra.Zorn.G2BNBruhatFramework.g2weylGroup)
    (v : {v : Fin 7 → SplitOctF2 // admissibleBasis7 v}) :
    admissibleBasis7 ((w : SplitOctF2Aut) • v).1 := by
  exact ((w : SplitOctF2Aut) • v).property

/-- Explicit Setoid for admissible bases so that `Quotient.mk'` can find it
without type-class synthesis through `Setoid (Fin 7 → SplitOctF2)`. -/
noncomputable instance : Setoid {v : Fin 7 → SplitOctF2 // admissibleBasis7 v} :=
  MulAction.orbitRel (↥InfoGeometry.Algebra.Zorn.G2BNBruhatFramework.g2weylGroup) {v : Fin 7 → SplitOctF2 // admissibleBasis7 v}

/-- The quotient of admissible bases by the Weyl group is nonempty. -/
theorem admissible_bases_quotient_nonempty :
    Nonempty (Quotient (MulAction.orbitRel (↥InfoGeometry.Algebra.Zorn.G2BNBruhatFramework.g2weylGroup) {v : Fin 7 → SplitOctF2 // admissibleBasis7 v})) := by
  exact ⟨Quotient.mk' InfoGeometry.Algebra.Zorn.G2BNBruhatFramework.standardAdmissibleBasis7⟩

end InfoGeometry.Algebra.Zorn.G2ProjectiveQuotientBridge
