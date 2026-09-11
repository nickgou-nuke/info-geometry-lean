import InfoGeometry.Canonical.ArnoldMajoranaNetwork
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Logic.Equiv.Defs

namespace InfoGeometry.Canonical.MoE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

/--
Two Arnold-Majorana networks are gauge-equivalent if they differ by a permutation of their experts.
This establishes the basis for the Moduli Stack of KAN configurations $\mathcal{M}_{\text{KAN}}$.
-/
def ArnoldMajoranaNetworkRel (n : Nat) (N1 N2 : ArnoldMajoranaNetwork n E) : Prop :=
  ∃ (σ : Equiv (Fin n) (Fin n)), ∀ i, N1.moe.experts i = N2.moe.experts (σ i)

theorem arnold_majorana_network_refl (n : Nat) (N : ArnoldMajoranaNetwork n E) :
    ArnoldMajoranaNetworkRel n N N := by
  use Equiv.refl (Fin n)
  intro i
  rfl

theorem arnold_majorana_network_symm (n : Nat) {N1 N2 : ArnoldMajoranaNetwork n E}
    (h : ArnoldMajoranaNetworkRel n N1 N2) : ArnoldMajoranaNetworkRel n N2 N1 := by
  rcases h with ⟨σ, hσ⟩
  use σ.symm
  intro i
  have hs := hσ (σ.symm i)
  simp only [Equiv.apply_symm_apply] at hs
  exact hs.symm

theorem arnold_majorana_network_trans (n : Nat) {N1 N2 N3 : ArnoldMajoranaNetwork n E}
    (h1 : ArnoldMajoranaNetworkRel n N1 N2) (h2 : ArnoldMajoranaNetworkRel n N2 N3) :
    ArnoldMajoranaNetworkRel n N1 N3 := by
  rcases h1 with ⟨σ1, hσ1⟩
  rcases h2 with ⟨σ2, hσ2⟩
  use σ1.trans σ2
  intro i
  rw [hσ1]
  have h2s := hσ2 (σ1 i)
  rw [h2s]
  rfl

/-- The Setoid representing the gauge symmetry of the Arnold-Majorana network. -/
def arnoldMajoranaNetworkSetoid (n : Nat) (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E] :
    Setoid (ArnoldMajoranaNetwork n E) where
  r := ArnoldMajoranaNetworkRel n
  iseqv := {
    refl := arnold_majorana_network_refl n
    symm := arnold_majorana_network_symm n
    trans := arnold_majorana_network_trans n
  }

/--
The Moduli Stack (Quotient Space) of Arnold-Majorana Networks.
This formalizes the space of networks modulo internal node permutation symmetries.
-/
def ArnoldMajoranaModuli (n : Nat) (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E] : Type _ :=
  Quotient (arnoldMajoranaNetworkSetoid n E)

end InfoGeometry.Canonical.MoE
