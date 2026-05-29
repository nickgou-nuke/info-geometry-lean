import InfoGeometry.Canonical.SplitCliffordHeisenbergBridge
import InfoGeometry.Canonical.SplitCliffordInfiniteCurrent
import InfoGeometry.Canonical.SplitCliffordSourceCurrentWick

/-!
# InfoGeometry.Canonical.SplitCliffordSourceHeisenberg

Strict packaging from proved endomorphism-valued current laws to the existing
split Heisenberg witness.

This file introduces no pseudo-closure surfaces.
-/

namespace InfoGeometry.Canonical.SplitCliffordSourceHeisenberg

open Filter
open InfoGeometry.Canonical.SplitCliffordSourceCurrentWick
open InfoGeometry.Canonical.SplitCliffordHeisenbergBridge
open InfoGeometry.Canonical.SplitCliffordInfiniteCurrent
open InfoGeometry.Canonical.SplitCliffordSourceCurrent

/--
Bundle a proved endomorphism-valued current family into the split Heisenberg
bridge witness.
-/
def packagedHeisenbergWitness
    {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    (Jlift : Int → V →ₗ[𝕜] V)
    (hTruncLift : ∀ v : V, ∀ᶠ l : Int in atTop, Jlift l v = 0)
    (hCommLift : SplitSourceEndWickLaw Jlift) :
    SplitCliffordHeisenbergWitness 𝕜 V where
  J := Jlift
  trunc := hTruncLift
  comm := hCommLift

/--
`truncLift`: extract eventual truncation from the concrete charged-Fock source
current witness.
-/
theorem truncLift_of_represented_current
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    ∃ J :
        Int →
          VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
            VirasoroProject.ChargedFockSpace 𝕜 α,
      ∀ v, ∀ᶠ n : Int in Filter.atTop, J n v = 0 := by
  rcases represented_current_commutator_chargedFock (𝕜 := 𝕜) α with ⟨J, htrunc, _⟩
  exact ⟨J, htrunc⟩

/--
`wickLift`: extract the endomorphism-valued Wick/Heisenberg commutator law
from the concrete charged-Fock source current witness.
-/
theorem wickLift_of_represented_current
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    ∃ J :
        Int →
          VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
            VirasoroProject.ChargedFockSpace 𝕜 α,
      SplitSourceEndWickLaw J := by
  rcases represented_current_commutator_chargedFock (𝕜 := 𝕜) α with ⟨J, _, hwick⟩
  exact ⟨J, hwick⟩

/--
Strict witness packaging theorem: the concrete charged-Fock current family
provides a `SplitCliffordHeisenbergWitness` without any extra closure surface.
-/
theorem strictWitness_of_represented_current
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    Nonempty
      (SplitCliffordHeisenbergWitness 𝕜
        (VirasoroProject.ChargedFockSpace 𝕜 α)) := by
  rcases represented_current_commutator_chargedFock (𝕜 := 𝕜) α with
    ⟨J, hTruncLift, hCommLift⟩
  exact ⟨packagedHeisenbergWitness J hTruncLift hCommLift⟩

/-! ## Packaging from split source lift data -/

universe u

/--
Any split-source current lift datum gives eventual truncation for its lifted
mode family.
-/
theorem truncLift_of_splitCurrentLiftDatum
    {𝕜 V : Type u} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    (L : SplitCliffordSourceCurrent.SplitCurrentLiftDatum (𝕜 := 𝕜) (V := V)) :
    ∀ v : V, ∀ᶠ l : Int in atTop, L.Jlift l v = 0 :=
  L.trunc

/--
If a split-source lifted current family satisfies the endomorphism-valued Wick
commutator law, it packages into a split Heisenberg witness.

This is the strict bridge step from source-side lift data to the existing
`CurrentHeisenbergRep` interface.
-/
def strictWitness_of_splitCurrentLiftDatum
    {𝕜 V : Type u} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    (L : SplitCliffordSourceCurrent.SplitCurrentLiftDatum (𝕜 := 𝕜) (V := V))
    (hCommLift : SplitSourceEndWickLaw L.Jlift) :
    SplitCliffordHeisenbergWitness 𝕜 V :=
  packagedHeisenbergWitness L.Jlift L.trunc hCommLift

/--
The same source-side hypotheses already yield the existing repository
`CurrentHeisenbergRep` package.
-/
noncomputable def currentRep_of_splitCurrentLiftDatum
    {𝕜 V : Type u} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    (L : SplitCliffordSourceCurrent.SplitCurrentLiftDatum (𝕜 := 𝕜) (V := V))
    (hCommLift : SplitSourceEndWickLaw L.Jlift) :
    InfoGeometry.Canonical.CurrentSugawaraBridge.CurrentHeisenbergRep 𝕜 V :=
  splitClifford_to_currentHeisenbergRep
    (strictWitness_of_splitCurrentLiftDatum L hCommLift)

/-! ## Explicit infinite-current consumer readouts -/

/--
Consumer readout: the canonical infinite current from the external Heisenberg
algebra satisfies the full mode commutator law.
-/
theorem canonicalInfiniteCurrent_commutator_readout
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]
    (m n : Int) :
    ⁅Jinf 𝕜 m, Jinf 𝕜 n⁆ =
      if m + n = 0 then (m : 𝕜) • Kinf 𝕜 else 0 :=
  canonicalInfiniteCurrent_lie (𝕜 := 𝕜) m n

/--
Consumer readout: the first central mode pair of the canonical infinite
current is exactly `[J₁,J₋₁] = 1 • K`.
-/
theorem canonicalInfiniteCurrent_one_negOne
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] :
    ⁅Jinf 𝕜 1, Jinf 𝕜 (-1)⁆ = (1 : 𝕜) • Kinf 𝕜 :=
  canonicalInfiniteCurrent_lie_one_neg_one (𝕜 := 𝕜)

/--
Consumer readout: the canonical central generator commutes with every element.
-/
theorem canonicalInfiniteCurrent_central
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]
    (Z : InfiniteCurrentAlg 𝕜) :
    ⁅Kinf 𝕜, Z⁆ = 0 :=
  canonicalInfiniteCurrent_lie_central (𝕜 := 𝕜) Z

end InfoGeometry.Canonical.SplitCliffordSourceHeisenberg
