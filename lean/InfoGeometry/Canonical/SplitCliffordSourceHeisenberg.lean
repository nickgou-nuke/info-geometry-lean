import InfoGeometry.Canonical.SplitCliffordHeisenbergBridge
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

end InfoGeometry.Canonical.SplitCliffordSourceHeisenberg
