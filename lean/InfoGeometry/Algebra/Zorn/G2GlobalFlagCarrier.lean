import InfoGeometry.Algebra.Zorn.G2ParabolicGeometry
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Type-level carrier for the certified global incidence flags

The incidence table already supplies the finite set of all point-line flags.
This owner packages that set as a subtype, keeping the future automorphism
action separate from the carrier and its cardinality.
-/

namespace InfoGeometry.Algebra.Zorn.G2GlobalFlagCarrier

open InfoGeometry.Algebra.Zorn.G2ParabolicGeometry

abbrev GlobalFlag := {f : Point × Line // f ∈ flags}

noncomputable instance : Fintype GlobalFlag :=
  Fintype.ofFinset flags (by
    intro f
    rfl)

theorem globalFlag_card : Fintype.card GlobalFlag = 189 := by
  calc
    Fintype.card GlobalFlag = flags.card :=
      Fintype.card_ofFinset flags (by intro f; rfl)
    _ = 189 := flag_card

end InfoGeometry.Algebra.Zorn.G2GlobalFlagCarrier
