import InfoGeometry.RootSystem.D4DualCosetNormalForm
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Cardinality of the `D₄` discriminant carrier

The explicit four-coset normal form and the previously proved distinctness of
the four representatives give an actual finite equivalence.  No group
identification or triality action is asserted here.
-/

namespace InfoGeometry.RootSystem.D4

theorem discriminantRepresentatives_surjective :
    Function.Surjective discriminantRepresentatives := by
  intro q
  obtain ⟨x, rfl⟩ := discriminantMap_surjective q
  obtain ⟨i, hi⟩ := discriminantMap_eq_one_of_four_representatives x
  exact ⟨i, hi.symm⟩

noncomputable def discriminantRepresentativeEquiv :
    Fin 4 ≃ discriminantCarrier :=
  Equiv.ofBijective discriminantRepresentatives
    ⟨discriminantRepresentatives_injective,
      discriminantRepresentatives_surjective⟩

instance : Finite discriminantCarrier :=
  Finite.of_surjective discriminantRepresentatives
    discriminantRepresentatives_surjective

noncomputable instance : Fintype discriminantCarrier := Fintype.ofFinite _

theorem discriminantCarrier_fintype_card :
    Fintype.card discriminantCarrier = 4 := by
  classical
  calc
    Fintype.card discriminantCarrier = Fintype.card (Fin 4) :=
      Fintype.card_congr discriminantRepresentativeEquiv.symm
    _ = 4 := Fintype.card_fin 4

end InfoGeometry.RootSystem.D4
