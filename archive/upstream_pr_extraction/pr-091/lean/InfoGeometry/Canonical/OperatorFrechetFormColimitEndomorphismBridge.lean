import InfoGeometry.Canonical.OperatorFrechetFormColimit
import InfoGeometry.Canonical.TopCatColimitCompatibleEndomorphism

/-!
# Concrete bridge for the native Toeplitz exchange

The existing native ternary Toeplitz owner constructs its colimit exchange via
`colim.map`.  This owner identifies that map with the generic universal
property construction for a compatible TopCat endomorphism family.
-/

namespace InfoGeometry.Canonical.OperatorFrechetFormColimit.NativeToeplitzCuntzThree

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.TopCatColimitCompatibleEndomorphism

theorem exchangeColimit_eq_induced :
    exchangeColimit = induced stageDiagram exchangeNat := by
  apply colimit.hom_ext
  intro n
  rw [exchangeColimit_stage,
    induced_on_stage stageDiagram exchangeNat n]
  rfl

theorem induced_exchange_involutive :
    induced stageDiagram exchangeNat ≫
        induced stageDiagram exchangeNat =
      𝟙 (colimit stageDiagram) := by
  rw [induced_comp, exchangeNat_involutive,
    TopCatColimitCompatibleEndomorphism.induced_id]

noncomputable def exchangeColimitIso :
    colimit stageDiagram ≅ colimit stageDiagram :=
  inducedIso stageDiagram exchangeNat exchangeNat
    exchangeNat_involutive exchangeNat_involutive

theorem exchangeColimitIso_hom_eq_exchangeColimit :
    (exchangeColimitIso).hom = exchangeColimit := by
  exact (exchangeColimit_eq_induced).symm

end InfoGeometry.Canonical.OperatorFrechetFormColimit.NativeToeplitzCuntzThree
