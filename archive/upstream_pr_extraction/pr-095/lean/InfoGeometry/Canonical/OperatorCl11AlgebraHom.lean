import Mathlib.Algebra.Category.Ring.Colimits
import InfoGeometry.Canonical.OperatorCl11WittBasis

/-!
# Functoriality of the abstract operator `Cl(1,1)` packet

The involution and anticommutation relations are transported by ordinary
unital ring homomorphisms.  Consequently the relations survive the native
`RingCat` colimit injections without introducing an auxiliary colimit carrier.
-/

open CategoryTheory CategoryTheory.Limits

variable {A B : Type*} [Ring A] [Ring B]

namespace InfoGeometry.Canonical.OperatorCl11AlgebraHom

open InfoGeometry.Canonical.OperatorCl11WittBasis

theorem ringHom_map_operatorCl11
    (Γ J : A) [hCl : OperatorCl11 Γ J] (φ : A →+* B) :
    OperatorCl11 (φ Γ) (φ J) where
  gamma_sq := by
    have h := congrArg φ hCl.gamma_sq
    simpa only [map_mul, map_one] using h
  exchange_sq := by
    have h := congrArg φ hCl.exchange_sq
    simpa only [map_mul, map_one] using h
  exchange_gamma_anticomm := by
    have h := congrArg φ hCl.exchange_gamma_anticomm
    simpa only [map_mul, map_add, map_neg] using h

theorem ringCat_colimit_ι_operatorCl11
    {JIndex : Type*} [Category JIndex]
    {F : JIndex ⥤ RingCat} [HasColimit F]
    (j : JIndex) (Γ J : F.obj j)
    [hCl : OperatorCl11 Γ J] :
    OperatorCl11 ((colimit.ι F j).hom Γ) ((colimit.ι F j).hom J) := by
  exact ringHom_map_operatorCl11 Γ J (colimit.ι F j).hom

end InfoGeometry.Canonical.OperatorCl11AlgebraHom
