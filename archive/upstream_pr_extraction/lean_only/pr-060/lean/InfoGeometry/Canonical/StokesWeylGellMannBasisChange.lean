import Mathlib
import InfoGeometry.Canonical.StokesQutritChannelBasis
import InfoGeometry.Canonical.StokesGellMannChannelBasis
import InfoGeometry.Canonical.FiniteWeylStarProduct

/-!
# Coordinate change between the two verified 36-channel bases

`StokesQutritChannelBasis` and `StokesGellMannChannelBasis` prove two bases of
the same finite matrix algebra.  This owner records only their canonical
coordinate change; no extra physical identification is assumed.
-/

noncomputable section

namespace InfoGeometry.Canonical.StokesWeylGellMannBasisChange

open InfoGeometry.Canonical.StokesQutritChannelBasis
open InfoGeometry.Canonical.StokesGellMannChannelBasis

abbrev WeylIndex := Fin 4 × (Fin 3 × Fin 3)
abbrev GellMannIndex := Fin 4 × Fin 9
abbrev M6C := Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ

abbrev WeylFunctionSymbol := WeylIndex → ℂ
abbrev GellMannFunctionSymbol := GellMannIndex → ℂ

/-- The unique linear coordinate change induced by the two certified bases. -/
def stokesWeylToGellMann :
    (WeylIndex →₀ ℂ) ≃ₗ[ℂ] (GellMannIndex →₀ ℂ) :=
  (stokesWeylBasis.repr.symm).trans stokesGellMannBasis.repr

@[simp] theorem stokesWeylToGellMann_apply (A : M6C) :
    stokesWeylToGellMann (stokesWeylBasis.repr A) =
      stokesGellMannBasis.repr A := by
  simp [stokesWeylToGellMann]

@[simp] theorem stokesWeylToGellMann_symm_apply (A : M6C) :
    stokesWeylToGellMann.symm (stokesGellMannBasis.repr A) =
      stokesWeylBasis.repr A := by
  simp [stokesWeylToGellMann]

theorem stokesWeylToGellMann_apply_channel (x : WeylIndex) :
    stokesWeylToGellMann (stokesWeylBasis.repr (stokesWeylChannel x.1 x.2)) =
      stokesGellMannBasis.repr (stokesWeylChannel x.1 x.2) := by
  exact stokesWeylToGellMann_apply _

theorem basis_change_is_bijective :
    Function.Bijective stokesWeylToGellMann :=
  stokesWeylToGellMann.bijective

/-! The finite star-product owner uses function symbols (`equivFun`), while
the basis API above uses finitely-supported coordinates (`repr`).  This is
the canonical coordinate change at the former interface. -/

def stokesWeylFunctionToGellMannFunction :
    WeylFunctionSymbol ≃ₗ[ℂ] GellMannFunctionSymbol :=
  (stokesWeylBasis.equivFun.symm).trans stokesGellMannBasis.equivFun

def gellMannSymbolToOperator :
    GellMannFunctionSymbol ≃ₗ[ℂ] M6C :=
  stokesGellMannBasis.equivFun.symm

@[simp] theorem gellMannSymbolToOperator_apply_coordinate_change
    (f : WeylFunctionSymbol) :
    gellMannSymbolToOperator
        (stokesWeylFunctionToGellMannFunction f) =
      InfoGeometry.Canonical.FiniteWeylStarProduct.symbolToOperator f := by
  change stokesGellMannBasis.equivFun.symm
      (stokesGellMannBasis.equivFun (stokesWeylBasis.equivFun.symm f)) =
    stokesWeylBasis.equivFun.symm f
  exact stokesGellMannBasis.equivFun.symm_apply_apply _

def finiteGellMannStar (f g : GellMannFunctionSymbol) :
    GellMannFunctionSymbol :=
  gellMannSymbolToOperator.symm
    (gellMannSymbolToOperator f * gellMannSymbolToOperator g)

def finiteGellMannUnit : GellMannFunctionSymbol :=
  gellMannSymbolToOperator.symm (1 : M6C)

theorem finiteGellMannStar_assoc
    (f g h : GellMannFunctionSymbol) :
    finiteGellMannStar (finiteGellMannStar f g) h =
      finiteGellMannStar f (finiteGellMannStar g h) := by
  apply gellMannSymbolToOperator.injective
  simp only [finiteGellMannStar, LinearEquiv.apply_symm_apply]
  exact mul_assoc _ _ _

theorem finiteGellMannUnit_star (f : GellMannFunctionSymbol) :
    finiteGellMannStar finiteGellMannUnit f = f := by
  apply gellMannSymbolToOperator.injective
  simp [finiteGellMannStar, finiteGellMannUnit]

theorem finiteGellMannStar_unit (f : GellMannFunctionSymbol) :
    finiteGellMannStar f finiteGellMannUnit = f := by
  apply gellMannSymbolToOperator.injective
  simp [finiteGellMannStar, finiteGellMannUnit]

theorem finiteGellMannStar_coordinate_change (f g : WeylFunctionSymbol) :
    finiteGellMannStar
        (stokesWeylFunctionToGellMannFunction f)
        (stokesWeylFunctionToGellMannFunction g) =
      stokesWeylFunctionToGellMannFunction
        (InfoGeometry.Canonical.FiniteWeylStarProduct.finiteWeylStar f g) := by
  apply gellMannSymbolToOperator.injective
  simp only [finiteGellMannStar,
    gellMannSymbolToOperator_apply_coordinate_change,
    InfoGeometry.Canonical.FiniteWeylStarProduct.symbolToOperator_finiteWeylStar,
    LinearEquiv.apply_symm_apply]

theorem finiteGellMannStar_is_associative_and_unital :
    (∀ f g h, finiteGellMannStar (finiteGellMannStar f g) h =
      finiteGellMannStar f (finiteGellMannStar g h)) ∧
    (∀ f, finiteGellMannStar finiteGellMannUnit f = f) ∧
    (∀ f, finiteGellMannStar f finiteGellMannUnit = f) := by
  exact ⟨finiteGellMannStar_assoc, finiteGellMannUnit_star,
    finiteGellMannStar_unit⟩

end InfoGeometry.Canonical.StokesWeylGellMannBasisChange

end noncomputable section
