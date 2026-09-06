import InfoGeometry.Canonical.StokesQutritChannelBasis

/-!
# Finite Weyl star product on the six-state symbol space

The owned Stokes--Weyl basis identifies the six-state operator algebra with a
finite function space.  This file transports matrix multiplication across
that linear equivalence.  The resulting product is an exact finite symbol
calculus: associativity and the unit are inherited from `M₆(ℂ)`.

This is deliberately not a claim about the Kontsevich formality theorem or a
smooth Poisson manifold.  It is the finite Weyl/operator-multiplication layer
that can be proved natively from the existing basis owner.
-/

noncomputable section

namespace InfoGeometry.Canonical.FiniteWeylStarProduct

open InfoGeometry.Canonical.TwoSheetOperatorCoordinates
open InfoGeometry.Canonical.StokesQutritChannelBasis

abbrev WeylSymbol6 := Fin 4 × (Fin 3 × Fin 3) → ℂ

/-- The coefficient-to-operator map supplied by the owned Stokes--Weyl basis. -/
def symbolToOperator : WeylSymbol6 ≃ₗ[ℂ] M6C :=
  stokesWeylBasis.equivFun.symm

/-- The exact finite Weyl product, transported from matrix multiplication. -/
def finiteWeylStar (f g : WeylSymbol6) : WeylSymbol6 :=
  symbolToOperator.symm (symbolToOperator f * symbolToOperator g)

/-- The symbol of the identity operator. -/
def finiteWeylUnit : WeylSymbol6 :=
  symbolToOperator.symm (1 : M6C)

theorem symbolToOperator_finiteWeylStar (f g : WeylSymbol6) :
    symbolToOperator (finiteWeylStar f g) =
      symbolToOperator f * symbolToOperator g := by
  simp [finiteWeylStar]

theorem finiteWeylStar_assoc (f g h : WeylSymbol6) :
    finiteWeylStar (finiteWeylStar f g) h =
      finiteWeylStar f (finiteWeylStar g h) := by
  apply symbolToOperator.injective
  simp only [symbolToOperator_finiteWeylStar]
  exact mul_assoc _ _ _

theorem finiteWeylUnit_star (f : WeylSymbol6) :
    finiteWeylStar finiteWeylUnit f = f := by
  apply symbolToOperator.injective
  simp [symbolToOperator_finiteWeylStar, finiteWeylUnit]

theorem finiteWeylStar_unit (f : WeylSymbol6) :
    finiteWeylStar f finiteWeylUnit = f := by
  apply symbolToOperator.injective
  simp [symbolToOperator_finiteWeylStar, finiteWeylUnit]

theorem finiteWeylStar_mul_correspondence (f g : WeylSymbol6) :
    symbolToOperator (finiteWeylStar f g) =
      symbolToOperator f * symbolToOperator g :=
  symbolToOperator_finiteWeylStar f g

@[simp] theorem finiteWeylStar_zero_left (f : WeylSymbol6) :
    finiteWeylStar 0 f = 0 := by
  apply symbolToOperator.injective
  simp [symbolToOperator_finiteWeylStar]

@[simp] theorem finiteWeylStar_zero_right (f : WeylSymbol6) :
    finiteWeylStar f 0 = 0 := by
  apply symbolToOperator.injective
  simp [symbolToOperator_finiteWeylStar]

theorem finiteWeylStar_add_left (f g h : WeylSymbol6) :
    finiteWeylStar (f + g) h =
      finiteWeylStar f h + finiteWeylStar g h := by
  apply symbolToOperator.injective
  simp only [symbolToOperator_finiteWeylStar, map_add, add_mul]

theorem finiteWeylStar_add_right (f g h : WeylSymbol6) :
    finiteWeylStar f (g + h) =
      finiteWeylStar f g + finiteWeylStar f h := by
  apply symbolToOperator.injective
  simp only [symbolToOperator_finiteWeylStar, map_add, mul_add]

theorem finiteWeylStar_smul_left (r : ℂ) (f g : WeylSymbol6) :
    finiteWeylStar (r • f) g = r • finiteWeylStar f g := by
  apply symbolToOperator.injective
  simp only [symbolToOperator_finiteWeylStar, map_smul, smul_mul_assoc]

theorem finiteWeylStar_smul_right (r : ℂ) (f g : WeylSymbol6) :
    finiteWeylStar f (r • g) = r • finiteWeylStar f g := by
  apply symbolToOperator.injective
  simp only [symbolToOperator_finiteWeylStar, map_smul, mul_smul_comm]

/- The finite involution is transported from matrix adjoint.  This records the
   *-algebra law only; it makes no analytic completion or positivity claim. -/
def finiteWeylInvolution (f : WeylSymbol6) : WeylSymbol6 :=
  symbolToOperator.symm (star (symbolToOperator f))

@[simp] theorem finiteWeylInvolution_quantized (A : M6C) :
    finiteWeylInvolution (symbolToOperator.symm A) =
      symbolToOperator.symm (star A) := by
  simp [finiteWeylInvolution]

theorem finiteWeylInvolution_mul (f g : WeylSymbol6) :
    finiteWeylInvolution (finiteWeylStar f g) =
      finiteWeylStar (finiteWeylInvolution g) (finiteWeylInvolution f) := by
  apply symbolToOperator.injective
  simp [finiteWeylInvolution, finiteWeylStar,
    map_mul, star_mul]

end InfoGeometry.Canonical.FiniteWeylStarProduct

end noncomputable section
