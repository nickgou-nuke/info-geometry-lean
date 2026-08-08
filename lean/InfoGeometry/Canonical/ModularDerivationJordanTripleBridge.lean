import InfoGeometry.Algebra.JordanInnerDerivations
import InfoGeometry.Algebra.NonAssocDerivation
import InfoGeometry.Canonical.BogoliubovFrameDeformationEntropy
import InfoGeometry.Canonical.OperatorialFierzDerivationBridge
import InfoGeometry.Canonical.SuperJordanLie
import InfoGeometry.Canonical.SuperUnified
import InfoGeometry.Quantum.GeometricTensorOperatorLift

/-!
# Modular derivations, two-form transport, and Jordan--Lie splitting

This file connects existing owner theorems without identifying distinct
carriers:

* a Level-0 logarithmic variation generates an inner commutator derivation;
* ring homomorphisms preserve inner commutators;
* on doubled-space endomorphisms the commutator is the Lie half of the
  associative product, while the anticommutator is its Jordan half;
* the operator-induced Berry two-form is linear in the commutator generator.

The nonassociative Jordan and polarized-triple derivation theorems remain owned
by `JordanInnerDerivations` and `NonAssocDerivation`.
-/

noncomputable section

namespace InfoGeometry.Canonical.ModularDerivationJordanTripleBridge

open scoped InnerProductSpace
open InfoGeometry.Canonical.BogoliubovFrameDeformationEntropy
open InfoGeometry.Canonical.OperatorialFierz
open InfoGeometry.OperatorAlgebra.SpatialDerivativeLogarithmicVariation
open InfoGeometry.Quantum.GeometricQuantumTensor

/-! ## Algebraic naturality of the modular commutator -/

variable {A B : Type*}
variable [NormedRing A] [NormedAlgebra ℝ A] [StarRing A]
variable [NormedRing B] [NormedAlgebra ℝ B] [StarRing B]

omit [StarRing A] [StarRing B] in
/-- A ring homomorphism transports an inner commutator exactly. -/
theorem map_innerDerivation
    (f : A →+* B) (K X : A) :
    f (innerDerivation K X) =
      innerDerivation (f K) (f X) := by
  simp [innerDerivation]

omit [StarRing A] in
/-- Negating the generator negates its inner derivation. -/
theorem innerDerivation_neg_generator
    (K X : A) :
    innerDerivation (-K) X = -(innerDerivation K X) := by
  simp only [innerDerivation]
  noncomm_ring

/-! ## Level-0 logarithmic variation to modular derivation -/

variable {E : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => InfoGeometry.Krein.DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

variable
  {V : InfoGeometry.Canonical.BogoliubovVielbein.BogoliubovVielbeinBundle
    (E := E)}
  {R : UnitFrameRealization V}

/--
For a property exponential relative frame, `d ln Delta = -K'` induces the
opposite inner commutator derivation.
-/
theorem innerDerivation_dLnDelta_eq_neg_generatorDerivative
    (G : ExponentialGenerator R)
    {t : ℝ} {K' : EndH}
    (hK : HasDerivAt G.K K' t)
    (hcomm : Commute K' (G.K t))
    (X : EndH) :
    innerDerivation (R.dLnDelta t) X =
      -(innerDerivation K' X) := by
  rw [G.dLnDelta_eq_neg_generatorDerivative hK hcomm]
  exact innerDerivation_neg_generator K' X

/--
The same sign law after applying the split-`Cl(1,1)` Berry two-form lift.
-/
theorem berryTwoForm_innerDerivation_dLnDelta_eq_neg
    (G : ExponentialGenerator R)
    {t : ℝ} {K' : EndH}
    (hK : HasDerivAt G.K K' t)
    (hcomm : Commute K' (G.K t))
    (X : EndH) :
    berryTwoFormJEpsOfOperator (E := E)
        (innerDerivation (R.dLnDelta t) X)
      =
    -berryTwoFormJEpsOfOperator (E := E)
        (innerDerivation K' X) := by
  rw [innerDerivation_dLnDelta_eq_neg_generatorDerivative
    G hK hcomm X]
  exact berryTwoFormJEpsOfOperator_neg
    (E := E) (innerDerivation K' X)

/-! ## Clifford associative product to Jordan--Lie channels -/

/-- The modular commutator is twice the native antisymmetric Lie product. -/
theorem innerDerivation_eq_two_smul_lieProduct
    (K X : EndH) :
    innerDerivation K X =
      (2 : ℝ) • InfoGeometry.Canonical.SuperJordanLie.lieProduct K X := by
  simpa [innerDerivation,
    InfoGeometry.Canonical.BogoliubovFockSuper.fockCommutator,
    InfoGeometry.Canonical.BogoliubovFockSuper.superBracket_even_left] using
    (InfoGeometry.Canonical.SuperJordanLie.fockCommutator_eq_two_smul_lieProduct
      (E := E) K X)

/--
The doubled-space associative product is the sum of its symmetric Jordan
channel and half its modular commutator.
-/
theorem associativeProduct_eq_jordan_add_half_innerDerivation
    (K X : EndH) :
    K.comp X =
      InfoGeometry.SuperUnified.jordanProduct K X +
        (2 : ℝ)⁻¹ • innerDerivation K X := by
  simpa [InfoGeometry.SuperUnified.lieBracket, innerDerivation] using
    (InfoGeometry.SuperUnified.clifford_decomposition
      (E := E) K X)

/-! ## Existing nonassociative triple-product endpoint -/

variable {S J : Type*}
  [CommRing S] [AddCommGroup J] [Module S J]

/--
A quadratic derivation acts in all three slots of the polarized Jordan triple
product.  This bridge theorem exposes the existing nonassociative endpoint
without replacing its owner proof.
-/
theorem quadraticDerivation_acts_on_polarizedTriple
    (U : J → J → J)
    (D : Module.End S J)
    (hD : InfoGeometry.Algebra.NonAssocDerivation.IsQuadraticDerivation U D)
    (haddLeft : ∀ X₁ X₂ Y Z : J,
      InfoGeometry.Algebra.NonAssocDerivation.polarizedU U (X₁ + X₂) Y Z =
        InfoGeometry.Algebra.NonAssocDerivation.polarizedU U X₁ Y Z +
          InfoGeometry.Algebra.NonAssocDerivation.polarizedU U X₂ Y Z)
    (haddRight : ∀ X Y Z₁ Z₂ : J,
      InfoGeometry.Algebra.NonAssocDerivation.polarizedU U X Y (Z₁ + Z₂) =
        InfoGeometry.Algebra.NonAssocDerivation.polarizedU U X Y Z₁ +
          InfoGeometry.Algebra.NonAssocDerivation.polarizedU U X Y Z₂)
    (houter : ∀ X Y Z : J,
      InfoGeometry.Algebra.NonAssocDerivation.polarizedU U X Y Z =
        InfoGeometry.Algebra.NonAssocDerivation.polarizedU U Z Y X)
    (X Y Z : J) :
    D (InfoGeometry.Algebra.NonAssocDerivation.polarizedU U X Y Z) =
      InfoGeometry.Algebra.NonAssocDerivation.polarizedU U (D X) Y Z +
        InfoGeometry.Algebra.NonAssocDerivation.polarizedU U X (D Y) Z +
          InfoGeometry.Algebra.NonAssocDerivation.polarizedU U X Y (D Z) :=
  InfoGeometry.Algebra.NonAssocDerivation.map_polarizedU
    U D hD haddLeft haddRight houter X Y Z

end InfoGeometry.Canonical.ModularDerivationJordanTripleBridge
