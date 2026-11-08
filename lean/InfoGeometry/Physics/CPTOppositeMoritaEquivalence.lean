import InfoGeometry.Physics.AlgebraicTomitaTakesakiBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.TomitaTakesakiModularFlow
import Mathlib.RingTheory.Morita.Basic

/-!
  A native categorical Morita bridge for a real-structure-induced opposite
  frame.  This owner proves only the algebraic/module-category statement:
  an anti-automorphism identifies `Aᵐᵒᵖ` with `A`, hence their module
  categories are equivalent.  It does not assert an analytic Hilbert
  bimodule, a spectral-triple Hodge condition, or a full commutant equality.
-/

namespace InfoGeometry.Physics

open MulOpposite

variable {A : Type*} [Ring A]

namespace CPTOppositeMorita

/-! The full commutant equality is exposed with the standard-form/Tomita
 hypothesis explicit.  It is not derivable from anti-multiplicativity alone. -/
theorem full_commutant_eq_of_tomita_data
    (T : TomitaConjugationData A) (M : Set A)
    (hT : TomitaCommutantData A T M) :
    tomitaImage A T M = Commutant A M :=
  tomita_image_eq_commutant A T M hT

private def oppositeAlgEquivOver
    {K : Type*} [CommSemiring K] [Algebra K A]
    (J : AntiAutomorphism A)
    (hK : ∀ r : K, J.toFun (algebraMap K A r) = algebraMap K A r) :
    Aᵐᵒᵖ ≃ₐ[K] A :=
  AlgEquiv.ofRingEquiv (f := antiOppositeRingEquiv J) (by
    intro r
    simpa using hK r)

/-- Scalar-compatible version: when the anti-automorphism fixes the scalar
subalgebra, the opposite and original module categories are equivalent over
that scalar base. -/
noncomputable def oppositeMoritaEquivalenceOver
    {K : Type*} [CommSemiring K] [Algebra K A]
    (J : AntiAutomorphism A)
    (hK : ∀ r : K, J.toFun (algebraMap K A r) = algebraMap K A r) :
    MoritaEquivalence K Aᵐᵒᵖ A :=
  MoritaEquivalence.ofAlgEquiv (oppositeAlgEquivOver J hK)

theorem oppositeMoritaEquivalenceOver_isMoritaEquivalent
    {K : Type*} [CommSemiring K] [Algebra K A]
    (J : AntiAutomorphism A)
    (hK : ∀ r : K, J.toFun (algebraMap K A r) = algebraMap K A r) :
    IsMoritaEquivalent K Aᵐᵒᵖ A :=
  ⟨Nonempty.intro (oppositeMoritaEquivalenceOver J hK)⟩

private def oppositeAlgEquiv (J : AntiAutomorphism A) : Aᵐᵒᵖ ≃ₐ[ℤ] A :=
  AlgEquiv.ofRingEquiv (f := antiOppositeRingEquiv J) (by
    intro n
    simp)

/-- The opposite frame and the original frame have equivalent module
categories, via the native Mathlib `MoritaEquivalence` object. -/
noncomputable def oppositeMoritaEquivalence
    (J : AntiAutomorphism A) :
    MoritaEquivalence ℤ Aᵐᵒᵖ A :=
  MoritaEquivalence.ofAlgEquiv (oppositeAlgEquiv J)

theorem oppositeMoritaEquivalence_isMoritaEquivalent
    (J : AntiAutomorphism A) :
    IsMoritaEquivalent ℤ Aᵐᵒᵖ A :=
  ⟨Nonempty.intro (oppositeMoritaEquivalence J)⟩

theorem oppositeMoritaEquivalence_two_cycle
    (J : AntiAutomorphism A) :
    (antiOppositeRingEquiv J).symm.trans (antiOppositeRingEquiv J) =
      RingEquiv.refl A := by
  ext a
  exact J.inv a

end CPTOppositeMorita

end InfoGeometry.Physics
