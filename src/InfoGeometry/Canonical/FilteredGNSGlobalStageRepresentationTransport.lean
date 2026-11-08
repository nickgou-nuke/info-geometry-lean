import InfoGeometry.Canonical.FilteredGNSGlobalStageRepresentation
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.StarAlgEquivTransport
import Mathlib.Analysis.Normed.Operator.ContinuousAlgEquiv

/-!
# Transport normal form for global GNS stage representations

The global stage representation is defined by conjugating a cofinal-tail
representation through a unitary `LinearIsometryEquiv`.  This owner records
that definition in the generic `StarAlgEquivTransport` normal form, so
composition and inverse-coherence lemmas apply without unfolding operator
conjugation at each use site.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredGNSGlobalStageRepresentationTransport

set_option synthInstance.maxHeartbeats 80000
set_option linter.unusedSectionVars false

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNSHilbertColimit
open CStarStateColimit.Native.FilteredGNSGlobalStageRepresentation
open CStarStateColimit.Native.FilteredGNSTailRepresentation
open CStarStateColimit.Native.FilteredGNSTailStarRepresentation
open CStarStateColimit.Native.FilteredGNSCofinalTail
open InfoGeometry.Canonical.FilteredIsometricInnerProductColimit
open InfoGeometry.Canonical.FilteredIsometricInnerProductDirectLimit
open InfoGeometry.Canonical.FilteredIsometricHilbertCompletion

universe u

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable [DecidableEq I]
variable (Stage : I → Type u)
variable [∀ i, CStarAlgebra (Stage i)]
variable [∀ i, PartialOrder (Stage i)]
variable [∀ i, StarOrderedRing (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)
variable
  (ω :
    ContinuousStarInductiveSystem.CompatibleStateFamily
      Stage sys)

local notation "E" =>
  TailGNSStage Stage sys ω
local notation "S" =>
  tailGNSIsometricDirectSystem Stage sys ω

/-- The concrete global stage representation is exactly the generic star
algebra transport of the tail representation along the canonical unitary. -/
theorem globalStageRepresentation_eq_transport
    {i₀ : I} :
    globalStageRepresentationStarAlgHom Stage sys ω i₀ =
      StarAlgEquivTransport.map
        ((tailHilbertGlobalEquiv Stage sys ω i₀).conjStarAlgEquiv)
        (tailCompletedRepresentationStarAlgHom Stage sys ω i₀) := by
  rfl

@[simp] theorem globalStageRepresentation_transport_apply
    {i₀ : I} (a : Stage i₀) :
    StarAlgEquivTransport.map
        ((tailHilbertGlobalEquiv Stage sys ω i₀).conjStarAlgEquiv)
        (tailCompletedRepresentationStarAlgHom Stage sys ω i₀) a =
      (tailHilbertGlobalEquiv Stage sys ω i₀).conjStarAlgEquiv
        (tailCompletedRepresentationStarAlgHom Stage sys ω i₀ a) := by
  rfl

/- The conjugation formula is topological at the vector level: it is a
composition of the continuous unitary, the completed tail operator, and the
continuous inverse unitary. -/
theorem globalStageRepresentation_conjugation_continuous
    {i₀ : I} (a : Stage i₀) :
    Continuous
      (fun z : GNSHilbertColimit Stage sys ω =>
        tailHilbertGlobalEquiv Stage sys ω i₀
          (tailCompletedRepresentation Stage sys ω a
            ((tailHilbertGlobalEquiv Stage sys ω i₀).symm z))) := by
  exact
    (tailHilbertGlobalEquiv Stage sys ω i₀).continuous.comp
      ((tailCompletedRepresentation Stage sys ω a).continuous.comp
        (tailHilbertGlobalEquiv Stage sys ω i₀).symm.continuous)

theorem globalStageRepresentation_continuous_apply
    {i₀ : I} (a : Stage i₀) :
    Continuous
      (globalStageRepresentationStarAlgHom Stage sys ω i₀ a) :=
  (globalStageRepresentationStarAlgHom Stage sys ω i₀ a).continuous

/-- The unitary conjugation also has a native operator-norm homeomorphism
between the tail and global bounded-operator algebras. -/
def globalStageOperatorConjugationHomeomorph
    (i₀ : I) :
    (HilbertDirectLimit (E i₀) (S i₀) →L[ℂ]
        HilbertDirectLimit (E i₀) (S i₀)) ≃ₜ
      (GNSHilbertColimit Stage sys ω →L[ℂ]
        GNSHilbertColimit Stage sys ω) :=
  (ContinuousLinearEquiv.conjContinuousAlgEquiv
    (tailHilbertGlobalEquiv Stage sys ω i₀).toContinuousLinearEquiv).toHomeomorph

@[simp] theorem globalStageOperatorConjugationHomeomorph_apply
    {i₀ : I}
    (T : HilbertDirectLimit (E i₀) (S i₀) →L[ℂ]
      HilbertDirectLimit (E i₀) (S i₀)) :
    globalStageOperatorConjugationHomeomorph Stage sys ω i₀ T =
      (tailHilbertGlobalEquiv Stage sys ω i₀).conjStarAlgEquiv T :=
  rfl

theorem globalStageOperatorConjugationHomeomorph_continuous
    (i₀ : I) :
    Continuous (globalStageOperatorConjugationHomeomorph Stage sys ω i₀) :=
  (ContinuousLinearEquiv.conjContinuousAlgEquiv
    (tailHilbertGlobalEquiv Stage sys ω i₀).toContinuousLinearEquiv).continuous

theorem globalStageOperatorConjugationHomeomorph_continuous_inv
    (i₀ : I) :
    Continuous
      (globalStageOperatorConjugationHomeomorph Stage sys ω i₀).symm :=
  (ContinuousLinearEquiv.conjContinuousAlgEquiv
    (tailHilbertGlobalEquiv Stage sys ω i₀).toContinuousLinearEquiv).symm.continuous

end CStarStateColimit.Native.FilteredGNSGlobalStageRepresentationTransport
