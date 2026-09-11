import InfoGeometry.Exceptional.G2ArtinPresentation
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.KleinNativeSemidirectProductBridge
import InfoGeometry.Algebra.Zorn.G2CoordinateCoxeterRelations
import InfoGeometry.Canonical.KleinPresentedGroup
import InfoGeometry.Canonical.KleinMonodromyRepresentationSpace
import InfoGeometry.Exceptional.G2KleinRootLabelBridge

/-!
# Klein/Artin bridge on the actual `G₂` Artin carrier

This file deliberately does not identify the Klein glide with a Weyl
reflection.  It packages the missing common-carrier datum: a glide and a
monodromy element living in `ArtinG2` and satisfying the Klein conjugation
relation.  Once that datum is supplied, the existing universal Klein
representation gives the canonical map into the Artin carrier.
-/

namespace InfoGeometry.Exceptional.G2ArtinKleinBridge

open InfoGeometry.Canonical.KleinPresentedGroup
open InfoGeometry.Canonical.KleinMonodromyRepresentationSpace
open InfoGeometry.Exceptional.G2ArtinPresentation
open InfoGeometry.Canonical.KleinNativeSemidirectProductBridge
open InfoGeometry.Algebra.Zorn.G2CoordinateCoxeterRelations
open InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction
open InfoGeometry.Exceptional.G2KleinRootLabelBridge

structure G2ArtinKleinActionData where
  glide : ArtinG2
  monodromy : ArtinG2
  glide_conjugates_monodromy :
    glide * monodromy * glide⁻¹ = monodromy⁻¹

def kleinToArtin (D : G2ArtinKleinActionData) : KleinGroup →* ArtinG2 :=
  kleinRep D.glide D.monodromy D.glide_conjugates_monodromy

theorem kleinToArtin_glide (D : G2ArtinKleinActionData) :
    kleinToArtin D (toKlein genA) = D.glide := by
  exact (kleinRep_relator_relation D.glide D.monodromy
    D.glide_conjugates_monodromy).1

theorem kleinToArtin_monodromy (D : G2ArtinKleinActionData) :
    kleinToArtin D (toKlein genB) = D.monodromy := by
  exact (kleinRep_relator_relation D.glide D.monodromy
    D.glide_conjugates_monodromy).2

theorem g2Artin_kleinConjugation (D : G2ArtinKleinActionData) :
    kleinToArtin D (toKlein genA) *
        kleinToArtin D (toKlein genB) *
        (kleinToArtin D (toKlein genA))⁻¹ =
      (kleinToArtin D (toKlein genB))⁻¹ := by
  rw [kleinToArtin_glide D, kleinToArtin_monodromy D]
  exact D.glide_conjugates_monodromy

/-- The canonical morphism from a concrete Klein-monodromy carrier whose
generators already live in the `G₂` Artin carrier. -/
def kleinMonodromyToArtin
    (rho : KleinMonodromyPair ArtinG2) : KleinGroup →* ArtinG2 :=
  kleinRep rho.a rho.b rho.relation

@[simp] theorem kleinMonodromyToArtin_a
    (rho : KleinMonodromyPair ArtinG2) :
    kleinMonodromyToArtin rho (toKlein genA) = rho.a := by
  exact (kleinRep_relator_relation rho.a rho.b rho.relation).1

@[simp] theorem kleinMonodromyToArtin_b
    (rho : KleinMonodromyPair ArtinG2) :
    kleinMonodromyToArtin rho (toKlein genB) = rho.b := by
  exact (kleinRep_relator_relation rho.a rho.b rho.relation).2

theorem kleinMonodromyToArtin_relation
    (rho : KleinMonodromyPair ArtinG2) :
    kleinMonodromyToArtin rho (toKlein genA) *
        kleinMonodromyToArtin rho (toKlein genB) *
        (kleinMonodromyToArtin rho (toKlein genA))⁻¹ =
      (kleinMonodromyToArtin rho (toKlein genB))⁻¹ := by
  rw [kleinMonodromyToArtin_a, kleinMonodromyToArtin_b]
  exact rho.relation

/-! ## Artin representation readback

The following pair lives in the concrete permutation quotient of `ArtinG2`.
It is not an assertion that the Artin generators themselves are involutions.
-/

noncomputable def artinCoordinateKleinPair :
    InfoGeometry.Canonical.KleinMonodromyRepresentationSpace.KleinMonodromyPair
      (Equiv.Perm G2CoordinateRoot) := by
  exact ⟨(coordinateAction sigmaZero,
    coordinateAction (sigmaOne * sigmaZero)), by
      rw [map_mul, coordinateAction_sigmaZero, coordinateAction_sigmaOne]
      change s1Root * (s2Root * s1Root) * s1Root =
        (s2Root * s1Root)⁻¹
      simpa [cRoot, Equiv.Perm.mul_def] using coordinate_s1_conj_c⟩

noncomputable def kleinToArtinCoordinate : KleinGroup →* Equiv.Perm G2CoordinateRoot :=
  kleinRep artinCoordinateKleinPair.a artinCoordinateKleinPair.b
    artinCoordinateKleinPair.relation

@[simp] theorem kleinToArtinCoordinate_genA :
    kleinToArtinCoordinate (toKlein genA) = s1Root := by
  change coordinateAction sigmaZero = s1Root
  exact coordinateAction_sigmaZero

@[simp] theorem kleinToArtinCoordinate_genB :
    kleinToArtinCoordinate (toKlein genB) = s2Root * s1Root := by
  change coordinateAction (sigmaOne * sigmaZero) = s2Root * s1Root
  rw [map_mul, coordinateAction_sigmaOne, coordinateAction_sigmaZero]

theorem g2Artin_coordinateAction_kleinConjugation :
    coordinateAction sigmaZero *
        coordinateAction (sigmaOne * sigmaZero) *
        (coordinateAction sigmaZero)⁻¹ =
      (coordinateAction (sigmaOne * sigmaZero))⁻¹ := by
  rw [coordinateAction_sigmaZero]
  change s1Root * coordinateAction (sigmaOne * sigmaZero) * s1Root =
    (coordinateAction (sigmaOne * sigmaZero))⁻¹
  rw [map_mul, coordinateAction_sigmaOne, coordinateAction_sigmaZero]
  simpa [cRoot, Equiv.Perm.mul_def] using coordinate_s1_conj_c

/-! The throat involution intertwines the global Artin generator swap with the
coordinate action.  This is stated pointwise to keep the carrier alignment
explicit; the global extension is then a homomorphism extensionality step. -/

theorem kleinRootLabelThroatFlip_coordinateAction_swap_sigmaZero
    (x : G2CoordinateRoot) :
    kleinRootLabelThroatFlip
        (coordinateAction sigmaZero x) =
      coordinateAction sigmaOne (kleinRootLabelThroatFlip x) := by
  simpa [coordinateAction_sigmaZero, coordinateAction_sigmaOne] using
    kleinRootLabelThroatFlip_conjugates_s1 x

theorem kleinRootLabelThroatFlip_coordinateAction_swap_sigmaOne
    (x : G2CoordinateRoot) :
    kleinRootLabelThroatFlip
        (coordinateAction sigmaOne x) =
      coordinateAction sigmaZero (kleinRootLabelThroatFlip x) := by
  simpa [coordinateAction_sigmaZero, coordinateAction_sigmaOne] using
    kleinRootLabelThroatFlip_conjugates_s2 x

/-! Conjugation by the throat involution is packaged as a genuine group
homomorphism on the coordinate-root permutation carrier. -/

noncomputable def throatConjugation :
    Equiv.Perm G2CoordinateRoot →* Equiv.Perm G2CoordinateRoot where
  toFun p := kleinRootLabelThroatFlip * p * kleinRootLabelThroatFlip⁻¹
  map_one' := by simp
  map_mul' p q := by simp [mul_assoc]

theorem throatConjugation_involutive :
    throatConjugation.comp throatConjugation =
      MonoidHom.id (Equiv.Perm G2CoordinateRoot) := by
  apply MonoidHom.ext
  intro p
  apply Equiv.ext
  intro x
  have hflip : kleinRootLabelThroatFlip.symm = kleinRootLabelThroatFlip := by
    apply Equiv.ext
    intro y
    apply kleinRootLabelThroatFlip.injective
    simp [kleinRootLabelThroatFlip_involutive]
  simp [throatConjugation, Equiv.Perm.mul_apply, hflip,
    kleinRootLabelThroatFlip_involutive]

theorem throatConjugation_coordinateAction_swap :
    throatConjugation.comp coordinateAction =
      coordinateAction.comp artinGeneratorSwap := by
  apply PresentedGroup.ext
  intro i
  fin_cases i
  · apply Equiv.ext
    intro x
    simpa [throatConjugation, coordinateAction_sigmaZero,
      artinGeneratorSwap_sigmaZero] using
      (kleinRootLabelThroatFlip_coordinateAction_swap_sigmaZero
        (kleinRootLabelThroatFlip.symm x))
  · apply Equiv.ext
    intro x
    simpa [throatConjugation, coordinateAction_sigmaOne,
      artinGeneratorSwap_sigmaOne] using
      (kleinRootLabelThroatFlip_coordinateAction_swap_sigmaOne
        (kleinRootLabelThroatFlip.symm x))

/-! The semidirect Klein carrier maps to the Artin-coordinate carrier through
    the existing universal Klein presentation lift.  This retains the
    non-involutive glide/monodromy data before any Weyl quotient. -/

noncomputable def nativeKleinToArtinCoordinate :
    NativeKleinSemidirect →* Equiv.Perm G2CoordinateRoot :=
  kleinToArtinCoordinate.comp nativeKleinPresentationInverse

theorem nativeKleinToArtinCoordinate_glide :
    nativeKleinToArtinCoordinate nativeKleinGlide = s1Root := by
  rw [nativeKleinToArtinCoordinate, MonoidHom.coe_comp]
  change kleinToArtinCoordinate
      (nativeKleinPresentationInverse nativeKleinGlide) = s1Root
  have hleft := nativeKleinPresentationInverse_left
  have hgen := nativeKleinPresentationRep_generators
  have hrep : nativeKleinPresentationInverse nativeKleinGlide = toKlein genA := by
    have h := congrArg
      (fun F : KleinGroup →* KleinGroup => F (toKlein genA)) hleft
    change nativeKleinPresentationInverse
        (nativeKleinPresentationRep (toKlein genA)) = toKlein genA at h
    rw [hgen.1] at h
    simpa using h
  rw [hrep]
  exact kleinToArtinCoordinate_genA

theorem nativeKleinToArtinCoordinate_translation :
    nativeKleinToArtinCoordinate nativeKleinTranslation =
      s2Root * s1Root := by
  rw [nativeKleinToArtinCoordinate, MonoidHom.coe_comp]
  change kleinToArtinCoordinate
      (nativeKleinPresentationInverse nativeKleinTranslation) = s2Root * s1Root
  have hleft := nativeKleinPresentationInverse_left
  have hgen := nativeKleinPresentationRep_generators
  have hrep :
      nativeKleinPresentationInverse nativeKleinTranslation = toKlein genB := by
    have h := congrArg
      (fun F : KleinGroup →* KleinGroup => F (toKlein genB)) hleft
    change nativeKleinPresentationInverse
        (nativeKleinPresentationRep (toKlein genB)) = toKlein genB at h
    rw [hgen.2] at h
    simpa using h
  rw [hrep]
  exact kleinToArtinCoordinate_genB

theorem nativeKleinToArtinCoordinate_klein_relation :
    nativeKleinToArtinCoordinate nativeKleinGlide *
        nativeKleinToArtinCoordinate nativeKleinTranslation *
        (nativeKleinToArtinCoordinate nativeKleinGlide)⁻¹ =
      (nativeKleinToArtinCoordinate nativeKleinTranslation)⁻¹ := by
  rw [nativeKleinToArtinCoordinate_glide,
    nativeKleinToArtinCoordinate_translation]
  exact g2Artin_coordinateAction_kleinConjugation

/-! A compact, kernel-checked algebraic pipeline packet.  This records the
semidirect Klein carrier, its two coordinate-root readbacks, and the Klein
conjugation law together.  It is deliberately not a topological realization
or a link/closure theorem. -/

theorem g2ArtinKleinCoordinatePipeline_packet :
    (nativeKleinToArtinCoordinate nativeKleinGlide = s1Root) ∧
    (nativeKleinToArtinCoordinate nativeKleinTranslation = s2Root * s1Root) ∧
    (nativeKleinToArtinCoordinate nativeKleinGlide *
        nativeKleinToArtinCoordinate nativeKleinTranslation *
        (nativeKleinToArtinCoordinate nativeKleinGlide)⁻¹ =
      (nativeKleinToArtinCoordinate nativeKleinTranslation)⁻¹) := by
  exact ⟨nativeKleinToArtinCoordinate_glide,
    nativeKleinToArtinCoordinate_translation,
    nativeKleinToArtinCoordinate_klein_relation⟩

end InfoGeometry.Exceptional.G2ArtinKleinBridge
