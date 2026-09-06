import InfoGeometry.Algebra.Zorn.G2RootWeylAdjointCharacter
import InfoGeometry.Algebra.Zorn.G2NativeRootIndexAlignment
import InfoGeometry.Algebra.Zorn.G2NativeWeylRootSpaceTransport
import InfoGeometry.Algebra.Zorn.G2NativeWeylFiniteNormalization
import InfoGeometry.Algebra.Zorn.G2CyclotomicWeylBridge
import InfoGeometry.Algebra.Zorn.G2WeylDihedralEquiv
import InfoGeometry.Lie.CanonicalZornG2ToMatrixBridge
import InfoGeometry.Lie.CanonicalZornG2RootStarAction
import InfoGeometry.Exceptional.G2ConcreteCoordinateCalibration

/-!
# Carrier bridge from coordinate roots to the native Lie root index

The coordinate-root Artin action and the Lie root-star action use different
carriers.  This file supplies only their existing, proved carrier
equivalence; action equivariance remains a separate theorem.
-/

noncomputable section

namespace InfoGeometry.Exceptional.G2CoordinateRootIndexBridge

open InfoGeometry.Algebra.Zorn.G2RootWeylAdjointCharacter
open InfoGeometry.Algebra.Zorn.G2NativeRootIndexAlignment
open InfoGeometry.Algebra.Zorn.G2NativeWeylRootSpaceTransport
open InfoGeometry.Algebra.Zorn.G2CyclotomicWeyl
open InfoGeometry.Algebra.Zorn.G2TwoRootSystem
open InfoGeometry.Algebra.Zorn.G2NativeWeylFiniteNormalization
open InfoGeometry.Algebra.Zorn.G2RootSystemWeylBridge
open InfoGeometry.Lie.CanonicalZornRootSystemComparison

abbrev CoordinateRoot :=
  InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction.G2CoordinateRoot

abbrev NativeNonzeroIndex :=
  InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.nonzeroIndex

def coordinateRootToNativeRootIndex :
    CoordinateRoot ≃ NativeNonzeroIndex :=
  finiteRootCoordinateEquiv.symm.trans
    InfoGeometry.Algebra.Zorn.G2NativeRootIndexAlignment.rootIndexEquiv

def coordinateRootToLieRootIndex :
    CoordinateRoot ≃ RootIndex :=
  coordinateRootToNativeRootIndex.trans nativeRootIndexEquiv

/-! The finite-root and concrete-coordinate owners use different cyclic
    labels.  Their canonical comparison is therefore an equivalence of the
    root carrier, not an equality of the two label maps. -/

noncomputable def finiteToConcreteRootCalibration : G2Root ≃ G2Root :=
  finiteRootCoordinateEquiv.trans
    InfoGeometry.Exceptional.G2ConcreteCoordinateCalibration.concreteRootCoordinateEquiv.symm

theorem finiteToConcreteRootCalibration_transport :
    finiteToConcreteRootCalibration.trans
        InfoGeometry.Exceptional.G2ConcreteCoordinateCalibration.concreteRootCoordinateEquiv =
      finiteRootCoordinateEquiv := by
  simp [finiteToConcreteRootCalibration, Equiv.trans_assoc]

/-! Canonical finite cyclotomic carrier for the coordinate roots.  This is
    only an equivalence of carriers; action equivariance is proved separately. -/

noncomputable def coordinateRootToCyclotomicRoot :
    CoordinateRoot ≃ InfoGeometry.Algebra.Zorn.G2CyclotomicWeyl.Root :=
  finiteRootCoordinateEquiv.symm.trans finiteRootCyclotomicEquiv

@[simp] theorem coordinateRootToCyclotomicRoot_apply (x : CoordinateRoot) :
    coordinateRootToCyclotomicRoot x =
      finiteRootCyclotomicEquiv (finiteRootCoordinateEquiv.symm x) := rfl

/-! The canonical finite dihedral action transported to the coordinate-root
    carrier.  This is a genuine homomorphism; its equality with the Artin
    readback is a separate generator-compatibility theorem. -/

noncomputable def dihedralCoordinatePermutationRep :
    DihedralGroup 6 →* Equiv.Perm CoordinateRoot where
  toFun g := coordinateRootToCyclotomicRoot.trans
    ((dihedralRootPermutationRep g).trans coordinateRootToCyclotomicRoot.symm)
  map_one' := by
    apply Equiv.ext
    intro x
    simp
  map_mul' := by
    intro g h
    apply Equiv.ext
    intro x
    simp only [Equiv.trans_apply, Equiv.Perm.mul_apply]
    rw [map_mul]
    simp

/-! The concrete Weyl subgroup inherits its coordinate-root action by the
    existing dihedral equivalence.  This is the canonical finite transport:
    no new presentation or normal-form argument is introduced here. -/

noncomputable def concreteWeylCoordinateActionHom :
    InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.weylG2Subgroup →*
      Equiv.Perm CoordinateRoot :=
  dihedralCoordinatePermutationRep.comp
    InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.dihedralWeylMulEquiv.symm.toMonoidHom

@[simp] theorem concreteWeylCoordinateActionHom_apply (x :
    InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.weylG2Subgroup) :
    concreteWeylCoordinateActionHom x =
      dihedralCoordinatePermutationRep
        (InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.dihedralWeylMulEquiv.symm x) :=
  rfl

theorem dihedralCoordinatePermutationRep_injective :
    Function.Injective dihedralCoordinatePermutationRep := by
  intro g h hgh
  apply InfoGeometry.Algebra.Zorn.G2CyclotomicWeyl.dihedralRootPermutationRep_injective
  apply Equiv.ext
  intro x
  have hx := congrArg
    (fun f : Equiv.Perm CoordinateRoot =>
      f (coordinateRootToCyclotomicRoot.symm x)) hgh
  have := congrArg coordinateRootToCyclotomicRoot hx
  simpa [dihedralCoordinatePermutationRep] using this

theorem concreteWeylCoordinateActionHom_injective :
    Function.Injective concreteWeylCoordinateActionHom := by
  intro x y hxy
  obtain ⟨g, rfl⟩ :=
    InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.dihedralWeylMulEquiv.surjective x
  obtain ⟨h, rfl⟩ :=
    InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.dihedralWeylMulEquiv.surjective y
  have hgh : dihedralCoordinatePermutationRep g =
      dihedralCoordinatePermutationRep h := by
    simpa [concreteWeylCoordinateActionHom,
      dihedralCoordinatePermutationRep] using hxy
  have gh : g = h := dihedralCoordinatePermutationRep_injective hgh
  exact congrArg InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.dihedralWeylMulEquiv gh

theorem concreteWeylCoordinateActionHom_dihedral (d : DihedralGroup 6) :
    concreteWeylCoordinateActionHom
        (InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.dihedralWeylMulEquiv d) =
      dihedralCoordinatePermutationRep d := by
  rw [concreteWeylCoordinateActionHom_apply]
  simp

/-! Transport the concrete action all the way to the native `RootIndex`
    carrier.  This is only a conjugated permutation representation; it does
    not assert compatibility with the separately defined Lie `RootPairing`
    action. -/

noncomputable def concreteWeylRootIndexActionHom :
    InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.weylG2Subgroup →*
      Equiv.Perm RootIndex where
  toFun x := coordinateRootToLieRootIndex.symm.trans
    ((concreteWeylCoordinateActionHom x).trans coordinateRootToLieRootIndex)
  map_one' := by
    apply Equiv.ext
    intro x
    simp
  map_mul' := by
    intro x y
    apply Equiv.ext
    intro z
    simp only [Equiv.trans_apply, Equiv.Perm.mul_apply]
    rw [map_mul]
    simp

@[simp] theorem concreteWeylRootIndexActionHom_apply (x :
    InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.weylG2Subgroup) :
    concreteWeylRootIndexActionHom x = coordinateRootToLieRootIndex.symm.trans
      ((concreteWeylCoordinateActionHom x).trans coordinateRootToLieRootIndex) :=
  rfl

theorem concreteWeylRootIndexActionHom_injective :
    Function.Injective concreteWeylRootIndexActionHom := by
  intro x y hxy
  apply concreteWeylCoordinateActionHom_injective
  apply Equiv.ext
  intro z
  have hz := congrArg (fun f : Equiv.Perm RootIndex =>
      coordinateRootToLieRootIndex.symm
        (f (coordinateRootToLieRootIndex z))) hxy
  simpa only [concreteWeylRootIndexActionHom_apply, Equiv.trans_apply,
    Equiv.symm_apply_apply, Equiv.apply_symm_apply] using hz

theorem concreteWeylRootIndexActionHom_dihedral (d : DihedralGroup 6) :
    concreteWeylRootIndexActionHom
        (InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.dihedralWeylMulEquiv d) =
      coordinateRootToLieRootIndex.symm.trans
        ((dihedralCoordinatePermutationRep d).trans coordinateRootToLieRootIndex) := by
  rw [concreteWeylRootIndexActionHom_apply,
    concreteWeylCoordinateActionHom_dihedral]



@[simp] theorem coordinateRootToNativeRootIndex_apply (x : CoordinateRoot) :
    coordinateRootToNativeRootIndex x =
      InfoGeometry.Algebra.Zorn.G2NativeRootIndexAlignment.rootIndexEquiv
        (finiteRootCoordinateEquiv.symm x) := rfl

@[simp] theorem coordinateRootToLieRootIndex_apply (x : CoordinateRoot) :
    coordinateRootToLieRootIndex x =
      nativeRootIndexEquiv (coordinateRootToNativeRootIndex x) := rfl

theorem coordinateRootToLieRootIndex_bijective :
    Function.Bijective coordinateRootToLieRootIndex :=
  coordinateRootToLieRootIndex.bijective

/-! The finite Weyl permutation transported to the native non-Cartan index.
This is the canonical carrier bridge; it does not identify the finite action
with the separate `RootPairing` root-star reflection owner. -/

noncomputable def coordinateRootActionOnNative
    (p : InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification.WeylG2) :
    NativeNonzeroIndex ≃ NativeNonzeroIndex :=
  Equiv.ofBijective
    (InfoGeometry.Algebra.Zorn.G2NativeWeylRootSpaceTransport.nonzeroIndexAction p)
    (InfoGeometry.Algebra.Zorn.G2NativeWeylRootSpaceTransport.nonzeroIndexAction_bijective p)

theorem coordinateRootActionOnNative_apply
    (p : InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification.WeylG2)
    (x : CoordinateRoot) :
    coordinateRootActionOnNative p (coordinateRootToNativeRootIndex x) =
      coordinateRootToNativeRootIndex
        (finiteRootCoordinateEquiv
          (InfoGeometry.Algebra.Zorn.G2RootSystemWeylBridge.weylRootAction p
            (finiteRootCoordinateEquiv.symm x))) := by
  rw [coordinateRootActionOnNative]
  change nonzeroIndexAction p
      (rootIndexOf (finiteRootCoordinateEquiv.symm x)) = _
  rw [nonzeroIndexAction_apply_root]
  change rootIndexOf (weylRootAction p (finiteRootCoordinateEquiv.symm x)) =
    rootIndexOf (finiteRootCoordinateEquiv.symm
      (finiteRootCoordinateEquiv (weylRootAction p
        (finiteRootCoordinateEquiv.symm x))))
  rw [finiteRootCoordinateEquiv.symm_apply_apply]

theorem coordinateRootActionOnNative_reflection_readback
    (x : CoordinateRoot) :
    coordinateRootActionOnNative (0, true)
        (coordinateRootToNativeRootIndex x) =
      coordinateRootToNativeRootIndex
        (finiteRootCoordinateEquiv
          (InfoGeometry.Algebra.Zorn.G2TwoRootSystem.sAction
            (finiteRootCoordinateEquiv.symm x))) := by
  simpa [InfoGeometry.Algebra.Zorn.G2RootSystemWeylBridge.weylRootAction]
    using coordinateRootActionOnNative_apply (0, true) x

/- theorem coordinateRootActionOnNative_reflection_apply (x : CoordinateRoot) :
    coordinateRootActionOnNative (0, true)
        (coordinateRootToNativeRootIndex x) =
      coordinateRootToNativeRootIndex
        (InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction.s1Root x) := by
  -- Requires an explicit compatibility theorem for the two coordinate calibrations.
 -/
noncomputable def nativeNonzeroIndexActionEquiv
    (p : InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification.WeylG2) :
    NativeNonzeroIndex ≃ NativeNonzeroIndex :=
  Equiv.ofBijective (nonzeroIndexAction p) (nonzeroIndexAction_bijective p)

noncomputable def lieRootAction
    (p : InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification.WeylG2) :
    RootIndex ≃ RootIndex :=
    nativeRootIndexEquiv.symm.trans
    ((nativeNonzeroIndexActionEquiv p).trans nativeRootIndexEquiv)

theorem coordinateRootActionOnNative_lieRootIndex
    (p : InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification.WeylG2)
    (x : CoordinateRoot) :
    nativeRootIndexEquiv
        (coordinateRootActionOnNative p (coordinateRootToNativeRootIndex x)) =
      lieRootAction p (coordinateRootToLieRootIndex x) := by
  simp [coordinateRootActionOnNative, lieRootAction,
    nativeNonzeroIndexActionEquiv, coordinateRootToLieRootIndex,
    coordinateRootToNativeRootIndex,
    nonzeroIndexAction_apply_root]

noncomputable def rootIndexToG2Root : RootIndex ≃
    InfoGeometry.Algebra.Zorn.G2TwoRootSystem.G2Root :=
  nativeRootIndexEquiv.symm.trans
    InfoGeometry.Algebra.Zorn.G2NativeRootIndexAlignment.rootIndexEquiv.symm

/-! The transported finite Weyl action acts on the existing exhaustive
    root-star carrier.  This is a carrier/action statement; it deliberately
    does not identify the action with `P.reflectionPerm` until that separate
    compatibility theorem is proved. -/

noncomputable def rootStarWeylAction
    (p : InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification.WeylG2)
    (S : Finset RootIndex) : Finset RootIndex :=
  by
    classical
    exact S.image (lieRootAction p)

theorem rootStarWeylAction_canonical
    (p : InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification.WeylG2) :
    rootStarWeylAction p
        InfoGeometry.Lie.CanonicalZornG2RootStarAction.canonicalRootStar.roots =
      InfoGeometry.Lie.CanonicalZornG2RootStarAction.canonicalRootStar.roots := by
  classical
  rw [InfoGeometry.Lie.CanonicalZornG2RootStarAction.canonicalRootStar_roots]
  ext r
  constructor
  · intro h
    exact Finset.mem_univ r
  · intro h
    obtain ⟨q, hq⟩ := (lieRootAction p).surjective r
    exact Finset.mem_image.mpr ⟨q, Finset.mem_univ q, hq⟩

theorem rootStarWeylAction_singleton (p :
    InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification.WeylG2)
    (r : RootIndex) :
    rootStarWeylAction p {r} = {lieRootAction p r} := by
  classical
  simp [rootStarWeylAction]

theorem rootStarWeylAction_card
    (p : InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification.WeylG2)
    (S : Finset RootIndex) :
    (rootStarWeylAction p S).card = S.card := by
  classical
  exact Finset.card_image_of_injective S (lieRootAction p).injective

theorem rootStarWeylAction_canonical_card
    (p : InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification.WeylG2) :
    (rootStarWeylAction p
      InfoGeometry.Lie.CanonicalZornG2RootStarAction.canonicalRootStar.roots).card =
        12 := by
  rw [rootStarWeylAction_card]
  exact InfoGeometry.Lie.CanonicalZornG2RootStarAction.canonicalRootStar_card

theorem lieRootAction_apply_native
    (p : InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification.WeylG2)
    (r : InfoGeometry.Algebra.Zorn.G2TwoRootSystem.G2Root) :
    lieRootAction p (nativeRootIndexEquiv (rootIndexOf r)) =
      nativeRootIndexEquiv (rootIndexOf (weylRootAction p r)) := by
  simp [lieRootAction, nativeNonzeroIndexActionEquiv,
    nonzeroIndexAction_apply_root]

theorem rootIndexToG2Root_lieRootAction
    (p : InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification.WeylG2)
    (i : RootIndex) :
    rootIndexToG2Root (lieRootAction p i) =
      weylRootAction p (rootIndexToG2Root i) := by
  let r : InfoGeometry.Algebra.Zorn.G2TwoRootSystem.G2Root :=
    rootIndexToG2Root i
  have hi : nativeRootIndexEquiv (rootIndexOf r) = i := by
    change nativeRootIndexEquiv
      (rootIndexEquiv (rootIndexEquiv.symm (nativeRootIndexEquiv.symm i))) = i
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rw [← hi, lieRootAction_apply_native]
  dsimp [rootIndexToG2Root]
  simp only [Equiv.symm_apply_apply]
  change rootIndexEquiv.symm (rootIndexOf (weylRootAction p r)) =
    weylRootAction p (rootIndexEquiv.symm (rootIndexOf r))
  have h₁ : rootIndexEquiv.symm (rootIndexOf (weylRootAction p r)) =
      weylRootAction p r := by
    rw [← InfoGeometry.Algebra.Zorn.G2NativeRootIndexAlignment.rootIndexEquiv_apply]
    exact rootIndexEquiv.symm_apply_apply _
  have h₂ : rootIndexEquiv.symm (rootIndexOf r) = r := by
    rw [← InfoGeometry.Algebra.Zorn.G2NativeRootIndexAlignment.rootIndexEquiv_apply]
    exact rootIndexEquiv.symm_apply_apply _
  rw [h₁, h₂]

theorem lieRootAction_weylMul
    (p q : InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification.WeylG2) :
    lieRootAction (InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.weylMul p q) =
      lieRootAction p ∘ lieRootAction q := by
  funext i
  let r : InfoGeometry.Algebra.Zorn.G2TwoRootSystem.G2Root :=
    rootIndexEquiv.symm (nativeRootIndexEquiv.symm i)
  have hi : nativeRootIndexEquiv (rootIndexOf r) = i := by
    change nativeRootIndexEquiv
      (rootIndexEquiv (rootIndexEquiv.symm (nativeRootIndexEquiv.symm i))) = i
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rw [← hi]
  simp only [Function.comp_apply]
  rw [lieRootAction_apply_native, lieRootAction_apply_native,
    lieRootAction_apply_native]
  rw [InfoGeometry.Algebra.Zorn.G2RootWeylAdjointCharacter.weylRootAction_mul_semidirect]
  rfl

theorem rootStarWeylAction_weylMul
    (p q : InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification.WeylG2)
    (S : Finset RootIndex) :
    rootStarWeylAction
        (InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.weylMul p q) S =
      rootStarWeylAction p (rootStarWeylAction q S) := by
  simp [rootStarWeylAction, lieRootAction_weylMul, Finset.image_image]

noncomputable def rootStarToG2Root (S : Finset RootIndex) :
    Finset InfoGeometry.Algebra.Zorn.G2TwoRootSystem.G2Root :=
  S.image rootIndexToG2Root

theorem rootStarToG2Root_weylAction
    (p : InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification.WeylG2)
    (S : Finset RootIndex) :
    rootStarToG2Root (rootStarWeylAction p S) =
      (rootStarToG2Root S).image (weylRootAction p) := by
  have h : rootIndexToG2Root ∘ lieRootAction p =
      weylRootAction p ∘ rootIndexToG2Root := by
    funext i
    exact rootIndexToG2Root_lieRootAction p i
  simp only [rootStarToG2Root, rootStarWeylAction, Finset.image_image,
    h]

theorem rootStarWeylAction_singleton_native
    (p : InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification.WeylG2)
    (r : InfoGeometry.Algebra.Zorn.G2TwoRootSystem.G2Root) :
    rootStarWeylAction p
        {nativeRootIndexEquiv (rootIndexOf r)} =
      {nativeRootIndexEquiv (rootIndexOf (weylRootAction p r))} := by
  rw [rootStarWeylAction_singleton, lieRootAction_apply_native]

/-! The simple reflection readback is the first pointwise identification of
    the transported root-star action with the concrete finite Weyl action. -/

theorem rootStarWeylAction_reflection_singleton_native
    (r : InfoGeometry.Algebra.Zorn.G2TwoRootSystem.G2Root) :
    rootStarWeylAction (0, true)
        {nativeRootIndexEquiv (rootIndexOf r)} =
      {nativeRootIndexEquiv (rootIndexOf
        (sAction r))} := by
  rw [rootStarWeylAction_singleton_native]
  rw [rootIndexOf_weylRootAction_reflection]

/-! Unified downstream packet for the root-star/concrete-Weyl seam.  It
    exposes both finite-set transport and the pointwise root readback while
    leaving Bruhat cells and the finite Chevalley group as separate carriers.
-/

theorem rootStarWeylAction_concrete_readback
    (p : InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification.WeylG2)
    (S : Finset RootIndex)
    (r : InfoGeometry.Algebra.Zorn.G2TwoRootSystem.G2Root) :
    (rootStarToG2Root (rootStarWeylAction p S) =
        (rootStarToG2Root S).image (weylRootAction p)) ∧
    (rootStarWeylAction p
        {nativeRootIndexEquiv (rootIndexOf r)} =
      {nativeRootIndexEquiv (rootIndexOf (weylRootAction p r))}) := by
  exact ⟨rootStarToG2Root_weylAction p S,
    rootStarWeylAction_singleton_native p r⟩

end InfoGeometry.Exceptional.G2CoordinateRootIndexBridge
