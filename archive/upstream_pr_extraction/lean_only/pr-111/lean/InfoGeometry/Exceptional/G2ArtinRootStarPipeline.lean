import InfoGeometry.Exceptional.G2ArtinWeylBridge
import InfoGeometry.Exceptional.G2CoordinateRootIndexBridge

/-!
# Artin-to-root-star pipeline packet

This owner packages the already proved Artin factorisation and the native
root-star readback.  The Artin carrier remains potentially infinite; only its
coordinate action factors through the finite Weyl carrier.
-/

namespace InfoGeometry.Exceptional.G2ArtinRootStarPipeline

open InfoGeometry.Exceptional.G2ArtinPresentation
open InfoGeometry.Exceptional.G2ArtinWeylBridge
open InfoGeometry.Exceptional.G2ArtinKleinBridge
open InfoGeometry.Exceptional.G2CoordinateRootIndexBridge
open InfoGeometry.Exceptional.G2ConcreteCoordinateCalibration
open InfoGeometry.Algebra.Zorn.G2TwoRootSystem
open InfoGeometry.Algebra.Zorn.G2NativeRootIndexAlignment
open InfoGeometry.Lie.CanonicalZornRootSystemComparison

attribute [local instance] Classical.decEq

noncomputable def dihedralRootStarHom :
    DihedralGroup 6 →* Equiv.Perm RootIndex where
  toFun d := lieRootAction
    (InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.dihedralParameterMap d)
  map_one' := by
    change lieRootAction (0, false) = 1
    apply Equiv.ext
    intro i
    change nativeRootIndexEquiv
      (InfoGeometry.Algebra.Zorn.G2NativeWeylRootSpaceTransport.nonzeroIndexAction
        (0, false) (nativeRootIndexEquiv.symm i)) = i
    simpa using congrArg nativeRootIndexEquiv
      (InfoGeometry.Algebra.Zorn.G2NativeWeylRootSpaceTransport.nonzeroIndexAction_one
        (nativeRootIndexEquiv.symm i))
  map_mul' g h := by
    rw [InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.dihedralParameterMap_mul]
    rw [← InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.weylMul_eq_weylSemidirectMul]
    apply Equiv.ext
    intro i
    exact congrFun
      (lieRootAction_weylMul
        (InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.dihedralParameterMap g)
        (InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.dihedralParameterMap h)) i

@[simp] theorem dihedralRootStarHom_apply (d : DihedralGroup 6) :
    dihedralRootStarHom d = lieRootAction
      (InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.dihedralParameterMap d) := rfl

theorem dihedralRootStarHom_sr_zero :
    dihedralRootStarHom (.sr 0) = lieRootAction (0, true) := by
  rfl

theorem dihedralRootStarHom_sr_one :
    dihedralRootStarHom (.sr 1) = lieRootAction (1, true) := by
  rfl

theorem dihedralRootStarHom_action (d : DihedralGroup 6) (S : Finset RootIndex) :
    rootStarWeylAction
        (InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.dihedralParameterMap d) S =
      S.image (dihedralRootStarHom d) := by
  rfl

theorem g2Artin_rootStar_pipeline_packet
    (w : ArtinG2) (r : G2Root) :
    (coordinateAction =
      InfoGeometry.Algebra.Zorn.G2CoordinateSemidirectBridge.calibratedDihedralCoordinateHom.comp
        artinToCoxeter) ∧
    (concreteRootCoordinateEquiv (concreteRootAction w r) =
      coordinateAction w (concreteRootCoordinateEquiv r)) ∧
    (rootStarWeylAction
        (InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.dihedralParameterMap
          (artinToCoxeter w))
        InfoGeometry.Lie.CanonicalZornG2RootStarAction.canonicalRootStar.roots =
      InfoGeometry.Lie.CanonicalZornG2RootStarAction.canonicalRootStar.roots) := by
  exact ⟨g2Artin_coordinateAction_eq_weylAction,
    concreteAction_coordinateAction_compatible w r,
    rootStarWeylAction_canonical
      (InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.dihedralParameterMap
        (artinToCoxeter w))⟩

theorem g2Artin_rootStar_klein_pipeline_packet :
    (coordinateAction =
      InfoGeometry.Algebra.Zorn.G2CoordinateSemidirectBridge.calibratedDihedralCoordinateHom.comp
        artinToCoxeter) ∧
    (throatConjugation.comp coordinateAction =
      coordinateAction.comp artinGeneratorSwap) := by
  exact ⟨g2Artin_coordinateAction_eq_weylAction,
    throatConjugation_coordinateAction_swap⟩

/-! Integrated finite-boundary packet.  It combines the Artin-to-Weyl
    factorisation, the explicit throat intertwining, and preservation of the
    native root-star carrier.  The three carriers remain distinct in the
    statement. -/
theorem g2Artin_rootStar_klein_artin_packet
    (w : ArtinG2) :
    (coordinateAction w =
      InfoGeometry.Algebra.Zorn.G2CoordinateSemidirectBridge.calibratedDihedralCoordinateHom
        (artinToCoxeter w)) ∧
    (throatConjugation (coordinateAction w) =
      coordinateAction (artinGeneratorSwap w)) ∧
    (rootStarWeylAction
        (InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.dihedralParameterMap
          (artinToCoxeter w))
        InfoGeometry.Lie.CanonicalZornG2RootStarAction.canonicalRootStar.roots =
      InfoGeometry.Lie.CanonicalZornG2RootStarAction.canonicalRootStar.roots) := by
  refine ⟨?_, ?_, ?_⟩
  · exact DFunLike.congr_fun
      g2Artin_coordinateAction_eq_weylAction w
  · exact DFunLike.congr_fun
      G2ArtinKleinBridge.throatConjugation_coordinateAction_swap w
  · exact rootStarWeylAction_canonical _

/-! A single seam theorem for the concrete Weyl representative and the
    transported root-star action.  The two conjuncts intentionally retain
    their native carriers: the first is an automorphism conjugation statement,
    while the second is a finite root-index readback. -/

theorem g2Artin_concreteWeyl_rootStar_bridge
    (w : ArtinG2) (r : G2Root) :
    (concreteAction w * rootAut r * (concreteAction w)⁻¹ =
      rootAut (InfoGeometry.Algebra.Zorn.G2RootSystemWeylBridge.weylRootAction
        (InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.dihedralParameterMap
          (artinToCoxeter w)) r)) ∧
    (rootStarWeylAction
        (InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.dihedralParameterMap
          (artinToCoxeter w))
        {nativeRootIndexEquiv (rootIndexOf r)} =
      {nativeRootIndexEquiv (rootIndexOf
        (InfoGeometry.Algebra.Zorn.G2RootSystemWeylBridge.weylRootAction
          (InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.dihedralParameterMap
            (artinToCoxeter w)) r))}) := by
  exact ⟨concreteAction_rootAut_conj w r,
    rootStarWeylAction_singleton_native
      (InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.dihedralParameterMap
        (artinToCoxeter w)) r⟩

end InfoGeometry.Exceptional.G2ArtinRootStarPipeline
