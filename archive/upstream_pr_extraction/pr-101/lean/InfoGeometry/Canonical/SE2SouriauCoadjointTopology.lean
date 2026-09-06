import InfoGeometry.Canonical.SE2SouriauCoadjointOrbit
import InfoGeometry.Canonical.SE2SouriauNoncompact
import InfoGeometry.Canonical.SE2SouriauCompactOrbit
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Topology of full `SE(2)` coadjoint orbit carriers

The algebraic coadjoint orbit map has a useful topological refinement: its
range can be represented as a subtype, and the resulting orbit carrier is
path connected because the full Euclidean carrier is path connected.
-/

namespace SE2Souriau
namespace SE2Vector

open SE2Souriau.CompactRotation

structure EquivariantTopologicalEquiv
    (M X Y : Type*) [SMul M X] [SMul M Y]
    [TopologicalSpace X] [TopologicalSpace Y] where
  homeomorph : X ≃ₜ Y
  forward : X →[M] Y
  backward : Y →[M] X
  forward_coe : (forward : X → Y) = homeomorph
  backward_coe : (backward : Y → X) = homeomorph.symm

namespace EquivariantTopologicalEquiv

variable {M X Y : Type*} [SMul M X] [SMul M Y]
  [TopologicalSpace X] [TopologicalSpace Y]

def toFun_hom (e : EquivariantTopologicalEquiv M X Y) : X →[M] Y :=
  e.forward

def invFun_hom (e : EquivariantTopologicalEquiv M X Y) : Y →[M] X :=
  e.backward

@[simp] theorem toFun_hom_apply (e : EquivariantTopologicalEquiv M X Y)
    (x : X) : e.toFun_hom x = e.forward x := rfl

@[simp] theorem invFun_hom_apply (e : EquivariantTopologicalEquiv M X Y)
    (y : Y) : e.invFun_hom y = e.backward y := rfl

theorem ext
    {e f : EquivariantTopologicalEquiv M X Y}
    (hhomeomorph : e.homeomorph = f.homeomorph)
    (hforward : e.toFun_hom = f.toFun_hom)
    (hbackward : e.invFun_hom = f.invFun_hom) :
    e = f := by
  cases e with
  | mk ehome eforward ebackward eforward_coe ebackward_coe =>
    cases f with
    | mk fhome fforward fbackward fforward_coe fbackward_coe =>
      simp only [toFun_hom, invFun_hom] at hforward hbackward
      cases hhomeomorph
      cases hforward
      cases hbackward
      rfl

theorem forward_injective (e : EquivariantTopologicalEquiv M X Y) :
    Function.Injective e.forward := by
  rw [e.forward_coe]
  exact e.homeomorph.injective

theorem forward_surjective (e : EquivariantTopologicalEquiv M X Y) :
    Function.Surjective e.forward := by
  rw [e.forward_coe]
  exact e.homeomorph.surjective

theorem forward_bijective (e : EquivariantTopologicalEquiv M X Y) :
    Function.Bijective e.forward :=
  ⟨e.forward_injective, e.forward_surjective⟩

theorem backward_injective (e : EquivariantTopologicalEquiv M X Y) :
    Function.Injective e.backward := by
  rw [e.backward_coe]
  exact e.homeomorph.symm.injective

theorem backward_surjective (e : EquivariantTopologicalEquiv M X Y) :
    Function.Surjective e.backward := by
  rw [e.backward_coe]
  exact e.homeomorph.symm.surjective

theorem backward_bijective (e : EquivariantTopologicalEquiv M X Y) :
    Function.Bijective e.backward :=
  ⟨e.backward_injective, e.backward_surjective⟩

theorem forward_continuous (e : EquivariantTopologicalEquiv M X Y) :
    Continuous e.forward := by
  rw [e.forward_coe]
  exact e.homeomorph.continuous

theorem backward_continuous (e : EquivariantTopologicalEquiv M X Y) :
    Continuous e.backward := by
  rw [e.backward_coe]
  exact e.homeomorph.symm.continuous

theorem forward_isEmbedding (e : EquivariantTopologicalEquiv M X Y) :
    Topology.IsEmbedding e.forward := by
  rw [e.forward_coe]
  exact e.homeomorph.isEmbedding

theorem forward_isClosedEmbedding (e : EquivariantTopologicalEquiv M X Y) :
    Topology.IsClosedEmbedding e.forward := by
  rw [e.forward_coe]
  exact e.homeomorph.isClosedEmbedding

theorem forward_isOpenMap (e : EquivariantTopologicalEquiv M X Y) :
    IsOpenMap e.forward := by
  rw [e.forward_coe]
  exact e.homeomorph.isOpenMap

theorem forward_isClosedMap (e : EquivariantTopologicalEquiv M X Y) :
    IsClosedMap e.forward := by
  rw [e.forward_coe]
  exact e.homeomorph.isClosedMap

theorem forward_isQuotientMap (e : EquivariantTopologicalEquiv M X Y) :
    Topology.IsQuotientMap e.forward := by
  rw [e.forward_coe]
  exact e.homeomorph.isQuotientMap

theorem forward_isProperMap (e : EquivariantTopologicalEquiv M X Y) :
    IsProperMap e.forward := by
  rw [e.forward_coe]
  exact e.homeomorph.isProperMap

theorem backward_isEmbedding (e : EquivariantTopologicalEquiv M X Y) :
    Topology.IsEmbedding e.backward := by
  rw [e.backward_coe]
  exact e.homeomorph.symm.isEmbedding

theorem backward_isClosedEmbedding (e : EquivariantTopologicalEquiv M X Y) :
    Topology.IsClosedEmbedding e.backward := by
  rw [e.backward_coe]
  exact e.homeomorph.symm.isClosedEmbedding

theorem backward_isOpenMap (e : EquivariantTopologicalEquiv M X Y) :
    IsOpenMap e.backward := by
  rw [e.backward_coe]
  exact e.homeomorph.symm.isOpenMap

theorem backward_isClosedMap (e : EquivariantTopologicalEquiv M X Y) :
    IsClosedMap e.backward := by
  rw [e.backward_coe]
  exact e.homeomorph.symm.isClosedMap

theorem backward_isQuotientMap (e : EquivariantTopologicalEquiv M X Y) :
    Topology.IsQuotientMap e.backward := by
  rw [e.backward_coe]
  exact e.homeomorph.symm.isQuotientMap

theorem backward_isProperMap (e : EquivariantTopologicalEquiv M X Y) :
    IsProperMap e.backward := by
  rw [e.backward_coe]
  exact e.homeomorph.symm.isProperMap

def trans
    {Z : Type*} [SMul M Z] [TopologicalSpace Z]
    (e : EquivariantTopologicalEquiv M X Y)
    (f : EquivariantTopologicalEquiv M Y Z) :
    EquivariantTopologicalEquiv M X Z where
  homeomorph := e.homeomorph.trans f.homeomorph
  forward := f.forward.comp e.forward
  backward := e.backward.comp f.backward
  forward_coe := by
    funext x
    change f.forward (e.forward x) =
      f.homeomorph (e.homeomorph x)
    rw [e.forward_coe, f.forward_coe]
  backward_coe := by
    funext z
    change e.backward (f.backward z) =
      e.homeomorph.symm (f.homeomorph.symm z)
    rw [e.backward_coe, f.backward_coe]

def symm (e : EquivariantTopologicalEquiv M X Y) :
    EquivariantTopologicalEquiv M Y X where
  homeomorph := e.homeomorph.symm
  forward := e.backward
  backward := e.forward
  forward_coe := e.backward_coe
  backward_coe := by simpa using e.forward_coe

def refl (M X : Type*) [SMul M X] [TopologicalSpace X] :
    EquivariantTopologicalEquiv M X X where
  homeomorph := Homeomorph.refl X
  forward := MulActionHom.id M
  backward := MulActionHom.id M
  forward_coe := rfl
  backward_coe := rfl

theorem symm_trans_eq_refl
    (e : EquivariantTopologicalEquiv M X Y) :
    trans (symm e) e = refl M Y := by
  apply EquivariantTopologicalEquiv.ext
  · apply Homeomorph.ext
    intro y
    change e.homeomorph (e.homeomorph.symm y) = y
    exact e.homeomorph.apply_symm_apply y
  · apply MulActionHom.ext
    intro y
    change e.forward (e.backward y) = y
    rw [e.forward_coe, e.backward_coe]
    exact e.homeomorph.apply_symm_apply y
  · apply MulActionHom.ext
    intro y
    change e.forward (e.backward y) = y
    rw [e.forward_coe, e.backward_coe]
    exact e.homeomorph.apply_symm_apply y

theorem trans_symm_eq_refl
    (e : EquivariantTopologicalEquiv M X Y) :
    trans e (symm e) = refl M X := by
  apply EquivariantTopologicalEquiv.ext
  · apply Homeomorph.ext
    intro x
    change e.homeomorph.symm (e.homeomorph x) = x
    exact e.homeomorph.symm_apply_apply x
  · apply MulActionHom.ext
    intro x
    change e.backward (e.forward x) = x
    rw [e.backward_coe, e.forward_coe]
    exact e.homeomorph.symm_apply_apply x
  · apply MulActionHom.ext
    intro x
    change e.backward (e.forward x) = x
    rw [e.backward_coe, e.forward_coe]
    exact e.homeomorph.symm_apply_apply x

@[simp] theorem trans_forward_apply
    {Z : Type*} [SMul M Z] [TopologicalSpace Z]
    (e : EquivariantTopologicalEquiv M X Y)
    (f : EquivariantTopologicalEquiv M Y Z) (x : X) :
    (trans e f).forward x = f.forward (e.forward x) := rfl

@[simp] theorem trans_backward_apply
    {Z : Type*} [SMul M Z] [TopologicalSpace Z]
    (e : EquivariantTopologicalEquiv M X Y)
    (f : EquivariantTopologicalEquiv M Y Z) (z : Z) :
    (trans e f).backward z = e.backward (f.backward z) := rfl

@[simp] theorem trans_assoc_forward_apply
    {Z W : Type*} [SMul M Z] [SMul M W]
    [TopologicalSpace Z] [TopologicalSpace W]
    (e : EquivariantTopologicalEquiv M X Y)
    (f : EquivariantTopologicalEquiv M Y Z)
    (g : EquivariantTopologicalEquiv M Z W) (x : X) :
    (trans (trans e f) g).forward x =
      (trans e (trans f g)).forward x := rfl

@[simp] theorem trans_assoc_backward_apply
    {Z W : Type*} [SMul M Z] [SMul M W]
    [TopologicalSpace Z] [TopologicalSpace W]
    (e : EquivariantTopologicalEquiv M X Y)
    (f : EquivariantTopologicalEquiv M Y Z)
    (g : EquivariantTopologicalEquiv M Z W) (x : W) :
    (trans (trans e f) g).backward x =
      (trans e (trans f g)).backward x := rfl

@[simp] theorem symm_forward_apply
    (e : EquivariantTopologicalEquiv M X Y) (y : Y) :
    (symm e).forward y = e.backward y := rfl

@[simp] theorem symm_backward_apply
    (e : EquivariantTopologicalEquiv M X Y) (x : X) :
    (symm e).backward x = e.forward x := rfl

@[simp] theorem refl_forward_apply
    (M X : Type*) [SMul M X] [TopologicalSpace X] (x : X) :
    (refl M X).forward x = x := rfl

@[simp] theorem refl_backward_apply
    (M X : Type*) [SMul M X] [TopologicalSpace X] (x : X) :
    (refl M X).backward x = x := rfl

end EquivariantTopologicalEquiv

theorem casimirFiberCylinderParam_injective_of_pos
    {r : ℝ} (hr : 0 < r) :
    Function.Injective (casimirFiberCylinderParam (le_of_lt hr)) := by
  intro p q hpq
  have hj : p.1 = q.1 := by
    have hcoord := congrArg
      (fun w : CasimirFiberCarrier r => w.1.1) hpq
    simpa [casimirFiberCylinderParam, coadjointRotationRepresentative,
      rotationMomentumAction, momentumRotationFiber,
      momentumRotationCoordinates] using hcoord
  have hrep : coadjointRotationRepresentative (le_of_lt hr) p.1 =
      coadjointRotationRepresentative (le_of_lt hr) q.1 := by
    rw [hj]
  have hrot : p.2 • coadjointRotationRepresentative (le_of_lt hr) p.1 =
      q.2 • coadjointRotationRepresentative (le_of_lt hr) p.1 := by
    simpa [casimirFiberCylinderParam, hrep] using hpq
  have hgroup : p.2 = q.2 := by
    exact rotationOrbitMap_injective_of_pos hr
      (coadjointRotationRepresentative (le_of_lt hr) p.1) hrot
  exact Prod.ext hj hgroup

noncomputable def casimirFiberCylinderInverse_of_pos
    {r : ℝ} (hr : 0 < r) :
    CasimirFiberCarrier r → ℝ × RotationCarrier := fun q =>
  (q.1.1,
    ⟨(q.1.2.1 / Real.sqrt r, q.1.2.2 / Real.sqrt r), by
      have hq : q.1.2.1 ^ 2 + q.1.2.2 ^ 2 = r := q.2
      have hs : (Real.sqrt r) ^ 2 = r := Real.sq_sqrt (le_of_lt hr)
      have hs0 : Real.sqrt r ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hr)
      change (q.1.2.1 / Real.sqrt r) ^ 2 +
        (q.1.2.2 / Real.sqrt r) ^ 2 = 1
      field_simp [hs0]
      nlinarith⟩)

theorem continuous_casimirFiberCylinderInverse_of_pos
    {r : ℝ} (hr : 0 < r) :
    Continuous (casimirFiberCylinderInverse_of_pos hr) := by
  unfold casimirFiberCylinderInverse_of_pos
  fun_prop

theorem casimirFiberCylinderInverse_leftInverse_of_pos
    {r : ℝ} (hr : 0 < r) :
    Function.LeftInverse
      (casimirFiberCylinderInverse_of_pos hr)
      (casimirFiberCylinderParam (le_of_lt hr)) := by
  intro p
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    ext
    · change ((p.2.1.1 * Real.sqrt r - p.2.1.2 * 0) /
        Real.sqrt r) = p.2.1.1
      field_simp [ne_of_gt (Real.sqrt_pos.2 hr)]
      ring
    · change ((p.2.1.2 * Real.sqrt r + p.2.1.1 * 0) /
        Real.sqrt r) = p.2.1.2
      field_simp [ne_of_gt (Real.sqrt_pos.2 hr)]
      ring

theorem casimirFiberCylinderInverse_rightInverse_of_pos
    {r : ℝ} (hr : 0 < r) :
    Function.RightInverse
      (casimirFiberCylinderInverse_of_pos hr)
      (casimirFiberCylinderParam (le_of_lt hr)) := by
  intro q
  apply Subtype.ext
  ext
  · rfl
  · dsimp [casimirFiberCylinderParam, casimirFiberCylinderInverse_of_pos,
      coadjointRotationRepresentative, rotationMomentumAction,
      momentumRotationFiber, momentumRotationCoordinates]
    change (q.1.2.1 / Real.sqrt r) * Real.sqrt r -
      (q.1.2.2 / Real.sqrt r) * 0 = q.1.2.1
    field_simp [ne_of_gt (Real.sqrt_pos.2 hr)]
    ring
  · dsimp [casimirFiberCylinderParam, casimirFiberCylinderInverse_of_pos,
      coadjointRotationRepresentative, rotationMomentumAction,
      momentumRotationFiber, momentumRotationCoordinates]
    change (q.1.2.2 / Real.sqrt r) * Real.sqrt r +
      (q.1.2.1 / Real.sqrt r) * 0 = q.1.2.2
    field_simp [ne_of_gt (Real.sqrt_pos.2 hr)]
    ring

noncomputable def casimirFiberCylinderHomeomorph_of_pos
    {r : ℝ} (hr : 0 < r) :
    (ℝ × RotationCarrier) ≃ₜ CasimirFiberCarrier r where
  toFun := casimirFiberCylinderParam (le_of_lt hr)
  invFun := casimirFiberCylinderInverse_of_pos hr
  left_inv := casimirFiberCylinderInverse_leftInverse_of_pos hr
  right_inv := casimirFiberCylinderInverse_rightInverse_of_pos hr
  continuous_toFun := continuous_casimirFiberCylinderParam (le_of_lt hr)
  continuous_invFun := continuous_casimirFiberCylinderInverse_of_pos hr

theorem noncompactSpace_casimirFiberCarrier_of_nonneg
    {r : ℝ} (hr : 0 ≤ r) :
    NoncompactSpace (CasimirFiberCarrier r) where
  noncompact_univ := noncompact_casimirFiber_univ hr

noncomputable def se2CarrierProductHomeomorph :
    MatrixSE2Carrier ≃ₜ
      RotationCarrier × InfoGeometry.Canonical.SE2SouriauCocycle.Point2 where
  toFun := fun g =>
    (⟨(g.1.1, g.1.2.1), g.2⟩, (g.1.2.2.1, g.1.2.2.2))
  invFun := fun p =>
    ⟨(p.1.1.1, p.1.1.2, p.2.1, p.2.2), p.1.2⟩
  left_inv := by
    intro g
    apply Subtype.ext
    rfl
  right_inv := by
    intro p
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · rfl
  continuous_toFun := by
    fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    fun_prop

noncomputable def se2CarrierRotationProjection : MatrixSE2Carrier → RotationCarrier :=
  fun g => (se2CarrierProductHomeomorph g).1

instance noncompactSpace_matrixSE2Carrier : NoncompactSpace MatrixSE2Carrier where
  noncompact_univ := by
    intro hcompact
    exact InfoGeometry.Canonical.SE2SouriauCocycle.not_compactSpace_SE2RotationCarrier
      ⟨hcompact⟩

theorem continuous_se2CarrierRotationProjection :
    Continuous se2CarrierRotationProjection := by
  exact continuous_fst.comp se2CarrierProductHomeomorph.continuous

theorem se2CarrierRotationProjection_surjective :
    Function.Surjective se2CarrierRotationProjection := by
  intro g
  refine ⟨se2CarrierProductHomeomorph.symm (g, (0, 0)), ?_⟩
  rfl

theorem isOpenMap_se2CarrierRotationProjection :
    IsOpenMap se2CarrierRotationProjection := by
  simpa only [se2CarrierRotationProjection, Function.comp_apply] using
    isOpenMap_fst.comp se2CarrierProductHomeomorph.isOpenMap

theorem isQuotientMap_se2CarrierRotationProjection :
    Topology.IsQuotientMap se2CarrierRotationProjection := by
  exact (isOpenMap_se2CarrierRotationProjection).isQuotientMap
    continuous_se2CarrierRotationProjection
    se2CarrierRotationProjection_surjective

theorem isOpenQuotientMap_se2CarrierRotationProjection :
    IsOpenQuotientMap se2CarrierRotationProjection := by
  exact IsOpenQuotientMap.of_isOpenMap_isQuotientMap
    isOpenMap_se2CarrierRotationProjection
    isQuotientMap_se2CarrierRotationProjection

theorem se2CarrierRotationProjection_one :
    se2CarrierRotationProjection (1 : MatrixSE2Carrier) = 1 := by
  rfl

theorem se2CarrierRotationProjection_mul
    (g h : MatrixSE2Carrier) :
    se2CarrierRotationProjection (g * h) =
      se2CarrierRotationProjection g * se2CarrierRotationProjection h := by
  apply Subtype.ext
  rfl

noncomputable def se2CarrierRotationProjectionMonoidHom :
    MatrixSE2Carrier →ₜ* RotationCarrier where
  toMonoidHom :=
    { toFun := se2CarrierRotationProjection
      map_one' := se2CarrierRotationProjection_one
      map_mul' := se2CarrierRotationProjection_mul }
  continuous_toFun := continuous_se2CarrierRotationProjection

theorem isOpenMap_casimirFiberCylinderParam_of_pos
    {r : ℝ} (hr : 0 < r) :
    IsOpenMap (casimirFiberCylinderParam (le_of_lt hr)) := by
  exact (casimirFiberCylinderHomeomorph_of_pos hr).isOpenMap

theorem isClosedMap_casimirFiberCylinderParam_of_pos
    {r : ℝ} (hr : 0 < r) :
    IsClosedMap (casimirFiberCylinderParam (le_of_lt hr)) := by
  exact (casimirFiberCylinderHomeomorph_of_pos hr).isClosedMap

theorem isProperMap_casimirFiberCylinderParam_of_pos
    {r : ℝ} (hr : 0 < r) :
    IsProperMap (casimirFiberCylinderParam (le_of_lt hr)) := by
  exact (casimirFiberCylinderHomeomorph_of_pos hr).isProperMap

theorem isQuotientMap_casimirFiberCylinderParam_of_pos
    {r : ℝ} (hr : 0 < r) :
    Topology.IsQuotientMap (casimirFiberCylinderParam (le_of_lt hr)) := by
  exact (casimirFiberCylinderHomeomorph_of_pos hr).isQuotientMap

abbrev SE2CarrierOrbitCarrier
    {r : ℝ} (q : CasimirFiberCarrier r) :=
  {w : CasimirFiberCarrier r // w ∈ se2CarrierOrbit q}

theorem se2CarrierOrbit_eq_rotationOrbit
    {r : ℝ} (q : CasimirFiberCarrier r) :
    se2CarrierOrbit q = rotationOrbit q := by
  apply Set.Subset.antisymm
  · rintro w ⟨g, rfl⟩
    let rg : RotationCarrier :=
      ⟨(g.1.1, g.1.2.1), g.2⟩
    refine ⟨rg, ?_⟩
    apply Subtype.ext
    rfl

  · rintro w ⟨rg, rfl⟩
    let g : MatrixSE2Carrier :=
      ⟨(rg.1.1, rg.1.2, 0, 0), rg.2⟩
    refine ⟨g, ?_⟩
    apply Subtype.ext
    rfl

noncomputable def rotationOrbitCarrierHomeomorph
    {r : ℝ} (q : CasimirFiberCarrier r) :
    RotationOrbitCarrier q ≃ₜ SE2CarrierOrbitCarrier q :=
  Homeomorph.setCongr (se2CarrierOrbit_eq_rotationOrbit q).symm

noncomputable def se2CarrierOrbitQuotientMap
    {r : ℝ} (q : CasimirFiberCarrier r) :
    RotationCarrier → SE2CarrierOrbitCarrier q := fun g =>
      rotationOrbitCarrierHomeomorph q (rotationOrbitMapCarrier q g)

noncomputable def se2CarrierOrbitHomeomorph_of_pos
    {r : ℝ} (hr : 0 < r) (q : CasimirFiberCarrier r) :
    RotationCarrier ≃ₜ SE2CarrierOrbitCarrier q :=
  (rotationOrbitHomeomorph_of_pos hr q).trans (rotationOrbitCarrierHomeomorph q)

theorem se2CarrierOrbitQuotientMap_eq_homeomorph_of_pos
    {r : ℝ} (hr : 0 < r) (q : CasimirFiberCarrier r) :
    se2CarrierOrbitQuotientMap q = se2CarrierOrbitHomeomorph_of_pos hr q := by
  funext g
  apply Subtype.ext
  rfl

theorem injective_se2CarrierOrbitQuotientMap_of_pos
    {r : ℝ} (hr : 0 < r) (q : CasimirFiberCarrier r) :
    Function.Injective (se2CarrierOrbitQuotientMap q) := by
  rw [se2CarrierOrbitQuotientMap_eq_homeomorph_of_pos hr q]
  exact (se2CarrierOrbitHomeomorph_of_pos hr q).injective

theorem isEmbedding_se2CarrierOrbitQuotientMap_of_pos
    {r : ℝ} (hr : 0 < r) (q : CasimirFiberCarrier r) :
    Topology.IsEmbedding (se2CarrierOrbitQuotientMap q) := by
  rw [se2CarrierOrbitQuotientMap_eq_homeomorph_of_pos hr q]
  exact (se2CarrierOrbitHomeomorph_of_pos hr q).isEmbedding

theorem isQuotientMap_se2CarrierOrbitQuotientMap_of_pos
    {r : ℝ} (hr : 0 < r) (q : CasimirFiberCarrier r) :
    Topology.IsQuotientMap (se2CarrierOrbitQuotientMap q) := by
  simpa only [se2CarrierOrbitQuotientMap, Function.comp_apply] using
    (rotationOrbitCarrierHomeomorph q).isQuotientMap.comp
      (isQuotientMap_rotationOrbitMapCarrier_of_pos hr q)

noncomputable def se2CarrierOrbitQuotientSection_of_pos
    {r : ℝ} (hr : 0 < r) (q : CasimirFiberCarrier r) :
    SE2CarrierOrbitCarrier q → RotationCarrier :=
  (rotationOrbitHomeomorph_of_pos hr q).symm ∘
    (rotationOrbitCarrierHomeomorph q).symm

theorem continuous_se2CarrierOrbitQuotientSection_of_pos
    {r : ℝ} (hr : 0 < r) (q : CasimirFiberCarrier r) :
    Continuous (se2CarrierOrbitQuotientSection_of_pos hr q) := by
  exact (rotationOrbitHomeomorph_of_pos hr q).symm.continuous.comp
    (rotationOrbitCarrierHomeomorph q).symm.continuous

theorem se2CarrierOrbitQuotientSection_rightInverse_of_pos
    {r : ℝ} (hr : 0 < r) (q : CasimirFiberCarrier r) :
    Function.RightInverse
      (se2CarrierOrbitQuotientSection_of_pos hr q)
      (se2CarrierOrbitQuotientMap q) := by
  intro w
  change rotationOrbitCarrierHomeomorph q
      (rotationOrbitMapCarrier q
        ((rotationOrbitHomeomorph_of_pos hr q).symm
          ((rotationOrbitCarrierHomeomorph q).symm w))) = w
  have hmap (g : RotationCarrier) :
      rotationOrbitCarrierHomeomorph q (rotationOrbitMapCarrier q g) =
        rotationOrbitCarrierHomeomorph q
          (rotationOrbitHomeomorph_of_pos hr q g) := by
    apply Subtype.ext
    rfl
  rw [hmap]
  rw [(rotationOrbitHomeomorph_of_pos hr q).apply_symm_apply]
  exact (rotationOrbitCarrierHomeomorph q).apply_symm_apply w

theorem isProperMap_se2CarrierOrbitQuotientMap
    {r : ℝ} (q : CasimirFiberCarrier r) :
    IsProperMap (se2CarrierOrbitQuotientMap q) := by
  simpa only [se2CarrierOrbitQuotientMap, Function.comp_apply] using
    (rotationOrbitCarrierHomeomorph q).isProperMap.comp
      (isProperMap_rotationOrbitMapCarrier q)

theorem continuous_se2CarrierOrbitQuotientMap
    {r : ℝ} (q : CasimirFiberCarrier r) :
    Continuous (se2CarrierOrbitQuotientMap q) := by
  exact (rotationOrbitCarrierHomeomorph q).continuous.comp
    (continuous_rotationOrbitMapCarrier q)

theorem se2CarrierOrbitQuotientMap_surjective
    {r : ℝ} (q : CasimirFiberCarrier r) :
    Function.Surjective (se2CarrierOrbitQuotientMap q) := by
  intro w
  obtain ⟨wr, hwr⟩ := (rotationOrbitCarrierHomeomorph q).surjective w
  obtain ⟨g, hg⟩ := rotationOrbitMapCarrier_surjective q wr
  refine ⟨g, ?_⟩
  rw [se2CarrierOrbitQuotientMap]
  rw [hg]
  exact hwr

theorem isOpenMap_rotationOrbitMapCarrier_of_pos
    {r : ℝ} (hr : 0 < r) (q : CasimirFiberCarrier r) :
    IsOpenMap (rotationOrbitMapCarrier q) := by
  have hfun : rotationOrbitMapCarrier q =
      rotationOrbitHomeomorph_of_pos hr q := by
    funext g
    apply Subtype.ext
    rfl
  rw [hfun]
  exact (rotationOrbitHomeomorph_of_pos hr q).isOpenMap

theorem isOpenMap_se2CarrierOrbitQuotientMap_of_pos
    {r : ℝ} (hr : 0 < r) (q : CasimirFiberCarrier r) :
    IsOpenMap (se2CarrierOrbitQuotientMap q) := by
  simpa only [se2CarrierOrbitQuotientMap, Function.comp_apply] using
    (rotationOrbitCarrierHomeomorph q).isOpenMap.comp
      (isOpenMap_rotationOrbitMapCarrier_of_pos hr q)

theorem isOpenQuotientMap_se2CarrierOrbitQuotientMap_of_pos
    {r : ℝ} (hr : 0 < r) (q : CasimirFiberCarrier r) :
    IsOpenQuotientMap (se2CarrierOrbitQuotientMap q) := by
  exact IsOpenQuotientMap.of_isOpenMap_isQuotientMap
    (isOpenMap_se2CarrierOrbitQuotientMap_of_pos hr q)
    (isQuotientMap_se2CarrierOrbitQuotientMap_of_pos hr q)

theorem isClosedMap_se2CarrierOrbitQuotientMap
    {r : ℝ} (q : CasimirFiberCarrier r) :
    IsClosedMap (se2CarrierOrbitQuotientMap q) := by
  exact (isProperMap_se2CarrierOrbitQuotientMap q).isClosedMap

theorem isQuotientMap_se2CarrierOrbitQuotientMap
    {r : ℝ} (q : CasimirFiberCarrier r) :
    Topology.IsQuotientMap (se2CarrierOrbitQuotientMap q) := by
  exact (isClosedMap_se2CarrierOrbitQuotientMap q).isQuotientMap
    (continuous_se2CarrierOrbitQuotientMap q)
    (se2CarrierOrbitQuotientMap_surjective q)

instance subsingleton_se2CarrierOrbitCarrier_zero
    (q : CasimirFiberCarrier 0) :
    Subsingleton (SE2CarrierOrbitCarrier q) := by
  constructor
  intro x y
  apply Subtype.ext
  have hx : x.1 ∈ rotationOrbit q := by
    rw [← se2CarrierOrbit_eq_rotationOrbit q]
    exact x.2
  have hy : y.1 ∈ rotationOrbit q := by
    rw [← se2CarrierOrbit_eq_rotationOrbit q]
    exact y.2
  rw [rotationOrbit_eq_singleton_of_zero q] at hx hy
  exact hx.trans hy.symm

theorem isQuotientMap_se2CarrierOrbitQuotientMap_zero
    (q : CasimirFiberCarrier 0) :
    Topology.IsQuotientMap (se2CarrierOrbitQuotientMap q) := by
  have hclosed : IsClosedMap (se2CarrierOrbitQuotientMap q) := by
    intro s hs
    by_cases hne : s.Nonempty
    · have himage : se2CarrierOrbitQuotientMap q '' s = Set.univ := by
        apply Set.eq_univ_of_forall
        intro w
        obtain ⟨x, hx⟩ := hne
        exact ⟨x, hx, Subsingleton.elim _ _⟩
      rw [himage]
      exact isClosed_univ
    · rw [Set.not_nonempty_iff_eq_empty.mp hne, Set.image_empty]
      exact isClosed_empty
  exact hclosed.isQuotientMap
    (continuous_se2CarrierOrbitQuotientMap q)
    (se2CarrierOrbitQuotientMap_surjective q)

theorem isOpenMap_se2CarrierOrbitQuotientMap_zero
    (q : CasimirFiberCarrier 0) :
    IsOpenMap (se2CarrierOrbitQuotientMap q) := by
  intro s hs
  by_cases hne : s.Nonempty
  · have himage : se2CarrierOrbitQuotientMap q '' s = Set.univ := by
      apply Set.eq_univ_of_forall
      intro w
      obtain ⟨x, hx⟩ := hne
      exact ⟨x, hx, Subsingleton.elim _ _⟩
    rw [himage]
    exact isOpen_univ
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, Set.image_empty]
    exact isOpen_empty

theorem isOpenQuotientMap_se2CarrierOrbitQuotientMap_zero
    (q : CasimirFiberCarrier 0) :
    IsOpenQuotientMap (se2CarrierOrbitQuotientMap q) := by
  exact IsOpenQuotientMap.of_isOpenMap_isQuotientMap
    (isOpenMap_se2CarrierOrbitQuotientMap_zero q)
    (isQuotientMap_se2CarrierOrbitQuotientMap_zero q)

theorem isOpenQuotientMap_se2CarrierOrbitQuotientMap_all
    {r : ℝ} (q : CasimirFiberCarrier r) :
    IsOpenQuotientMap (se2CarrierOrbitQuotientMap q) := by
  by_cases hr : r = 0
  · subst r
    exact isOpenQuotientMap_se2CarrierOrbitQuotientMap_zero q
  · have hrnonneg : 0 ≤ r := by
      have hq := q.2
      change q.1.2.1 ^ 2 + q.1.2.2 ^ 2 = r at hq
      nlinarith [sq_nonneg q.1.2.1, sq_nonneg q.1.2.2]
    have hrpos : 0 < r := lt_of_le_of_ne hrnonneg (Ne.symm hr)
    exact isOpenQuotientMap_se2CarrierOrbitQuotientMap_of_pos hrpos q

theorem isCompact_se2CarrierOrbitCarrier
    {r : ℝ} (q : CasimirFiberCarrier r) :
    IsCompact (Set.univ : Set (SE2CarrierOrbitCarrier q)) := by
  have himage : se2CarrierOrbitQuotientMap q ''
      (Set.univ : Set RotationCarrier) = Set.univ := by
    rw [Set.image_univ]
    exact Set.range_eq_univ.mpr (se2CarrierOrbitQuotientMap_surjective q)
  rw [← himage]
  exact isCompact_univ.image (continuous_se2CarrierOrbitQuotientMap q)

instance compactSpace_se2CarrierOrbitCarrier
    {r : ℝ} (q : CasimirFiberCarrier r) :
    CompactSpace (SE2CarrierOrbitCarrier q) where
  isCompact_univ := isCompact_se2CarrierOrbitCarrier q

theorem isCompact_se2CarrierOrbit
    {r : ℝ} (q : CasimirFiberCarrier r) :
    IsCompact (se2CarrierOrbit q) := by
  rw [se2CarrierOrbit_eq_rotationOrbit q]
  exact isCompact_rotationOrbit q

theorem isPathConnected_se2CarrierOrbit
    {r : ℝ} (q : CasimirFiberCarrier r) :
    IsPathConnected (se2CarrierOrbit q) := by
  rw [se2CarrierOrbit_eq_rotationOrbit q]
  exact isPathConnected_rotationOrbit q

theorem isClosed_se2CarrierOrbit
    {r : ℝ} (q : CasimirFiberCarrier r) :
    IsClosed (se2CarrierOrbit q) := by
  rw [se2CarrierOrbit_eq_rotationOrbit q]
  exact isClosed_rotationOrbit q

theorem isClosedEmbedding_se2CarrierOrbitCarrier_subtypeVal
    {r : ℝ} (q : CasimirFiberCarrier r) :
    Topology.IsClosedEmbedding
      ((↑) : SE2CarrierOrbitCarrier q → CasimirFiberCarrier r) := by
  exact (isClosed_se2CarrierOrbit q).isClosedEmbedding_subtypeVal

instance t2Space_se2CarrierOrbitCarrier
    {r : ℝ} (q : CasimirFiberCarrier r) :
    T2Space (SE2CarrierOrbitCarrier q) :=
  (isClosedEmbedding_se2CarrierOrbitCarrier_subtypeVal q).isEmbedding.t2Space

instance secondCountableTopology_se2CarrierOrbitCarrier
    {r : ℝ} (q : CasimirFiberCarrier r) :
    SecondCountableTopology (SE2CarrierOrbitCarrier q) :=
  (isClosedEmbedding_se2CarrierOrbitCarrier_subtypeVal q).isEmbedding.secondCountableTopology

instance locallyCompactSpace_se2CarrierOrbitCarrier
    {r : ℝ} (q : CasimirFiberCarrier r) :
    LocallyCompactSpace (SE2CarrierOrbitCarrier q) := by
  exact (isClosedEmbedding_se2CarrierOrbitCarrier_subtypeVal q).locallyCompactSpace

theorem isClosedMap_se2CarrierOrbitCarrier_subtypeVal
    {r : ℝ} (q : CasimirFiberCarrier r) :
    IsClosedMap
      ((↑) : SE2CarrierOrbitCarrier q → CasimirFiberCarrier r) := by
  exact (isClosedEmbedding_se2CarrierOrbitCarrier_subtypeVal q).isClosedMap

theorem isProperMap_se2CarrierOrbitCarrier_subtypeVal
    {r : ℝ} (q : CasimirFiberCarrier r) :
    IsProperMap
      ((↑) : SE2CarrierOrbitCarrier q → CasimirFiberCarrier r) := by
  exact (isClosedEmbedding_se2CarrierOrbitCarrier_subtypeVal q).isProperMap

def se2CarrierOrbitCarrierAction
    {r : ℝ} (q : CasimirFiberCarrier r)
    (g : MatrixSE2Carrier) (w : SE2CarrierOrbitCarrier q) :
  SE2CarrierOrbitCarrier q :=
  ⟨g • w.1, by
    rcases w.2 with ⟨h, hw⟩
    refine ⟨g * h, ?_⟩
    rw [se2CarrierOrbitMap_mul, hw]
    rfl⟩

theorem se2CarrierOrbitCarrierAction_one
    {r : ℝ} (q : CasimirFiberCarrier r)
    (w : SE2CarrierOrbitCarrier q) :
    se2CarrierOrbitCarrierAction q 1 w = w := by
  apply Subtype.ext
  exact one_smul MatrixSE2Carrier w.1

theorem se2CarrierOrbitCarrierAction_mul
    {r : ℝ} (q : CasimirFiberCarrier r)
    (g h : MatrixSE2Carrier) (w : SE2CarrierOrbitCarrier q) :
    se2CarrierOrbitCarrierAction q (g * h) w =
      se2CarrierOrbitCarrierAction q g
        (se2CarrierOrbitCarrierAction q h w) := by
  apply Subtype.ext
  exact mul_smul g h w.1

instance {r : ℝ} (q : CasimirFiberCarrier r) :
    MulAction MatrixSE2Carrier (SE2CarrierOrbitCarrier q) where
  smul := se2CarrierOrbitCarrierAction q
  one_smul := se2CarrierOrbitCarrierAction_one q
  mul_smul := se2CarrierOrbitCarrierAction_mul q

theorem continuous_se2CarrierOrbitCarrierAction
    {r : ℝ} (q : CasimirFiberCarrier r) :
    Continuous (fun p : MatrixSE2Carrier × SE2CarrierOrbitCarrier q =>
      p.1 • p.2) := by
  apply Continuous.subtype_mk
  have hmap : Continuous (fun p : MatrixSE2Carrier × SE2CarrierOrbitCarrier q =>
      (p.1, p.2.1)) := by
    fun_prop
  simpa only [Function.comp_apply] using
    continuous_se2CarrierMomentumAction.comp hmap

instance {r : ℝ} (q : CasimirFiberCarrier r) :
    ContinuousSMul MatrixSE2Carrier (SE2CarrierOrbitCarrier q) where
  continuous_smul := continuous_se2CarrierOrbitCarrierAction q

def rotationCarrierLift (g : RotationCarrier) : MatrixSE2Carrier :=
  ⟨(g.1.1, g.1.2, 0, 0), g.2⟩

theorem rotationCarrierLift_one :
    rotationCarrierLift (1 : RotationCarrier) =
      (1 : MatrixSE2Carrier) := by
  apply Subtype.ext
  change (1, 0, 0, 0) =
    InfoGeometry.Canonical.SE2SouriauCocycle.se2ParameterIdentity
  rfl

theorem rotationCarrierLift_mul (g h : RotationCarrier) :
    rotationCarrierLift (g * h) =
      rotationCarrierLift g * rotationCarrierLift h := by
  apply Subtype.ext
  change
    (g.1.1 * h.1.1 - g.1.2 * h.1.2,
      g.1.2 * h.1.1 + g.1.1 * h.1.2, 0, 0) =
    InfoGeometry.Canonical.SE2SouriauCocycle.se2ParameterProduct
      g.1.1 g.1.2 0 0 h.1.1 h.1.2 0 0
  dsimp [InfoGeometry.Canonical.SE2SouriauCocycle.se2ParameterProduct]
  ring

theorem continuous_rotationCarrierLift :
    Continuous rotationCarrierLift := by
  unfold rotationCarrierLift
  apply Continuous.subtype_mk
  fun_prop

def rotationCarrierLiftMonoidHom :
    RotationCarrier →ₜ* MatrixSE2Carrier where
  toMonoidHom :=
    { toFun := rotationCarrierLift
      map_one' := rotationCarrierLift_one
      map_mul' := rotationCarrierLift_mul }
  continuous_toFun := continuous_rotationCarrierLift

theorem se2CarrierRotationProjection_rotationCarrierLift
    (g : RotationCarrier) :
    se2CarrierRotationProjection (rotationCarrierLift g) = g := by
  apply Subtype.ext
  rfl

theorem se2CarrierRotationProjectionMonoidHom_comp_lift :
    se2CarrierRotationProjectionMonoidHom.comp rotationCarrierLiftMonoidHom =
      ContinuousMonoidHom.id RotationCarrier := by
  apply ContinuousMonoidHom.ext
  intro g
  change se2CarrierRotationProjection (rotationCarrierLift g) = g
  exact se2CarrierRotationProjection_rotationCarrierLift g

def se2CarrierTranslationSlice
    (t : InfoGeometry.Canonical.SE2SouriauCocycle.Point2) :
    MatrixSE2Carrier :=
  ⟨(1, 0, t.1, t.2), by
    norm_num [InfoGeometry.Canonical.SE2SouriauCocycle.se2RotationParameters,
      InfoGeometry.Canonical.SE2SouriauCocycle.rotationConstraint]⟩

theorem continuous_se2CarrierTranslationSlice :
    Continuous se2CarrierTranslationSlice := by
  unfold se2CarrierTranslationSlice
  apply Continuous.subtype_mk
  fun_prop

theorem injective_se2CarrierTranslationSlice :
    Function.Injective se2CarrierTranslationSlice := by
  intro t u h
  have hval := congrArg (fun g : MatrixSE2Carrier => g.1) h
  apply Prod.ext
  · exact congrArg (fun g : InfoGeometry.Canonical.SE2SouriauCocycle.SE2Parameters =>
      g.2.2.1) hval
  · exact congrArg (fun g : InfoGeometry.Canonical.SE2SouriauCocycle.SE2Parameters =>
      g.2.2.2) hval

def se2CarrierTranslationProjection
    (g : MatrixSE2Carrier) :
    InfoGeometry.Canonical.SE2SouriauCocycle.Point2 :=
  (g.1.2.2.1, g.1.2.2.2)

theorem continuous_se2CarrierTranslationProjection :
    Continuous se2CarrierTranslationProjection := by
  unfold se2CarrierTranslationProjection
  fun_prop

theorem se2CarrierTranslationProjection_slice_leftInverse :
    Function.LeftInverse se2CarrierTranslationProjection
      se2CarrierTranslationSlice := by
  intro t
  rfl

theorem isClosedEmbedding_se2CarrierTranslationSlice :
    Topology.IsClosedEmbedding se2CarrierTranslationSlice := by
  exact se2CarrierTranslationProjection_slice_leftInverse.isClosedEmbedding
    continuous_se2CarrierTranslationProjection
    continuous_se2CarrierTranslationSlice

theorem isClosedMap_se2CarrierTranslationSlice :
    IsClosedMap se2CarrierTranslationSlice := by
  exact isClosedEmbedding_se2CarrierTranslationSlice.isClosedMap

theorem isProperMap_se2CarrierTranslationSlice :
    IsProperMap se2CarrierTranslationSlice := by
  exact isClosedEmbedding_se2CarrierTranslationSlice.isProperMap

theorem se2CarrierRotationProjection_translationSlice
    (t : InfoGeometry.Canonical.SE2SouriauCocycle.Point2) :
    se2CarrierRotationProjection (se2CarrierTranslationSlice t) = 1 := by
  apply Subtype.ext
  rfl

def se2CarrierTranslationKernel : Set MatrixSE2Carrier :=
  {g | se2CarrierRotationProjection g = 1}

noncomputable def se2CarrierTranslationKernelSubgroup : Subgroup MatrixSE2Carrier :=
  (se2CarrierRotationProjectionMonoidHom.toMonoidHom).ker

instance se2CarrierTranslationKernelSubgroup_normal :
    se2CarrierTranslationKernelSubgroup.Normal := by
  change (se2CarrierRotationProjectionMonoidHom.toMonoidHom).ker.Normal
  exact MonoidHom.normal_ker _

abbrev se2CarrierTranslationQuotient :=
  MatrixSE2Carrier ⧸ se2CarrierTranslationKernelSubgroup

noncomputable def se2CarrierTranslationQuotientEquiv :
    se2CarrierTranslationQuotient ≃* RotationCarrier :=
  QuotientGroup.quotientKerEquivOfSurjective
    se2CarrierRotationProjectionMonoidHom.toMonoidHom
    se2CarrierRotationProjection_surjective

theorem se2CarrierTranslationQuotientEquiv_mk
    (g : MatrixSE2Carrier) :
    se2CarrierTranslationQuotientEquiv (QuotientGroup.mk g) =
      se2CarrierRotationProjection g := by
  rfl

theorem continuous_se2CarrierTranslationQuotientEquiv :
    Continuous (se2CarrierTranslationQuotientEquiv :
      se2CarrierTranslationQuotient → RotationCarrier) := by
  have hq : Topology.IsQuotientMap
      (QuotientGroup.mk : MatrixSE2Carrier → se2CarrierTranslationQuotient) :=
    QuotientGroup.isQuotientMap_mk _
  apply hq.continuous_iff.mpr
  simpa only [Function.comp_apply,
    se2CarrierTranslationQuotientEquiv_mk] using
    continuous_se2CarrierRotationProjection

theorem se2CarrierTranslationQuotientEquiv_symm_eq_lift :
    (se2CarrierTranslationQuotientEquiv.symm :
      RotationCarrier → se2CarrierTranslationQuotient) =
      (fun g : RotationCarrier => QuotientGroup.mk (rotationCarrierLift g)) := by
  funext g
  apply se2CarrierTranslationQuotientEquiv.injective
  calc
    se2CarrierTranslationQuotientEquiv
        (se2CarrierTranslationQuotientEquiv.symm g) = g :=
      EquivLike.right_inv se2CarrierTranslationQuotientEquiv g
    _ = se2CarrierTranslationQuotientEquiv
        (QuotientGroup.mk (rotationCarrierLift g)) := by
      rw [se2CarrierTranslationQuotientEquiv_mk,
        se2CarrierRotationProjection_rotationCarrierLift]

noncomputable def se2CarrierTranslationQuotientHomeomorph :
    se2CarrierTranslationQuotient ≃ₜ RotationCarrier :=
  { se2CarrierTranslationQuotientEquiv with
    continuous_toFun := continuous_se2CarrierTranslationQuotientEquiv
    continuous_invFun := by
      change Continuous (se2CarrierTranslationQuotientEquiv.symm :
        RotationCarrier → se2CarrierTranslationQuotient)
      rw [se2CarrierTranslationQuotientEquiv_symm_eq_lift]
      exact QuotientGroup.continuous_mk.comp continuous_rotationCarrierLift }

instance compactSpace_se2CarrierTranslationQuotient :
    CompactSpace se2CarrierTranslationQuotient where
  isCompact_univ :=
    (se2CarrierTranslationQuotientHomeomorph.symm.compactSpace).isCompact_univ

instance pathConnectedSpace_se2CarrierTranslationQuotient :
    PathConnectedSpace se2CarrierTranslationQuotient := by
  exact se2CarrierTranslationQuotientHomeomorph.symm.surjective.pathConnectedSpace
    se2CarrierTranslationQuotientHomeomorph.symm.continuous

theorem isPathConnected_se2CarrierTranslationQuotient_univ :
    IsPathConnected (Set.univ : Set se2CarrierTranslationQuotient) := by
  letI := pathConnectedSpace_se2CarrierTranslationQuotient
  exact isPathConnected_univ

instance connectedSpace_se2CarrierTranslationQuotient :
    ConnectedSpace se2CarrierTranslationQuotient := by
  apply connectedSpace_iff_univ.mpr
  exact isPathConnected_se2CarrierTranslationQuotient_univ.isConnected

instance t2Space_se2CarrierTranslationQuotient :
    T2Space se2CarrierTranslationQuotient :=
  se2CarrierTranslationQuotientHomeomorph.symm.t2Space

instance locallyCompactSpace_se2CarrierTranslationQuotient :
    LocallyCompactSpace se2CarrierTranslationQuotient :=
  se2CarrierTranslationQuotientHomeomorph.isOpenEmbedding.locallyCompactSpace

instance secondCountableTopology_se2CarrierTranslationQuotient :
    SecondCountableTopology se2CarrierTranslationQuotient :=
  se2CarrierTranslationQuotientHomeomorph.secondCountableTopology

theorem isOpenQuotientMap_se2CarrierTranslationQuotient_mk :
    IsOpenQuotientMap
      (QuotientGroup.mk : MatrixSE2Carrier → se2CarrierTranslationQuotient) :=
  QuotientGroup.isOpenQuotientMap_mk

theorem se2CarrierTranslationKernelSubgroup_carrier :
    (se2CarrierTranslationKernelSubgroup : Set MatrixSE2Carrier) =
      se2CarrierTranslationKernel := by
  rfl

theorem se2CarrierTranslationSlice_range_eq_kernel :
    Set.range se2CarrierTranslationSlice = se2CarrierTranslationKernel := by
  apply Set.Subset.antisymm
  · rintro g ⟨t, rfl⟩
    exact se2CarrierRotationProjection_translationSlice t
  · intro g hg
    let t := se2CarrierTranslationProjection g
    refine ⟨t, ?_⟩
    apply Subtype.ext
    have hc := congrArg (fun x : RotationCarrier => x.1.1) hg
    have hs := congrArg (fun x : RotationCarrier => x.1.2) hg
    ext
    · simpa [se2CarrierRotationProjection, se2CarrierProductHomeomorph,
        se2CarrierTranslationSlice] using hc.symm
    · simpa [se2CarrierRotationProjection, se2CarrierProductHomeomorph,
        se2CarrierTranslationSlice] using hs.symm
    · rfl
    · rfl

theorem isClosed_se2CarrierTranslationKernel :
    IsClosed se2CarrierTranslationKernel := by
  rw [← se2CarrierTranslationSlice_range_eq_kernel]
  exact isClosedEmbedding_se2CarrierTranslationSlice.isClosed_range

theorem isClosed_se2CarrierTranslationKernelSubgroup :
    IsClosed (se2CarrierTranslationKernelSubgroup : Set MatrixSE2Carrier) := by
  rw [se2CarrierTranslationKernelSubgroup_carrier]
  exact isClosed_se2CarrierTranslationKernel

theorem se2CarrierTranslationSlice_range_eq_subgroup :
    Set.range se2CarrierTranslationSlice =
      (se2CarrierTranslationKernelSubgroup : Set MatrixSE2Carrier) := by
  rw [se2CarrierTranslationKernelSubgroup_carrier]
  exact se2CarrierTranslationSlice_range_eq_kernel

theorem se2CarrierTranslationSlice_action
    {r : ℝ} (t : InfoGeometry.Canonical.SE2SouriauCocycle.Point2)
    (q : CasimirFiberCarrier r) :
    se2CarrierMomentumAction (se2CarrierTranslationSlice t) q = q := by
  apply Subtype.ext
  change momentumRotationCoordinates 1 0 q.1 = q.1
  ext <;> dsimp [momentumRotationCoordinates] <;> ring

def rotationOrbitCarrierAction
    {r : ℝ} (q : CasimirFiberCarrier r)
    (g : RotationCarrier) (w : SE2CarrierOrbitCarrier q) :
    SE2CarrierOrbitCarrier q :=
  se2CarrierOrbitCarrierAction q (rotationCarrierLift g) w

theorem rotationOrbitCarrierAction_one
    {r : ℝ} (q : CasimirFiberCarrier r)
    (w : SE2CarrierOrbitCarrier q) :
    rotationOrbitCarrierAction q 1 w = w := by
  exact se2CarrierOrbitCarrierAction_one q w

theorem rotationOrbitCarrierAction_mul
    {r : ℝ} (q : CasimirFiberCarrier r)
    (g h : RotationCarrier) (w : SE2CarrierOrbitCarrier q) :
    rotationOrbitCarrierAction q (g * h) w =
      rotationOrbitCarrierAction q g
        (rotationOrbitCarrierAction q h w) := by
  apply Subtype.ext
  change rotationCarrierLift (g * h) • w.1 =
    rotationCarrierLift g • (rotationCarrierLift h • w.1)
  rw [rotationCarrierLift_mul, mul_smul]

instance {r : ℝ} (q : CasimirFiberCarrier r) :
    MulAction RotationCarrier (SE2CarrierOrbitCarrier q) where
  smul := rotationOrbitCarrierAction q
  one_smul := rotationOrbitCarrierAction_one q
  mul_smul := rotationOrbitCarrierAction_mul q

theorem continuous_rotationOrbitCarrierAction
    {r : ℝ} (q : CasimirFiberCarrier r) :
    Continuous (fun p : RotationCarrier × SE2CarrierOrbitCarrier q =>
      p.1 • p.2) := by
  change Continuous (fun p : RotationCarrier × SE2CarrierOrbitCarrier q =>
    se2CarrierOrbitCarrierAction q (rotationCarrierLift p.1) p.2)
  exact continuous_se2CarrierOrbitCarrierAction q |>.comp
    (continuous_rotationCarrierLift.comp continuous_fst |>.prodMk continuous_snd)

instance {r : ℝ} (q : CasimirFiberCarrier r) :
    ContinuousSMul RotationCarrier (SE2CarrierOrbitCarrier q) where
  continuous_smul := continuous_rotationOrbitCarrierAction q

theorem se2CarrierOrbitQuotientMap_mul
    {r : ℝ} (q : CasimirFiberCarrier r)
    (g h : RotationCarrier) :
    se2CarrierOrbitQuotientMap q (g * h) =
      se2CarrierOrbitCarrierAction q (rotationCarrierLift g)
        (se2CarrierOrbitQuotientMap q h) := by
  apply Subtype.ext
  change rotationMomentumAction (g * h) q =
    se2CarrierMomentumAction (rotationCarrierLift g)
      (rotationMomentumAction h q)
  rw [rotationMomentumAction_mul]
  rfl

def se2CarrierOrbitCarrierMap
    {r : ℝ} (q : CasimirFiberCarrier r) :
    MatrixSE2Carrier → SE2CarrierOrbitCarrier q := fun g =>
      ⟨se2CarrierOrbitMap q g, ⟨g, rfl⟩⟩

theorem se2CarrierOrbitCarrierMap_one
    {r : ℝ} (q : CasimirFiberCarrier r) :
    se2CarrierOrbitCarrierMap q 1 =
      ⟨q, ⟨1, se2CarrierMomentumAction_one q⟩⟩ := by
  apply Subtype.ext
  exact se2CarrierMomentumAction_one q

theorem se2CarrierOrbitCarrierMap_mul
    {r : ℝ} (q : CasimirFiberCarrier r)
    (g h : MatrixSE2Carrier) :
    se2CarrierOrbitCarrierMap q (g * h) =
      se2CarrierOrbitCarrierAction q g (se2CarrierOrbitCarrierMap q h) := by
  apply Subtype.ext
  change se2CarrierOrbitMap q (g * h) =
    se2CarrierMomentumAction g (se2CarrierOrbitMap q h)
  rw [se2CarrierOrbitMap_mul]
  rfl

theorem se2CarrierOrbitCarrierMap_translationSlice_left
    {r : ℝ} (t : InfoGeometry.Canonical.SE2SouriauCocycle.Point2)
    (q : CasimirFiberCarrier r) (g : MatrixSE2Carrier) :
    se2CarrierOrbitCarrierMap q (se2CarrierTranslationSlice t * g) =
      se2CarrierOrbitCarrierMap q g := by
  rw [se2CarrierOrbitCarrierMap_mul]
  apply Subtype.ext
  exact se2CarrierTranslationSlice_action t (se2CarrierOrbitMap q g)

theorem se2CarrierOrbitCarrierMap_translationSlice_right
    {r : ℝ} (t : InfoGeometry.Canonical.SE2SouriauCocycle.Point2)
    (q : CasimirFiberCarrier r) (g : MatrixSE2Carrier) :
    se2CarrierOrbitCarrierMap q (g * se2CarrierTranslationSlice t) =
      se2CarrierOrbitCarrierMap q g := by
  rw [se2CarrierOrbitCarrierMap_mul]
  have ht : se2CarrierOrbitMap q (se2CarrierTranslationSlice t) = q := by
    exact se2CarrierTranslationSlice_action t q
  apply Subtype.ext
  change se2CarrierMomentumAction g
      (se2CarrierOrbitMap q (se2CarrierTranslationSlice t)) =
    se2CarrierOrbitMap q g
  rw [ht]
  rfl

theorem se2CarrierOrbitCarrierMap_translationKernel_left
    {r : ℝ} (k : se2CarrierTranslationKernelSubgroup)
    (q : CasimirFiberCarrier r) (g : MatrixSE2Carrier) :
    se2CarrierOrbitCarrierMap q (k.1 * g) =
      se2CarrierOrbitCarrierMap q g := by
  have hk : k.1 ∈ (se2CarrierTranslationKernelSubgroup : Set MatrixSE2Carrier) := k.2
  rw [← se2CarrierTranslationSlice_range_eq_subgroup] at hk
  rcases hk with ⟨t, ht⟩
  rw [← ht]
  exact se2CarrierOrbitCarrierMap_translationSlice_left t q g

theorem se2CarrierOrbitCarrierMap_translationKernel_right
    {r : ℝ} (k : se2CarrierTranslationKernelSubgroup)
    (q : CasimirFiberCarrier r) (g : MatrixSE2Carrier) :
    se2CarrierOrbitCarrierMap q (g * k.1) =
      se2CarrierOrbitCarrierMap q g := by
  have hk : k.1 ∈ (se2CarrierTranslationKernelSubgroup : Set MatrixSE2Carrier) := k.2
  rw [← se2CarrierTranslationSlice_range_eq_subgroup] at hk
  rcases hk with ⟨t, ht⟩
  rw [← ht]
  exact se2CarrierOrbitCarrierMap_translationSlice_right t q g

theorem se2CarrierOrbitCarrierMap_eq_comp_projection
    {r : ℝ} (q : CasimirFiberCarrier r) :
    se2CarrierOrbitCarrierMap q =
      se2CarrierOrbitQuotientMap q ∘ se2CarrierRotationProjection := by
  funext g
  apply Subtype.ext
  rfl

noncomputable def se2CarrierTranslationQuotientOrbitHomeomorph_of_pos
    {r : ℝ} (hr : 0 < r) (q : CasimirFiberCarrier r) :
    se2CarrierTranslationQuotient ≃ₜ SE2CarrierOrbitCarrier q :=
  se2CarrierTranslationQuotientHomeomorph.trans
    (se2CarrierOrbitHomeomorph_of_pos hr q)

theorem se2CarrierOrbitCarrierMap_eq_comp_quotientMk_homeomorph_of_pos
    {r : ℝ} (hr : 0 < r) (q : CasimirFiberCarrier r) :
    se2CarrierOrbitCarrierMap q =
      (se2CarrierTranslationQuotientOrbitHomeomorph_of_pos hr q) ∘
        (QuotientGroup.mk : MatrixSE2Carrier → se2CarrierTranslationQuotient) := by
  funext g
  rw [se2CarrierOrbitCarrierMap_eq_comp_projection q]
  change se2CarrierOrbitQuotientMap q (se2CarrierRotationProjection g) =
    se2CarrierOrbitHomeomorph_of_pos hr q
      (se2CarrierTranslationQuotientHomeomorph (QuotientGroup.mk g))
  rw [se2CarrierOrbitQuotientMap_eq_homeomorph_of_pos hr q]
  congr 1

noncomputable def se2CarrierTranslationQuotientOrbitAction
    {r : ℝ} (q : CasimirFiberCarrier r)
    (a : se2CarrierTranslationQuotient)
    (w : SE2CarrierOrbitCarrier q) : SE2CarrierOrbitCarrier q :=
  se2CarrierTranslationQuotientEquiv a • w

noncomputable instance se2CarrierTranslationQuotientOrbitSMul
    {r : ℝ} (q : CasimirFiberCarrier r) :
    SMul se2CarrierTranslationQuotient (SE2CarrierOrbitCarrier q) where
  smul := se2CarrierTranslationQuotientOrbitAction q

theorem se2CarrierTranslationQuotientOrbitAction_one
    {r : ℝ} (q : CasimirFiberCarrier r)
    (w : SE2CarrierOrbitCarrier q) :
    se2CarrierTranslationQuotientOrbitAction q 1 w = w := by
  dsimp [se2CarrierTranslationQuotientOrbitAction]
  rw [map_one, one_smul]

theorem se2CarrierTranslationQuotientOrbitAction_mul
    {r : ℝ} (q : CasimirFiberCarrier r)
    (a b : se2CarrierTranslationQuotient)
    (w : SE2CarrierOrbitCarrier q) :
    se2CarrierTranslationQuotientOrbitAction q (a * b) w =
      se2CarrierTranslationQuotientOrbitAction q a
        (se2CarrierTranslationQuotientOrbitAction q b w) := by
  dsimp [se2CarrierTranslationQuotientOrbitAction]
  rw [map_mul, mul_smul]

noncomputable instance se2CarrierTranslationQuotientOrbitMulAction
    {r : ℝ} (q : CasimirFiberCarrier r) :
    MulAction se2CarrierTranslationQuotient (SE2CarrierOrbitCarrier q) where
  smul := se2CarrierTranslationQuotientOrbitAction q
  one_smul := se2CarrierTranslationQuotientOrbitAction_one q
  mul_smul := se2CarrierTranslationQuotientOrbitAction_mul q

theorem continuous_se2CarrierTranslationQuotientOrbitAction
    {r : ℝ} (q : CasimirFiberCarrier r) :
    Continuous (fun p : se2CarrierTranslationQuotient ×
        SE2CarrierOrbitCarrier q => p.1 • p.2) := by
  let e := se2CarrierTranslationQuotientEquiv
  change Continuous (fun p : se2CarrierTranslationQuotient ×
    SE2CarrierOrbitCarrier q => e p.1 • p.2)
  exact continuous_rotationOrbitCarrierAction q |>.comp <|
    (continuous_se2CarrierTranslationQuotientEquiv.comp continuous_fst).prodMk
      continuous_snd

theorem se2CarrierTranslationQuotientOrbitAction_mk
    {r : ℝ} (q : CasimirFiberCarrier r)
    (g : MatrixSE2Carrier) (w : SE2CarrierOrbitCarrier q) :
    (QuotientGroup.mk g : se2CarrierTranslationQuotient) • w =
      se2CarrierRotationProjection g • w := by
  change se2CarrierTranslationQuotientEquiv (QuotientGroup.mk g) • w =
    se2CarrierRotationProjection g • w
  rw [se2CarrierTranslationQuotientEquiv_mk]

theorem se2CarrierOrbitCarrierAction_eq_rotation
    {r : ℝ} (q : CasimirFiberCarrier r)
    (g : MatrixSE2Carrier) (w : SE2CarrierOrbitCarrier q) :
    se2CarrierOrbitCarrierAction q g w =
      rotationOrbitCarrierAction q (se2CarrierRotationProjection g) w := by
  apply Subtype.ext
  rfl

theorem se2CarrierOrbitCarrierMap_quotient_equivariant_mk
    {r : ℝ} (q : CasimirFiberCarrier r)
    (g h : MatrixSE2Carrier) :
    (QuotientGroup.mk g : se2CarrierTranslationQuotient) •
        se2CarrierOrbitCarrierMap q h =
      se2CarrierOrbitCarrierMap q (g * h) := by
  rw [se2CarrierTranslationQuotientOrbitAction_mk]
  change rotationOrbitCarrierAction q (se2CarrierRotationProjection g)
      (se2CarrierOrbitCarrierMap q h) =
    se2CarrierOrbitCarrierMap q (g * h)
  rw [← se2CarrierOrbitCarrierAction_eq_rotation q g
    (se2CarrierOrbitCarrierMap q h)]
  exact (se2CarrierOrbitCarrierMap_mul q g h).symm

theorem se2CarrierTranslationQuotientOrbitHomeomorph_equivariant
    {r : ℝ} (hr : 0 < r) (q : CasimirFiberCarrier r)
    (a b : se2CarrierTranslationQuotient) :
    se2CarrierTranslationQuotientOrbitHomeomorph_of_pos hr q (a * b) =
      a • se2CarrierTranslationQuotientOrbitHomeomorph_of_pos hr q b := by
  induction a using QuotientGroup.induction_on with
  | _ g =>
    induction b using QuotientGroup.induction_on with
    | _ h =>
      have hfactor (k : MatrixSE2Carrier) :
          se2CarrierOrbitCarrierMap q k =
            se2CarrierTranslationQuotientOrbitHomeomorph_of_pos hr q
              (QuotientGroup.mk k) :=
        congrFun
          (se2CarrierOrbitCarrierMap_eq_comp_quotientMk_homeomorph_of_pos hr q) k
      change se2CarrierTranslationQuotientOrbitHomeomorph_of_pos hr q
          (QuotientGroup.mk (g * h)) =
        (QuotientGroup.mk g : se2CarrierTranslationQuotient) •
          se2CarrierTranslationQuotientOrbitHomeomorph_of_pos hr q
            (QuotientGroup.mk h)
      rw [← hfactor (g * h), ← hfactor h]
      exact (se2CarrierOrbitCarrierMap_quotient_equivariant_mk q g h).symm

noncomputable def se2CarrierTranslationQuotientOrbitActionHom_of_pos
    {r : ℝ} (hr : 0 < r) (q : CasimirFiberCarrier r) :
    se2CarrierTranslationQuotient →[se2CarrierTranslationQuotient]
      SE2CarrierOrbitCarrier q where
  toFun := se2CarrierTranslationQuotientOrbitHomeomorph_of_pos hr q
  map_smul' := by
    intro a b
    exact se2CarrierTranslationQuotientOrbitHomeomorph_equivariant hr q a b

noncomputable def se2CarrierTranslationQuotientOrbitActionHom_inv_of_pos
    {r : ℝ} (hr : 0 < r) (q : CasimirFiberCarrier r) :
    SE2CarrierOrbitCarrier q →[se2CarrierTranslationQuotient]
      se2CarrierTranslationQuotient where
  toFun := (se2CarrierTranslationQuotientOrbitHomeomorph_of_pos hr q).symm
  map_smul' := by
    intro a w
    let H := se2CarrierTranslationQuotientOrbitHomeomorph_of_pos hr q
    apply H.injective
    calc
      H (H.symm (a • w)) = a • w := H.apply_symm_apply _
      _ = a • H (H.symm w) := by rw [H.apply_symm_apply]
      _ = H (a * H.symm w) :=
        (se2CarrierTranslationQuotientOrbitHomeomorph_equivariant hr q a
          (H.symm w)).symm

theorem continuous_se2CarrierTranslationQuotientOrbitActionHom_inv_of_pos
    {r : ℝ} (hr : 0 < r) (q : CasimirFiberCarrier r) :
    Continuous (se2CarrierTranslationQuotientOrbitActionHom_inv_of_pos hr q :
      SE2CarrierOrbitCarrier q → se2CarrierTranslationQuotient) := by
  exact (se2CarrierTranslationQuotientOrbitHomeomorph_of_pos hr q).symm.continuous

theorem se2CarrierTranslationQuotientOrbitActionHom_inv_left_of_pos
    {r : ℝ} (hr : 0 < r) (q : CasimirFiberCarrier r)
    (a : se2CarrierTranslationQuotient) :
    se2CarrierTranslationQuotientOrbitActionHom_inv_of_pos hr q
        (se2CarrierTranslationQuotientOrbitActionHom_of_pos hr q a) = a := by
  exact (se2CarrierTranslationQuotientOrbitHomeomorph_of_pos hr q).symm_apply_apply a

theorem se2CarrierTranslationQuotientOrbitActionHom_inv_right_of_pos
    {r : ℝ} (hr : 0 < r) (q : CasimirFiberCarrier r)
    (w : SE2CarrierOrbitCarrier q) :
    se2CarrierTranslationQuotientOrbitActionHom_of_pos hr q
        (se2CarrierTranslationQuotientOrbitActionHom_inv_of_pos hr q w) = w := by
  exact (se2CarrierTranslationQuotientOrbitHomeomorph_of_pos hr q).apply_symm_apply w

noncomputable def se2CarrierTranslationQuotientOrbitEquivariantTopologicalEquiv_of_pos
    {r : ℝ} (hr : 0 < r) (q : CasimirFiberCarrier r) :
    EquivariantTopologicalEquiv se2CarrierTranslationQuotient
      se2CarrierTranslationQuotient (SE2CarrierOrbitCarrier q) where
  homeomorph := se2CarrierTranslationQuotientOrbitHomeomorph_of_pos hr q
  forward := se2CarrierTranslationQuotientOrbitActionHom_of_pos hr q
  backward := se2CarrierTranslationQuotientOrbitActionHom_inv_of_pos hr q
  forward_coe := rfl
  backward_coe := rfl

noncomputable def se2CarrierOrbitLeafHomeomorph_of_pos
    {r : ℝ} (hr : 0 < r) (q w : CasimirFiberCarrier r) :
    SE2CarrierOrbitCarrier q ≃ₜ SE2CarrierOrbitCarrier w :=
  (se2CarrierTranslationQuotientOrbitHomeomorph_of_pos hr q).symm.trans
    (se2CarrierTranslationQuotientOrbitHomeomorph_of_pos hr w)

noncomputable def se2CarrierOrbitLeafActionHom_of_pos
    {r : ℝ} (hr : 0 < r) (q w : CasimirFiberCarrier r) :
    SE2CarrierOrbitCarrier q →[se2CarrierTranslationQuotient]
      SE2CarrierOrbitCarrier w where
  toFun := se2CarrierOrbitLeafHomeomorph_of_pos hr q w
  map_smul' := by
    intro a x
    let Hq := se2CarrierTranslationQuotientOrbitHomeomorph_of_pos hr q
    let Hw := se2CarrierTranslationQuotientOrbitHomeomorph_of_pos hr w
    let L := se2CarrierOrbitLeafHomeomorph_of_pos hr q w
    change L (a • x) = a • L x
    apply Hw.symm.injective
    change Hw.symm (L (a • x)) = Hw.symm (a • L x)
    calc
      Hw.symm (L (a • x)) = Hq.symm (a • x) := by
        change Hw.symm (Hw (Hq.symm (a • x))) = Hq.symm (a • x)
        rw [Hw.symm_apply_apply]
      _ = a * Hq.symm x := by
        apply Hq.injective
        calc
          Hq (Hq.symm (a • x)) = a • x := Hq.apply_symm_apply _
          _ = a • Hq (Hq.symm x) := by rw [Hq.apply_symm_apply]
          _ = Hq (a * Hq.symm x) :=
            (se2CarrierTranslationQuotientOrbitHomeomorph_equivariant hr q a
              (Hq.symm x)).symm
      _ = a * Hw.symm (L x) := by
        change a * Hq.symm x = a * Hw.symm (Hw (Hq.symm x))
        rw [Hw.symm_apply_apply]
      _ = Hw.symm (a • L x) := by
        rw [← Hw.apply_symm_apply (L x)]
        rw [← se2CarrierTranslationQuotientOrbitHomeomorph_equivariant hr w a
          (Hw.symm (L x))]
        rw [Hw.symm_apply_apply]
        change a * Hw.symm (L x) = Hw.symm (Hw (a * Hw.symm (L x)))
        rw [Hw.symm_apply_apply]

noncomputable def se2CarrierOrbitLeafActionHom_inv_of_pos
    {r : ℝ} (hr : 0 < r) (q w : CasimirFiberCarrier r) :
    SE2CarrierOrbitCarrier w →[se2CarrierTranslationQuotient]
      SE2CarrierOrbitCarrier q :=
  se2CarrierOrbitLeafActionHom_of_pos hr w q

noncomputable def se2CarrierOrbitLeafEquivariantTopologicalEquiv_of_pos
    {r : ℝ} (hr : 0 < r) (q w : CasimirFiberCarrier r) :
    EquivariantTopologicalEquiv se2CarrierTranslationQuotient
      (SE2CarrierOrbitCarrier q) (SE2CarrierOrbitCarrier w) where
  homeomorph := se2CarrierOrbitLeafHomeomorph_of_pos hr q w
  forward := se2CarrierOrbitLeafActionHom_of_pos hr q w
  backward := se2CarrierOrbitLeafActionHom_inv_of_pos hr q w
  forward_coe := rfl
  backward_coe := rfl

theorem se2CarrierOrbitLeafActionHom_inv_left_of_pos
    {r : ℝ} (hr : 0 < r) (q w : CasimirFiberCarrier r)
    (x : SE2CarrierOrbitCarrier q) :
    se2CarrierOrbitLeafActionHom_inv_of_pos hr q w
        (se2CarrierOrbitLeafActionHom_of_pos hr q w x) = x := by
  exact (se2CarrierOrbitLeafHomeomorph_of_pos hr q w).symm_apply_apply x

theorem se2CarrierOrbitLeafActionHom_inv_right_of_pos
    {r : ℝ} (hr : 0 < r) (q w : CasimirFiberCarrier r)
    (y : SE2CarrierOrbitCarrier w) :
    se2CarrierOrbitLeafActionHom_of_pos hr q w
        (se2CarrierOrbitLeafActionHom_inv_of_pos hr q w y) = y := by
  exact (se2CarrierOrbitLeafHomeomorph_of_pos hr q w).apply_symm_apply y

theorem continuous_se2CarrierOrbitLeafActionHom_of_pos
    {r : ℝ} (hr : 0 < r) (q w : CasimirFiberCarrier r) :
    Continuous (se2CarrierOrbitLeafActionHom_of_pos hr q w :
      SE2CarrierOrbitCarrier q → SE2CarrierOrbitCarrier w) := by
  exact (se2CarrierOrbitLeafHomeomorph_of_pos hr q w).continuous

theorem continuous_se2CarrierOrbitLeafActionHom_inv_of_pos
    {r : ℝ} (hr : 0 < r) (q w : CasimirFiberCarrier r) :
    Continuous (se2CarrierOrbitLeafActionHom_inv_of_pos hr q w :
      SE2CarrierOrbitCarrier w → SE2CarrierOrbitCarrier q) := by
  exact (se2CarrierOrbitLeafHomeomorph_of_pos hr q w).symm.continuous

theorem isEmbedding_se2CarrierOrbitLeafActionHom_of_pos
    {r : ℝ} (hr : 0 < r) (q w : CasimirFiberCarrier r) :
    Topology.IsEmbedding (se2CarrierOrbitLeafActionHom_of_pos hr q w :
      SE2CarrierOrbitCarrier q → SE2CarrierOrbitCarrier w) := by
  exact (se2CarrierOrbitLeafHomeomorph_of_pos hr q w).isEmbedding

theorem isClosedEmbedding_se2CarrierOrbitLeafActionHom_of_pos
    {r : ℝ} (hr : 0 < r) (q w : CasimirFiberCarrier r) :
    Topology.IsClosedEmbedding (se2CarrierOrbitLeafActionHom_of_pos hr q w :
      SE2CarrierOrbitCarrier q → SE2CarrierOrbitCarrier w) := by
  exact (se2CarrierOrbitLeafHomeomorph_of_pos hr q w).isClosedEmbedding

theorem isEmbedding_se2CarrierOrbitLeafActionHom_inv_of_pos
    {r : ℝ} (hr : 0 < r) (q w : CasimirFiberCarrier r) :
    Topology.IsEmbedding (se2CarrierOrbitLeafActionHom_inv_of_pos hr q w :
      SE2CarrierOrbitCarrier w → SE2CarrierOrbitCarrier q) := by
  exact (se2CarrierOrbitLeafHomeomorph_of_pos hr q w).symm.isEmbedding

theorem isClosedEmbedding_se2CarrierOrbitLeafActionHom_inv_of_pos
    {r : ℝ} (hr : 0 < r) (q w : CasimirFiberCarrier r) :
    Topology.IsClosedEmbedding (se2CarrierOrbitLeafActionHom_inv_of_pos hr q w :
      SE2CarrierOrbitCarrier w → SE2CarrierOrbitCarrier q) := by
  exact (se2CarrierOrbitLeafHomeomorph_of_pos hr q w).symm.isClosedEmbedding

theorem isOpenMap_se2CarrierOrbitLeafActionHom_of_pos
    {r : ℝ} (hr : 0 < r) (q w : CasimirFiberCarrier r) :
    IsOpenMap (se2CarrierOrbitLeafActionHom_of_pos hr q w :
      SE2CarrierOrbitCarrier q → SE2CarrierOrbitCarrier w) := by
  exact (se2CarrierOrbitLeafHomeomorph_of_pos hr q w).isOpenMap

theorem isClosedMap_se2CarrierOrbitLeafActionHom_of_pos
    {r : ℝ} (hr : 0 < r) (q w : CasimirFiberCarrier r) :
    IsClosedMap (se2CarrierOrbitLeafActionHom_of_pos hr q w :
      SE2CarrierOrbitCarrier q → SE2CarrierOrbitCarrier w) := by
  exact (se2CarrierOrbitLeafHomeomorph_of_pos hr q w).isClosedMap

theorem isQuotientMap_se2CarrierOrbitLeafActionHom_of_pos
    {r : ℝ} (hr : 0 < r) (q w : CasimirFiberCarrier r) :
    Topology.IsQuotientMap (se2CarrierOrbitLeafActionHom_of_pos hr q w :
      SE2CarrierOrbitCarrier q → SE2CarrierOrbitCarrier w) := by
  exact (se2CarrierOrbitLeafHomeomorph_of_pos hr q w).isQuotientMap

theorem isProperMap_se2CarrierOrbitLeafActionHom_of_pos
    {r : ℝ} (hr : 0 < r) (q w : CasimirFiberCarrier r) :
    IsProperMap (se2CarrierOrbitLeafActionHom_of_pos hr q w :
      SE2CarrierOrbitCarrier q → SE2CarrierOrbitCarrier w) := by
  exact (se2CarrierOrbitLeafHomeomorph_of_pos hr q w).isProperMap

theorem isOpenMap_se2CarrierOrbitLeafActionHom_inv_of_pos
    {r : ℝ} (hr : 0 < r) (q w : CasimirFiberCarrier r) :
    IsOpenMap (se2CarrierOrbitLeafActionHom_inv_of_pos hr q w :
      SE2CarrierOrbitCarrier w → SE2CarrierOrbitCarrier q) := by
  exact (se2CarrierOrbitLeafHomeomorph_of_pos hr q w).symm.isOpenMap

theorem isClosedMap_se2CarrierOrbitLeafActionHom_inv_of_pos
    {r : ℝ} (hr : 0 < r) (q w : CasimirFiberCarrier r) :
    IsClosedMap (se2CarrierOrbitLeafActionHom_inv_of_pos hr q w :
      SE2CarrierOrbitCarrier w → SE2CarrierOrbitCarrier q) := by
  exact (se2CarrierOrbitLeafHomeomorph_of_pos hr q w).symm.isClosedMap

theorem isQuotientMap_se2CarrierOrbitLeafActionHom_inv_of_pos
    {r : ℝ} (hr : 0 < r) (q w : CasimirFiberCarrier r) :
    Topology.IsQuotientMap (se2CarrierOrbitLeafActionHom_inv_of_pos hr q w :
      SE2CarrierOrbitCarrier w → SE2CarrierOrbitCarrier q) := by
  exact (se2CarrierOrbitLeafHomeomorph_of_pos hr q w).symm.isQuotientMap

theorem isProperMap_se2CarrierOrbitLeafActionHom_inv_of_pos
    {r : ℝ} (hr : 0 < r) (q w : CasimirFiberCarrier r) :
    IsProperMap (se2CarrierOrbitLeafActionHom_inv_of_pos hr q w :
      SE2CarrierOrbitCarrier w → SE2CarrierOrbitCarrier q) := by
  exact (se2CarrierOrbitLeafHomeomorph_of_pos hr q w).symm.isProperMap

theorem se2CarrierOrbitLeafEquivariantTopologicalEquiv_self_apply
    {r : ℝ} (hr : 0 < r) (q : CasimirFiberCarrier r)
    (x : SE2CarrierOrbitCarrier q) :
    (se2CarrierOrbitLeafEquivariantTopologicalEquiv_of_pos hr q q).forward x = x := by
  change (se2CarrierOrbitLeafHomeomorph_of_pos hr q q) x = x
  change (se2CarrierTranslationQuotientOrbitHomeomorph_of_pos hr q)
      ((se2CarrierTranslationQuotientOrbitHomeomorph_of_pos hr q).symm x) = x
  exact (se2CarrierTranslationQuotientOrbitHomeomorph_of_pos hr q).apply_symm_apply x

theorem se2CarrierOrbitLeafEquivariantTopologicalEquiv_trans_apply
    {r : ℝ} (hr : 0 < r)
    (q w u : CasimirFiberCarrier r) (x : SE2CarrierOrbitCarrier q) :
    (EquivariantTopologicalEquiv.trans
      (se2CarrierOrbitLeafEquivariantTopologicalEquiv_of_pos hr q w)
      (se2CarrierOrbitLeafEquivariantTopologicalEquiv_of_pos hr w u)).forward x =
      (se2CarrierOrbitLeafEquivariantTopologicalEquiv_of_pos hr q u).forward x := by
  change
    (se2CarrierTranslationQuotientOrbitHomeomorph_of_pos hr u)
        ((se2CarrierTranslationQuotientOrbitHomeomorph_of_pos hr w).symm
          ((se2CarrierTranslationQuotientOrbitHomeomorph_of_pos hr w)
            ((se2CarrierTranslationQuotientOrbitHomeomorph_of_pos hr q).symm x))) =
      (se2CarrierTranslationQuotientOrbitHomeomorph_of_pos hr u)
        ((se2CarrierTranslationQuotientOrbitHomeomorph_of_pos hr q).symm x)
  rw [(se2CarrierTranslationQuotientOrbitHomeomorph_of_pos hr w).symm_apply_apply]

theorem se2CarrierOrbitLeafEquivariantTopologicalEquiv_trans_backward_apply
    {r : ℝ} (hr : 0 < r)
    (q w u : CasimirFiberCarrier r) (x : SE2CarrierOrbitCarrier u) :
    (EquivariantTopologicalEquiv.trans
      (se2CarrierOrbitLeafEquivariantTopologicalEquiv_of_pos hr q w)
      (se2CarrierOrbitLeafEquivariantTopologicalEquiv_of_pos hr w u)).backward x =
      (se2CarrierOrbitLeafEquivariantTopologicalEquiv_of_pos hr q u).backward x := by
  change
    (se2CarrierTranslationQuotientOrbitHomeomorph_of_pos hr q)
        ((se2CarrierTranslationQuotientOrbitHomeomorph_of_pos hr w).symm
          ((se2CarrierTranslationQuotientOrbitHomeomorph_of_pos hr w)
            ((se2CarrierTranslationQuotientOrbitHomeomorph_of_pos hr u).symm x))) =
      (se2CarrierTranslationQuotientOrbitHomeomorph_of_pos hr q)
        ((se2CarrierTranslationQuotientOrbitHomeomorph_of_pos hr u).symm x)
  rw [(se2CarrierTranslationQuotientOrbitHomeomorph_of_pos hr w).symm_apply_apply]

theorem se2CarrierOrbitLeafEquivariantTopologicalEquiv_trans_eq
    {r : ℝ} (hr : 0 < r)
    (q w u : CasimirFiberCarrier r) :
    EquivariantTopologicalEquiv.trans
        (se2CarrierOrbitLeafEquivariantTopologicalEquiv_of_pos hr q w)
        (se2CarrierOrbitLeafEquivariantTopologicalEquiv_of_pos hr w u) =
      se2CarrierOrbitLeafEquivariantTopologicalEquiv_of_pos hr q u := by
  apply EquivariantTopologicalEquiv.ext
  · apply Homeomorph.ext
    intro x
    change (EquivariantTopologicalEquiv.trans
        (se2CarrierOrbitLeafEquivariantTopologicalEquiv_of_pos hr q w)
        (se2CarrierOrbitLeafEquivariantTopologicalEquiv_of_pos hr w u)).forward x =
      (se2CarrierOrbitLeafEquivariantTopologicalEquiv_of_pos hr q u).forward x
    exact se2CarrierOrbitLeafEquivariantTopologicalEquiv_trans_apply hr q w u x
  · apply MulActionHom.ext
    intro x
    exact se2CarrierOrbitLeafEquivariantTopologicalEquiv_trans_apply hr q w u x
  · apply MulActionHom.ext
    intro x
    exact se2CarrierOrbitLeafEquivariantTopologicalEquiv_trans_backward_apply hr q w u x

theorem se2CarrierOrbitLeafEquivariantTopologicalEquiv_symm_trans_eq_refl
    {r : ℝ} (hr : 0 < r) (q w : CasimirFiberCarrier r) :
    EquivariantTopologicalEquiv.trans
        (EquivariantTopologicalEquiv.symm
          (se2CarrierOrbitLeafEquivariantTopologicalEquiv_of_pos hr q w))
        (se2CarrierOrbitLeafEquivariantTopologicalEquiv_of_pos hr q w) =
      EquivariantTopologicalEquiv.refl se2CarrierTranslationQuotient
        (SE2CarrierOrbitCarrier w) := by
  exact EquivariantTopologicalEquiv.symm_trans_eq_refl _

theorem se2CarrierOrbitLeafEquivariantTopologicalEquiv_trans_symm_eq_refl
    {r : ℝ} (hr : 0 < r) (q w : CasimirFiberCarrier r) :
    EquivariantTopologicalEquiv.trans
        (se2CarrierOrbitLeafEquivariantTopologicalEquiv_of_pos hr q w)
        (EquivariantTopologicalEquiv.symm
          (se2CarrierOrbitLeafEquivariantTopologicalEquiv_of_pos hr q w)) =
      EquivariantTopologicalEquiv.refl se2CarrierTranslationQuotient
        (SE2CarrierOrbitCarrier q) := by
  exact EquivariantTopologicalEquiv.trans_symm_eq_refl _

theorem se2CarrierOrbitLeafEquivariantTopologicalEquiv_assoc_forward_apply
    {r : ℝ} (hr : 0 < r)
    (q w u v : CasimirFiberCarrier r) (x : SE2CarrierOrbitCarrier q) :
    (EquivariantTopologicalEquiv.trans
      (EquivariantTopologicalEquiv.trans
        (se2CarrierOrbitLeafEquivariantTopologicalEquiv_of_pos hr q w)
        (se2CarrierOrbitLeafEquivariantTopologicalEquiv_of_pos hr w u))
      (se2CarrierOrbitLeafEquivariantTopologicalEquiv_of_pos hr u v)).forward x =
      (EquivariantTopologicalEquiv.trans
        (se2CarrierOrbitLeafEquivariantTopologicalEquiv_of_pos hr q w)
        (EquivariantTopologicalEquiv.trans
          (se2CarrierOrbitLeafEquivariantTopologicalEquiv_of_pos hr w u)
          (se2CarrierOrbitLeafEquivariantTopologicalEquiv_of_pos hr u v))).forward x := by
  exact EquivariantTopologicalEquiv.trans_assoc_forward_apply _ _ _ _

theorem se2CarrierOrbitLeafEquivariantTopologicalEquiv_assoc_backward_apply
    {r : ℝ} (hr : 0 < r)
    (q w u v : CasimirFiberCarrier r) (x : SE2CarrierOrbitCarrier v) :
    (EquivariantTopologicalEquiv.trans
      (EquivariantTopologicalEquiv.trans
        (se2CarrierOrbitLeafEquivariantTopologicalEquiv_of_pos hr q w)
        (se2CarrierOrbitLeafEquivariantTopologicalEquiv_of_pos hr w u))
      (se2CarrierOrbitLeafEquivariantTopologicalEquiv_of_pos hr u v)).backward x =
      (EquivariantTopologicalEquiv.trans
        (se2CarrierOrbitLeafEquivariantTopologicalEquiv_of_pos hr q w)
        (EquivariantTopologicalEquiv.trans
          (se2CarrierOrbitLeafEquivariantTopologicalEquiv_of_pos hr w u)
          (se2CarrierOrbitLeafEquivariantTopologicalEquiv_of_pos hr u v))).backward x := by
  exact EquivariantTopologicalEquiv.trans_assoc_backward_apply _ _ _ _

theorem se2CarrierTranslationQuotientOrbitEquivariantTopologicalEquiv_trans_refl_left
    {r : ℝ} (hr : 0 < r) (q : CasimirFiberCarrier r)
    (a : se2CarrierTranslationQuotient) :
    (EquivariantTopologicalEquiv.trans
      (EquivariantTopologicalEquiv.refl
        se2CarrierTranslationQuotient se2CarrierTranslationQuotient)
      (se2CarrierTranslationQuotientOrbitEquivariantTopologicalEquiv_of_pos hr q)).forward a =
      (se2CarrierTranslationQuotientOrbitEquivariantTopologicalEquiv_of_pos hr q).forward a := by
  simp [EquivariantTopologicalEquiv.trans_forward_apply]

theorem se2CarrierTranslationQuotientOrbitEquivariantTopologicalEquiv_trans_refl_right
    {r : ℝ} (hr : 0 < r) (q : CasimirFiberCarrier r)
    (a : se2CarrierTranslationQuotient) :
    (EquivariantTopologicalEquiv.trans
      (se2CarrierTranslationQuotientOrbitEquivariantTopologicalEquiv_of_pos hr q)
      (EquivariantTopologicalEquiv.refl
        se2CarrierTranslationQuotient (SE2CarrierOrbitCarrier q))).forward a =
      (se2CarrierTranslationQuotientOrbitEquivariantTopologicalEquiv_of_pos hr q).forward a := by
  simp [EquivariantTopologicalEquiv.trans_forward_apply]

theorem se2CarrierTranslationQuotientOrbitEquivariantTopologicalEquiv_symm_trans
    {r : ℝ} (hr : 0 < r) (q : CasimirFiberCarrier r)
    (w : SE2CarrierOrbitCarrier q) :
    (EquivariantTopologicalEquiv.trans
      (EquivariantTopologicalEquiv.symm
        (se2CarrierTranslationQuotientOrbitEquivariantTopologicalEquiv_of_pos hr q))
      (se2CarrierTranslationQuotientOrbitEquivariantTopologicalEquiv_of_pos hr q)).forward w = w := by
  simpa [EquivariantTopologicalEquiv.trans_forward_apply,
    EquivariantTopologicalEquiv.symm_forward_apply] using
    se2CarrierTranslationQuotientOrbitActionHom_inv_right_of_pos hr q w

theorem se2CarrierTranslationQuotientOrbitEquivariantTopologicalEquiv_trans_symm
    {r : ℝ} (hr : 0 < r) (q : CasimirFiberCarrier r)
    (a : se2CarrierTranslationQuotient) :
    (EquivariantTopologicalEquiv.trans
      (se2CarrierTranslationQuotientOrbitEquivariantTopologicalEquiv_of_pos hr q)
      (EquivariantTopologicalEquiv.symm
        (se2CarrierTranslationQuotientOrbitEquivariantTopologicalEquiv_of_pos hr q))).forward a = a := by
  simpa [EquivariantTopologicalEquiv.trans_forward_apply,
    EquivariantTopologicalEquiv.symm_forward_apply] using
    se2CarrierTranslationQuotientOrbitActionHom_inv_left_of_pos hr q a

theorem se2CarrierTranslationQuotientOrbitEquivariantTopologicalEquiv_symm_trans_eq_refl
    {r : ℝ} (hr : 0 < r) (q : CasimirFiberCarrier r) :
    EquivariantTopologicalEquiv.trans
        (EquivariantTopologicalEquiv.symm
          (se2CarrierTranslationQuotientOrbitEquivariantTopologicalEquiv_of_pos hr q))
        (se2CarrierTranslationQuotientOrbitEquivariantTopologicalEquiv_of_pos hr q) =
      EquivariantTopologicalEquiv.refl se2CarrierTranslationQuotient
        (SE2CarrierOrbitCarrier q) := by
  exact EquivariantTopologicalEquiv.symm_trans_eq_refl _

theorem se2CarrierTranslationQuotientOrbitEquivariantTopologicalEquiv_trans_symm_eq_refl
    {r : ℝ} (hr : 0 < r) (q : CasimirFiberCarrier r) :
    EquivariantTopologicalEquiv.trans
        (se2CarrierTranslationQuotientOrbitEquivariantTopologicalEquiv_of_pos hr q)
        (EquivariantTopologicalEquiv.symm
          (se2CarrierTranslationQuotientOrbitEquivariantTopologicalEquiv_of_pos hr q)) =
      EquivariantTopologicalEquiv.refl se2CarrierTranslationQuotient
        se2CarrierTranslationQuotient := by
  exact EquivariantTopologicalEquiv.trans_symm_eq_refl _

theorem continuous_se2CarrierTranslationQuotientOrbitActionHom_of_pos
    {r : ℝ} (hr : 0 < r) (q : CasimirFiberCarrier r) :
    Continuous (se2CarrierTranslationQuotientOrbitActionHom_of_pos hr q :
      se2CarrierTranslationQuotient → SE2CarrierOrbitCarrier q) := by
  exact (se2CarrierTranslationQuotientOrbitHomeomorph_of_pos hr q).continuous

theorem isEmbedding_se2CarrierTranslationQuotientOrbitActionHom_of_pos
    {r : ℝ} (hr : 0 < r) (q : CasimirFiberCarrier r) :
    Topology.IsEmbedding (se2CarrierTranslationQuotientOrbitActionHom_of_pos hr q :
      se2CarrierTranslationQuotient → SE2CarrierOrbitCarrier q) := by
  exact (se2CarrierTranslationQuotientOrbitHomeomorph_of_pos hr q).isEmbedding

theorem isClosedEmbedding_se2CarrierTranslationQuotientOrbitActionHom_of_pos
    {r : ℝ} (hr : 0 < r) (q : CasimirFiberCarrier r) :
    Topology.IsClosedEmbedding (se2CarrierTranslationQuotientOrbitActionHom_of_pos hr q :
      se2CarrierTranslationQuotient → SE2CarrierOrbitCarrier q) := by
  exact (se2CarrierTranslationQuotientOrbitHomeomorph_of_pos hr q).isClosedEmbedding

theorem isOpenMap_se2CarrierTranslationQuotientOrbitActionHom_of_pos
    {r : ℝ} (hr : 0 < r) (q : CasimirFiberCarrier r) :
    IsOpenMap (se2CarrierTranslationQuotientOrbitActionHom_of_pos hr q :
      se2CarrierTranslationQuotient → SE2CarrierOrbitCarrier q) := by
  exact (se2CarrierTranslationQuotientOrbitHomeomorph_of_pos hr q).isOpenMap

theorem isClosedMap_se2CarrierTranslationQuotientOrbitActionHom_of_pos
    {r : ℝ} (hr : 0 < r) (q : CasimirFiberCarrier r) :
    IsClosedMap (se2CarrierTranslationQuotientOrbitActionHom_of_pos hr q :
      se2CarrierTranslationQuotient → SE2CarrierOrbitCarrier q) := by
  exact (se2CarrierTranslationQuotientOrbitHomeomorph_of_pos hr q).isClosedMap

theorem isQuotientMap_se2CarrierTranslationQuotientOrbitActionHom_of_pos
    {r : ℝ} (hr : 0 < r) (q : CasimirFiberCarrier r) :
    Topology.IsQuotientMap (se2CarrierTranslationQuotientOrbitActionHom_of_pos hr q :
      se2CarrierTranslationQuotient → SE2CarrierOrbitCarrier q) := by
  exact (se2CarrierTranslationQuotientOrbitHomeomorph_of_pos hr q).isQuotientMap

theorem isProperMap_se2CarrierTranslationQuotientOrbitActionHom_of_pos
    {r : ℝ} (hr : 0 < r) (q : CasimirFiberCarrier r) :
    IsProperMap (se2CarrierTranslationQuotientOrbitActionHom_of_pos hr q :
      se2CarrierTranslationQuotient → SE2CarrierOrbitCarrier q) := by
  exact (se2CarrierTranslationQuotientOrbitHomeomorph_of_pos hr q).isProperMap

instance se2CarrierTranslationQuotientOrbitContinuousSMul
    {r : ℝ} (q : CasimirFiberCarrier r) :
    ContinuousSMul se2CarrierTranslationQuotient (SE2CarrierOrbitCarrier q) where
  continuous_smul := continuous_se2CarrierTranslationQuotientOrbitAction q

theorem se2CarrierOrbitCarrierMap_eq_iff_projection_eq_of_pos
    {r : ℝ} (hr : 0 < r) (q : CasimirFiberCarrier r)
    (g h : MatrixSE2Carrier) :
    se2CarrierOrbitCarrierMap q g = se2CarrierOrbitCarrierMap q h ↔
      se2CarrierRotationProjection g = se2CarrierRotationProjection h := by
  constructor
  · intro hmap
    apply injective_se2CarrierOrbitQuotientMap_of_pos hr q
    simpa only [se2CarrierOrbitCarrierMap_eq_comp_projection,
      Function.comp_apply] using hmap
  · intro hproj
    simpa only [se2CarrierOrbitCarrierMap_eq_comp_projection,
      Function.comp_apply] using
      congrArg (se2CarrierOrbitQuotientMap q) hproj

theorem continuous_se2CarrierOrbitCarrierMap
    {r : ℝ} (q : CasimirFiberCarrier r) :
    Continuous (se2CarrierOrbitCarrierMap q) := by
  apply Continuous.subtype_mk
  exact continuous_se2CarrierOrbitMap q

theorem isOpenMap_se2CarrierOrbitCarrierMap_of_pos
    {r : ℝ} (hr : 0 < r) (q : CasimirFiberCarrier r) :
    IsOpenMap (se2CarrierOrbitCarrierMap q) := by
  rw [se2CarrierOrbitCarrierMap_eq_comp_projection q]
  exact (isOpenMap_se2CarrierOrbitQuotientMap_of_pos hr q).comp
    isOpenMap_se2CarrierRotationProjection

theorem se2CarrierOrbitCarrierMap_surjective
    {r : ℝ} (q : CasimirFiberCarrier r) :
    Function.Surjective (se2CarrierOrbitCarrierMap q) := by
  intro w
  rcases w.2 with ⟨g, hg⟩
  refine ⟨g, ?_⟩
  apply Subtype.ext
  exact hg

theorem isQuotientMap_se2CarrierOrbitCarrierMap_of_pos
    {r : ℝ} (hr : 0 < r) (q : CasimirFiberCarrier r) :
    Topology.IsQuotientMap (se2CarrierOrbitCarrierMap q) := by
  exact (isOpenMap_se2CarrierOrbitCarrierMap_of_pos hr q).isQuotientMap
    (continuous_se2CarrierOrbitCarrierMap q)
    (se2CarrierOrbitCarrierMap_surjective q)

theorem isOpenQuotientMap_se2CarrierOrbitCarrierMap_all
    {r : ℝ} (q : CasimirFiberCarrier r) :
    IsOpenQuotientMap (se2CarrierOrbitCarrierMap q) := by
  rw [se2CarrierOrbitCarrierMap_eq_comp_projection q]
  exact (isOpenQuotientMap_se2CarrierOrbitQuotientMap_all q).comp
    isOpenQuotientMap_se2CarrierRotationProjection

instance pathConnectedSpace_se2CarrierOrbitCarrier
    {r : ℝ} (q : CasimirFiberCarrier r) :
    PathConnectedSpace (SE2CarrierOrbitCarrier q) := by
  exact (se2CarrierOrbitCarrierMap_surjective q).pathConnectedSpace
    (continuous_se2CarrierOrbitCarrierMap q)

theorem isPathConnected_se2CarrierOrbit_univ
    {r : ℝ} (q : CasimirFiberCarrier r) :
    IsPathConnected (Set.univ : Set (SE2CarrierOrbitCarrier q)) := by
  letI := pathConnectedSpace_se2CarrierOrbitCarrier q
  exact isPathConnected_univ

theorem isConnected_se2CarrierOrbit_univ
    {r : ℝ} (q : CasimirFiberCarrier r) :
    IsConnected (Set.univ : Set (SE2CarrierOrbitCarrier q)) := by
  exact (isPathConnected_se2CarrierOrbit_univ q).isConnected

end SE2Vector
end SE2Souriau
