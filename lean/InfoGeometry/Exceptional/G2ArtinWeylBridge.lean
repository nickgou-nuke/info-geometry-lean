/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Exceptional.G2ArtinPresentation
import InfoGeometry.Algebra.Zorn.G2TwoConcreteWeylG2
import InfoGeometry.Algebra.Zorn.G2WeylDihedralEquiv
import InfoGeometry.Algebra.Zorn.G2RootSystemWeylBridge
import InfoGeometry.Algebra.Zorn.G2RootWeylNormalForm
import InfoGeometry.Exceptional.G2ConcreteCoordinateCalibration
import InfoGeometry.Exceptional.G2ArtinKleinBridge
import InfoGeometry.Algebra.Zorn.G2CoordinateCoxeterRelations
import InfoGeometry.Algebra.Zorn.G2CoordinateSemidirectBridge
import InfoGeometry.Algebra.Zorn.G2RootWeylAdjointCharacter
import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# G₂ Artin-to-Weyl quotient bridge

The native presentation owner already supplies the quotient action
`coordinateAction : ArtinG2 →* Equiv.Perm G2CoordinateRoot`.  This owner
exposes its longest-element readback without introducing a second Weyl
carrier or a duplicate presentation.
-/

namespace InfoGeometry.Exceptional.G2ArtinWeylBridge

open InfoGeometry.Exceptional.G2ArtinPresentation
open InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction
open InfoGeometry.Algebra.Zorn.G2CoordinateCoxeterRelations
open InfoGeometry.Algebra.Zorn.G2ReducedWords
open InfoGeometry.Algebra.Zorn.G2ConcreteWeyl
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2TwoRootSystem
open InfoGeometry.Algebra.Zorn.G2RootWeylNormalForm
open InfoGeometry.Algebra.Zorn.G2RootSystemWeylBridge
open InfoGeometry.Exceptional.G2ConcreteCoordinateCalibration
open InfoGeometry.Algebra.Zorn.G2RootWeylAdjointCharacter

noncomputable section

/-! The two root-to-coordinate equivalences are distinct label conventions.
    Their canonical comparison is the reindexing equivalence below. -/

noncomputable def rootCoordinateCalibration :
    G2CoordinateRoot ≃ G2CoordinateRoot :=
  (InfoGeometry.Algebra.Zorn.G2RootWeylAdjointCharacter.finiteRootCoordinateEquiv.symm).trans
    concreteRootCoordinateEquiv

theorem rootCoordinateCalibration_apply (r : G2Root) :
    rootCoordinateCalibration
        (InfoGeometry.Algebra.Zorn.G2RootWeylAdjointCharacter.finiteRootCoordinateEquiv r) =
      concreteRootCoordinateEquiv r := by
  change concreteRootCoordinateEquiv
      (InfoGeometry.Algebra.Zorn.G2RootWeylAdjointCharacter.finiteRootCoordinateEquiv.symm
        (InfoGeometry.Algebra.Zorn.G2RootWeylAdjointCharacter.finiteRootCoordinateEquiv r)) =
    concreteRootCoordinateEquiv r
  rw [InfoGeometry.Algebra.Zorn.G2RootWeylAdjointCharacter.finiteRootCoordinateEquiv.symm_apply_apply]

noncomputable def rootCyclotomicCalibration :
    InfoGeometry.Algebra.Zorn.G2CyclotomicWeyl.Root ≃ G2CoordinateRoot :=
  InfoGeometry.Algebra.Zorn.G2RootWeylAdjointCharacter.finiteRootCyclotomicEquiv.symm.trans
    concreteRootCoordinateEquiv

theorem rootCyclotomicCalibration_weylRootAction
    (p : InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification.WeylG2)
    (r : G2Root) :
    rootCyclotomicCalibration
        (InfoGeometry.Algebra.Zorn.G2RootWeylAdjointCharacter.finiteRootCyclotomicEquiv
          (InfoGeometry.Algebra.Zorn.G2RootSystemWeylBridge.weylRootAction p r)) =
      concreteRootCoordinateEquiv
        (InfoGeometry.Algebra.Zorn.G2RootSystemWeylBridge.weylRootAction p r) := by
  unfold rootCyclotomicCalibration
  change concreteRootCoordinateEquiv
      (InfoGeometry.Algebra.Zorn.G2RootWeylAdjointCharacter.finiteRootCyclotomicEquiv.symm
        (InfoGeometry.Algebra.Zorn.G2RootWeylAdjointCharacter.finiteRootCyclotomicEquiv
          (InfoGeometry.Algebra.Zorn.G2RootSystemWeylBridge.weylRootAction p r))) = _
  rw [InfoGeometry.Algebra.Zorn.G2RootWeylAdjointCharacter.finiteRootCyclotomicEquiv.symm_apply_apply]

noncomputable def concreteRootTransport :
    Equiv.Perm G2CoordinateRoot →* Equiv.Perm G2Root where
  toFun p := (concreteRootCoordinateEquiv.trans
    (p.trans concreteRootCoordinateEquiv.symm) : G2Root ≃ G2Root)
  map_one' := by
    apply Equiv.ext
    intro x
    simp
  map_mul' p q := by
    apply Equiv.ext
    intro x
    simp [Equiv.Perm.mul_def, Equiv.trans_assoc]

/-! Root permutations obtained by transporting the already calibrated
    coordinate reflections. -/

noncomputable def concreteRootS : Equiv.Perm G2Root :=
  concreteRootTransport s1Root

noncomputable def concreteRootT : Equiv.Perm G2Root :=
  concreteRootTransport s2Root

theorem concreteRootS_apply (r : G2Root) :
    concreteRootS r = sAction r := by
  apply concreteRootCoordinateEquiv.injective
  dsimp [concreteRootS, concreteRootTransport]
  rw [concreteRootCoordinateEquiv.apply_symm_apply]
  exact (concreteRootCoordinateEquiv_sAction r).symm

theorem concreteRootT_apply (r : G2Root) :
    concreteRootT r = sAction (cAction r) := by
  apply concreteRootCoordinateEquiv.injective
  dsimp [concreteRootT, concreteRootTransport]
  rw [concreteRootCoordinateEquiv.apply_symm_apply]
  exact (concreteRootCoordinateEquiv_sAction_cAction r).symm

/-! Transport the Artin root action back to the native finite `G₂` root
    carrier.  The transport is a homomorphism because it is conjugation by
    the already calibrated root equivalence. -/

noncomputable def concreteRootAction :
    G2ArtinPresentation.ArtinG2 →* Equiv.Perm G2Root :=
  concreteRootTransport.comp coordinateAction

theorem concreteRootAction_sigmaZero :
    concreteRootAction G2ArtinPresentation.sigmaZero = concreteRootS := by
  rw [concreteRootAction, MonoidHom.comp_apply,
    coordinateAction_sigmaZero]
  rfl

theorem concreteRootAction_sigmaOne :
    concreteRootAction G2ArtinPresentation.sigmaOne = concreteRootT := by
  rw [concreteRootAction, MonoidHom.comp_apply,
    coordinateAction_sigmaOne]
  rfl

theorem concreteRootAction_sigmaZero_apply (r : G2Root) :
    concreteRootAction G2ArtinPresentation.sigmaZero r = sAction r := by
  rw [concreteRootAction_sigmaZero]
  exact concreteRootS_apply r

theorem concreteRootAction_sigmaOne_apply (r : G2Root) :
    concreteRootAction G2ArtinPresentation.sigmaOne r =
      sAction (cAction r) := by
  rw [concreteRootAction_sigmaOne]
  exact concreteRootT_apply r

theorem weylRootAction_sr_zero_apply (r : G2Root) :
    InfoGeometry.Algebra.Zorn.G2RootSystemWeylBridge.weylRootAction
        (0, true) r = concreteRootAction G2ArtinPresentation.sigmaZero r := by
  simpa [InfoGeometry.Algebra.Zorn.G2RootSystemWeylBridge.weylRootAction,
    InfoGeometry.Algebra.Zorn.G2RootSystemWeylBridge.cActionPow,
    InfoGeometry.Algebra.Zorn.G2RootSystemWeylBridge.cActionPowNat] using
    (concreteRootAction_sigmaZero_apply r).symm

theorem weylRootAction_sr_one_apply (r : G2Root) :
    InfoGeometry.Algebra.Zorn.G2RootSystemWeylBridge.weylRootAction
        (1, true) r = concreteRootAction G2ArtinPresentation.sigmaOne r := by
  simpa [InfoGeometry.Algebra.Zorn.G2RootSystemWeylBridge.weylRootAction,
    InfoGeometry.Algebra.Zorn.G2RootSystemWeylBridge.cActionPow,
    InfoGeometry.Algebra.Zorn.G2RootSystemWeylBridge.cActionPowNat] using
    (concreteRootAction_sigmaOne_apply r).symm

/-! The transported root action has the expected coordinate readback for
    every Artin element.  This is the global compatibility statement for
    the calibrated root carrier; it is just the defining conjugation
    transport, not a finite enumeration of Artin words. -/

theorem concreteRootAction_coordinate_readback
    (w : G2ArtinPresentation.ArtinG2) (r : G2Root) :
    concreteRootCoordinateEquiv (concreteRootAction w r) =
      coordinateAction w (concreteRootCoordinateEquiv r) := by
  simp [concreteRootAction, concreteRootTransport]

/-- Public compatibility surface for the two Artin actions.  The concrete
automorphism carrier is observed on roots through concreteRootAction; the
calibration then agrees exactly with the coordinate permutation action. -/
theorem concreteAction_coordinateAction_compatible
    (w : G2ArtinPresentation.ArtinG2) (r : G2Root) :
    concreteRootCoordinateEquiv (concreteRootAction w r) =
      coordinateAction w (concreteRootCoordinateEquiv r) :=
  concreteRootAction_coordinate_readback w r

theorem concreteRootCoordinateEquiv_cAction (r : G2Root) :
    concreteRootCoordinateEquiv (cAction r) =
      s1Root (s2Root (concreteRootCoordinateEquiv r)) := by
  apply s1Root.injective
  calc
    s1Root (concreteRootCoordinateEquiv (cAction r)) =
        concreteRootCoordinateEquiv (sAction (cAction r)) := by
          simpa using (concreteRootCoordinateEquiv_sAction (cAction r)).symm
    _ = s2Root (concreteRootCoordinateEquiv r) :=
      concreteRootCoordinateEquiv_sAction_cAction r
    _ = s1Root (s1Root (s2Root (concreteRootCoordinateEquiv r))) :=
      (s1Root_involutive _).symm

theorem coordinate_s1_mul_s2_eq_cRoot_inv :
    s1Root * s2Root = cRoot⁻¹ := by
  have hs1 : s1Root.symm = s1Root := by
    apply Equiv.ext
    intro x
    apply s1Root.injective
    simp [s1Root_involutive]
  have hs2 : s2Root.symm = s2Root := by
    apply Equiv.ext
    intro x
    apply s2Root.injective
    simp [s2Root_involutive]
  apply Equiv.ext
  intro x
  simp [cRoot, Equiv.Perm.mul_def, hs1, hs2]

theorem concreteRootCoordinateEquiv_cActionPowNat (n : ℕ) (r : G2Root) :
    concreteRootCoordinateEquiv
        (InfoGeometry.Algebra.Zorn.G2RootSystemWeylBridge.cActionPowNat n r) =
      ((s1Root * s2Root) ^ n) (concreteRootCoordinateEquiv r) := by
  induction n with
  | zero => simp [InfoGeometry.Algebra.Zorn.G2RootSystemWeylBridge.cActionPowNat]
  | succ n ih =>
      simp only [InfoGeometry.Algebra.Zorn.G2RootSystemWeylBridge.cActionPowNat]
      rw [concreteRootCoordinateEquiv_cAction]
      rw [ih]
      rw [pow_succ']
      rfl

theorem concreteRootCoordinateEquiv_cActionPowNat_inv (n : ℕ) (r : G2Root) :
    concreteRootCoordinateEquiv
        (InfoGeometry.Algebra.Zorn.G2RootSystemWeylBridge.cActionPowNat n r) =
      ((cRoot⁻¹) ^ n) (concreteRootCoordinateEquiv r) := by
  rw [← coordinate_s1_mul_s2_eq_cRoot_inv]
  exact concreteRootCoordinateEquiv_cActionPowNat n r

theorem concreteRootCoordinateEquiv_weylRootAction_oriented
    (p : InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification.WeylG2)
    (r : G2Root) :
    concreteRootCoordinateEquiv
        (InfoGeometry.Algebra.Zorn.G2RootSystemWeylBridge.weylRootAction p r) =
      if p.2 then
        s1Root (((s1Root * s2Root) ^ p.1.val)
          (concreteRootCoordinateEquiv r))
      else
        ((s1Root * s2Root) ^ p.1.val)
          (concreteRootCoordinateEquiv r) := by
  by_cases hp : p.2
  · simp only [InfoGeometry.Algebra.Zorn.G2RootSystemWeylBridge.weylRootAction,
      hp, ↓reduceIte, InfoGeometry.Algebra.Zorn.G2RootSystemWeylBridge.cActionPow]
    rw [concreteRootCoordinateEquiv_sAction,
      concreteRootCoordinateEquiv_cActionPowNat]
  · simp only [InfoGeometry.Algebra.Zorn.G2RootSystemWeylBridge.weylRootAction,
      hp, Bool.false_eq_true, ↓reduceIte,
      InfoGeometry.Algebra.Zorn.G2RootSystemWeylBridge.cActionPow]
    rw [concreteRootCoordinateEquiv_cActionPowNat]

theorem rootWeylNF_orientation
    (p : InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification.WeylG2) :
    InfoGeometry.Algebra.Zorn.G2RootWeylNormalForm.rootWeylNF p =
      if p.2 then
        InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction.coordinateWeylAction
          (-p.1, true)
      else
        InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction.coordinateWeylAction
          (p.1, false) := by
  rcases p with ⟨k, b⟩
  cases b
  · rfl
  · exact InfoGeometry.Algebra.Zorn.G2RootWeylNormalForm.rootWeylNF_reflection_orientation k

theorem rootWeylNF_reflection_transport (k : ZMod 6) :
    s1Root.trans (cRoot ^ k.val) =
      s1Root * cRoot ^ (-k).val := by
  simpa [InfoGeometry.Algebra.Zorn.G2RootWeylNormalForm.rootWeylNF,
    InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction.coordinateWeylAction,
    InfoGeometry.Algebra.Zorn.G2RootWeylNormalForm.rootWeylNF_reflection_orientation] using
    (InfoGeometry.Algebra.Zorn.G2RootWeylNormalForm.rootWeylNF_reflection_orientation k)

theorem rootWeylNF_sector_calibration
    (p : InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification.WeylG2) :
    InfoGeometry.Algebra.Zorn.G2RootWeylNormalForm.rootWeylNF
        (if p.2 then p else (-p.1, false)) =
      InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction.coordinateWeylAction
        (-p.1, p.2) := by
  rcases p with ⟨k, b⟩
  cases b
  · rfl
  · exact InfoGeometry.Algebra.Zorn.G2RootWeylNormalForm.rootWeylNF_reflection_orientation k

def sectorAwareWeylParameter
    (p : InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification.WeylG2) :
    InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification.WeylG2 :=
  if p.2 then p else (-p.1, false)

theorem rootWeylNF_sectorAwareWeylParameter
    (p : InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification.WeylG2) :
    InfoGeometry.Algebra.Zorn.G2RootWeylNormalForm.rootWeylNF
        (sectorAwareWeylParameter p) =
      InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction.coordinateWeylAction
        (-p.1, p.2) := by
  exact rootWeylNF_sector_calibration p

/-! The concrete subgroup acts on the calibrated coordinate-root carrier by
    decoding its unique normal-form witness.  The subgroup remains the group
    owner; this is only its root-action readout. -/

noncomputable def concreteWeylCoordinateAction
    (x : InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.weylG2Subgroup) :
    Equiv.Perm G2CoordinateRoot :=
  rootWeylNF
    (InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.weylG2ParameterEquiv.symm x)

@[simp] theorem concreteWeylCoordinateAction_parameter
    (p : InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification.WeylG2) :
    concreteWeylCoordinateAction
        (InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.weylG2ParameterEquiv p) =
      rootWeylNF p := by
  simp [concreteWeylCoordinateAction]

theorem concreteWeylCoordinateAction_sigmaZero :
    concreteWeylCoordinateAction
        ⟨s, s_mem_weylG2Subgroup⟩ = s1Root := by
  have hp :
      InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.weylG2ParameterEquiv.symm
          ⟨s, s_mem_weylG2Subgroup⟩ = (0, true) := by
    apply InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.weylG2ParameterEquiv.injective
    apply Subtype.ext
    simp [InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.weylG2ParameterEquiv_apply,
      InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.weylNF]
  rw [concreteWeylCoordinateAction, hp]
  apply Equiv.ext
  intro x
  simp [rootWeylNF]

theorem concreteWeylCoordinateAction_sigmaOne :
    concreteWeylCoordinateAction
        ⟨t, t_mem_weylG2Subgroup⟩ = s2Root := by
  have hp :
      InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.weylG2ParameterEquiv.symm
          ⟨t, t_mem_weylG2Subgroup⟩ = (1, true) := by
    apply InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.weylG2ParameterEquiv.injective
    apply Subtype.ext
    have hval : ZMod.val (1 : ZMod 6) = 1 := by decide
    simp [InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.weylG2ParameterEquiv_apply,
      InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.weylNF, t, hval]
  rw [concreteWeylCoordinateAction, hp]
  apply Equiv.ext
  intro x
  change cRoot (s1Root x) = s2Root x
  change s2Root (s1Root (s1Root x)) = s2Root x
  rw [s1Root_involutive]

theorem artinToWeyl_garside :
    coordinateAction G2ArtinPresentation.garside =
      dihedralToPerm
        InfoGeometry.Algebra.Zorn.G2LongestElementBridge.g2LongestNF := by
  exact G2ArtinPresentation.garsideWord_is_longest_readback

theorem artinToWeyl_garside_sq :
    coordinateAction
        (G2ArtinPresentation.garside * G2ArtinPresentation.garside) = 1 := by
  rw [map_mul, artinToWeyl_garside]
  apply Equiv.ext
  intro x
  fin_cases x <;> rfl

/-! ## Coxeter quotient

The finite Weyl action is obtained only after imposing the two Coxeter
involution relations.  This map is therefore kept separate from the raw
Artin representation above.
-/

private def artinToCoxeterAssignment :
    G2ArtinPresentation.Generator → DihedralGroup 6
  | 0 => DihedralGroup.sr 0
  | 1 => DihedralGroup.sr 1

private theorem artinToCoxeterRelationRespected :
    ∀ r ∈ G2ArtinPresentation.relations,
      FreeGroup.lift artinToCoxeterAssignment r = 1 := by
  intro r hr
  have hr' : r = G2ArtinPresentation.relation := by
    simpa [G2ArtinPresentation.relations] using hr
  subst r
  simp only [G2ArtinPresentation.relation, map_mul, map_inv,
    FreeGroup.lift_apply_of, artinToCoxeterAssignment]
  simp [DihedralGroup.sr_mul_sr, DihedralGroup.r_mul_r,
    DihedralGroup.inv_r]
  convert (DihedralGroup.r_one_pow_n (n := 6)) using 1

noncomputable def artinToCoxeter :
    G2ArtinPresentation.ArtinG2 →* DihedralGroup 6 :=
  PresentedGroup.toGroup (f := artinToCoxeterAssignment)
    (rels := G2ArtinPresentation.relations) artinToCoxeterRelationRespected

@[simp] theorem artinToCoxeter_sigmaZero :
    artinToCoxeter G2ArtinPresentation.sigmaZero = DihedralGroup.sr 0 := by
  change PresentedGroup.toGroup (f := artinToCoxeterAssignment)
    (rels := G2ArtinPresentation.relations) artinToCoxeterRelationRespected
      (PresentedGroup.of 0) = _
  rw [PresentedGroup.toGroup.of]
  rfl

@[simp] theorem artinToCoxeter_sigmaOne :
    artinToCoxeter G2ArtinPresentation.sigmaOne = DihedralGroup.sr 1 := by
  change PresentedGroup.toGroup (f := artinToCoxeterAssignment)
    (rels := G2ArtinPresentation.relations) artinToCoxeterRelationRespected
      (PresentedGroup.of 1) = _
  rw [PresentedGroup.toGroup.of]
  rfl

theorem artinToCoxeter_surjective : Function.Surjective artinToCoxeter := by
  intro g
  cases g with
  | r k =>
      refine ⟨(G2ArtinPresentation.sigmaZero *
        G2ArtinPresentation.sigmaOne) ^ k.val, ?_⟩
      rw [map_pow, map_mul, artinToCoxeter_sigmaZero,
        artinToCoxeter_sigmaOne, DihedralGroup.sr_mul_sr,
        DihedralGroup.r_pow]
      simp
  | sr k =>
      refine ⟨G2ArtinPresentation.sigmaZero *
        (G2ArtinPresentation.sigmaZero *
          G2ArtinPresentation.sigmaOne) ^ k.val, ?_⟩
      rw [map_mul, artinToCoxeter_sigmaZero, map_pow, map_mul,
        artinToCoxeter_sigmaZero, artinToCoxeter_sigmaOne,
        DihedralGroup.sr_mul_sr, DihedralGroup.r_pow,
        DihedralGroup.sr_mul_r]
      simp

/-! The Artin generator swap descends to the Coxeter quotient.  In the native
    dihedral coordinates it reverses rotations and sends `sr k` to
    `sr (1 - k)`, matching the calibrated simple reflections. -/

def dihedralSwap : DihedralGroup 6 → DihedralGroup 6
  | .r k => .r (-k)
  | .sr k => .sr (1 - k)

noncomputable def dihedralSwapHom : DihedralGroup 6 →* DihedralGroup 6 where
  toFun := dihedralSwap
  map_one' := by rfl
  map_mul' := by
    intro a b
    cases a <;> cases b <;>
      simp only [dihedralSwap, DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr,
        DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr]
    all_goals (congr 1; ring)

@[simp] theorem dihedralSwapHom_r (k : ZMod 6) :
    dihedralSwapHom (.r k) = .r (-k) := rfl

@[simp] theorem dihedralSwapHom_sr (k : ZMod 6) :
    dihedralSwapHom (.sr k) = .sr (1 - k) := rfl

theorem dihedralSwapHom_involutive :
    dihedralSwapHom.comp dihedralSwapHom = MonoidHom.id (DihedralGroup 6) := by
  apply MonoidHom.ext
  intro x
  cases x <;> simp [dihedralSwapHom, dihedralSwap]

theorem artinToCoxeter_swap_compatibility
    (w : G2ArtinPresentation.ArtinG2) :
    artinToCoxeter (G2ArtinPresentation.artinGeneratorSwap w) =
      dihedralSwapHom (artinToCoxeter w) := by
  have h : artinToCoxeter.comp G2ArtinPresentation.artinGeneratorSwap =
      dihedralSwapHom.comp artinToCoxeter := by
    apply PresentedGroup.ext (rels := G2ArtinPresentation.relations)
    intro i
    fin_cases i
    · change artinToCoxeter G2ArtinPresentation.sigmaOne =
        dihedralSwapHom (artinToCoxeter G2ArtinPresentation.sigmaZero)
      rw [artinToCoxeter_sigmaOne, artinToCoxeter_sigmaZero]
      rfl
    · change artinToCoxeter G2ArtinPresentation.sigmaZero =
        dihedralSwapHom (artinToCoxeter G2ArtinPresentation.sigmaOne)
      rw [artinToCoxeter_sigmaZero, artinToCoxeter_sigmaOne]
      rfl
  exact DFunLike.congr_fun h w

theorem involutionKernel_le_artinToCoxeter_ker :
    G2ArtinPresentation.involutionKernel ≤ artinToCoxeter.ker := by
  apply Subgroup.normalClosure_le_normal
  intro x hx
  rcases hx with rfl | rfl
  · change artinToCoxeter (G2ArtinPresentation.sigmaZero ^ 2) = 1
    rw [map_pow, artinToCoxeter_sigmaZero]
    rw [pow_two, DihedralGroup.sr_mul_self]
  · change artinToCoxeter (G2ArtinPresentation.sigmaOne ^ 2) = 1
    rw [map_pow, artinToCoxeter_sigmaOne]
    rw [pow_two, DihedralGroup.sr_mul_self]

def quotientToDihedral : G2ArtinPresentation.WeylQuotient →* DihedralGroup 6 :=
  QuotientGroup.lift G2ArtinPresentation.involutionKernel artinToCoxeter
    involutionKernel_le_artinToCoxeter_ker

@[simp] theorem quotientToDihedral_mk (w : G2ArtinPresentation.ArtinG2) :
    quotientToDihedral (G2ArtinPresentation.artinQuotientMap w) =
      artinToCoxeter w := by
  exact QuotientGroup.lift_mk' _ _ _

/-! The concrete split-octonion Weyl representatives factor through the same
    Coxeter quotient.  This preserves the distinction between the infinite
    Artin carrier and the finite concrete Weyl subgroup. -/

noncomputable def quotientToConcreteWeyl :
    G2ArtinPresentation.WeylQuotient →*
      InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.weylG2Subgroup :=
  InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.dihedralWeylHom.comp
    quotientToDihedral

theorem quotientToDihedral_swap_compatibility (w : G2ArtinPresentation.WeylQuotient) :
    quotientToDihedral
        (G2ArtinPresentation.descendedArtinGeneratorSwap w) =
      dihedralSwapHom (quotientToDihedral w) := by
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective
    G2ArtinPresentation.involutionKernel w
  change quotientToDihedral
      (G2ArtinPresentation.descendedArtinGeneratorSwap
        (G2ArtinPresentation.artinQuotientMap w)) =
    dihedralSwapHom (quotientToDihedral
      (G2ArtinPresentation.artinQuotientMap w))
  rw [G2ArtinPresentation.descendedArtinGeneratorSwap_mk,
    quotientToDihedral_mk, quotientToDihedral_mk,
    artinToCoxeter_swap_compatibility]

/-! Public Weyl-level name for the Klein/throat descent.  This is a
    compatibility theorem for the descended quotient automorphism; it does
    not identify the throat involution with an element of the Weyl group. -/
theorem g2Weyl_kleinCompatibility
    (w : G2ArtinPresentation.WeylQuotient) :
    quotientToDihedral
        (G2ArtinPresentation.descendedArtinGeneratorSwap w) =
      dihedralSwapHom (quotientToDihedral w) :=
  quotientToDihedral_swap_compatibility w

/-! The Artin generator swap descends all the way to the concrete Weyl
    subgroup.  This is the carrier-level compatibility seam; it uses the
    quotient descent and the existing dihedral lift, without introducing a
    second concrete action or enumerating Weyl words. -/

theorem quotientToConcreteWeyl_swap_compatibility
    (w : G2ArtinPresentation.WeylQuotient) :
    quotientToConcreteWeyl
        (G2ArtinPresentation.descendedArtinGeneratorSwap w) =
      InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.dihedralWeylHom
        (dihedralSwapHom (quotientToDihedral w)) := by
  rw [quotientToConcreteWeyl, MonoidHom.comp_apply,
    quotientToDihedral_swap_compatibility]

/-! Concrete-subgroup presentation of the same descent.  The right-hand side
    remains the image of the descended dihedral swap, so this theorem keeps
    the outer throat symmetry distinct from an inner Weyl representative. -/
theorem g2Weyl_concrete_kleinCompatibility
    (w : G2ArtinPresentation.WeylQuotient) :
    quotientToConcreteWeyl
        (G2ArtinPresentation.descendedArtinGeneratorSwap w) =
      InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.dihedralWeylHom
        (dihedralSwapHom (quotientToDihedral w)) :=
  quotientToConcreteWeyl_swap_compatibility w

theorem involutionKernel_le_coordinateAction_ker :
    G2ArtinPresentation.involutionKernel ≤ coordinateAction.ker := by
  apply Subgroup.normalClosure_le_normal
  intro x hx
  rcases hx with rfl | rfl
  · change coordinateAction (G2ArtinPresentation.sigmaZero ^ 2) = 1
    rw [map_pow, coordinateAction_sigmaZero]
    exact InfoGeometry.Algebra.Zorn.G2CoordinateCoxeterRelations.coordinate_s1_sq
  · change coordinateAction (G2ArtinPresentation.sigmaOne ^ 2) = 1
    rw [map_pow, coordinateAction_sigmaOne]
    exact InfoGeometry.Algebra.Zorn.G2CoordinateCoxeterRelations.coordinate_s2_sq

def quotientToCoordinate : G2ArtinPresentation.WeylQuotient →*
    Equiv.Perm G2CoordinateRoot :=
  QuotientGroup.lift G2ArtinPresentation.involutionKernel coordinateAction
    involutionKernel_le_coordinateAction_ker

@[simp] theorem quotientToCoordinate_mk
    (w : G2ArtinPresentation.ArtinG2) :
    quotientToCoordinate (G2ArtinPresentation.artinQuotientMap w) =
      coordinateAction w := by
  exact QuotientGroup.lift_mk' _ _ _

/-! The transported action descends through the existing Coxeter quotient. -/

noncomputable def quotientToRoot :
    G2ArtinPresentation.WeylQuotient →* Equiv.Perm G2Root :=
  concreteRootTransport.comp quotientToCoordinate

@[simp] theorem quotientToRoot_mk
    (w : G2ArtinPresentation.ArtinG2) :
    quotientToRoot (G2ArtinPresentation.artinQuotientMap w) =
      concreteRootAction w := by
  rw [quotientToRoot, MonoidHom.comp_apply, quotientToCoordinate_mk]
  rfl

theorem quotientToRoot_comp_artinQuotientMap :
    quotientToRoot.comp G2ArtinPresentation.artinQuotientMap =
      concreteRootAction := by
  apply MonoidHom.ext
  intro w
  exact quotientToRoot_mk w

theorem quotientToRoot_coordinate_readback
    (w : G2ArtinPresentation.ArtinG2) (r : G2Root) :
    concreteRootCoordinateEquiv
        (quotientToRoot (G2ArtinPresentation.artinQuotientMap w) r) =
      coordinateAction w (concreteRootCoordinateEquiv r) := by
  rw [quotientToRoot_mk]
  exact concreteRootAction_coordinate_readback w r

theorem g2Artin_coordinateAction_factor_through_weyl :
    quotientToCoordinate.comp G2ArtinPresentation.artinQuotientMap =
      coordinateAction := by
  apply MonoidHom.ext
  intro w
  exact quotientToCoordinate_mk w

theorem artin_coordinateAction_factors_through_calibrated_dihedral :
    coordinateAction =
      InfoGeometry.Algebra.Zorn.G2CoordinateSemidirectBridge.calibratedDihedralCoordinateHom.comp
        artinToCoxeter := by
  apply PresentedGroup.ext (rels := G2ArtinPresentation.relations)
  intro i
  fin_cases i
  · change coordinateAction G2ArtinPresentation.sigmaZero =
      InfoGeometry.Algebra.Zorn.G2CoordinateSemidirectBridge.calibratedDihedralCoordinateHom
        (artinToCoxeter G2ArtinPresentation.sigmaZero)
    rw [coordinateAction_sigmaZero, artinToCoxeter_sigmaZero]
    exact InfoGeometry.Algebra.Zorn.G2CoordinateSemidirectBridge.calibratedDihedralCoordinateHom_sr_zero.symm
  · change coordinateAction G2ArtinPresentation.sigmaOne =
      InfoGeometry.Algebra.Zorn.G2CoordinateSemidirectBridge.calibratedDihedralCoordinateHom
        (artinToCoxeter G2ArtinPresentation.sigmaOne)
    rw [coordinateAction_sigmaOne, artinToCoxeter_sigmaOne]
    exact InfoGeometry.Algebra.Zorn.G2CoordinateSemidirectBridge.calibratedDihedralCoordinateHom_sr_one.symm

theorem g2Artin_coordinateAction_eq_weylAction :
    coordinateAction =
      InfoGeometry.Algebra.Zorn.G2CoordinateSemidirectBridge.calibratedDihedralCoordinateHom.comp
        artinToCoxeter :=
  artin_coordinateAction_factors_through_calibrated_dihedral

theorem throatConjugation_quotientToCoordinate_swap :
    G2ArtinKleinBridge.throatConjugation.comp quotientToCoordinate =
      quotientToCoordinate.comp
        G2ArtinPresentation.descendedArtinGeneratorSwap := by
  apply MonoidHom.ext
  intro w
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
    G2ArtinPresentation.involutionKernel w
  simp only [MonoidHom.coe_comp]
  change G2ArtinKleinBridge.throatConjugation
      (quotientToCoordinate (G2ArtinPresentation.artinQuotientMap g)) =
    quotientToCoordinate
      (G2ArtinPresentation.descendedArtinGeneratorSwap
        (G2ArtinPresentation.artinQuotientMap g))
  rw [G2ArtinPresentation.descendedArtinGeneratorSwap_mk,
    quotientToCoordinate_mk, quotientToCoordinate_mk]
  exact DFunLike.congr_fun
    G2ArtinKleinBridge.throatConjugation_coordinateAction_swap g

noncomputable def artinToConcreteWeyl :
    G2ArtinPresentation.ArtinG2 →*
      InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.weylG2Subgroup :=
  MonoidHom.comp
    InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.dihedralWeylHom artinToCoxeter

theorem artinToConcreteWeyl_swap_compatibility
    (w : G2ArtinPresentation.ArtinG2) :
    artinToConcreteWeyl (G2ArtinPresentation.artinGeneratorSwap w) =
      InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.dihedralWeylHom
        (dihedralSwapHom (artinToCoxeter w)) := by
  rw [artinToConcreteWeyl, MonoidHom.comp_apply,
    artinToCoxeter_swap_compatibility]

theorem artinToConcreteWeyl_rootAut_conj
    (w : G2ArtinPresentation.ArtinG2)
    (r : InfoGeometry.Algebra.Zorn.G2TwoRootSystem.G2Root) :
    (artinToConcreteWeyl w).val * rootAut r *
        ((artinToConcreteWeyl w).val)⁻¹ =
      rootAut (InfoGeometry.Algebra.Zorn.G2RootSystemWeylBridge.weylRootAction
        (InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.dihedralParameterMap
          (artinToCoxeter w)) r) := by
  simpa [artinToConcreteWeyl,
    InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.dihedralWeylHom,
    InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.dihedralWeylSubgroupEquiv,
    InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.dihedralParameterEquiv,
    InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.dihedralParameterMap] using
    (InfoGeometry.Algebra.Zorn.G2RootSystemWeylBridge.weylNF_rootAut_conj
      (InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.dihedralParameterMap
        (artinToCoxeter w)) r)

@[simp] theorem quotientToConcreteWeyl_mk
    (w : G2ArtinPresentation.ArtinG2) :
    quotientToConcreteWeyl (G2ArtinPresentation.artinQuotientMap w) =
      artinToConcreteWeyl w := by
  rw [quotientToConcreteWeyl, MonoidHom.comp_apply,
    quotientToDihedral_mk]
  rfl

theorem quotientToConcreteWeyl_rootAut_conj
    (w : G2ArtinPresentation.WeylQuotient)
    (r : InfoGeometry.Algebra.Zorn.G2TwoRootSystem.G2Root) :
    (quotientToConcreteWeyl w).val * rootAut r *
        ((quotientToConcreteWeyl w).val)⁻¹ =
      rootAut (InfoGeometry.Algebra.Zorn.G2RootSystemWeylBridge.weylRootAction
        (InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.dihedralParameterMap
          (quotientToDihedral w)) r) := by
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective
    G2ArtinPresentation.involutionKernel w
  simpa only [quotientToConcreteWeyl_mk, quotientToDihedral_mk] using
    (artinToConcreteWeyl_rootAut_conj w r)

@[simp] theorem artinToConcreteWeyl_sigmaZero :
    artinToConcreteWeyl G2ArtinPresentation.sigmaZero =
      ⟨s, s_mem_weylG2Subgroup⟩ := by
  change InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.dihedralWeylHom
    (DihedralGroup.sr 0) = _
  rfl

@[simp] theorem artinToConcreteWeyl_sigmaOne :
    artinToConcreteWeyl G2ArtinPresentation.sigmaOne =
      ⟨t, t_mem_weylG2Subgroup⟩ := by
  rw [artinToConcreteWeyl, MonoidHom.comp_apply,
    artinToCoxeter_sigmaOne]
  rfl

/-! ## Concrete automorphism target

The coordinate-root action above is the finite normal-form readback.  The
following homomorphism is the corresponding map into the existing concrete
split-octonion automorphism group; it does not introduce a second Weyl
carrier.
-/

theorem concrete_simple_reflections_relation :
    s * t * s * t * s * t = t * s * t * s * t * s := by
  exact st_artin_braid_relation

private def concreteAssignment :
    G2ArtinPresentation.Generator →
      InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.SplitOctF2Aut
  | 0 => s
  | 1 => t

private theorem concreteRelationRespected :
    ∀ r ∈ G2ArtinPresentation.relations,
      FreeGroup.lift concreteAssignment r = 1 := by
  intro r hr
  have hr' : r = G2ArtinPresentation.relation := by
    simpa [G2ArtinPresentation.relations] using hr
  subst r
  simpa only [G2ArtinPresentation.relation, map_mul, map_inv,
    FreeGroup.lift_apply_of] using
    (show s * t * s * t * s * t *
        (t * s * t * s * t * s)⁻¹ =
      (1 : InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.SplitOctF2Aut) by
      exact mul_inv_eq_one.mpr concrete_simple_reflections_relation)

noncomputable def concreteAction :
    G2ArtinPresentation.ArtinG2 →*
      InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.SplitOctF2Aut :=
  PresentedGroup.toGroup (f := concreteAssignment)
    (rels := G2ArtinPresentation.relations) concreteRelationRespected

@[simp] theorem concreteAction_sigmaZero :
    concreteAction G2ArtinPresentation.sigmaZero = s := by
  change PresentedGroup.toGroup (f := concreteAssignment)
    (rels := G2ArtinPresentation.relations) concreteRelationRespected
      (PresentedGroup.of 0) = s
  rw [PresentedGroup.toGroup.of]
  rfl

@[simp] theorem concreteAction_sigmaOne :
    concreteAction G2ArtinPresentation.sigmaOne = t := by
  change PresentedGroup.toGroup (f := concreteAssignment)
    (rels := G2ArtinPresentation.relations) concreteRelationRespected
      (PresentedGroup.of 1) = t
  rw [PresentedGroup.toGroup.of]
  rfl

/-! The ambient concrete Artin representation and the Weyl-subgroup lift are
    the same representation after forgetting the subgroup witness.  This is
    the global carrier-identification seam; it uses only generator
    extensionality, so it does not enumerate Artin words. -/

theorem concreteAction_eq_artinToConcreteWeyl_val
    (w : G2ArtinPresentation.ArtinG2) :
    concreteAction w = (artinToConcreteWeyl w).val := by
  have h : concreteAction =
      (InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.weylG2Subgroup.subtype).comp
        artinToConcreteWeyl := by
    apply PresentedGroup.ext (rels := G2ArtinPresentation.relations)
    intro i
    fin_cases i
    · change concreteAction G2ArtinPresentation.sigmaZero =
        (artinToConcreteWeyl G2ArtinPresentation.sigmaZero).val
      rw [concreteAction_sigmaZero, artinToConcreteWeyl_sigmaZero]
    · change concreteAction G2ArtinPresentation.sigmaOne =
        (artinToConcreteWeyl G2ArtinPresentation.sigmaOne).val
      rw [concreteAction_sigmaOne, artinToConcreteWeyl_sigmaOne]
  exact DFunLike.congr_fun h w

theorem g2Artin_concreteWeyl_factorization :
    concreteAction =
      (InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.weylG2Subgroup.subtype).comp
        artinToConcreteWeyl := by
  apply MonoidHom.ext
  intro w
  exact concreteAction_eq_artinToConcreteWeyl_val w

/-! Global concrete conjugation readback.  The equality of the ambient
    automorphism representations is used only to transport the already
    established Weyl normal-form conjugation theorem. -/

theorem concreteAction_rootAut_conj
    (w : G2ArtinPresentation.ArtinG2) (r : G2Root) :
    concreteAction w * rootAut r * (concreteAction w)⁻¹ =
      rootAut (InfoGeometry.Algebra.Zorn.G2RootSystemWeylBridge.weylRootAction
        (InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.dihedralParameterMap
          (artinToCoxeter w)) r) := by
  rw [concreteAction_eq_artinToConcreteWeyl_val w]
  exact artinToConcreteWeyl_rootAut_conj w r

theorem concreteAction_sigmaZero_rootAut_conj (r :
    InfoGeometry.Algebra.Zorn.G2TwoRootSystem.G2Root) :
    concreteAction G2ArtinPresentation.sigmaZero * rootAut r *
        (concreteAction G2ArtinPresentation.sigmaZero)⁻¹ =
      rootAut (sAction r) := by
  rw [concreteAction_sigmaZero]
  exact s_rootAut_s r

theorem concreteAction_sigmaOne_rootAut_conj (r :
    InfoGeometry.Algebra.Zorn.G2TwoRootSystem.G2Root) :
    concreteAction G2ArtinPresentation.sigmaOne * rootAut r *
        (concreteAction G2ArtinPresentation.sigmaOne)⁻¹ =
      rootAut (sAction (cAction r)) := by
  rw [concreteAction_sigmaOne]
  dsimp [t]
  calc
    (s * c) * rootAut r * (s * c)⁻¹ =
        s * (c * rootAut r * c⁻¹) * s⁻¹ := by group
    _ = s * rootAut (cAction r) * s⁻¹ := by rw [c_rootAut_c]
    _ = rootAut (sAction (cAction r)) := by
      exact s_rootAut_s (cAction r)

/-! The concrete conjugation readbacks agree with the calibrated coordinate
    root action.  This is the generator-level compatibility seam between the
    split-octonion Weyl representatives and the Artin coordinate quotient. -/

theorem concreteAction_sigmaZero_coordinate_conj (r : G2Root) :
    concreteRootCoordinateEquiv (sAction r) =
      s1Root (concreteRootCoordinateEquiv r) := by
  exact concreteRootCoordinateEquiv_sAction r

theorem concreteAction_sigmaOne_coordinate_conj (r : G2Root) :
    concreteRootCoordinateEquiv (sAction (cAction r)) =
      s2Root (concreteRootCoordinateEquiv r) := by
  exact concreteRootCoordinateEquiv_sAction_cAction r

theorem concreteAction_sigmaZero_coordinateAction (r : G2Root) :
    concreteRootCoordinateEquiv (sAction r) =
      coordinateAction G2ArtinPresentation.sigmaZero
        (concreteRootCoordinateEquiv r) := by
  rw [coordinateAction_sigmaZero]
  exact concreteAction_sigmaZero_coordinate_conj r

theorem concreteAction_sigmaOne_coordinateAction (r : G2Root) :
    concreteRootCoordinateEquiv (sAction (cAction r)) =
      coordinateAction G2ArtinPresentation.sigmaOne
        (concreteRootCoordinateEquiv r) := by
  rw [coordinateAction_sigmaOne]
  exact concreteAction_sigmaOne_coordinate_conj r

/-! These are the coordinate-valued conjugation readbacks.  They retain the
    concrete automorphism carrier on the left and use the calibrated root
    equivalence only at the observable coordinate boundary. -/

theorem concreteAction_sigmaZero_coordinate (r : G2Root) :
    concreteAction G2ArtinPresentation.sigmaZero * rootAut r *
        (concreteAction G2ArtinPresentation.sigmaZero)⁻¹ =
      rootAut (concreteRootCoordinateEquiv.symm
        (coordinateAction G2ArtinPresentation.sigmaZero
          (concreteRootCoordinateEquiv r))) := by
  rw [coordinateAction_sigmaZero]
  have hcoord := congrArg concreteRootCoordinateEquiv.symm
    (concreteRootCoordinateEquiv_sAction r)
  rw [← hcoord]
  simpa using concreteAction_sigmaZero_rootAut_conj r

theorem concreteAction_sigmaOne_coordinate (r : G2Root) :
    concreteAction G2ArtinPresentation.sigmaOne * rootAut r *
        (concreteAction G2ArtinPresentation.sigmaOne)⁻¹ =
      rootAut (concreteRootCoordinateEquiv.symm
        (coordinateAction G2ArtinPresentation.sigmaOne
          (concreteRootCoordinateEquiv r))) := by
  rw [coordinateAction_sigmaOne]
  have hcoord := congrArg concreteRootCoordinateEquiv.symm
    (concreteRootCoordinateEquiv_sAction_cAction r)
  rw [← hcoord]
  simpa using concreteAction_sigmaOne_rootAut_conj r

theorem concreteAction_garside :
    concreteAction G2ArtinPresentation.garside = c ^ 3 := by
  have h0 : concreteAction (PresentedGroup.of 0) = s := by
    simpa [G2ArtinPresentation.sigmaZero] using concreteAction_sigmaZero
  have h1 : concreteAction (PresentedGroup.of 1) = t := by
    simpa [G2ArtinPresentation.sigmaOne] using concreteAction_sigmaOne
  change concreteAction (PresentedGroup.of 0 * PresentedGroup.of 1 *
    PresentedGroup.of 0 * PresentedGroup.of 1 * PresentedGroup.of 0 *
    PresentedGroup.of 1) = c ^ 3
  rw [map_mul, map_mul, map_mul, map_mul, map_mul, h0, h1]
  have hst : s * t = c := by
    dsimp [t]
    rw [← mul_assoc, s_sq, one_mul]
  calc
    s * t * s * t * s * t = (s * t) ^ 3 := by
      simp [pow_succ, mul_assoc]
    _ = c ^ 3 := by rw [hst]

theorem concreteAction_garside_eq_swapCartan :
    concreteAction G2ArtinPresentation.garside = swapCartanAut := by
  rw [concreteAction_garside, c_pow_three_eq_swapCartan]

theorem concreteAction_garside_sq :
    concreteAction
        (G2ArtinPresentation.garside * G2ArtinPresentation.garside) = 1 := by
  rw [map_mul, concreteAction_garside_eq_swapCartan, swapCartanAut_sq]

theorem concreteAction_garside_up0 :
    (concreteAction G2ArtinPresentation.garside).1
        InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.up0 =
      InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.down0 := by
  rw [concreteAction_garside]
  exact c_cube_up0

/-! ## Artin action with the Weyl-subgroup carrier retained

The ambient concrete representation lands in the full automorphism group.  The
same presentation can be lifted to the already proved Weyl subgroup, which
retains the quotient information needed by the root normal-form action.
-/

private def concreteWeylAssignment :
    G2ArtinPresentation.Generator →
      InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.weylG2Subgroup
  | 0 => ⟨s, s_mem_weylG2Subgroup⟩
  | 1 => ⟨t, t_mem_weylG2Subgroup⟩

private theorem concreteWeylRelationRespected :
    ∀ r ∈ G2ArtinPresentation.relations,
      FreeGroup.lift concreteWeylAssignment r = 1 := by
  intro r hr
  have hr' : r = G2ArtinPresentation.relation := by
    simpa [G2ArtinPresentation.relations] using hr
  subst r
  apply Subtype.ext
  simpa only [G2ArtinPresentation.relation, map_mul, map_inv,
    FreeGroup.lift_apply_of, concreteWeylAssignment] using
    (show s * t * s * t * s * t *
        (t * s * t * s * t * s)⁻¹ =
      (1 : InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.SplitOctF2Aut) from
      mul_inv_eq_one.mpr concrete_simple_reflections_relation)

noncomputable def concreteActionWeyl :
    G2ArtinPresentation.ArtinG2 →*
      InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.weylG2Subgroup :=
  PresentedGroup.toGroup (f := concreteWeylAssignment)
    (rels := G2ArtinPresentation.relations) concreteWeylRelationRespected

@[simp] theorem concreteActionWeyl_sigmaZero :
    concreteActionWeyl G2ArtinPresentation.sigmaZero =
      ⟨s, s_mem_weylG2Subgroup⟩ := by
  change PresentedGroup.toGroup (f := concreteWeylAssignment)
    (rels := G2ArtinPresentation.relations) concreteWeylRelationRespected
      (PresentedGroup.of 0) = _
  rw [PresentedGroup.toGroup.of]
  rfl

@[simp] theorem concreteActionWeyl_sigmaOne :
    concreteActionWeyl G2ArtinPresentation.sigmaOne =
      ⟨t, t_mem_weylG2Subgroup⟩ := by
  change PresentedGroup.toGroup (f := concreteWeylAssignment)
    (rels := G2ArtinPresentation.relations) concreteWeylRelationRespected
      (PresentedGroup.of 1) = _
  rw [PresentedGroup.toGroup.of]
  rfl

theorem concreteActionWeyl_eq_artinToConcreteWeyl :
    concreteActionWeyl = artinToConcreteWeyl := by
  apply PresentedGroup.ext
  intro x
  fin_cases x
  · simpa [G2ArtinPresentation.sigmaZero] using concreteActionWeyl_sigmaZero
  · simpa [G2ArtinPresentation.sigmaOne] using concreteActionWeyl_sigmaOne

/-! The two existing Artin representations agree on generator labels.  The
carriers remain intentionally distinct: one is the explicit root
permutation carrier and the other is the concrete automorphism Weyl subgroup.
-/

theorem artin_generators_coordinate_concrete_packet :
    (coordinateAction G2ArtinPresentation.sigmaZero = s1Root ∧
      concreteActionWeyl G2ArtinPresentation.sigmaZero =
        ⟨s, s_mem_weylG2Subgroup⟩) ∧
    (coordinateAction G2ArtinPresentation.sigmaOne = s2Root ∧
      concreteActionWeyl G2ArtinPresentation.sigmaOne =
        ⟨t, t_mem_weylG2Subgroup⟩) := by
  exact ⟨⟨coordinateAction_sigmaZero, concreteActionWeyl_sigmaZero⟩,
    ⟨coordinateAction_sigmaOne, concreteActionWeyl_sigmaOne⟩⟩

end

end InfoGeometry.Exceptional.G2ArtinWeylBridge
