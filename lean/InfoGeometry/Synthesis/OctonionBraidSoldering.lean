import InfoGeometry.Lie.SplitOctonionCircularZ3Grading
import InfoGeometry.Canonical.SplitOctonionCARBdGRegularLift
import InfoGeometry.Canonical.ArtinBraidFilteredColimit
import InfoGeometry.Canonical.SplitOctonionRightRegularBraid
import InfoGeometry.Canonical.SplitOctonionExteriorRightRegularBdGIntertwiner

noncomputable section

namespace InfoGeometry.Synthesis.OctonionBraidSoldering

open InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading
open InfoGeometry.Lie.SplitOctonionEllPolarization
open InfoGeometry.Lie.SplitOctonionEllCrossChannel
open InfoGeometry.Canonical.ArtinBraidFilteredColimit
open InfoGeometry.Algebra.Zorn.SplitQuaternionCore
open InfoGeometry.Canonical.SplitOctonionRightRegularBraid
  (braidUnit braidRepresentation braidConjugation braidRepresentation_artin)
open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge
  (Exterior3 exteriorWedge3 exteriorContract3 modeVector modeCovector)
open InfoGeometry.Canonical.SplitOctonionExteriorRightRegularBdGIntertwiner
  (fockBdGEquiv fockBdG_conjugates_creation fockBdG_conjugates_annihilation)

abbrev EndCZ := InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.EndCZ

def sandwich (metric left right : EndCZ) : EndCZ := left * metric * right

theorem sandwich_associative (metric first second third : EndCZ) :
    sandwich metric (sandwich metric first second) third =
      sandwich metric first (sandwich metric second third) := by
  simp only [sandwich, mul_assoc]

theorem sandwich_covariant (transport : EndCZ ≃ₐ[ℝ] EndCZ)
    (metric left right : EndCZ) :
    transport (sandwich metric left right) =
      sandwich (transport metric) (transport left) (transport right) := by
  simp only [sandwich, map_mul]

theorem sandwich_equivariant (transport : EndCZ ≃ₐ[ℝ] EndCZ)
    (metric left right : EndCZ) (metric_fixed : transport metric = metric) :
    transport (sandwich metric left right) =
      sandwich metric (transport left) (transport right) := by
  rw [sandwich_covariant, metric_fixed]

theorem regular_composition_defect :
    (leftRegular (rootPlus 0) * leftRegular (rootPlus 1) -
      leftRegular (rootPlus 0 * rootPlus 1)) (rootPlus 2) = -(uMinus - uPlus) := by
  change rootPlus 0 * (rootPlus 1 * rootPlus 2) -
    (rootPlus 0 * rootPlus 1) * rootPlus 2 = _
  calc
    rootPlus 0 * (rootPlus 1 * rootPlus 2) -
        (rootPlus 0 * rootPlus 1) * rootPlus 2 =
        -((rootPlus 0 * rootPlus 1) * rootPlus 2 -
          rootPlus 0 * (rootPlus 1 * rootPlus 2)) := by abel
    _ = -(uMinus - uPlus) := by
      rw [InfoGeometry.Lie.SplitOctonionCircularZ3Grading.rootPlus_associator_zero_one_two]

theorem transported_regular_CAR (transport : EndCZ ≃ₐ[ℝ] EndCZ) (mode : Fin 3) :
    transport (leftRegular (rootMinus mode)) * transport (leftRegular (rootPlus mode)) +
      transport (leftRegular (rootPlus mode)) * transport (leftRegular (rootMinus mode)) = 1 := by
  simpa only [map_add, map_mul, map_one] using congrArg transport
    (InfoGeometry.Canonical.SplitOctonionCARBdGRegularLift.leftRegular_root_CAR mode)

theorem represented_artin_on_sandwich
    (metric left right : EndCZ) :
    braidConjugation (PresentedGroup.of (0 : Fin 2) * PresentedGroup.of (1 : Fin 2) *
        PresentedGroup.of (0 : Fin 2))
        (sandwich metric left right) =
      braidConjugation (PresentedGroup.of (1 : Fin 2) * PresentedGroup.of (0 : Fin 2) *
        PresentedGroup.of (1 : Fin 2)) (sandwich metric left right) := by
  exact congrArg (fun gate : EndCZˣ =>
    gate.toLinearEquiv.conjAlgEquiv ℝ (sandwich metric left right)) braidRepresentation_artin

theorem braid_sandwich_covariant (braid : ArtinBraid 2) (metric left right : EndCZ) :
    braidConjugation braid (sandwich metric left right) =
      sandwich (braidConjugation braid metric) (braidConjugation braid left)
        (braidConjugation braid right) :=
  sandwich_covariant (braidConjugation braid) metric left right

theorem braid_sandwich_equivariant (braid : ArtinBraid 2) (metric left right : EndCZ)
    (metric_fixed : braidConjugation braid metric = metric) :
    braidConjugation braid (sandwich metric left right) =
      sandwich metric (braidConjugation braid left) (braidConjugation braid right) :=
  sandwich_equivariant (braidConjugation braid) metric left right metric_fixed

def fockMajorana (mode : Fin 3) : Module.End ℝ Exterior3 :=
  exteriorWedge3 (modeVector mode) + exteriorContract3 (modeCovector mode)

theorem fock_majorana_transport (mode : Fin 3) :
    fockBdGEquiv.conjAlgEquiv ℝ (fockMajorana mode) =
      InfoGeometry.Canonical.SplitOctonionRightRegularBraid.majorana mode := by
  unfold fockMajorana InfoGeometry.Canonical.SplitOctonionRightRegularBraid.majorana
  rw [map_add]
  exact congrArg₂ (fun first second : EndCZ => first + second)
    (fockBdG_conjugates_creation mode) (fockBdG_conjugates_annihilation mode)

def fockBraid (index : Fin 2) : Module.End ℝ Exterior3 :=
  1 + fockMajorana index.castSucc * fockMajorana index.succ

theorem fock_braid_transport (index : Fin 2) :
    fockBdGEquiv.conjAlgEquiv ℝ (fockBraid index) = (braidUnit index : EndCZ) := by
  change fockBdGEquiv.conjAlgEquiv ℝ
      (1 + fockMajorana index.castSucc * fockMajorana index.succ) = _
  rw [map_add, map_one, map_mul, fock_majorana_transport, fock_majorana_transport]
  rfl

theorem fock_braid_intertwines (index : Fin 2) (state : Exterior3) :
    fockBdGEquiv (fockBraid index state) = (braidUnit index : EndCZ) (fockBdGEquiv state) := by
  have transported := congrArg (fun operator : EndCZ => operator (fockBdGEquiv state))
    (fock_braid_transport index)
  change fockBdGEquiv (fockBraid index (fockBdGEquiv.symm (fockBdGEquiv state))) = _
    at transported
  simpa only [LinearEquiv.symm_apply_apply] using transported

theorem braidUnit_ne_one (index : Fin 2) : braidUnit index ≠ 1 := by
  letI : Nontrivial InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge.CZ :=
    fockBdGEquiv.injective.nontrivial
  intro equality
  have values : 1 + InfoGeometry.Canonical.SplitOctonionRightRegularBraid.bivector index =
      (1 : EndCZ) := congrArg Units.val equality
  have zero : InfoGeometry.Canonical.SplitOctonionRightRegularBraid.bivector index = 0 :=
    add_eq_left.mp values
  have neg_one_zero : -(1 : EndCZ) = 0 := by
    simpa only [zero, zero_mul] using
      (InfoGeometry.Canonical.SplitOctonionRightRegularBraid.bivector_sq index).symm
  exact (neg_ne_zero.mpr one_ne_zero) neg_one_zero

end InfoGeometry.Synthesis.OctonionBraidSoldering
