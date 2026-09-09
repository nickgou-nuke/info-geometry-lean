import InfoGeometry.Lie.SplitOctonionAxialCartanErlangen
import InfoGeometry.Algebra.Zorn.SplitOctonionG2TwoClassificationBoundary
import InfoGeometry.Lie.SplitOctonionImaginaryTensor
import InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge

/-!
# Concrete candidate readout for the axial Cartan flow

The traceless Cartan flow is already proved to preserve the native Zorn
multiplication and determinant.  This owner packages those facts through the
repository's explicit `G2TwoCandidate` boundary.  It does not identify the
full automorphism group with a named Lie group.
-/

noncomputable section

open scoped LinearAlgebra.Projectivization

namespace InfoGeometry.Lie.SplitOctonionAxialG2Candidate

open InfoGeometry.Algebra.Zorn
open InfoGeometry.Algebra.Zorn.G2TrifactorSU3
open InfoGeometry.Algebra.Zorn.SplitOctonionG2TwoClassificationBoundary
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Canonical
open InfoGeometry.Lie.SplitOctonionAxialCartanFlow
open InfoGeometry.Lie.SplitOctonionAxialCartanErlangen
open InfoGeometry.Lie.SplitOctonionAxialCartanProjective
open InfoGeometry.Lie.SplitOctonionAxialKleinProjective
open InfoGeometry.Lie.SplitOctonionAxialWittReduction
open InfoGeometry.Lie.SplitOctonionImaginaryAction
open InfoGeometry.Lie.SplitOctonionImaginaryTensor

abbrev CZ := InfoGeometry.Canonical.ZornMatrix ℝ

noncomputable def axialCartanG2TwoCandidate
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ) :
    G2TwoCandidate realZornCompositionDatum where
  map := axialCartanFlow k t
  map_mulZ := by
    intro X Y
    exact axialCartanFlow_map_mul k hk t X Y
  map_OP1 := by
    ext <;> simp [OP1, axialCartanFlow]
  map_OP2 := by
    ext <;> simp [OP2, axialCartanFlow]
  map_detZ := by
    intro X
    exact axialCartanCompositionAut_preserves_det k hk t X

@[simp] theorem axialCartanG2TwoCandidate_apply
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ) (X : CZ) :
    (axialCartanG2TwoCandidate k hk t).map X = axialCartanFlow k t X :=
  rfl

theorem axialCartanFlow_preserves_colorPart
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ) (X : CZ) :
    axialCartanFlow k t (colorPart X) =
      colorPart (axialCartanFlow k t X) := by
  apply op_stabilizer_preserves_colorPart
  refine ⟨?_, ?_, ?_⟩
  · intro X Y
    exact axialCartanFlow_map_mul k hk t X Y
  · ext <;> simp [OP1, axialCartanFlow]
  · ext <;> simp [OP2, axialCartanFlow]

theorem axialCartanFlow_preserves_anticolorPart
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ) (X : CZ) :
    axialCartanFlow k t (anticolorPart X) =
      anticolorPart (axialCartanFlow k t X) := by
  apply op_stabilizer_preserves_anticolorPart
  refine ⟨?_, ?_, ?_⟩
  · intro X Y
    exact axialCartanFlow_map_mul k hk t X Y
  · ext <;> simp [OP1, axialCartanFlow]
  · ext <;> simp [OP2, axialCartanFlow]

@[simp] theorem axialCartanG2TwoCandidate_zero_apply
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (X : CZ) :
    (axialCartanG2TwoCandidate k hk 0).map X = X := by
  exact axialCartanFlow_zero k X

theorem axialCartanG2TwoCandidate_add_apply
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (s t : ℝ) (X : CZ) :
    (axialCartanG2TwoCandidate k hk (s + t)).map X =
      (axialCartanG2TwoCandidate k hk s).map
        ((axialCartanG2TwoCandidate k hk t).map X) := by
  exact axialCartanFlow_add k s t X

theorem axialCartanG2TwoCandidate_commute_apply
    (k l : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (hl : ∑ i, l i = 0)
    (s t : ℝ) (X : CZ) :
    (axialCartanG2TwoCandidate k hk s).map
        ((axialCartanG2TwoCandidate l hl t).map X) =
      (axialCartanG2TwoCandidate l hl t).map
        ((axialCartanG2TwoCandidate k hk s).map X) := by
  exact SplitOctonionAxialCartanFlow.axialCartanFlow_commute k l s t X

@[simp] theorem axialCartanG2TwoCandidate_neg_left_inverse
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ) (X : CZ) :
    (axialCartanG2TwoCandidate k hk (-t)).map
        ((axialCartanG2TwoCandidate k hk t).map X) = X := by
  rw [← axialCartanG2TwoCandidate_add_apply, neg_add_cancel,
    axialCartanG2TwoCandidate_zero_apply]

@[simp] theorem axialCartanG2TwoCandidate_neg_right_inverse
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ) (X : CZ) :
    (axialCartanG2TwoCandidate k hk t).map
        ((axialCartanG2TwoCandidate k hk (-t)).map X) = X := by
  rw [← axialCartanG2TwoCandidate_add_apply, add_neg_cancel,
    axialCartanG2TwoCandidate_zero_apply]

theorem axialCartanG2TwoCandidate_preserves_product
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ) (X Y : CZ) :
    (axialCartanG2TwoCandidate k hk t).map (realZornCompositionDatum.mulZ X Y) =
      realZornCompositionDatum.mulZ
        ((axialCartanG2TwoCandidate k hk t).map X)
        ((axialCartanG2TwoCandidate k hk t).map Y) := by
  exact (axialCartanG2TwoCandidate k hk t).preserves_product X Y

@[simp] theorem axialCartanG2TwoCandidate_preserves_one
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ) :
    (axialCartanG2TwoCandidate k hk t).map (1 : CZ) = 1 := by
  exact axialCartanFlow_one k t

theorem axialCartanG2TwoCandidate_injective
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ) :
    Function.Injective (axialCartanG2TwoCandidate k hk t).map := by
  simpa only [axialCartanG2TwoCandidate_apply] using
    (axialCartanFlow k t).injective

theorem axialCartanG2TwoCandidate_preserves_null_cone
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ) (X : CZ)
    (hX : ZornMatrix.IsNull realCrossProduct3 X) :
    ZornMatrix.IsNull realCrossProduct3 ((axialCartanG2TwoCandidate k hk t).map X) := by
  exact (axialCartanG2TwoCandidate k hk t).preserves_null_cone X hX

theorem axialCartanG2TwoCandidate_null_iff
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ) (X : CZ) :
    ZornMatrix.IsNull realCrossProduct3 ((axialCartanG2TwoCandidate k hk t).map X) ↔
      ZornMatrix.IsNull realCrossProduct3 X := by
  unfold ZornMatrix.IsNull
  rw [show ZornMatrix.detZ realCrossProduct3
        ((axialCartanG2TwoCandidate k hk t).map X) = ZornMatrix.detZ realCrossProduct3 X by
      simpa only [axialCartanG2TwoCandidate_apply] using
        axialCartanCompositionAut_preserves_det k hk t X]

theorem axialCartanG2TwoCandidate_preserves_incident
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ) (X Y : CZ) :
    IncidentRep realCrossProduct3
        ((axialCartanG2TwoCandidate k hk t).map X)
        ((axialCartanG2TwoCandidate k hk t).map Y) ↔
      IncidentRep realCrossProduct3 X Y := by
  simpa only [axialCartanG2TwoCandidate_apply] using
    axialCartanFlow_preserves_incident k hk t X Y

theorem axialCartanG2TwoCandidate_preserves_polar
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ) (X Y : CZ) :
    polarZ realCrossProduct3
        ((axialCartanG2TwoCandidate k hk t).map X)
        ((axialCartanG2TwoCandidate k hk t).map Y) =
      polarZ realCrossProduct3 X Y := by
  simpa only [axialCartanG2TwoCandidate_apply] using
    axialCartanFlow_preserves_polar k hk t X Y

theorem axialCartanG2TwoCandidate_preserves_colorPart
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ) (X : CZ) :
    (axialCartanG2TwoCandidate k hk t).map (colorPart X) =
      colorPart ((axialCartanG2TwoCandidate k hk t).map X) := by
  exact axialCartanFlow_preserves_colorPart k hk t X

theorem axialCartanG2TwoCandidate_preserves_anticolorPart
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ) (X : CZ) :
    (axialCartanG2TwoCandidate k hk t).map (anticolorPart X) =
      anticolorPart ((axialCartanG2TwoCandidate k hk t).map X) := by
  exact axialCartanFlow_preserves_anticolorPart k hk t X

theorem axialCartanG2TwoCandidate_boundary_packet
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ) :
    (∀ X Y : CZ,
      (axialCartanG2TwoCandidate k hk t).map (realZornCompositionDatum.mulZ X Y) =
        realZornCompositionDatum.mulZ
          ((axialCartanG2TwoCandidate k hk t).map X)
          ((axialCartanG2TwoCandidate k hk t).map Y)) ∧
      (∀ X : CZ,
        ZornMatrix.detZ realCrossProduct3 ((axialCartanG2TwoCandidate k hk t).map X) =
          ZornMatrix.detZ realCrossProduct3 X) ∧
      (∀ X : CZ,
        (axialCartanG2TwoCandidate k hk t).map (colorPart X) =
          colorPart ((axialCartanG2TwoCandidate k hk t).map X)) ∧
      (∀ X : CZ,
        (axialCartanG2TwoCandidate k hk t).map (anticolorPart X) =
          anticolorPart ((axialCartanG2TwoCandidate k hk t).map X)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X Y
    simpa only [axialCartanG2TwoCandidate_apply] using
      axialCartanFlow_map_mul k hk t X Y
  · intro X
    exact axialCartanCompositionAut_preserves_det k hk t X
  · intro X
    simpa only [axialCartanG2TwoCandidate_apply] using
      axialCartanFlow_preserves_colorPart k hk t X
  · intro X
    simpa only [axialCartanG2TwoCandidate_apply] using
      axialCartanFlow_preserves_anticolorPart k hk t X

theorem axialCartanG2TwoCandidate_preserves_projective_Klein_null
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ)
    (p : ℙ ℝ ActiveSector) :
    _root_.InfoGeometry.Projective.ExteriorKleinProjective.IsKlein
        (activeExteriorProjectiveMap (activeCartanProjectiveMap k hk t p)) ↔
      _root_.InfoGeometry.Projective.ExteriorKleinProjective.IsKlein
        (activeExteriorProjectiveMap p) := by
  exact activeCartanProjectiveMap_preserves_Klein_null k hk t p

theorem axialCartanG2TwoCandidate_preserves_imaginary_commutator_form
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ)
    (X Y Z : InfoGeometry.Lie.SplitOctonionImaginaryAction.Imaginary) :
    imaginaryCommutatorForm
        (imaginaryAut (axialCartanCompositionAut k hk t) X)
        (imaginaryAut (axialCartanCompositionAut k hk t) Y)
        (imaginaryAut (axialCartanCompositionAut k hk t) Z) =
      imaginaryCommutatorForm X Y Z := by
  exact imaginaryAut_preserves_commutatorForm
    (axialCartanCompositionAut k hk t) X Y Z

theorem axialCartanG2TwoCandidate_preserves_imaginary_exterior_evaluation
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ)
    (X Y Z : InfoGeometry.Lie.SplitOctonionImaginaryAction.Imaginary) :
    imaginaryCommutatorExteriorMap
        (exteriorPower.ιMulti ℝ 3 ![
          imaginaryAut (axialCartanCompositionAut k hk t) X,
          imaginaryAut (axialCartanCompositionAut k hk t) Y,
          imaginaryAut (axialCartanCompositionAut k hk t) Z]) =
      imaginaryCommutatorExteriorMap
        (exteriorPower.ιMulti ℝ 3 ![X, Y, Z]) := by
  exact imaginaryAut_preserves_exteriorEvaluation
    (axialCartanCompositionAut k hk t) X Y Z

theorem axialCartanG2TwoCandidate_preserves_imaginary_exterior_map
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ) :
    imaginaryCommutatorExteriorMap.comp
        (exteriorPower.map 3
          (imaginaryAut (axialCartanCompositionAut k hk t)).toLinearMap) =
      imaginaryCommutatorExteriorMap := by
  apply exteriorPower.linearMap_ext
  ext v
  change imaginaryCommutatorExteriorMap
      (exteriorPower.map 3
        (imaginaryAut (axialCartanCompositionAut k hk t)).toLinearMap
        (exteriorPower.ιMulti ℝ 3 v)) =
    imaginaryCommutatorExteriorMap (exteriorPower.ιMulti ℝ 3 v)
  rw [exteriorPower.map_apply_ιMulti]
  change imaginaryCommutatorExteriorMap
      (exteriorPower.ιMulti ℝ 3
        (![imaginaryAut (axialCartanCompositionAut k hk t) (v 0),
          imaginaryAut (axialCartanCompositionAut k hk t) (v 1),
          imaginaryAut (axialCartanCompositionAut k hk t) (v 2)])) =
    imaginaryCommutatorExteriorMap (exteriorPower.ιMulti ℝ 3 v)
  have hv : v = ![v 0, v 1, v 2] := by
    funext i
    fin_cases i <;> rfl
  rw [hv, imaginaryCommutatorExteriorMap_ιMulti]
  rw [imaginaryCommutatorExteriorMap_ιMulti]
  exact axialCartanG2TwoCandidate_preserves_imaginary_commutator_form
    k hk t (v 0) (v 1) (v 2)

theorem axialCartanG2TwoCandidate_infinitesimal_commutator_form_invariant
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0)
    (X Y Z : InfoGeometry.Lie.SplitOctonionImaginaryAction.Imaginary) :
    imaginaryCommutatorForm (axialCartanImaginaryEnd k X) Y Z +
        imaginaryCommutatorForm X (axialCartanImaginaryEnd k Y) Z +
        imaginaryCommutatorForm X Y (axialCartanImaginaryEnd k Z) = 0 := by
  exact axialCartanImaginaryEnd_commutatorForm_lieInvariant k hk X Y Z

end InfoGeometry.Lie.SplitOctonionAxialG2Candidate
