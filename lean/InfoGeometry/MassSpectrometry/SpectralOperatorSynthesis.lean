import InfoGeometry.MassSpectrometry.AbsorbingDrazinBridge
import InfoGeometry.MassSpectrometry.SignatureIdentificationBridge
import InfoGeometry.MassSpectrometry.SignatureCyclotomicBridge

/-!
# Ranked fragmentation → signature Gram → observable MP support → cyclotomic lift

All constructions here use the same supplied grammar and readout. Physical
interpretation, calibration and chemical-class separation remain additional
obligations. This closes the finite algebraic diagram, not an infinite-dimensional
Fredholm determinant or a claim that spectral data has physical cyclic dynamics.
-/
noncomputable section
namespace InfoGeometry.MassSpectrometry.SpectralOperatorSynthesis
open FragmentObservability SignatureGeometry SignatureCyclotomic
open InfoGeometry.Algebra.RankedMatrixPowers
open InfoGeometry.Core.DiracSuperalgebra

variable {n : ℕ} {J : Type*} [Fintype J] [DecidableEq J] {D : FragmentationDAG n}

def signature (G : StochasticGrammar D) (C : Matrix J (Fin n) ℝ) :=
  historyMap G.transientMatrix C (rankHorizon D.rank)

/-- The same constructed metric support detects the actual finite signature kernel. -/
theorem signature_support_iff_all_readouts_zero
    (G : StochasticGrammar D) (C : Matrix J (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    visible (signature G C) x = 0 ↔
      ∀ t : Fin (rankHorizon D.rank), matrixMap (C*G.transientMatrix^t.val) x=0 := by
  rw [visible_gram_kernel]
  change gram (historyMap G.transientMatrix C (rankHorizon D.rank)) x=0 ↔ _
  rw [← historyGram_realization]
  exact historyGram_zero_iff _ _ _ _

/-- Actual doubled support, with all polynomial operators constructed from it. -/
theorem signature_active_support
    (G : StochasticGrammar D) (C : Matrix J (Fin n) ℝ) :
    activeSupport (signatureRaise (signature G C)) (signatureLower (signature G C)) =
      !![visible (signature G C), 0; 0, visible (signature G C)] :=
  doubled_support _ (visible_idempotent _)

/-- Native ambient unit built from the same readout support. -/
theorem signature_ambient_fourth_power
    (G : StochasticGrammar D) (C : Matrix J (Fin n) ℝ) :
    (signatureWeylUnit (signature G C)).val^4=1 := signatureWeyl_fourth _

/-- Finite compatibility on the actual signature carrier. -/
theorem signature_compatibility
    (G : StochasticGrammar D) (C : Matrix J (Fin n) ℝ)
    (y : EuclideanSpace ℝ (Fin (rankHorizon D.rank) × J)) :
    (∃ x, signature G C x=y) ↔ y ∈ (signature G C).toLinearMap.adjoint.kerᗮ :=
  finite_fredholm_alternative _ y

end InfoGeometry.MassSpectrometry.SpectralOperatorSynthesis
