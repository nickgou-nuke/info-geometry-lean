import InfoGeometry.SignedNetwork.BranchingInitialization
import InfoGeometry.SignedNetwork.QubitWignerBridge

/-!
# Actual ensemble jumps realize the installed qubit Liouville generator locally

The finite phase-point frame and Hamiltonian generator are reused. No new
quantum correspondence is assumed. This owner connects the ensemble jump
calculation to that already specified Hamiltonian commutator, and proves exact
cancellation invariance of random-state readouts and their Bochner integrals.

The continuous-time equality with unitary conjugation still requires the
infinite jump process, nonexplosion, and passage from stopped first moments.
-/

noncomputable section

namespace InfoGeometry.SignedNetwork.BranchingQubitGenerator

open MeasureTheory
open InfoGeometry.SignedNetwork.ExactCancellation
open InfoGeometry.SignedNetwork.BranchingEnsembleGenerator
open InfoGeometry.SignedNetwork.BranchingEventLaw
open InfoGeometry.SignedNetwork.QubitWignerBridge
open InfoGeometry.SignedNetwork.CoherenceAndProjection
open InfoGeometry.SignedNetwork.BranchingInitialization
open InfoGeometry.Canonical.PauliHestenesSpinMomentum

/-- Completeness of the installed four phase-point frame on the existing
real Pauli carrier, not just analysis after synthesis. -/
theorem synthesis_analysis_pauli (P : PauliParavector) :
    synthesis (analysis P.pauliMatrix) = P.pauliMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [synthesis, analysis, phasePoint, phaseDirection,
      InfoGeometry.SignedNetwork.PauliContextBridge.contextProjector,
      PauliParavector.pauliMatrix, Matrix.trace, Matrix.mul_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply,
      Fin.sum_univ_four, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im] <;> ring

/-- The expected coordinates of the actual weighted seed law reconstruct
the given Pauli operator. -/
theorem expected_initial_coordinates_reconstruct (P : PauliParavector) :
    synthesis (fun a =>
      ∫ e, seedMass (analysis P.pauliMatrix) *
        signedReal (seed (analysis P.pauliMatrix) e) a
        ∂(seedPMF (analysis P.pauliMatrix)).toMeasure) = P.pauliMatrix := by
  simp only [integral_weighted_seed]
  exact synthesis_analysis_pauli P

/-- Reconstruction of the random signed ensemble with a fixed sample weight. -/
def empiricalDensity (weight : ℝ) (p : Counts (Fin 4)) : Mat2 :=
  (weight : ℂ) • synthesis (signedReal p)

@[simp] theorem empiricalDensity_cancel (weight : ℝ) (p : Counts (Fin 4)) :
    empiricalDensity weight (cancel p) = empiricalDensity weight p := by
  simp only [empiricalDensity, synthesis, signedReal_cancel]

@[simp] theorem empiricalDensity_addNullPairs
    (weight : ℝ) (p : Counts (Fin 4)) (k : Fin 4 → ℕ) :
    empiricalDensity weight (addNullPairs p k) = empiricalDensity weight p := by
  simp only [empiricalDensity, synthesis, signedReal_addNullPairs]

/-- The jump generator applied to each signed coordinate reconstructs the
actual Hamiltonian commutator. -/
theorem ensemble_generator_intertwines (hbar : ℝ) (h : Fin 3 → ℝ)
    (p : Counts (Fin 4)) :
    synthesis (fun a => generator (wignerGenerator hbar h)
      (fun n => signedReal n a) p) =
        liouville hbar (hamiltonian h) (synthesis (signedReal p)) := by
  simp only [generator_signedReal _ (wignerGenerator_column_sum hbar h), linearDrift]
  exact synthesis_generator hbar h (signedReal p)

/-- Online after-event cancellation has the same reconstructed local drift. -/
theorem canceled_generator_intertwines (hbar : ℝ) (h : Fin 3 → ℝ)
    (p : Counts (Fin 4)) :
    synthesis (fun a => generatorAfterCancel (wignerGenerator hbar h)
      (fun n => signedReal n a) p) =
        liouville hbar (hamiltonian h) (synthesis (signedReal p)) := by
  simp only [generatorAfterCancel_signedReal _
    (wignerGenerator_column_sum hbar h), linearDrift]
  exact synthesis_generator hbar h (signedReal p)

/-- The concrete Hamiltonian generator inherits the finite linear rate bound. -/
theorem qubit_rate_bound (hbar : ℝ) (h : Fin 3 → ℝ) (p : Counts (Fin 4)) :
    totalRate (wignerGenerator hbar h) p ≤
      uniformRateBound (wignerGenerator hbar h) * mass p :=
  totalRate_le_uniformRateBound _ (wignerGenerator_column_sum hbar h) p

section RandomReadouts

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

/-- Random cancellation preserves integrability because the readouts are
pointwise equal. This does not assert equality of entire future path laws. -/
theorem integrable_empiricalDensity_cancel_iff
    (weight : ℝ) (X : Ω → Counts (Fin 4)) :
    Integrable (fun ω => empiricalDensity weight (cancel (X ω))) μ ↔
      Integrable (fun ω => empiricalDensity weight (X ω)) μ := by
  simp only [empiricalDensity_cancel]

/-- Genuine equality of Bochner expectations under exact cancellation. -/
theorem integral_empiricalDensity_cancel
    (weight : ℝ) (X : Ω → Counts (Fin 4)) :
    (∫ ω, empiricalDensity weight (cancel (X ω)) ∂μ) =
      ∫ ω, empiricalDensity weight (X ω) ∂μ := by
  simp only [empiricalDensity_cancel]

/-- Scalar version for any finite cell carrier and any random ensemble. -/
theorem integral_signedReal_cancel
    {C : Type*} [Fintype C] [DecidableEq C]
    (X : Ω → Counts C) (a : C) :
    (∫ ω, signedReal (cancel (X ω)) a ∂μ) =
      ∫ ω, signedReal (X ω) a ∂μ := by
  simp only [signedReal_cancel]

end RandomReadouts

end InfoGeometry.SignedNetwork.BranchingQubitGenerator
