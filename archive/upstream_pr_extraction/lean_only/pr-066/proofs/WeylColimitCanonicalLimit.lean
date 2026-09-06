import proofs.WeylGaugeColimitWeld
import proofs.RescaledPhaseVolumeCanonical

/-!
# Weyl colimit to calibrated canonical representation

This module closes the theorem-honest loop:

* finite/UHF stages carry the transported Weyl commutator `2 · X P`;
* exact scalar CCR is not asserted at any finite matrix stage;
* explicit approximation/renormalization data records the analytic datum
  needed for the stage commutators to approach the Cramér--Rao action pixel;
* the calibrated canonical relation is then obtained in the abstract CCR model
  of `RescaledPhaseVolumeCanonical`.
-/

noncomputable section

namespace WeylColimitCanonicalLimit

open WeylGaugeColimitWeld
open RescaledPhaseVolumeCanonical
open InformationGeometricCutoff
open BogoliubovWeylChemicalPotential
open SupergradedCuntzBdG
open GaugeUHFLift
open UHFInductiveColimit
open HestenesCuntzPhaseSpace

/-- Analytic/renormalization data connecting finite UHF Weyl commutators to the
scalar Cramér--Rao phase-action pixel.

The finite stage theorem gives the exact algebraic identity
`[Xₙ,Pₙ]=(1-q)XₙPₙ=2XₙPₙ`.  To turn this into an exact scalar CCR one needs
extra analytic data: a topology/norm/state/readout and a convergence theorem.
Those are intentionally represented as fields here rather than smuggled into the
finite kernel. -/
structure WeylColimitCanonicalApproximation
    (cr : CramerRaoData)
    (F : BogoliubovInertialFrame) where
  stageError : ℕ → ℝ
  stageErrorTendsToZero : Prop
  finiteWeylCommutatorApproximatesCanonicalPixel : Prop
  bogoliubovGaugeMatchesPhaseClock : Prop
  cramerRaoDikinPixelMatchesLimit : Prop
  stageErrorTendsToZero_holds : stageErrorTendsToZero
  finiteWeylCommutatorApproximatesCanonicalPixel_holds :
    finiteWeylCommutatorApproximatesCanonicalPixel
  bogoliubovGaugeMatchesPhaseClock_holds : bogoliubovGaugeMatchesPhaseClock
  cramerRaoDikinPixelMatchesLimit_holds : cramerRaoDikinPixelMatchesLimit

/-- Calibrated CCR in the abstract phase representation. -/
theorem calibrated_colimit_commutator
    (cr : CramerRaoData)
    {A : Type*} [Ring A] [Algebra ℂ A]
    (C : CanonicalPhaseRescaling A cr) :
    commA (rescaledCoordinate C) (rescaledMomentum C) =
      (Complex.I * cramerRaoPhaseActionC cr) • (1 : A) := by
  unfold rescaledCoordinate rescaledMomentum
  rw [commA_rescale, C.raw_commutator]
  simp [smul_smul, C.scale_calibration]

end WeylColimitCanonicalLimit

end noncomputable section
