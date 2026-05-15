import Mathlib
import InfoGeometry.Canonical.PrimeLeeYangDefectFreeLimit

/-!
# InfoGeometry.Canonical.PrimeMertensDefectBoundary

Mertens/random-walk defect boundary for the prime Lee--Yang program.

This module records the theorem-safe interface between a Möbius/Mertens
magnetization estimate and the defect-free Lee--Yang limit packet.

It does not prove Mertens bounds, the prime number theorem, a central limit
theorem, a large-deviation principle, Lee--Yang stability, or RH.  Those claims
remain explicit witness fields.
-/

noncomputable section

namespace InfoGeometry.Canonical.PrimeMertensDefectBoundary

open InfoGeometry.Canonical.PrimeLeeYangDefectFreeLimit
open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
open InfoGeometry.Canonical.PrimeLeeYangLargeDeviation

/--
Witness packet for the Mertens/random-walk boundary.

`mobiusMagnetization` is the macroscopic signed arithmetic readout, such as a
Mertens-type partial sum.  `randomWalkScale` is the comparison scale, such as a
square-root scale with logarithmic correction.  `defectExponent` records which
exponents are interpreted as macroscopic random-field defects.

All asymptotic estimates are carried as laws with certificates.
-/
structure MertensDefectBoundary where
  /-- Signed arithmetic magnetization readout. -/
  mobiusMagnetization : ℕ → ℝ

  /-- Random-walk comparison scale. -/
  randomWalkScale : ℕ → ℝ

  /-- Predicate for exponents that would represent macroscopic defects. -/
  defectExponent : ℝ → Prop

  /-- Mertens/random-walk type bound law. -/
  mertensBound_law : Prop
  mertensBound_certificate :
    mertensBound_law

  /-- Large-deviation suppression law for excursions beyond the chosen scale. -/
  largeDeviationSuppression_law : Prop
  largeDeviationSuppression_certificate :
    largeDeviationSuppression_law

  /-- No surviving macroscopic bias/random-field-defect law. -/
  noMacroscopicBias_law : Prop
  noMacroscopicBias_certificate :
    noMacroscopicBias_law

  /-- Guardrail: this boundary packet is not a proof of RH or Mertens. -/
  no_unconditional_RH_claim_guard : Type

namespace MertensDefectBoundary

variable (M : MertensDefectBoundary)

/-- Re-export of the supplied Mertens/random-walk bound law. -/
theorem mertensBound :
    M.mertensBound_law :=
  M.mertensBound_certificate

/-- Re-export of the supplied large-deviation suppression law. -/
theorem largeDeviationSuppression :
    M.largeDeviationSuppression_law :=
  M.largeDeviationSuppression_certificate

/-- Re-export of the supplied no-macroscopic-bias law. -/
theorem noMacroscopicBias :
    M.noMacroscopicBias_law :=
  M.noMacroscopicBias_certificate

end MertensDefectBoundary

/--
Analytic bridge data needed to turn a Mertens boundary packet into a
defect-free Lee--Yang limit packet.

This keeps the finite Lee--Yang approximation, large-deviation socket, `xi`
limit, and stability persistence separate from the Mertens/random-walk
boundary itself.
-/
structure MertensToDefectFreeBridge
    (CompletedXiReadout : Type) where
  approximation :
    LeeYangPrimeApproximation CompletedXiReadout
  largeDeviation :
    PrimeChainLargeDeviationWitness

  /-- Mertens/random-walk boundary implies zero mean/no spontaneous magnetization. -/
  zeroMean_from_mertens_law : Prop
  zeroMean_from_mertens_certificate :
    zeroMean_from_mertens_law

  /-- Mertens/random-walk boundary implies Gaussian or CLT-scale fluctuations. -/
  gaussian_from_mertens_law : Prop
  gaussian_from_mertens_certificate :
    gaussian_from_mertens_law

  /-- Mertens/random-walk boundary excludes random-field defects. -/
  noDefects_from_mertens_law : Prop
  noDefects_from_mertens_certificate :
    noDefects_from_mertens_law

  /-- Lee--Yang stability persistence supplied by the analytic model. -/
  leeYangStabilityPersists_law : Prop
  leeYangStabilityPersists_certificate :
    leeYangStabilityPersists_law

  /-- Completed-`xi` Cayley limit supplied by the analytic model. -/
  xiCayleyLimit_law : Prop
  xiCayleyLimit_certificate :
    xiCayleyLimit_law

  /-- Conditional critical-line zero-location reduction supplied by the model. -/
  defectFreeLimit_implies_criticalLineZeros_law : Prop
  defectFreeLimit_implies_criticalLineZeros_certificate :
    defectFreeLimit_implies_criticalLineZeros_law

namespace MertensToDefectFreeBridge

variable {CompletedXiReadout : Type}
variable (B : MertensToDefectFreeBridge CompletedXiReadout)

/-- Re-export of the supplied zero-mean implication law. -/
theorem zeroMean_from_mertens :
    B.zeroMean_from_mertens_law :=
  B.zeroMean_from_mertens_certificate

/-- Re-export of the supplied Gaussian/CLT implication law. -/
theorem gaussian_from_mertens :
    B.gaussian_from_mertens_law :=
  B.gaussian_from_mertens_certificate

/-- Re-export of the supplied no-defect implication law. -/
theorem noDefects_from_mertens :
    B.noDefects_from_mertens_law :=
  B.noDefects_from_mertens_certificate

end MertensToDefectFreeBridge

/--
Build a defect-free Lee--Yang limit packet from a Mertens/random-walk boundary
and the remaining analytic bridge data.

This theorem does not prove the laws.  It assembles the downstream packet from
the supplied certificates.
-/
def defectFreeLimit_of_mertensBoundary
    {CompletedXiReadout : Type}
    (M : MertensDefectBoundary)
    (B : MertensToDefectFreeBridge CompletedXiReadout) :
    DefectFreeLimitPacket CompletedXiReadout where
  approximation := B.approximation
  largeDeviation := B.largeDeviation
  zeroMeanMagnetization_law :=
    M.mertensBound_law ∧ B.zeroMean_from_mertens_law
  zeroMeanMagnetization_certificate :=
    ⟨M.mertensBound, B.zeroMean_from_mertens⟩
  gaussianFluctuation_law :=
    M.largeDeviationSuppression_law ∧ B.gaussian_from_mertens_law
  gaussianFluctuation_certificate :=
    ⟨M.largeDeviationSuppression, B.gaussian_from_mertens⟩
  noRandomFieldDefects_law :=
    M.noMacroscopicBias_law ∧ B.noDefects_from_mertens_law
  noRandomFieldDefects_certificate :=
    ⟨M.noMacroscopicBias, B.noDefects_from_mertens⟩
  leeYangStabilityPersists_law :=
    B.leeYangStabilityPersists_law
  leeYangStabilityPersists_certificate :=
    B.leeYangStabilityPersists_certificate
  xiCayleyLimit_law :=
    B.xiCayleyLimit_law
  xiCayleyLimit_certificate :=
    B.xiCayleyLimit_certificate
  defectFreeLimit_implies_criticalLineZeros_law :=
    B.defectFreeLimit_implies_criticalLineZeros_law
  defectFreeLimit_implies_criticalLineZeros_certificate :=
    B.defectFreeLimit_implies_criticalLineZeros_certificate
  no_unconditional_RH_claim_guard :=
    M.no_unconditional_RH_claim_guard

/-- Owner theorem: the assembled defect-free packet re-exports the Mertens laws. -/
theorem defectFreeLimit_of_mertensBoundary_reexports
    {CompletedXiReadout : Type}
    (M : MertensDefectBoundary)
    (B : MertensToDefectFreeBridge CompletedXiReadout) :
      (defectFreeLimit_of_mertensBoundary M B).zeroMeanMagnetization_law ∧
      (defectFreeLimit_of_mertensBoundary M B).gaussianFluctuation_law ∧
      (defectFreeLimit_of_mertensBoundary M B).noRandomFieldDefects_law := by
  exact ⟨
    (defectFreeLimit_of_mertensBoundary M B).zeroMeanMagnetization,
    (defectFreeLimit_of_mertensBoundary M B).gaussianFluctuation,
    (defectFreeLimit_of_mertensBoundary M B).noRandomFieldDefects⟩

end InfoGeometry.Canonical.PrimeMertensDefectBoundary

