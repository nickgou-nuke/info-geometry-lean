import Mathlib
import InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
import InfoGeometry.Canonical.PrimeLeeYangLargeDeviation
import InfoGeometry.Meta.SocketTarget

/-!
# InfoGeometry.Canonical.PrimeLeeYangDefectFreeLimit

witness-gated (Native Closure Mandated: Closure Debt) defect-free thermodynamic limit for the prime Lee--Yang program.

The finite modules upstream prove the elementary and finite pieces:

* Cayley geometry identifies the critical line with the Lee--Yang unit circle;
* the prime chain has explicit ferromagnetic logarithmic couplings;
* finite cumulant and finite Cramér-rate readouts are available.

This file records the remaining analytic burden as a proof-carrying packet:
no spontaneous magnetization, Gaussian/CLT-scale fluctuations, no random-field
defects, persistence of Lee--Yang stability in the thermodynamic limit, and the
renormalized completed-`xi` Cayley limit.

It does not prove RH, PNT, Mertens estimates, CLT, Lee--Yang stability, or a
relative determinant identity.
-/

noncomputable section

namespace InfoGeometry.Canonical.PrimeLeeYangDefectFreeLimit

open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
open InfoGeometry.Canonical.PrimeLeeYangLargeDeviation

/--
Defect-free thermodynamic limit packet for the prime Lee--Yang chain.

The packet deliberately keeps the analytic assertions as supplied laws.  This
is the theorem-safe location for claims such as:

* zero mean / no spontaneous magnetization;
* Gaussian or CLT-scale prime-energy fluctuations;
* large-deviation control excluding random-field defects;
* persistence of Lee--Yang zero location in the limit;
* convergence of a renormalized finite-volume determinant to the completed
  Riemann readout in Cayley coordinates.
-/
@[socket_debt_tag]
structure DefectFreeLimitPacket
    (CompletedXiReadout : Type) where
  /-- Finite-volume Lee--Yang approximation socket. -/
  approximation :
    LeeYangPrimeApproximation CompletedXiReadout

  /-- Large-deviation socket for the corresponding finite prime chains. -/
  largeDeviation :
    PrimeChainLargeDeviationWitness

  /-- No spontaneous magnetization in the chosen thermodynamic scaling. -/
  zeroMeanMagnetization_law : Prop
  zeroMeanMagnetization_certificate :
    zeroMeanMagnetization_law

  /-- Gaussian/CLT-scale fluctuation law for the weighted prime magnetization. -/
  gaussianFluctuation_law : Prop
  gaussianFluctuation_certificate :
    gaussianFluctuation_law

  /-- Defect-exclusion law: no macroscopic random-field bias survives. -/
  noRandomFieldDefects_law : Prop
  noRandomFieldDefects_certificate :
    noRandomFieldDefects_law

  /--
  Persistence law saying the finite Lee--Yang circle property survives the
  renormalized thermodynamic limit.
  -/
  leeYangStabilityPersists_law : Prop
  leeYangStabilityPersists_certificate :
    leeYangStabilityPersists_law

  /--
  The completed-`xi` Cayley limit law for the defect-free sequence.

  This is separate from the finite Lee--Yang law; it is the analytic bridge
  where a concrete scattering/determinant construction must enter.
  -/
  xiCayleyLimit_law : Prop
  xiCayleyLimit_certificate :
    xiCayleyLimit_law

  /--
  The final conditional reduction from the defect-free Lee--Yang/`xi` limit to
  critical-line zero location.

  This field is intentionally a law, not an unconditional theorem.
  -/
  defectFreeLimit_implies_criticalLineZeros_law : Prop
  defectFreeLimit_implies_criticalLineZeros_certificate :
    defectFreeLimit_implies_criticalLineZeros_law

  /-- Guardrail: this packet is not an unconditional RH proof. -/
  no_unconditional_RH_claim_guard : Type

namespace DefectFreeLimitPacket

variable {CompletedXiReadout : Type}
variable (W : DefectFreeLimitPacket CompletedXiReadout)

/-- Re-export of the supplied zero-mean magnetization law. -/
theorem zeroMeanMagnetization :
    W.zeroMeanMagnetization_law :=
  W.zeroMeanMagnetization_certificate

/-- Re-export of the supplied Gaussian/CLT fluctuation law. -/
theorem gaussianFluctuation :
    W.gaussianFluctuation_law :=
  W.gaussianFluctuation_certificate

/-- Re-export of the supplied no-random-field-defect law. -/
theorem noRandomFieldDefects :
    W.noRandomFieldDefects_law :=
  W.noRandomFieldDefects_certificate

/-- Re-export of the supplied Lee--Yang stability persistence law. -/
theorem leeYangStabilityPersists :
    W.leeYangStabilityPersists_law :=
  W.leeYangStabilityPersists_certificate

/-- Re-export of the supplied completed-`xi` Cayley limit law. -/
theorem xiCayleyLimit :
    W.xiCayleyLimit_law :=
  W.xiCayleyLimit_certificate

/-- Re-export of the supplied conditional critical-line zero-location reduction. -/
theorem defectFreeLimit_implies_criticalLineZeros :
    W.defectFreeLimit_implies_criticalLineZeros_law :=
  W.defectFreeLimit_implies_criticalLineZeros_certificate

/--
The defect-free packet contains the upstream finite Lee--Yang circle law.

This is a finite-volume statement only; the limiting zero-location statement is
the separate supplied law `defectFreeLimit_implies_criticalLineZeros`.
-/
theorem finiteZeros_on_unitCircle
    (N : ℕ)
    (z : ℂ)
    (hz : (W.approximation.Z N).IsRoot z) :
    OnLeeYangCircle z :=
  W.approximation.leeYang N z hz

/--
The defect-free packet contains the upstream finite large-deviation principle
law from its large-deviation component.
-/
theorem finitePrimeChain_largeDeviationPrinciple :
    W.largeDeviation.largeDeviationPrinciple_law :=
  W.largeDeviation.largeDeviationPrinciple

end DefectFreeLimitPacket

end InfoGeometry.Canonical.PrimeLeeYangDefectFreeLimit
