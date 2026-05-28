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

open scoped BigOperators

open InfoGeometry.Canonical.PrimeLeeYangDefectFreeLimit
open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
open InfoGeometry.Canonical.PrimeLeeYangLargeDeviation

/--
Witness packet for the Mertens/random-walk boundary.

`mobiusMagnetization` is the macroscopic signed arithmetic readout, such as a
Mertens-type partial sum.  `randomWalkScale` is the comparison scale, such as a
square-root scale with logarithmic correction.  `defectExponent` records which
exponents are interpreted as macroscopic random-field defects.

All asymptotic estimates must be proved in concrete downstream models; this
packet stores only the readout data.
-/
structure MertensDefectBoundary where
  /-- Signed arithmetic magnetization readout. -/
  mobiusMagnetization : ℕ → ℝ

  /-- Random-walk comparison scale. -/
  randomWalkScale : ℕ → ℝ

  /-- Predicate for exponents that would represent macroscopic defects. -/
  defectExponent : ℝ → Prop

  /-- Guardrail: this boundary packet is not a proof of RH or Mertens. -/
  no_unconditional_RH_claim_guard : Type

namespace MertensDefectBoundary

variable (M : MertensDefectBoundary)

end MertensDefectBoundary

/-! ## RH-scale Mertens/LDP boundary socket -/

/--
Möbius/Mertens data.

`μ` is intentionally supplied as data rather than tied to a particular
number-theory implementation.  This keeps the defect-boundary socket independent
of arithmetic infrastructure choices.
-/
structure MobiusMertensData where
  μ : ℕ → ℤ
  M : ℕ → ℤ
  M_eq_sum :
    ∀ N : ℕ, M N = (Finset.Icc 1 N).sum (fun n => μ n)

namespace MobiusMertensData

/-- Real absolute value of the Mertens readout. -/
def absMertens (D : MobiusMertensData) (N : ℕ) : ℝ :=
  |((D.M N) : ℝ)|

/-- Square-root normalized Mertens defect. -/
def normalizedDefect (D : MobiusMertensData) (N : ℕ) : ℝ :=
  D.absMertens N / Real.sqrt ((N : ℝ))

end MobiusMertensData

/--
RH-scale Mertens boundary:

`∀ ε > 0, eventually |M(N)| ≤ Cε N^(1/2 + ε)`.

This is the theorem-safe RH-scale target, not the classical Mertens conjecture.
-/
def RHScaleBoundary (D : MobiusMertensData) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧
      ∃ N0 : ℕ,
        ∀ N : ℕ, N0 ≤ N → 1 ≤ N →
          D.absMertens N ≤
            C * Real.rpow ((N : ℝ)) ((1 / 2 : ℝ) + ε)

/--
Finite or asymptotic entropy-defect readout for the Mertens lane.

The fields are numerical readouts only; their analytic meaning is supplied by
the witness fields in `MertensLDPBoundary`.
-/
structure MertensDefectReadout (D : MobiusMertensData) where
  entropyBarrier : ℝ
  defectCost : ℝ
  freeEnergyGap : ℝ

/--
Large-deviation boundary witness for the Mertens defect.

`entropyDominatesDefect` is the formal socket for an LDP estimate saying that
the entropy barrier beats the parity-defect cost.  The analytic implication from
that statement to the RH-scale Mertens boundary remains explicit data.
-/
structure MertensLDPBoundary (D : MobiusMertensData) where
  readout : MertensDefectReadout D
  speed : ℕ → ℝ
  rate : ℝ → ℝ
  defectObservable : ℕ → ℝ
  entropyDominatesDefect : Prop
  noMacroscopicDefect : Prop
  ldp_to_noMacroscopicDefect :
    entropyDominatesDefect → noMacroscopicDefect
  noMacroscopicDefect_to_RHScale :
    noMacroscopicDefect → RHScaleBoundary D

namespace MertensLDPBoundary

/-- Extract the RH-scale Mertens boundary from an LDP certificate. -/
theorem RHScaleBoundary_of_entropyDominance
    {D : MobiusMertensData}
    (B : MertensLDPBoundary D)
    (h : B.entropyDominatesDefect) :
    RHScaleBoundary D :=
  B.noMacroscopicDefect_to_RHScale
    (B.ldp_to_noMacroscopicDefect h)

end MertensLDPBoundary

/--
Packaged Mertens boundary theorem surface.

Later bridge files can consume this packet without asserting RH or a global
Mertens theorem.
-/
structure MertensBoundaryPacket where
  mertensData : MobiusMertensData
  boundary : RHScaleBoundary mertensData

/-- Build a boundary packet from an LDP witness. -/
def MertensBoundaryPacket.ofLDP
    (D : MobiusMertensData)
    (B : MertensLDPBoundary D)
    (h : B.entropyDominatesDefect) :
    MertensBoundaryPacket where
  mertensData := D
  boundary := MertensLDPBoundary.RHScaleBoundary_of_entropyDominance B h

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


namespace MertensToDefectFreeBridge

variable {CompletedXiReadout : Type}
variable (B : MertensToDefectFreeBridge CompletedXiReadout)

end MertensToDefectFreeBridge

end InfoGeometry.Canonical.PrimeMertensDefectBoundary
