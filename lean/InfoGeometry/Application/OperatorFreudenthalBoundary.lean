/-
InfoGeometry/Application/OperatorFreudenthalBoundary.lean

Operator-to-Freudenthal boundary bridge.

This file glues the operator-first STU bridge to the abstract Freudenthal
phase-space datum.  Coordinates do not appear here.  A coordinate
hypermatrix or Cayley hyperdeterminant may be attached later only through a
separate chart theorem.
-/

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Exceptional.Freudenthal
import InfoGeometry.Application.STUOperatorBridge

noncomputable section

open scoped InnerProductSpace

namespace InfoGeometry.Application.OperatorFreudenthalBoundary

open InfoGeometry.Exceptional.Freudenthal
open InfoGeometry.Application.STUOperator

section Hilbert

variable {E J : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [AddCommGroup J] [Module ℝ J]

local notation "EndH" => E →L[ℝ] E

/-- The zero Freudenthal charge. -/
def zeroCharge : FreudenthalCharge J :=
  { alpha := 0
    beta := 0
    x := 0
    y := 0 }

/-- Freudenthal regular chamber: nonzero quartic invariant. -/
def FreudenthalRegular
    (D : CubicJordanDatum J) (Q : FreudenthalCharge J) : Prop :=
  FreudenthalCharge.quarticInvariant D Q ≠ 0

/--
Freudenthal boundary divisor: quartic collapse, excluding the zero charge.

This is the algebraic boundary that later receives Drazin surgery.
-/
def FreudenthalBoundary
    (D : CubicJordanDatum J) (Q : FreudenthalCharge J) : Prop :=
  FreudenthalCharge.quarticInvariant D Q = 0 ∧ Q ≠ zeroCharge

/--
Operator-to-Freudenthal chart.

This is not a coordinate chart.  It maps an operator state to an abstract
Freudenthal charge and proves that the operator invariant is exactly the
Freudenthal quartic invariant.
-/
structure OperatorFreudenthalChart
    (D : CubicJordanDatum J) where
  /-- Extract the Freudenthal charge carried by an operator state. -/
  chargeOf : EndH → FreudenthalCharge J

  /-- Operator-side quartic invariant. -/
  invariant : OperatorQuarticInvariant (E := E)

  /-- The operator invariant agrees with the Freudenthal quartic. -/
  invariant_eq_quartic :
    ∀ ρ : EndH,
      invariant.quartic ρ =
        FreudenthalCharge.quarticInvariant D (chargeOf ρ)

  /--
  Nonzero reflection between the operator state and the extracted charge.

  This is needed to identify the nontrivial boundary, not just the divisor.
  -/
  nonzero_iff_charge_nonzero :
    ∀ ρ : EndH,
      ρ ≠ 0 ↔ chargeOf ρ ≠ zeroCharge

section
omit [CompleteSpace E]
/--
Regularity is preserved by the operator-to-Freudenthal chart.
-/
theorem chart_regular_iff
    {D : CubicJordanDatum J}
    (C : OperatorFreudenthalChart (E := E) (J := J) D)
    (ρ : EndH) :
    IsRegularOperator C.invariant ρ ↔
      FreudenthalRegular D (C.chargeOf ρ) := by
  unfold IsRegularOperator FreudenthalRegular
  rw [C.invariant_eq_quartic ρ]

/--
Boundary status is preserved by the operator-to-Freudenthal chart.
-/
theorem chart_boundary_iff
    {D : CubicJordanDatum J}
    (C : OperatorFreudenthalChart (E := E) (J := J) D)
    (ρ : EndH) :
    IsBoundaryOperator C.invariant ρ ↔
      FreudenthalBoundary D (C.chargeOf ρ) := by
  unfold IsBoundaryOperator FreudenthalBoundary
  constructor
  · rintro ⟨hI, hρ⟩
    exact
      ⟨by simpa [C.invariant_eq_quartic ρ] using hI,
       (C.nonzero_iff_charge_nonzero ρ).1 hρ⟩
  · rintro ⟨hQ, hQnonzero⟩
    exact
      ⟨by simpa [C.invariant_eq_quartic ρ] using hQ,
       (C.nonzero_iff_charge_nonzero ρ).2 hQnonzero⟩
end

/--
A chart induces an operator-first black-hole/qubit dictionary.

The GHZ/boundary language remains operatorial; the Freudenthal charge is only
the invariant carrier.
-/
def dictionaryOfFreudenthalChart
    {D : CubicJordanDatum J}
    (C : OperatorFreudenthalChart (E := E) (J := J) D) :
    BlackHoleQubitOperatorDictionary (E := E) where
  invariant := C.invariant

  GHZOperator := fun ρ =>
    FreudenthalRegular D (C.chargeOf ρ)

  BoundaryOperator := fun ρ =>
    FreudenthalBoundary D (C.chargeOf ρ)

  ghz_iff_regular := by
    intro ρ
    exact (chart_regular_iff C ρ).symm

  boundary_iff_quartic_boundary := by
    intro ρ
    exact (chart_boundary_iff C ρ).symm

  entropy := fun ρ =>
    entropyReadout C.invariant ρ

  entropy_eq_invariant_readout := by
    intro ρ
    rfl

/--
Freudenthal boundary surgery packet.

This is the next algebraic boundary: once the Freudenthal quartic collapses,
a detector operator is required, together with a Drazin inverse relation.
-/
structure FreudenthalBoundarySurgery
    {D : CubicJordanDatum J}
    (C : OperatorFreudenthalChart (E := E) (J := J) D) where
  /-- Boundary detector associated to an operator state. -/
  detector : EndH → EndH

  /-- Drazin inverse assigned at the boundary. -/
  drazinInverseAtBoundary : EndH → EndH

  /-- Boundary states admit Drazin surgery. -/
  boundary_has_drazin :
    ∀ ρ : EndH,
      FreudenthalBoundary D (C.chargeOf ρ) →
        InfoGeometry.Application.STUOperator.IsDrazinInverse
          (detector ρ)
          (drazinInverseAtBoundary ρ)

  /-- Core-compressed post-surgery state. -/
  postSurgeryState :
    ∀ ρ : EndH,
      FreudenthalBoundary D (C.chargeOf ρ) →
        EndH :=
    fun ρ _ =>
      drazinCoreCompression
        (detector ρ)
        (drazinInverseAtBoundary ρ)
        ρ

end Hilbert

end InfoGeometry.Application.OperatorFreudenthalBoundary
