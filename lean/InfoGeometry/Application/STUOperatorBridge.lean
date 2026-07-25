/-
InfoGeometry/Application/STUOperatorBridge.lean

Operator-first STU / black-hole / qubit bridge.

No coordinate amplitudes are primary here.  Coordinate hyperdeterminant
formulas may be added later only through chart theorems.
-/

import Mathlib.Tactic
import InfoGeometry.Meta.Architecture

noncomputable section

open scoped InnerProductSpace

namespace InfoGeometry.Application.STUOperator

section Hilbert

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "EndH" => E →L[ℝ] E

/-! ### 1. Drazin surgery as operator algebra -/

/--
Operator-level Drazin inverse relation.

`A` is the singular or boundary operator.
`D` is the Drazin inverse candidate.

The fields are intentionally operator equations, not coordinate equations.
-/
structure IsDrazinInverse (A D : EndH) : Prop where
  drazin_outer :
    D * A * D = D
  commute :
    A * D = D * A
  drazin_power :
    ∃ k : ℕ, A ^ (k + 1) * D = A ^ k

/-- Regular Drazin projector `P = A D`. -/
def drazinCoreProjector (A D : EndH) : EndH :=
  A * D

/-- Nilpotent or radical projector `N = 1 - A D`. -/
def drazinNilProjector (A D : EndH) : EndH :=
  1 - drazinCoreProjector A D

/-- The Drazin core as an operator range. -/
def drazinCoreSubspace (A D : EndH) : Submodule ℝ E :=
  (drazinCoreProjector A D).toLinearMap.range

/-- The Drazin radical as an operator range. -/
def drazinNilSubspace (A D : EndH) : Submodule ℝ E :=
  (drazinNilProjector A D).toLinearMap.range

section
omit [CompleteSpace E]

theorem drazinCore_add_nil
    (A D : EndH) :
    drazinCoreProjector A D + drazinNilProjector A D = 1 := by
  simp [drazinNilProjector]

theorem drazinNil_add_core
    (A D : EndH) :
    drazinNilProjector A D + drazinCoreProjector A D = 1 := by
  rw [add_comm]
  exact drazinCore_add_nil A D

theorem drazinCoreProjector_idempotent
    {A D : EndH} (hD : IsDrazinInverse A D) :
    drazinCoreProjector A D * drazinCoreProjector A D =
      drazinCoreProjector A D := by
  unfold drazinCoreProjector
  calc
    (A * D) * (A * D)
        = A * (D * A * D) := by
          rw [mul_assoc, ← mul_assoc D A D]
    _ = A * D := by
          rw [hD.drazin_outer]

theorem drazinNilProjector_idempotent
    {A D : EndH} (hD : IsDrazinInverse A D) :
    drazinNilProjector A D * drazinNilProjector A D =
      drazinNilProjector A D := by
  let P := drazinCoreProjector A D
  have hP : P * P = P := drazinCoreProjector_idempotent hD
  unfold drazinNilProjector
  change (1 - P) * (1 - P) = 1 - P
  calc
    (1 - P) * (1 - P)
        = 1 * (1 - P) - P * (1 - P) := by
          rw [sub_mul]
    _ = (1 - P) - (P * 1 - P * P) := by
          rw [one_mul, mul_sub]
    _ = (1 - P) - (P - P * P) := by
          rw [mul_one]
    _ = (1 - P) - (P - P) := by
          rw [hP]
    _ = 1 - P := by
          simp

theorem drazinCore_mul_nil
    {A D : EndH} (hD : IsDrazinInverse A D) :
    drazinCoreProjector A D * drazinNilProjector A D = 0 := by
  let P := drazinCoreProjector A D
  have hP : P * P = P := drazinCoreProjector_idempotent hD
  unfold drazinNilProjector
  change P * (1 - P) = 0
  calc
    P * (1 - P) = P * 1 - P * P := by
      rw [mul_sub]
    _ = P - P := by
      rw [mul_one, hP]
    _ = 0 := by
      simp

theorem drazinNil_mul_core
    {A D : EndH} (hD : IsDrazinInverse A D) :
    drazinNilProjector A D * drazinCoreProjector A D = 0 := by
  let P := drazinCoreProjector A D
  have hP : P * P = P := drazinCoreProjector_idempotent hD
  unfold drazinNilProjector
  change (1 - P) * P = 0
  calc
    (1 - P) * P = 1 * P - P * P := by
      rw [sub_mul]
    _ = P - P := by
      rw [one_mul, hP]
    _ = 0 := by
      simp
end

/-! ### 2. Operator invariants, not coordinate polynomials -/

/--
Operator-level quartic invariant.

For the STU model this is the operator-side object corresponding,
after choosing a chart, to Cayley's hyperdeterminant.

The invariant itself is not a coordinate polynomial here.
-/
structure OperatorQuarticInvariant where
  quartic : EndH → ℝ

  /--
  Similarity invariance under an explicitly supplied inverse.

  This is the operator analogue of SLOCC / duality invariance.
  -/
  conj_invariant :
    ∀ (U Uinv ρ : EndH),
      U * Uinv = 1 →
      Uinv * U = 1 →
      quartic (U * ρ * Uinv) = quartic ρ

/-- Regular operator chamber: nonzero quartic invariant. -/
def IsRegularOperator
    (I : OperatorQuarticInvariant (E := E)) (ρ : EndH) : Prop :=
  I.quartic ρ ≠ 0

/-- Boundary operator chamber: quartic invariant has collapsed. -/
def IsBoundaryOperator
    (I : OperatorQuarticInvariant (E := E)) (ρ : EndH) : Prop :=
  I.quartic ρ = 0 ∧ ρ ≠ 0

/--
Entropy readout from the operator invariant.

This remains an operator readout.  A coordinate formula may later prove that
`I.quartic` agrees with a hyperdeterminant in a selected chart.
-/
def entropyReadout
    (I : OperatorQuarticInvariant (E := E)) (ρ : EndH) : ℝ :=
  Real.pi * Real.sqrt |I.quartic ρ|

/-! ### 3. Operator Fisher / Souriau metric structure -/

/--
Operator-level Fisher metric structure.

The tangent space is the operator algebra `EndH`, not a coordinate vector space.
-/
structure OperatorFisherMetric
    (I : OperatorQuarticInvariant (E := E)) where
  metric :
    EndH → (EndH →L[ℝ] (EndH →L[ℝ] ℝ))

  inverseMetric :
    EndH → (EndH →L[ℝ] EndH)

  dPotential :
    EndH → (EndH →L[ℝ] ℝ)

  gradient :
    EndH → EndH

  gradient_spec :
    ∀ ρ : EndH,
      IsRegularOperator I ρ →
      ∀ δ : EndH,
        metric ρ (gradient ρ) δ = dPotential ρ δ

/--
Operator gradient flow packet.

This does not introduce coordinates.  It stores the vector field and its
gradient equation at the operator level.
-/
structure OperatorGradientFlow
    (I : OperatorQuarticInvariant (E := E)) where
  fisher :
    OperatorFisherMetric I

  vectorField :
    EndH → EndH

  vectorField_eq_negative_gradient :
    ∀ ρ : EndH,
      IsRegularOperator I ρ →
        vectorField ρ = - fisher.gradient ρ

  flow :
    ℝ → EndH → EndH

/-! ### 4. Operator Drazin compression of a state -/

/--
Compress an operator state to the Drazin core.

This is the operator version of “surgery”: keep the regular core and amputate
the radical.
-/
def drazinCoreCompression
    (A D ρ : EndH) : EndH :=
  let P := drazinCoreProjector A D
  P * ρ * P

/--
Extract the nilpotent/radical part of an operator state.
-/
def drazinNilCompression
    (A D ρ : EndH) : EndH :=
  let N := drazinNilProjector A D
  N * ρ * N

/--
Surgery packet at an operator boundary.

`A` is the singular operator detecting the rank collapse.
`D` is its Drazin inverse relation.
`ρ` is the state/operator being compressed.
-/
structure OperatorSurgeryPacket where
  state :
    EndH

  singularOperator :
    EndH

  drazinInverse :
    EndH

  drazin_inverse :
    IsDrazinInverse singularOperator drazinInverse

  coreState :
    EndH :=
      drazinCoreCompression singularOperator drazinInverse state

  radicalState :
    EndH :=
      drazinNilCompression singularOperator drazinInverse state

/-! ### 5. Black-hole/qubit dictionary as an operator structure -/

/--
Operator-first black-hole/qubit dictionary.

No amplitudes appear here.  The GHZ/W terminology is mediated by operator
invariants and boundary predicates.
-/
structure BlackHoleQubitOperatorDictionary where
  invariant :
    OperatorQuarticInvariant (E := E)

  GHZOperator :
    EndH → Prop

  BoundaryOperator :
    EndH → Prop

  ghz_iff_regular :
    ∀ ρ : EndH,
      GHZOperator ρ ↔ IsRegularOperator invariant ρ

  boundary_iff_quartic_boundary :
    ∀ ρ : EndH,
      BoundaryOperator ρ ↔ IsBoundaryOperator invariant ρ

  entropy :
    EndH → ℝ

  entropy_eq_invariant_readout :
    ∀ ρ : EndH,
      entropy ρ = entropyReadout invariant ρ

/--
Decoherence as operator surgery.

This is the operator-level statement.  A coordinate GHZ/W diagram can be
derived later only after choosing a chart.
-/
structure DecoherenceAsDrazinSurgery
    (Dict : BlackHoleQubitOperatorDictionary (E := E)) where
  decoherenceFlow :
    ℝ → EndH → EndH

  detector :
    EndH → EndH

  drazinInverseAtBoundary :
    EndH → EndH

  hits_boundary :
    ∀ ρ : EndH,
      Dict.GHZOperator ρ →
        ∃ t_c > 0,
          Dict.BoundaryOperator (decoherenceFlow t_c ρ)

  surgery_at_boundary :
    ∀ ρ : EndH,
      Dict.BoundaryOperator ρ →
        IsDrazinInverse
          (detector ρ)
          (drazinInverseAtBoundary ρ)

  post_surgery_state :
    ∀ ρ : EndH,
      Dict.BoundaryOperator ρ →
        EndH :=
    fun ρ _ =>
      drazinCoreCompression
        (detector ρ)
        (drazinInverseAtBoundary ρ)
        ρ

/-! ### 6. Coordinates only as optional charts -/

/--
Optional coordinate chart.

This is the only place where Cayley hyperdeterminants, STU amplitudes,
or concrete coordinate polynomials should enter.
-/
structure OperatorCoordinateChart
    (Coord : Type*)
    (I : OperatorQuarticInvariant (E := E)) where
  toCoord :
    EndH → Coord

  coordInvariant :
    Coord → ℝ

  invariant_eq_coordInvariant :
    ∀ ρ : EndH,
      I.quartic ρ = coordInvariant (toCoord ρ)

end Hilbert

end InfoGeometry.Application.STUOperator
