import InfoGeometry.Canonical.DeformedIdeleAction

/-!
# Deformed Idele Action Bridge

This file packages the finite algebraic corridor from
`InfoGeometry.Canonical.DeformedIdeleAction` into a conservative witness
bridge.

It keeps the split explicit:

* branch and adjoint branch values are tracked directly;
* the source-side isometry is a hypothesis;
* the range mismatch is an explicit hypothesis;
* the commutator is nonzero only under that mismatch.

The full idele-deformation narrative remains external evidence.
-/

noncomputable section

namespace DeformedIdeleActionBridge

/-- Lean-carrying status of the deformation claim. -/
inductive DeformedIdeleClaimStatus where
  | kernelProjectionReadout
  | externalEvidenceRequired
deriving DecidableEq, Repr

/-- The conservative status of the full idele deformation claim. -/
def claimStatus : DeformedIdeleClaimStatus := .externalEvidenceRequired

@[simp] theorem claimStatus_external :
    claimStatus = .externalEvidenceRequired := by
  rfl

/--
Finite witness packet for a branch operator and its adjoint.

This is intentionally generic: the bridge only uses the algebraic hypotheses
explicitly supplied to it.
-/
structure DeformedIdeleWitness (A : Type*) [Ring A] [StarRing A] where
  branch : A
  branchAdj : A
  source_isometry : branchAdj * branch = (1 : A)
  range_mismatch : branch * branchAdj ≠ (1 : A)
  status : DeformedIdeleClaimStatus

/--
The branch projector is idempotent once the explicit projection hypothesis is
provided.
-/
theorem branchProjection_idempotent
    {A : Type*} [Ring A] [StarRing A]
    (w : DeformedIdeleWitness A)
    (hproj : w.branch * w.branchAdj * (w.branch * w.branchAdj) = w.branch * w.branchAdj) :
    (w.branch * w.branchAdj) * (w.branch * w.branchAdj) = w.branch * w.branchAdj := by
  simpa [mul_assoc] using hproj

/--
The commutator is nonzero whenever the source side is an isometry and the range
projection is not the unit.
-/
theorem commutator_ne_zero_of_range_mismatch
    {A : Type*} [Ring A] [StarRing A]
    (w : DeformedIdeleWitness A) :
    w.branch * w.branchAdj - w.branchAdj * w.branch ≠ 0 := by
  have hcomm :
      w.branch * w.branchAdj - w.branchAdj * w.branch = w.branch * w.branchAdj - 1 := by
    rw [w.source_isometry]
  rw [hcomm]
  intro h
  exact w.range_mismatch (sub_eq_zero.mp h)

end DeformedIdeleActionBridge
