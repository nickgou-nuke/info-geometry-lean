import InfoGeometry.Canonical.SingularDecompositionSurrogate
import InfoGeometry.Canonical.GlobalChiralDecomposition
import InfoGeometry.Canonical.RelativeModularScaleShapeSplit
import InfoGeometry.Canonical.InverseKernelAlgebra
import InfoGeometry.Canonical.RelativeModularBlockDiagonalCore
import Mathlib.Tactic.NoncommRing

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.CapstoneSemanticAudit

Lean-native semantic audit helpers for the current canonical capstones.

This file provides:
1. explicit axiom-surface print checks for the three capstone theorems,
2. a non-vacuity degeneration lemma for the zero-apex regime,
3. a similarity-equivariance lemma for the idempotent+commutation hypotheses
   behind block-diagonal decoupling.
-/

-- Axiom-hygiene surface for the three capstone targets.
#print axioms InfoGeometry.Canonical.SingularDecompositionSurrogate.singular_decomposition_surrogate_package_of_commute
#print axioms InfoGeometry.Canonical.GlobalChiralDecomposition.singular_polar_surrogate_closure
#print axioms InfoGeometry.Canonical.RelativeModularScaleShapeSplit.relativeModular_scaleShapeSplit

namespace InfoGeometry.Canonical.CapstoneSemanticAudit

open InfoGeometry.Krein
open InfoGeometry.Canonical
open InfoGeometry.Canonical.GlobalChiralDecomposition
open InfoGeometry.Canonical.RelativeModularBlockDiagonalCore

section Core

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance

/--
Vacuum/non-defect specialization:
if the apex projector vanishes, the active spectral projector is the identity.
-/
@[rep_depth transport]
theorem spectralProjector_eq_one_of_apex_zero
    (CIK : CertifiedInverseKernel H₂)
    (hApex : CIK.spectralComplementaryProjector = 0) :
    CIK.spectralProjector = (1 : EndH) := by
  calc
    CIK.spectralProjector
        = CIK.spectralProjector + CIK.spectralComplementaryProjector := by
            simp [hApex]
    _ = (1 : EndH) := CIK.spectralProjector_add_spectralComplementaryProjector

/--
Non-vacuity degeneration:
under the same commutation witness, CP-003 active/apex split collapses to the
active block when the apex projector is zero.
-/
@[rep_depth transport]
theorem global_active_apex_decomposition_reduces_to_active_of_apex_zero
    (CIK : CertifiedInverseKernel H₂)
    (R : EndH)
    (hComm : Commute CIK.spectralProjector R)
    (hApex : CIK.spectralComplementaryProjector = 0) :
    R = CIK.spectralProjector * R * CIK.spectralProjector := by
  have hSplit :=
    global_active_apex_decomposition (E := E) (CIK := CIK) (R := R) hComm
  calc
    R =
      CIK.spectralComplementaryProjector * R * CIK.spectralComplementaryProjector
        +
      CIK.spectralProjector * R * CIK.spectralProjector := hSplit
    _ = 0 + CIK.spectralProjector * R * CIK.spectralProjector := by
          simp [hApex]
    _ = CIK.spectralProjector * R * CIK.spectralProjector := by simp

/--
Similarity transport preserves the idempotence+commutation witness package used
by block-diagonal decoupling.
-/
@[rep_depth transport]
theorem similarity_preserves_idempotent_and_commute
    (P R U Uinv : EndH)
    (hP : P * P = P)
    (hComm : Commute P R)
    (hInvL : Uinv * U = 1) :
    let P' := U * P * Uinv
    let R' := U * R * Uinv
    P' * P' = P' ∧ Commute P' R' := by
  intro P' R'
  constructor
  · calc
      P' * P' = U * P * Uinv * (U * P * Uinv) := rfl
      _ = U * P * (Uinv * U) * P * Uinv := by noncomm_ring
      _ = U * P * (1 : EndH) * P * Uinv := by rw [hInvL]
      _ = U * (P * P) * Uinv := by noncomm_ring
      _ = U * P * Uinv := by rw [hP]
      _ = P' := rfl
  · calc
      P' * R' = U * P * Uinv * (U * R * Uinv) := rfl
      _ = U * P * (Uinv * U) * R * Uinv := by noncomm_ring
      _ = U * P * (1 : EndH) * R * Uinv := by rw [hInvL]
      _ = U * (P * R) * Uinv := by noncomm_ring
      _ = U * (R * P) * Uinv := by rw [hComm.eq]
      _ = U * R * ((Uinv * U) * P) * Uinv := by
            rw [hInvL]
            simp [mul_assoc]
      _ = U * R * (Uinv * U) * P * Uinv := by simp [mul_assoc]
      _ = U * R * Uinv * (U * P * Uinv) := by simp [mul_assoc]
      _ = R' * P' := rfl

/--
Gauge/similarity specialization of block decoupling:
off-diagonal blocks still vanish after similarity transport of `(P, R)`.
-/
@[rep_depth transport]
theorem block_diagonal_of_commute_idempotent_similarity
    (P R U Uinv : EndH)
    (hP : P * P = P)
    (hComm : Commute P R)
    (hInvL : Uinv * U = 1) :
    let P' := U * P * Uinv
    let R' := U * R * Uinv
    ((1 : EndH) - P') * R' * P' = 0
      ∧
    P' * R' * ((1 : EndH) - P') = 0 := by
  intro P' R'
  have hPR :
      P' * P' = P'
        ∧
      Commute P' R' :=
    similarity_preserves_idempotent_and_commute
      (P := P) (R := R) (U := U) (Uinv := Uinv)
      hP hComm hInvL
  exact
    block_diagonal_of_commute_idempotent
      (E := E) (P := P') (R := R') hPR.1 hPR.2

end Core

end InfoGeometry.Canonical.CapstoneSemanticAudit
