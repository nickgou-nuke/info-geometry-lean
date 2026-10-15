import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.SpecialFunctions.Exp
import InfoGeometry.Canonical.InfoTreeGaugeHomotopy

/-!
# Proof-artifact holonomy as audit metadata

This module formalizes algebraic score propagation for externally supplied
nonnegative defect data. The score is metadata for audit and scheduling; it is
not a probability of correctness and cannot discharge a theorem. Propositions
are discharged directly by Lean proof terms; audit receipts do not wrap or
promote them.
-/

namespace InfoGeometry.Canonical.ProofArtifactHolonomyAudit

/-- An audit receipt records an identifier and a supplied nonnegative defect.
The defect's calibration is external and is not inferred from Lean proofs. -/
structure AuditReceipt where
  artifactId : String
  defect : ℝ
  defect_nonneg : 0 ≤ defect

/-- Exponential score associated to the externally supplied defect. -/
noncomputable def AuditReceipt.score (r : AuditReceipt) : ℝ :=
  Real.exp (-r.defect)

theorem AuditReceipt.score_pos (r : AuditReceipt) : 0 < r.score :=
  Real.exp_pos _

theorem AuditReceipt.score_le_one (r : AuditReceipt) : r.score ≤ 1 := by
  unfold score
  have hneg : -r.defect ≤ 0 := by linarith [r.defect_nonneg]
  have h := Real.exp_le_exp_of_le hneg
  simpa using h

/-- Composing two audit records adds their supplied defects. -/
def AuditReceipt.compose (r s : AuditReceipt) : AuditReceipt where
  artifactId := r.artifactId ++ "/" ++ s.artifactId
  defect := r.defect + s.defect
  defect_nonneg := add_nonneg r.defect_nonneg s.defect_nonneg

/-- Additive defect makes the associated exponential score multiplicative. -/
theorem AuditReceipt.score_compose (r s : AuditReceipt) :
    (r.compose s).score = r.score * s.score := by
  change Real.exp (-(r.defect + s.defect)) =
    Real.exp (-r.defect) * Real.exp (-s.defect)
  rw [neg_add, Real.exp_add]

/-- Product of local and upstream audit scores. The set of upstream artifacts
must represent distinct dependency contributions; shared ancestors should be
deduplicated before aggregation. -/
def effectiveScore {ι : Type*} (localScore : ℝ) (upstream : Finset ι)
    (score : ι → ℝ) : ℝ :=
  localScore * ∏ i ∈ upstream, score i

/-- If every factor is in `[0,1]`, their finite aggregate cannot exceed one of
the included upstream factors (the weakest-link bound). -/
theorem effectiveScore_le_upstream {ι : Type*} [DecidableEq ι]
    (localScore : ℝ) (upstream : Finset ι) (score : ι → ℝ)
    (hlocal : 0 ≤ localScore ∧ localScore ≤ 1)
    (hscores : ∀ i ∈ upstream, 0 ≤ score i ∧ score i ≤ 1)
    {i : ι} (hi : i ∈ upstream) :
    effectiveScore localScore upstream score ≤ score i := by
  unfold effectiveScore
  rw [← Finset.mul_prod_erase upstream score hi]
  have hrest_nonneg : 0 ≤ ∏ j ∈ upstream.erase i, score j :=
    Finset.prod_nonneg fun j hj => (hscores j (Finset.mem_of_mem_erase hj)).1
  have hrest_le : ∏ j ∈ upstream.erase i, score j ≤ 1 :=
    Finset.prod_le_one₀
      (fun j hj => (hscores j (Finset.mem_of_mem_erase hj)).1)
      (fun j hj => (hscores j (Finset.mem_of_mem_erase hj)).2)
  have htail_le : localScore * ∏ j ∈ upstream.erase i, score j ≤ 1 := by
    calc
      localScore * ∏ j ∈ upstream.erase i, score j ≤ localScore * 1 :=
        mul_le_mul_of_nonneg_left hrest_le hlocal.1
      _ ≤ 1 := by simpa using hlocal.2
  calc
    localScore * (score i * ∏ j ∈ upstream.erase i, score j) =
        score i * (localScore * ∏ j ∈ upstream.erase i, score j) := by ring
    _ ≤ score i := mul_le_of_le_one_right (hscores i hi).1 htail_le

end InfoGeometry.Canonical.ProofArtifactHolonomyAudit
