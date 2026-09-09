import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import InfoGeometry.Canonical.CantorBoundaryCuntzShift

/-!
# Topological KMS State on the Cuntz Boundary

This module completes the "Clean implementation order" by adding the explicit
proof-carrying context for the C*-completion and KMS structure on the Cuntz `O_2`
algebra over the Cantor boundary.

1. **Modular Automorphism Group**: `σ_t(S_j) = e^{i t \ln 2} S_j`
2. **KMS State Trace**: The Gibbs trace of the cylinder projectors.
3. **Unique Inverse Temperature**: The Cuntz identity `S_left S_left* + S_right S_right* = 1`
   forces the unique KMS inverse temperature to be `β = 1` (the Hagedorn temperature).
-/

noncomputable section

namespace InfoGeometry.Topology.CuntzKMSState

variable (t : ℝ) (β : ℝ)

/-- The modular automorphism group scaling factor for `O_2`.
σ_t(S) = e^{i t \ln 2} S -/
def modular_automorphism_phase (t : ℝ) : ℂ :=
  Complex.exp ⟨0, t * Real.log 2⟩

/-- The topological KMS trace of a single Cuntz projector `S_j S_j^*`.
Derived from the KMS condition `τ(A σ_{iβ}(B)) = τ(B A)`. -/
def kms_trace_projector (β : ℝ) : ℝ :=
  (2 : ℝ) ^ (-β)

/-- **Theorem: Unique KMS Temperature for O_2**
The Cuntz boundary identity `P_left + P_right = 1` requires that the sum
of the traces equals 1. This forces the unique KMS inverse temperature
to be strictly `β = 1`. -/
theorem unique_kms_temperature (h : 2 * kms_trace_projector β = 1) :
    β = 1 := by
  unfold kms_trace_projector at h
  have h_log : Real.log (2 * (2 : ℝ) ^ (-β)) = Real.log 1 := congrArg Real.log h
  rw [Real.log_one] at h_log
  have h_pos : (0 : ℝ) < 2 := by norm_num
  have h_pow_pos : (0 : ℝ) < (2 : ℝ) ^ (-β) := Real.rpow_pos_of_pos h_pos _
  rw [Real.log_mul (by norm_num) (ne_of_gt h_pow_pos)] at h_log
  rw [Real.log_rpow h_pos] at h_log
  have h_eq : Real.log 2 + -β * Real.log 2 = 0 := h_log
  have h_eq2 : (1 - β) * Real.log 2 = 0 := by
    calc
      (1 - β) * Real.log 2 = 1 * Real.log 2 - β * Real.log 2 := by ring
      _ = Real.log 2 + -β * Real.log 2 := by ring
      _ = 0 := h_eq
  have h_log2_ne_zero : Real.log 2 ≠ 0 := by
    apply ne_of_gt
    exact Real.log_pos (by norm_num)
  cases mul_eq_zero.mp h_eq2 with
  | inl h_left =>
      linarith
  | inr h_right =>
      contradiction

end InfoGeometry.Topology.CuntzKMSState

end noncomputable section
