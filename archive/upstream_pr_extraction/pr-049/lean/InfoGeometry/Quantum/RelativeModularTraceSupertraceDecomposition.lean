import Mathlib.LinearAlgebra.Trace

/-!
# Balanced two-sheet trace/supertrace decomposition

For equal-dimensional sheets this is the algebraic scalar decomposition behind
ordinary trace versus graded trace.  It deliberately does not identify an
ordinary block matrix with a full supermatrix Berezinian.
-/

namespace InfoGeometry.Quantum.RelativeModularTraceSupertraceDecomposition

noncomputable section

variable {𝕜 H : Type*} [Field 𝕜] [CharZero 𝕜]
  [AddCommGroup H] [Module 𝕜 H]
  [Module.Free 𝕜 H] [Module.Finite 𝕜 H]

local notation "EndH" => Module.End 𝕜 H

def commonTraceScalar (A B : EndH) : 𝕜 :=
  (LinearMap.trace 𝕜 H A + LinearMap.trace 𝕜 H B) /
    (2 * (Module.finrank 𝕜 H : 𝕜))

def relativeTraceScalar (A B : EndH) : 𝕜 :=
  (LinearMap.trace 𝕜 H A - LinearMap.trace 𝕜 H B) /
    (2 * (Module.finrank 𝕜 H : 𝕜))

def commonRemainder (A B : EndH) : EndH :=
  A - (commonTraceScalar A B + relativeTraceScalar A B) • LinearMap.id

def relativeRemainder (A B : EndH) : EndH :=
  B - (commonTraceScalar A B - relativeTraceScalar A B) • LinearMap.id

theorem common_relative_reconstruct (A B : EndH) :
    commonTraceScalar A B + relativeTraceScalar A B =
      (LinearMap.trace 𝕜 H A) / (Module.finrank 𝕜 H : 𝕜) := by
  unfold commonTraceScalar relativeTraceScalar
  field_simp
  ring

theorem common_relative_reconstruct' (A B : EndH) :
    commonTraceScalar A B - relativeTraceScalar A B =
      (LinearMap.trace 𝕜 H B) / (Module.finrank 𝕜 H : 𝕜) := by
  unfold commonTraceScalar relativeTraceScalar
  field_simp
  ring

theorem trace_common_mode (A B : EndH)
    (hn : (Module.finrank 𝕜 H : 𝕜) ≠ 0) :
    LinearMap.trace 𝕜 H A + LinearMap.trace 𝕜 H B =
      (2 * (Module.finrank 𝕜 H : 𝕜)) * commonTraceScalar A B := by
  unfold commonTraceScalar
  field_simp [hn]

theorem trace_relative_mode (A B : EndH)
    (hn : (Module.finrank 𝕜 H : 𝕜) ≠ 0) :
    LinearMap.trace 𝕜 H A - LinearMap.trace 𝕜 H B =
      (2 * (Module.finrank 𝕜 H : 𝕜)) * relativeTraceScalar A B := by
  unfold relativeTraceScalar
  field_simp [hn]

theorem commonRemainder_trace_zero (A B : EndH)
    (hn : (Module.finrank 𝕜 H : 𝕜) ≠ 0) :
    LinearMap.trace 𝕜 H (commonRemainder A B) = 0 := by
  rw [commonRemainder, map_sub, map_smul, LinearMap.trace_id]
  rw [common_relative_reconstruct A B]
  field_simp [hn]
  simp [smul_eq_mul, hn]

theorem relativeRemainder_trace_zero (A B : EndH)
    (hn : (Module.finrank 𝕜 H : 𝕜) ≠ 0) :
    LinearMap.trace 𝕜 H (relativeRemainder A B) = 0 := by
  rw [relativeRemainder, map_sub, map_smul, LinearMap.trace_id]
  rw [common_relative_reconstruct' A B]
  field_simp [hn]
  simp [smul_eq_mul, hn]

theorem balanced_decomposition (A B : EndH) :
    A = (commonTraceScalar A B + relativeTraceScalar A B) • LinearMap.id
        + commonRemainder A B ∧
    B = (commonTraceScalar A B - relativeTraceScalar A B) • LinearMap.id
        + relativeRemainder A B := by
  constructor <;> simp [commonRemainder, relativeRemainder]

end
end InfoGeometry.Quantum.RelativeModularTraceSupertraceDecomposition
