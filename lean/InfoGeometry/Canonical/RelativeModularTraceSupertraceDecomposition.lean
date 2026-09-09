import InfoGeometry.Lie.CanonicalZornDerivation
import InfoGeometry.Lie.CanonicalZornDerivationTrace
import InfoGeometry.Jordan.LogDet
import InfoGeometry.Jordan.BurgStein

namespace InfoGeometry.Canonical.RelativeModularTraceSupertraceDecomposition

open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.CanonicalZornDerivationTrace
open InfoGeometry.Jordan
open Matrix
open scoped MatrixOrder

/-- Every canonical Zorn derivation has trace zero (re-exported with capstone name). -/
theorem derivation_trace_zero
    (D : canonicalZornDerivations) :
    LinearMap.trace ℝ CZ (D : EndCZ) = 0 := by
  exact canonicalZornDerivation_trace_zero D

/-- The Burg / Stein divergence on SPD matrices. -/
noncomputable abbrev burgDivergence {n : ℕ} (X Y : SPD n) : ℝ :=
  steinLoss X Y

/-- The Burg/Stein divergence on SPD splits as trace distortion plus
    log-determinant barrier difference. -/
theorem burgStein_split {n : ℕ} (X Y : SPD n) :
    burgDivergence X Y =
      (Matrix.trace (normalizedDistortion X Y) - (n : ℝ)) +
      (logDetBarrier X - logDetBarrier Y) := by
  have h₁ : burgDivergence X Y = Matrix.trace (normalizedDistortion X Y) + logDetBarrier X - logDetBarrier Y - (n : ℝ) :=
    steinLoss_eq_trace_add_barrier_diff_sub_dim X Y
  linarith

/-- Trace distortion part: tr(Y⁻¹X) - n. -/
noncomputable def traceDistortionPart {n : ℕ} (X Y : SPD n) : ℝ :=
  Matrix.trace (normalizedDistortion X Y) - (n : ℝ)

/-- When the determinant of the normalized distortion is 1, the
    Burg/Stein divergence equals the trace distortion part.
    The determinant-only (volume) barrier vanishes, but the trace
    distortion can remain non-zero — shape deformation with zero
    volume surprisal but non-trivial statistical divergence. -/
theorem shape_deformation_nonzero_divergence {n : ℕ} (X Y : SPD n)
    (h_det : Matrix.det (normalizedDistortion X Y) = 1) :
    burgDivergence X Y = traceDistortionPart X Y := by
  have h₁ : burgDivergence X Y = traceDistortionPart X Y + (logDetBarrier X - logDetBarrier Y) := by
    calc
      burgDivergence X Y = (Matrix.trace (normalizedDistortion X Y) - (n : ℝ)) + (logDetBarrier X - logDetBarrier Y) :=
        burgStein_split X Y
      _ = traceDistortionPart X Y + (logDetBarrier X - logDetBarrier Y) := by
        simp [traceDistortionPart]
  have h₂ : logDetBarrier X - logDetBarrier Y = 0 := by
    have h₃ : Real.log (Matrix.det (normalizedDistortion X Y)) = 0 := by
      rw [h_det]
      simp
    have h₄ : Real.log (Matrix.det (normalizedDistortion X Y)) = -(logDetBarrier X - logDetBarrier Y) := by
      have hX : Matrix.det X.mat ≠ 0 := X.det_ne_zero
      have hY : Matrix.det Y.mat ≠ 0 := Y.det_ne_zero
      have h₅ : Matrix.det (normalizedDistortion X Y) = Matrix.det X.mat / Matrix.det Y.mat := by
        rw [normalizedDistortion_det]
      calc
        Real.log (Matrix.det (normalizedDistortion X Y)) = Real.log (Matrix.det X.mat / Matrix.det Y.mat) := by rw [h₅]
        _ = Real.log (Matrix.det X.mat) - Real.log (Matrix.det Y.mat) := by
          have h₆ : 0 < Matrix.det X.mat := X.det_pos
          have h₇ : 0 < Matrix.det Y.mat := Y.det_pos
          rw [Real.log_div (by positivity) (by positivity)]
        _ = -(-Real.log (Matrix.det X.mat)) + (-Real.log (Matrix.det Y.mat)) := by ring
        _ = -(logDetBarrier X - logDetBarrier Y) := by
          simp [logDetBarrier]
          ring
    linarith
  linarith

/-- Foundational capstone: every Zorn derivation is trace-free, and
    determinant-one deformations retain non-trivial trace distortion. -/
theorem relative_modular_trace_supertrace_capstone :
    (∀ (D : canonicalZornDerivations), LinearMap.trace ℝ CZ (D : EndCZ) = 0) ∧
    (∀ {n : ℕ} (X Y : SPD n), Matrix.det (normalizedDistortion X Y) = 1 →
        burgDivergence X Y = traceDistortionPart X Y) := by
  refine' ⟨fun D => derivation_trace_zero D, _⟩
  intro n X Y h
  exact shape_deformation_nonzero_divergence X Y h

end InfoGeometry.Canonical.RelativeModularTraceSupertraceDecomposition
