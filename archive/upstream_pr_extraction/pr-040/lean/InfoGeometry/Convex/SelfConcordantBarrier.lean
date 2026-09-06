import Mathlib.Tactic
import InfoGeometry.Canonical.BregmanAnalyticBound
import InfoGeometry.Analysis.BregmanAnalyticBound

noncomputable section

/-!
# Noncommutative Self-Concordant Barrier and Matrix Dikin Bounds

This file keeps the self-concordant/Dikin lane in the finite matrix algebra
`Mₙ(ℂ)`.  The real functions `ω` and `ω*` are only scalar readouts of a matrix
Hessian radius; the Bregman divergence and tangent directions are matrix data.

No global axioms are introduced.
-/

namespace InfoGeometry.Convex

/-! ## Dikin radius readouts -/

/-- Lower Dikin readout `ω(t) = t - log(1 + t)`. -/
noncomputable def omegaLow (t : ℝ) : ℝ :=
  t - Real.log (1 + t)

/-- Upper Dikin readout `ω*(t) = -t - log(1 - t)`; used when `t < 1`. -/
noncomputable def omegaHigh (t : ℝ) : ℝ :=
  -t - Real.log (1 - t)

/-- `ω(t)` is nonnegative on its natural domain `-1 < t`. -/
theorem omegaLow_nonneg (t : ℝ) (ht : -1 < t) :
    0 ≤ omegaLow t := by
  unfold omegaLow
  have h_exp : 1 + t ≤ Real.exp t := by
    simpa [add_comm] using Real.add_one_le_exp t
  have h_pos : 0 < 1 + t := by linarith only [ht]
  have h_log : Real.log (1 + t) ≤ t := by
    calc
      Real.log (1 + t) ≤ Real.log (Real.exp t) := Real.log_le_log h_pos h_exp
      _ = t := Real.log_exp t
  linarith

@[simp]
theorem omegaLow_zero :
    omegaLow 0 = 0 := by
  simp [omegaLow]

/-! ## Matrix self-concordant barrier carrier -/

/--
A self-concordant barrier on the noncommutative matrix algebra `Mₙ(ℂ)`.

The local fields are parameters because the analytic work depends on the
chosen cone, trace pairing, and Hessian model.  The carrier is nevertheless
matrix-native: both points and tangent directions are `InfoGeometry.Analysis.BregmanAnalyticBound.MatrixEnd n`.
-/
structure NoncommutativeSelfConcordantBarrier (n : ℕ) (ν : ℝ) where
  hν_pos : ν > 0
  potential : InfoGeometry.Analysis.BregmanAnalyticBound.MatrixEnd n → ℝ
  gradient : InfoGeometry.Analysis.BregmanAnalyticBound.MatrixEnd n → InfoGeometry.Analysis.BregmanAnalyticBound.MatrixEnd n
  bregmanDiv : InfoGeometry.Analysis.BregmanAnalyticBound.MatrixEnd n → InfoGeometry.Analysis.BregmanAnalyticBound.MatrixEnd n → ℝ
  localRadiusSq : InfoGeometry.Analysis.BregmanAnalyticBound.MatrixEnd n → InfoGeometry.Analysis.BregmanAnalyticBound.MatrixEnd n → ℝ
  localRadiusSq_nonneg : ∀ x h, 0 ≤ localRadiusSq x h
  selfConcordantEstimate :
    ∀ x h,
      omegaLow (Real.sqrt (localRadiusSq x h)) ≤ bregmanDiv (x + h) x ∧
        (Real.sqrt (localRadiusSq x h) < 1 →
          bregmanDiv (x + h) x ≤
            omegaHigh (Real.sqrt (localRadiusSq x h)))

namespace NoncommutativeSelfConcordantBarrier

variable {n : ℕ} {ν : ℝ}
variable (ψ : NoncommutativeSelfConcordantBarrier n ν)

/-- Lower half of the matrix self-concordant Dikin sandwich. -/
theorem dikin_lower (x h : InfoGeometry.Analysis.BregmanAnalyticBound.MatrixEnd n) :
    omegaLow (Real.sqrt (ψ.localRadiusSq x h)) ≤
      ψ.bregmanDiv (x + h) x :=
  (ψ.selfConcordantEstimate x h).1

/-- Upper half of the matrix self-concordant Dikin sandwich. -/
theorem dikin_upper (x h : InfoGeometry.Analysis.BregmanAnalyticBound.MatrixEnd n)
    (hsmall : Real.sqrt (ψ.localRadiusSq x h) < 1) :
    ψ.bregmanDiv (x + h) x ≤
      omegaHigh (Real.sqrt (ψ.localRadiusSq x h)) :=
  (ψ.selfConcordantEstimate x h).2 hsmall

end NoncommutativeSelfConcordantBarrier

/-- Dikin lower bound on a matrix tangent step. -/
def MatrixDikinLowerBound (n : ℕ)
    (ψ : NoncommutativeSelfConcordantBarrier n 1)
    (x h : InfoGeometry.Analysis.BregmanAnalyticBound.MatrixEnd n) : Prop :=
  ψ.localRadiusSq x h < 1 ∧
    omegaLow (Real.sqrt (ψ.localRadiusSq x h)) ≤ ψ.bregmanDiv (x + h) x

/-- Dikin upper bound on a matrix tangent step. -/
def MatrixDikinUpperBound (n : ℕ)
    (ψ : NoncommutativeSelfConcordantBarrier n 1)
    (x h : InfoGeometry.Analysis.BregmanAnalyticBound.MatrixEnd n) : Prop :=
  Real.sqrt (ψ.localRadiusSq x h) < 1 ∧
    ψ.bregmanDiv (x + h) x ≤ omegaHigh (Real.sqrt (ψ.localRadiusSq x h))

/--
Matrix Dikin lower/upper bounds induce the matrix envelope consumed by
`Analysis/BregmanAnalyticBound.lean`.
-/
def toMatrixDikinEnvelope {n : ℕ}
    (ψ : NoncommutativeSelfConcordantBarrier n 1)
    (hLower :
      ∀ x h, omegaLow (Real.sqrt (ψ.localRadiusSq x h)) ≤ ψ.bregmanDiv (x + h) x)
    (hUpper :
      ∀ x h, Real.sqrt (ψ.localRadiusSq x h) < 1 →
        ψ.bregmanDiv (x + h) x ≤
          omegaHigh (Real.sqrt (ψ.localRadiusSq x h))) :
    InfoGeometry.Analysis.BregmanAnalyticBound.HasMatrixSelfConcordantDikinEnvelope
      (fun x y => ψ.bregmanDiv x y)
      (fun x y => Real.sqrt (ψ.localRadiusSq y (x - y))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    exact Real.sqrt_nonneg _
  · intro x y
    have hxy : y + (x - y) = x := by
      abel
    simpa [hxy] using hLower y (x - y)
  · intro x y hsmall
    have hxy : y + (x - y) = x := by
      abel
    simpa [hxy] using hUpper y (x - y) hsmall

/--
The matrix self-concordance law carried by a barrier produces the repository's
native matrix Dikin envelope without an additional evidence argument.
-/
def NoncommutativeSelfConcordantBarrier.toMatrixDikinEnvelope
    {n : ℕ}
    (ψ : NoncommutativeSelfConcordantBarrier n 1) :
    InfoGeometry.Analysis.BregmanAnalyticBound.HasMatrixSelfConcordantDikinEnvelope
      (fun x y => ψ.bregmanDiv x y)
      (fun x y => Real.sqrt (ψ.localRadiusSq y (x - y))) :=
  InfoGeometry.Convex.toMatrixDikinEnvelope ψ
    (fun x h => ψ.dikin_lower x h)
    (fun x h hsmall => ψ.dikin_upper x h hsmall)

/-! ## Explicit finite model handoff -/

/--
The concrete `2 × 2` phase-axis finite Dikin estimate already proved in the
canonical finite model.
-/
theorem finite_model_satisfies_dikin
    (ε : ℝ) (hε : |ε| ≤ 1) :
    Real.sqrt
        (2 * ((Real.cos ε - 1) ^ 2 + (Real.sin ε - ε) ^ 2))
      ≤ (2 * Real.sqrt 2) * ε ^ 2 :=
  InfoGeometry.Canonical.BregmanAnalyticBound.bregman_quadratic_bound ε hε

end InfoGeometry.Convex
