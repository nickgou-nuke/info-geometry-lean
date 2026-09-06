import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.EA

/-- A fixed simple eigenvalue for the dominant hidden channel. -/
def simpleEigenvalue : ℝ := -1

/-- The spectral projection coefficient carried by a witness set. -/
def spectralProjection (c : ℝ) : ℝ := c

/-- Phase selection along even and odd subsequences. -/
def phaseSelector (n : ℕ) : ℝ := if Even n then 1 else simpleEigenvalue

/-- The isolated dominant nontrivial contribution. -/
def kernelProjectedTerm (c : ℝ) (n : ℕ) : ℝ := spectralProjection c * phaseSelector n

/-- The second main term is exactly the dominant projected mode. -/
def chebotarevSecondMainTermExpansion (c : ℝ) : Prop :=
  ∀ n : ℕ, kernelProjectedTerm c n = spectralProjection c * phaseSelector n

/-- Even and odd subsequences both retain the full witness magnitude. -/
def chebotarevOscillationLowerBound (c : ℝ) : Prop :=
  ∀ n : ℕ,
    |kernelProjectedTerm c (2 * n)| = |spectralProjection c| ∧
      |kernelProjectedTerm c (2 * n + 1)| = |spectralProjection c|

/-- Paper-facing wrapper for the dominant hidden-channel second main term.
    thm:kernel-chebotarev-second-main-term-witness -/
theorem kernel_chebotarev_second_main_term (c : ℝ) (hc : c ≠ 0) :
  chebotarevSecondMainTermExpansion c ∧
      spectralProjection c ≠ 0 ∧
      chebotarevOscillationLowerBound c := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    rfl
  · simpa [spectralProjection] using hc
  · intro n
    constructor
    · simp [kernelProjectedTerm, spectralProjection, phaseSelector]
    · have hAbs : |simpleEigenvalue| = 1 := by
        norm_num [simpleEigenvalue]
      calc
        |kernelProjectedTerm c (2 * n + 1)| = |spectralProjection c| * |simpleEigenvalue| := by
          simp [kernelProjectedTerm, spectralProjection, phaseSelector]
        _ = |spectralProjection c| := by rw [hAbs, mul_one]

end Omega.EA
