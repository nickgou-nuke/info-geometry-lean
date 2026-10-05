import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace InfoGeometry.Spectrometry.NormalizedAngularCoordinate

noncomputable section

open Real

section Normalization

def normalizedAngularFactor (W W₀ : ℝ) : ℝ := W / W₀

def coincidenceRate
    (A P12 ε₁ ε₂ W : ℝ) : ℝ := A * P12 * ε₁ * ε₂ * W

def normalizedCoincidence
    (A P12 ε₁ ε₂ W W₀ : ℝ) : ℝ :=
  coincidenceRate A P12 ε₁ ε₂ W / W₀

theorem normalized_coincidence_factorization
    (A P12 ε₁ ε₂ W W₀ : ℝ) (hW₀ : W₀ ≠ 0) :
    normalizedCoincidence A P12 ε₁ ε₂ W W₀ =
      (A * P12 * ε₁ * ε₂) * normalizedAngularFactor W W₀ := by
  dsimp [normalizedCoincidence, coincidenceRate, normalizedAngularFactor]
  field_simp [hW₀]

theorem normalized_coincidence_nonneg
    (A P12 ε₁ ε₂ W W₀ : ℝ)
    (hW₀ : 0 < W₀)
    (hbase : 0 ≤ A * P12 * ε₁ * ε₂)
    (hfactor : 0 ≤ normalizedAngularFactor W W₀) :
    0 ≤ normalizedCoincidence A P12 ε₁ ε₂ W W₀ := by
  rw [normalized_coincidence_factorization _ _ _ _ _ _ hW₀.ne']
  exact mul_nonneg hbase hfactor

theorem normalized_root_coordinate
    (A P12 ε₁ ε₂ W W₀ : ℝ)
    (hW₀ : 0 < W₀)
    (hbase : 0 ≤ A * P12 * ε₁ * ε₂) :
    Real.sqrt (normalizedCoincidence A P12 ε₁ ε₂ W W₀) =
      Real.sqrt (A * P12 * ε₁ * ε₂) *
        Real.sqrt (normalizedAngularFactor W W₀) := by
  rw [normalized_coincidence_factorization _ _ _ _ _ _ (ne_of_gt hW₀)]
  exact Real.sqrt_mul hbase _

end Normalization

section RestoredParabola

def observedResponse (C K X : ℝ) : ℝ := C * X - K * X ^ 2
def restoredResponse (C K X : ℝ) : ℝ := observedResponse C K X + K * X ^ 2

theorem restoration_is_linear (C K X : ℝ) :
    restoredResponse C K X = C * X := by
  dsimp [restoredResponse, observedResponse]
  ring

theorem parabola_has_zero_intercept (C K : ℝ) :
    observedResponse C K 0 = 0 := by
  dsimp [observedResponse]
  ring

theorem normalized_coordinate_preserves_shared_scale
    (C₁ C₂ X : ℝ) :
    (C₁ * X) * (C₂ * X) = (C₁ * C₂) * X ^ 2 := by
  ring

end RestoredParabola

end

end InfoGeometry.Spectrometry.NormalizedAngularCoordinate
