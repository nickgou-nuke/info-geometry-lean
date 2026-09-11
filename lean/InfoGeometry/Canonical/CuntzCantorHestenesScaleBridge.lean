import InfoGeometry.Algebra.CuntzTensorTreeRealizationBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.HestenesLogScaleSamplingBridge

/-!
# Cuntz word depth and Cantor metric scale

Words provide the finite rooted-tree carrier.  Their length controls the
metric scale, while the alphabet size remains independent of the scale base.
For the standard Cantor metric this base is `3`, regardless of the chosen
finite word alphabet.  The resulting depth time is sampled by an existing
Hestenes flow; no boundary completion is introduced.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzCantorHestenesScaleBridge

open InfoGeometry.Algebra.CuntzTensorQuotient
open InfoGeometry.Algebra.CuntzTensorTreeRealizationBridge
open InfoGeometry.Canonical.HestenesLogScaleSamplingBridge
open InfoGeometry.Canonical.HestenesModularRealizationBridge

variable {n : ℕ}

def cuntzWordCantorScale (w : List (Fin n)) : ℝ :=
  scaleAtDepth cantorScaleDatum w.length

def cuntzWordLogTime (w : List (Fin n)) : ℝ :=
  logTimeAtDepth cantorScaleDatum w.length

@[simp] theorem cuntzWordCantorScale_nil :
    cuntzWordCantorScale ([] : List (Fin n)) = 1 := by
  simp [cuntzWordCantorScale, scaleAtDepth]

theorem cuntzWordCantorScale_append (u v : List (Fin n)) :
    cuntzWordCantorScale (u ++ v) =
      cuntzWordCantorScale u * cuntzWordCantorScale v := by
  unfold cuntzWordCantorScale
  rw [List.length_append, scaleAtDepth_add]

@[simp] theorem cuntzWordLogTime_nil :
    cuntzWordLogTime ([] : List (Fin n)) = 0 := by
  simp [cuntzWordLogTime, logTimeAtDepth]

theorem cuntzWordLogTime_append (u v : List (Fin n)) :
    cuntzWordLogTime (u ++ v) =
      cuntzWordLogTime u + cuntzWordLogTime v := by
  unfold cuntzWordLogTime
  rw [List.length_append, logTimeAtDepth_add]

theorem cuntzWordLogTime_eq_neg_log_scale (w : List (Fin n)) :
    cuntzWordLogTime w = -Real.log (cuntzWordCantorScale w) := by
  unfold cuntzWordLogTime cuntzWordCantorScale
  exact logTimeAtDepth_eq_neg_log_scale cantorScaleDatum w.length

theorem cuntzWordLogTime_eq_length_log_three (w : List (Fin n)) :
    cuntzWordLogTime w = (w.length : ℝ) * Real.log 3 := by
  unfold cuntzWordLogTime
  rfl

def hestenesCuntzWordSample {M : Type*} [NormedAddCommGroup M]
    [NormedSpace ℝ M] [CompleteSpace M]
    (H : HestenesModularDatum (M := M)) (w : List (Fin n)) : M →L[ℝ] M :=
  hestenesScaleSample H cantorScaleDatum w.length

theorem hestenesCuntzWordSample_append
    {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] [CompleteSpace M]
    (H : HestenesModularDatum (M := M)) (u v : List (Fin n)) :
    hestenesCuntzWordSample H (u ++ v) =
      hestenesCuntzWordSample H u ∘L hestenesCuntzWordSample H v := by
  unfold hestenesCuntzWordSample
  rw [List.length_append]
  exact hestenesScaleSample_add H cantorScaleDatum u.length v.length

theorem hestenesCuntzWordSample_length
    {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] [CompleteSpace M]
    (H : HestenesModularDatum (M := M)) (w : List (Fin n)) :
    hestenesCuntzWordSample H w =
      H.Delta_real ((w.length : ℝ) * Real.log 3) := by
  unfold hestenesCuntzWordSample
  change H.Delta_real ((w.length : ℝ) * Real.log 3) = _
  rfl

theorem hestenesCuntzWordSample_eq_prime_power_sample
    {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] [CompleteSpace M]
    (H : HestenesModularDatum (M := M)) (w : List (Fin n)) :
    hestenesCuntzWordSample H w =
      hestenesLogScaleSample H (3 ^ w.length) := by
  unfold hestenesCuntzWordSample hestenesLogScaleSample
  change H.Delta_real ((w.length : ℝ) * Real.log 3) =
    H.Delta_real (Real.log ((3 ^ w.length : ℕ) : ℝ))
  rw [show ((3 ^ w.length : ℕ) : ℝ) = (3 : ℝ) ^ w.length by norm_num]
  rw [Real.log_pow 3 w.length]

end InfoGeometry.Canonical.CuntzCantorHestenesScaleBridge
