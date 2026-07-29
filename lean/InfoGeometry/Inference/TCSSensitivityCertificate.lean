/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import InfoGeometry.Inference.FisherVariance
import InfoGeometry.Inference.GibbsTemperatureCertificate

/-!
# Certified local TCS sensitivity

The selected Fisher certificate provides local quadratic sensitivity variances
for the physical `C` and `K` coordinates. These are local information-geometric
quantities; no global confidence or exact finite-sample covariance claim is
made here.
-/

namespace InfoGeometry.Inference

def tcsCDirection : Fin 2 → ℝ
  | 0 => 1
  | 1 => 0

def tcsKDirection : Fin 2 → ℝ
  | 0 => 0
  | 1 => 1

noncomputable def tcsCLocalVariance
    (I : Matrix (Fin 2) (Fin 2) ℝ)
    (c : GibbsTemperatureCertificate I) : ℝ :=
  localVariance I c.fisher tcsCDirection

noncomputable def tcsKLocalVariance
    (I : Matrix (Fin 2) (Fin 2) ℝ)
    (c : GibbsTemperatureCertificate I) : ℝ :=
  localVariance I c.fisher tcsKDirection

theorem tcsCLocalVariance_nonneg
    (I : Matrix (Fin 2) (Fin 2) ℝ)
    (c : GibbsTemperatureCertificate I) :
    0 ≤ tcsCLocalVariance I c := by
  exact localVariance_nonneg I c.fisher tcsCDirection

theorem tcsKLocalVariance_nonneg
    (I : Matrix (Fin 2) (Fin 2) ℝ)
    (c : GibbsTemperatureCertificate I) :
    0 ≤ tcsKLocalVariance I c := by
  exact localVariance_nonneg I c.fisher tcsKDirection

theorem tcsLocalVariance_nonneg
    (I : Matrix (Fin 2) (Fin 2) ℝ)
    (c : GibbsTemperatureCertificate I) (v : Fin 2 → ℝ) :
    0 ≤ localVariance I c.fisher v := by
  exact localVariance_nonneg I c.fisher v

end InfoGeometry.Inference
