/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import InfoGeometry.Inference.FisherVariance
import InfoGeometry.Inference.GibbsTemperatureCertificate
import InfoGeometry.Inference.TCSSensitivity

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

noncomputable def tcsCLocalStdDev
    (I : Matrix (Fin 2) (Fin 2) ℝ)
    (c : GibbsTemperatureCertificate I) : ℝ :=
  Real.sqrt (tcsCLocalVariance I c)

noncomputable def tcsKLocalStdDev
    (I : Matrix (Fin 2) (Fin 2) ℝ)
    (c : GibbsTemperatureCertificate I) : ℝ :=
  Real.sqrt (tcsKLocalVariance I c)

theorem tcsCLocalStdDev_nonneg
    (I : Matrix (Fin 2) (Fin 2) ℝ)
    (c : GibbsTemperatureCertificate I) :
    0 ≤ tcsCLocalStdDev I c := by
  exact Real.sqrt_nonneg _

theorem tcsKLocalStdDev_nonneg
    (I : Matrix (Fin 2) (Fin 2) ℝ)
    (c : GibbsTemperatureCertificate I) :
    0 ≤ tcsKLocalStdDev I c := by
  exact Real.sqrt_nonneg _

theorem tcsCLocalStdDev_sq
    (I : Matrix (Fin 2) (Fin 2) ℝ)
    (c : GibbsTemperatureCertificate I) :
    (tcsCLocalStdDev I c) ^ (2 : ℕ) = tcsCLocalVariance I c := by
  unfold tcsCLocalStdDev
  exact Real.sq_sqrt (tcsCLocalVariance_nonneg I c)

theorem tcsKLocalStdDev_sq
    (I : Matrix (Fin 2) (Fin 2) ℝ)
    (c : GibbsTemperatureCertificate I) :
    (tcsKLocalStdDev I c) ^ (2 : ℕ) = tcsKLocalVariance I c := by
  unfold tcsKLocalStdDev
  exact Real.sq_sqrt (tcsKLocalVariance_nonneg I c)

noncomputable def tcsMeanLocalVariance
    (I : Matrix (Fin 2) (Fin 2) ℝ)
    (c : GibbsTemperatureCertificate I)
    (liveTime x : ℝ) : ℝ :=
  localVariance I c.fisher (tcsSensitivity liveTime x)

noncomputable def tcsMeanLocalStdDev
    (I : Matrix (Fin 2) (Fin 2) ℝ)
    (c : GibbsTemperatureCertificate I)
    (liveTime x : ℝ) : ℝ :=
  Real.sqrt (tcsMeanLocalVariance I c liveTime x)

theorem tcsMeanLocalVariance_nonneg
    (I : Matrix (Fin 2) (Fin 2) ℝ)
    (c : GibbsTemperatureCertificate I)
    (liveTime x : ℝ) :
    0 ≤ tcsMeanLocalVariance I c liveTime x := by
  exact localVariance_nonneg I c.fisher (tcsSensitivity liveTime x)

theorem tcsMeanLocalStdDev_nonneg
    (I : Matrix (Fin 2) (Fin 2) ℝ)
    (c : GibbsTemperatureCertificate I)
    (liveTime x : ℝ) :
    0 ≤ tcsMeanLocalStdDev I c liveTime x := by
  exact Real.sqrt_nonneg _

theorem tcsMeanLocalStdDev_sq
    (I : Matrix (Fin 2) (Fin 2) ℝ)
    (c : GibbsTemperatureCertificate I)
    (liveTime x : ℝ) :
    (tcsMeanLocalStdDev I c liveTime x) ^ (2 : ℕ) =
      tcsMeanLocalVariance I c liveTime x := by
  unfold tcsMeanLocalStdDev
  exact Real.sq_sqrt (tcsMeanLocalVariance_nonneg I c liveTime x)

end InfoGeometry.Inference
