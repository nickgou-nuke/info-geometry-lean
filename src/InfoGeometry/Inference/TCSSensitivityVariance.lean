/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import InfoGeometry.Inference.FisherVariance
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Inference.TCSSensitivity

/-!
# TCS local sensitivity variance

This is the application bridge from the generic inverse-Fisher quadratic form
to the two-parameter TCS response. It provides a local sensitivity diagnostic,
not a global or finite-sample confidence guarantee.
-/

namespace InfoGeometry.Inference.TCSSensitivityVariance

noncomputable def tcsLocalVariance
    (I : Matrix (Fin 2) (Fin 2) ℝ)
    (hI : FisherInverseContract I)
    (liveTime x : ℝ) : ℝ :=
  localVariance I hI (tcsSensitivity liveTime x)

theorem tcsLocalVariance_nonneg
    (I : Matrix (Fin 2) (Fin 2) ℝ)
    (hI : FisherInverseContract I)
    (liveTime x : ℝ) :
    0 ≤ tcsLocalVariance I hI liveTime x := by
  exact localVariance_nonneg I hI (tcsSensitivity liveTime x)

end InfoGeometry.Inference.TCSSensitivityVariance
