import InfoGeometry.Canonical.ActualEntireRiemannXiSchwarzLogDerivativeBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ActualEntireRiemannXiZeroFreeLogDifferential

/-!
# Schwarz pullback on the actual zero-free logarithmic domain

The global derivative-level Schwarz identity is transported to the typed
zero-free subtype.  This is still a pointwise coefficient/one-form statement;
it does not assert a de Rham complex, closedness, periods, or cohomology.
-/

noncomputable section

namespace InfoGeometry.Canonical.ActualEntireRiemannXiZeroFreeSchwarzBridge

open InfoGeometry.Canonical.ActualEntireRiemannXiSchwarzLogDerivativeBridge
open InfoGeometry.Canonical.ActualEntireRiemannXiZeroFreeLogDifferential

theorem entireRiemannXiLogOneFormOnZeroFree_conjugation_pullback
    (s : EntireXiZeroFreePoint) (v : ℂ) :
    entireRiemannXiLogOneFormOnZeroFree (conjugateZeroFree s) (star v) =
      star (entireRiemannXiLogOneFormOnZeroFree s v) := by
  simpa [entireRiemannXiLogOneFormOnZeroFree, conjugateZeroFree] using
    (entireRiemannXiLogOneForm_conj s.1 v)

end InfoGeometry.Canonical.ActualEntireRiemannXiZeroFreeSchwarzBridge
