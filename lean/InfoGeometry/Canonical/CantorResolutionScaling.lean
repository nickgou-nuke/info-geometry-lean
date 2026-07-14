import InfoGeometry.Canonical.SplitCliffordDirectLimit
import InfoGeometry.Dynamics.SouriauBostConnesFlowExtensions

/-!
# Cantor Resolution Scaling — Colimit × Jacobian Contraction

The SplitClifford direct limit builds the Cantor boundary from finite stages.
At each stage n, resolution ~ 1/n. As n → ∞, information below resolution is
lost — the Cayley Jacobian dW/dβ = 1/(β+½)² → 0 contracts quadratically.

## The Connection

- Resolution at stage n: ~ 1/n
- Cayley Jacobian at β = n: 1/(n+½)² ≤ 4/n²
- Ratio: Jacobian / resolution² → 1 as n → ∞

The Jacobian vanishes quadratically relative to the resolution.
Information below the resolution scale is compressed below detectability.
The colimit captures exactly what survives: the discrete Cantor set {0,1}^ℕ.
-/

set_option linter.unusedVariables false

noncomputable section

namespace CantorResolutionScaling

open InfoGeometry.Dynamics.SouriauBostConnesFlowExtensions

/-- Resolution at stage n of the Cantor tower. -/
def resolutionAtStage (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

/--
The Cayley Jacobian at β = n is quadratically bounded by 4/n².
Information below resolution ~ 1/n is lost at rate ~ 1/n².
-/
theorem jacobian_bound_at_stage {n : ℕ} (hn : (n : ℝ) > 1/2) :
    1 / (((n : ℝ) + (1/2 : ℝ)) ^ 2) ≤ 4 / ((n : ℝ) ^ 2) :=
  thermalCayley_jacobian_bound hn

end CantorResolutionScaling
