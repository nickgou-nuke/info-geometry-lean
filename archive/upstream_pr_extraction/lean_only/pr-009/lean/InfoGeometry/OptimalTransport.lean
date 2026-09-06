import InfoGeometry.Thermo.FromBregman
import InfoGeometry.ExponentialFamily.KLBregman
import InfoGeometry.ExponentialFamily.Analytic.LogSumExp

/-!
# InfoGeometry.OptimalTransport

Codebase-wide explicit optimal-transport bridge layer.

This module exposes OT-facing names and equivalence theorems already derived in:
- thermodynamic Bregman energy (`Thermo.FromBregman`)
- finite exponential-family KL/Bregman bridges (`ExponentialFamily.KLBregman`)
- analytic log-sum-exp regularized KL identities (`ExponentialFamily.Analytic.LogSumExp`)
-/
