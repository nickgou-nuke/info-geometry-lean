import Mathlib

namespace InfoGeometry.Canonical

open Real

/-- The relative Rényi divergence of order q > 0, q ≠ 1.
    For two states (binary classification), it is:
    D_q^R(p|w) = (1 / (q - 1)) * log (p^q * w^(1 - q) + (1 - p)^q * (1 - w)^(1 - q)). -/
noncomputable def renyiDivergenceBinary (q p w : ℝ) : ℝ :=
  (1 / (q - 1)) * Real.log (p^q * w^(1 - q) + (1 - p)^q * (1 - w)^(1 - q))

end InfoGeometry.Canonical
