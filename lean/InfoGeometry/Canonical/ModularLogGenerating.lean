import InfoGeometry.Canonical.OperatorSurprisal

namespace InfoGeometry.Canonical

open Real
open Finset

/-- The spectral partition function Z_p(s) = Tr(p^s). -/
noncomputable def spectralPartition {n : ℕ} (p : Fin n → ℝ) (s : ℝ) : ℝ :=
  ∑ i : Fin n, (p i) ^ s

/-- The log-generating potential of modular-operator exponents. -/
noncomputable def modularLogGenerating {n : ℕ} (p : Fin n → ℝ) (s : ℝ) : ℝ :=
  Real.log (spectralPartition p s)

/-- The relative modular generating function. -/
noncomputable def relativeModularLogGenerating {n : ℕ} (p w : Fin n → ℝ) (s : ℝ) : ℝ :=
  Real.log (∑ i : Fin n, (p i) ^ s * (w i) ^ (1 - s))

end InfoGeometry.Canonical
