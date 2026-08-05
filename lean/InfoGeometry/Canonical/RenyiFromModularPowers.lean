import InfoGeometry.Canonical.ModularLogGenerating

namespace InfoGeometry.Canonical

open Real

/-- The Rényi entropy as a secant of the modular potential. -/
noncomputable def renyiEntropy {n : ℕ} (kB : ℝ) (p : Fin n → ℝ) (s : ℝ) : ℝ :=
  (kB / (1 - s)) * modularLogGenerating p s

/-- The Petz Rényi divergence (relative entropy). -/
noncomputable def petzRenyiDivergence {n : ℕ} (p w : Fin n → ℝ) (s : ℝ) : ℝ :=
  (1 / (s - 1)) * relativeModularLogGenerating p w s

end InfoGeometry.Canonical
