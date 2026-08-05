import Mathlib

namespace InfoGeometry.Canonical

open Real
open Finset

/-- The surprisal for a discrete probability state p. -/
noncomputable def stateSurprisal {n : ℕ} (p : Fin n → ℝ) (i : Fin n) : ℝ :=
  - Real.log (p i)

/-- The Gibbs/Shannon entropy as the expectation of the surprisal. -/
noncomputable def gibbsEntropy {n : ℕ} (kB : ℝ) (p : Fin n → ℝ) : ℝ :=
  kB * ∑ i : Fin n, p i * stateSurprisal p i

/-- Relative operator surprisal (log-ratio) between p and w. -/
noncomputable def relativeSurprisal {n : ℕ} (p w : Fin n → ℝ) (i : Fin n) : ℝ :=
  - Real.log (p i / w i)

end InfoGeometry.Canonical
