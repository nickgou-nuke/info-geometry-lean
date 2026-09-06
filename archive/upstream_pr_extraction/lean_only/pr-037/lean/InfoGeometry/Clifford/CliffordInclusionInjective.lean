import InfoGeometry.Canonical.SplitCliffordDirectLimit

/-!
# Split Clifford one-step injectivity

This module keeps the historical Clifford namespace surface, but the proof
owner is `InfoGeometry.Canonical.SplitCliffordDirectLimit`.
-/

noncomputable section

namespace InfoGeometry.Clifford

open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Canonical.SplitCliffordTensorBridge

/-- Historical name for the `n`th split Clifford algebra. -/
abbrev Cl_split (n : ℕ) := SplitClNNAlg n

/-- Historical name for the canonical split-Clifford one-step map. -/
abbrev incl_Cl_split (n : ℕ) : Cl_split n →ₐ[ℝ] Cl_split (n + 1) :=
  splitCliffordStep n

/-- The canonical split-Clifford one-step map is injective. -/
theorem incl_Cl_split_injective (n : ℕ) :
    Function.Injective (incl_Cl_split n) :=
  splitCliffordStep_injective n

end InfoGeometry.Clifford

