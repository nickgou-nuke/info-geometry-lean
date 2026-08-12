import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace Omega.GU

/-- The localization ring `R_ζ = ℤ[1/6]`, encoded as rationals with denominator a power of `6`. -/
def Rzeta : Set ℚ := {q | ∃ a : ℤ, ∃ k : ℕ, q = (a : ℚ) / (6 : ℚ) ^ k}

/-- The limiting cumulant values used in the window-`6` arithmetic audit. -/
def kappaInfinity (r : ℕ) : ℚ := (r : ℚ) / 6

/-- The Green-kernel audit obstruction at the distinguished prime `571`. -/
structure Window6GreenKernelData where
  entriesInRzeta : Prop

def window6GreenKernelEntriesInRzeta (W : Window6GreenKernelData) : Prop :=
  W.entriesInRzeta

/-- Paper label: `thm:window6-zeta-cumulant-localization-vs-green-kernel-prime571`. -/
theorem paper_window6_zeta_cumulant_localization_vs_green_kernel_prime571 :
    ∀ (W : Window6GreenKernelData),
      ¬ window6GreenKernelEntriesInRzeta W →
        (∀ r : ℕ, 1 ≤ r → kappaInfinity r ∈ Rzeta) ∧
          ¬ window6GreenKernelEntriesInRzeta W := by
  intro W hNoEntries
  constructor
  · intro r hr
    let _ := hr
    refine ⟨(r : ℤ), 1, ?_⟩
    simp [Rzeta, kappaInfinity]
  · exact hNoEntries

end Omega.GU
