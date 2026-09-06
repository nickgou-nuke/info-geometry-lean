import Mathlib.Tactic
import InfoGeometry.Canonical.HestenesKreinItakuraSaitoColimit
import InfoGeometry.Canonical.FilteredHestenesKreinColimit
import InfoGeometry.Canonical.FilteredHestenesIteratedTransport

/-!
# Real Rindler/modular readouts on the Hestenes--Krein colimit

This owner records the finite real algebra behind a wedge reflection: rapidity
is negated, the seam is its fixed point, and the doubled rapidity feeds the
Tomita/Itakura--Saito deviance.  It does not assert the Bisognano--Wichmann
theorem, an Unruh temperature formula, or a zeta spectral theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.HestenesKreinRindlerModularColimit

open InfoGeometry.Canonical.FilteredHestenesKreinColimit
open InfoGeometry.Canonical.HestenesKreinItakuraSaitoColimit
open InfoGeometry.Krein

def wedgeReflection (χ : ℝ) : ℝ := -χ

def modularRapidity (χ : ℝ) : ℝ := 2 * χ

def rightWedgeReadout (χ : ℝ) : ℝ := χ

def leftWedgeReadout (χ : ℝ) : ℝ := wedgeReflection χ

def netWedgeReadout (χ : ℝ) : ℝ :=
  rightWedgeReadout χ + leftWedgeReadout χ

theorem wedgeReflection_fixed_iff (χ : ℝ) :
    wedgeReflection χ = χ ↔ χ = 0 := by
  unfold wedgeReflection
  constructor <;> intro h <;> linarith

theorem modularRapidity_reflection (χ : ℝ) :
    modularRapidity (wedgeReflection χ) = -modularRapidity χ := by
  unfold modularRapidity wedgeReflection
  ring

theorem netWedgeReadout_eq_zero (χ : ℝ) :
    netWedgeReadout χ = 0 := by
  unfold netWedgeReadout rightWedgeReadout leftWedgeReadout wedgeReflection
  ring

theorem modularDeviance_nonneg (χ : ℝ) :
    0 ≤ modularTomitaDeviance (modularRapidity χ) := by
  exact modularTomitaDeviance_nonneg _

theorem modularDeviance_seam_zero :
    modularTomitaDeviance (modularRapidity 0) = 0 := by
  norm_num [modularTomitaDeviance, modularRapidity]

theorem modularRapidity_fixed_iff (χ : ℝ) :
    modularRapidity χ = 0 ↔ χ = 0 := by
  unfold modularRapidity
  constructor <;> intro h <;> linarith

def stageRapidityReadout
    {C : HestenesKreinCone}
    (rapidity : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (n : ℕ) (x : DoubledSpace (C.Base n)) : ℝ :=
  rapidity n x

def limitRapidityReadout
    {C : HestenesKreinCone}
    (rapidity : DoubledSpace C.LimitBase → ℝ)
    (x : DoubledSpace C.LimitBase) : ℝ :=
  rapidity x

theorem stageRapidityReadout_eq_limit
    {C : HestenesKreinCone}
    (stageRapidity : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (limitRapidity : DoubledSpace C.LimitBase → ℝ)
    (hrapidity : ∀ n x, stageRapidity n x = limitRapidity (C.ι n x))
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    stageRapidityReadout stageRapidity n x =
      limitRapidityReadout limitRapidity (C.ι n x) := by
  unfold stageRapidityReadout limitRapidityReadout
  exact hrapidity n x

theorem stageRapidityReadout_bondIterate_eq
    {C : HestenesKreinCone}
    (rapidity : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (hrapidity : ∀ n m x,
      rapidity (n + m) (C.toFilteredPhaseCone.bondIterate n m x) =
        rapidity n x)
    (n m : ℕ) (x : DoubledSpace (C.Base n)) :
    stageRapidityReadout rapidity (n + m)
        (C.toFilteredPhaseCone.bondIterate n m x) =
      stageRapidityReadout rapidity n x := by
  unfold stageRapidityReadout
  exact hrapidity n m x

end InfoGeometry.Canonical.HestenesKreinRindlerModularColimit

end noncomputable section
