import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.FilteredHestenesKreinColimit
import InfoGeometry.Canonical.FilteredHestenesIteratedTransport

noncomputable section

namespace InfoGeometry.Canonical.HestenesKreinMajoranaColimit

open InfoGeometry.Canonical.FilteredHestenesKreinColimit
open InfoGeometry.Canonical.FilteredInductiveHestenesAnalyticity
open InfoGeometry.Krein

theorem stageMBKReadout_eq_limitMBKReadout
    {C : HestenesKreinCone}
    (readout : ∀ n, Fin 5 → DoubledSpace (C.Base n) → ℝ)
    (limitReadout : Fin 5 → DoubledSpace C.LimitBase → ℝ)
    (hreadout : ∀ n channel x,
      readout n channel x = limitReadout channel (C.ι n x))
    (n : ℕ) (channel : Fin 5) (x : DoubledSpace (C.Base n)) :
    readout n channel x = limitReadout channel (C.ι n x) :=
  hreadout n channel x

theorem stageMBKReadout_bondIterate_eq
    {C : HestenesKreinCone}
    (readout : ∀ n, Fin 5 → DoubledSpace (C.Base n) → ℝ)
    (hreadout : ∀ n m channel x,
      readout (n + m) channel
          (FilteredPhaseCone.bondIterate C.toFilteredPhaseCone n m x) =
        readout n channel x)
    (n m : ℕ) (channel : Fin 5) (x : DoubledSpace (C.Base n)) :
    readout (n + m) channel
        (FilteredPhaseCone.bondIterate C.toFilteredPhaseCone n m x) =
      readout n channel x :=
  hreadout n m channel x

theorem stageMBKReadout_vector_eq_limit
    {C : HestenesKreinCone}
    (readout : ∀ n, Fin 5 → DoubledSpace (C.Base n) → ℝ)
    (limitReadout : Fin 5 → DoubledSpace C.LimitBase → ℝ)
    (hreadout : ∀ n channel x,
      readout n channel x = limitReadout channel (C.ι n x))
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    (fun channel => readout n channel x) =
      (fun channel => limitReadout channel (C.ι n x)) := by
  funext channel
  exact stageMBKReadout_eq_limitMBKReadout readout limitReadout hreadout n channel x

theorem stageMBKReadout_vector_bondIterate_eq
    {C : HestenesKreinCone}
    (readout : ∀ n, Fin 5 → DoubledSpace (C.Base n) → ℝ)
    (hreadout : ∀ n m channel x,
      readout (n + m) channel
          (FilteredPhaseCone.bondIterate C.toFilteredPhaseCone n m x) =
        readout n channel x)
    (n m : ℕ) (x : DoubledSpace (C.Base n)) :
    (fun channel =>
        readout (n + m) channel
          (FilteredPhaseCone.bondIterate C.toFilteredPhaseCone n m x)) =
      (fun channel => readout n channel x) := by
  funext channel
  exact stageMBKReadout_bondIterate_eq readout hreadout n m channel x

def criticalDeviation (realPart : ℝ) : ℝ := realPart - (1 / 2 : ℝ)

theorem criticalDeviation_eq_zero_iff (realPart : ℝ) :
    criticalDeviation realPart = 0 ↔ realPart = (1 / 2 : ℝ) := by
  unfold criticalDeviation
  constructor <;> intro h <;> linarith

def stageCriticalDeviation
    {C : HestenesKreinCone}
    (realPart : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (n : ℕ) (x : DoubledSpace (C.Base n)) : ℝ :=
  criticalDeviation (realPart n x)

def limitCriticalDeviation
    {C : HestenesKreinCone}
    (realPart : DoubledSpace C.LimitBase → ℝ)
    (x : DoubledSpace C.LimitBase) : ℝ :=
  criticalDeviation (realPart x)

theorem stageCriticalDeviation_eq_limit
    {C : HestenesKreinCone}
    (realPart : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (limitRealPart : DoubledSpace C.LimitBase → ℝ)
    (hrealPart : ∀ n x, realPart n x = limitRealPart (C.ι n x))
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    stageCriticalDeviation realPart n x =
      limitCriticalDeviation limitRealPart (C.ι n x) := by
  unfold stageCriticalDeviation limitCriticalDeviation
  rw [hrealPart n x]

theorem limitCriticalDeviation_eq_zero_of_stage
    {C : HestenesKreinCone}
    (realPart : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (limitRealPart : DoubledSpace C.LimitBase → ℝ)
    (hrealPart : ∀ n x, realPart n x = limitRealPart (C.ι n x))
    (hcritical : ∀ n x, stageCriticalDeviation realPart n x = 0)
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    limitCriticalDeviation limitRealPart (C.ι n x) = 0 := by
  rw [← stageCriticalDeviation_eq_limit realPart limitRealPart hrealPart n x]
  exact hcritical n x

theorem stagePfaffianReadout_eq_target
    {C : HestenesKreinCone}
    (readout : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (limitReadout : DoubledSpace C.LimitBase → ℝ)
    (target : DoubledSpace C.LimitBase → ℝ)
    (hreadout : ∀ n x, readout n x = limitReadout (C.ι n x))
    (hcalibration : ∀ x, limitReadout x = target x)
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    readout n x = target (C.ι n x) := by
  rw [hreadout n x, hcalibration]

theorem stagePfaffianReadout_bondIterate_eq
    {C : HestenesKreinCone}
    (readout : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (hreadout : ∀ n m x,
      readout (n + m)
          (FilteredPhaseCone.bondIterate C.toFilteredPhaseCone n m x) =
        readout n x)
    (n m : ℕ) (x : DoubledSpace (C.Base n)) :
    readout (n + m)
        (FilteredPhaseCone.bondIterate C.toFilteredPhaseCone n m x) =
      readout n x :=
  hreadout n m x

end InfoGeometry.Canonical.HestenesKreinMajoranaColimit
