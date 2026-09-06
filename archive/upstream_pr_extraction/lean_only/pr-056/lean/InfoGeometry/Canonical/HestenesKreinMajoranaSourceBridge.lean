import InfoGeometry.Canonical.HestenesKreinMajoranaColimit
import InfoGeometry.Arithmetic.MajoranaPolyaHilbert.BerryKeating
import InfoGeometry.Arithmetic.MajoranaPolyaHilbert.ZetaSpectral

/-!
# Majorana source packets on the Hestenes--Krein colimit

This owner connects the theorem-safe real-part packets supplied by the
Majorana/Pólya interfaces to the existing Hestenes--Krein critical-deviation
readout.  The source packets certify only the algebraic equality
`realPart = 1 / 2`; the colimit hypotheses certify how a chosen real readout
is transported.  No operator closure, scattering discretization, Pfaffian
identity, or statement about zeta zeros is introduced here.
-/

noncomputable section

namespace InfoGeometry.Canonical.HestenesKreinMajoranaSourceBridge

open InfoGeometry.Arithmetic.MajoranaPolyaHilbert
open InfoGeometry.Canonical.FilteredHestenesKreinColimit
open InfoGeometry.Canonical.FilteredInductiveHestenesAnalyticity
open InfoGeometry.Canonical.HestenesKreinMajoranaColimit
open InfoGeometry.Krein

theorem stageCriticalDeviation_eq_mellinPacket
    {MellinWave MellinNorm : Type}
    {C : HestenesKreinCone}
    (packets : ∀ n, MellinPlancherelCriticalLineData MellinWave MellinNorm)
    (realPartReadout : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (hreadout : ∀ n x, realPartReadout n x = (packets n).realPart)
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    stageCriticalDeviation realPartReadout n x =
      criticalDeviation (packets n).realPart := by
  unfold stageCriticalDeviation
  rw [hreadout n x]

theorem stageCriticalDeviation_eq_zero_of_mellinPacket
    {MellinWave MellinNorm : Type}
    {C : HestenesKreinCone}
    (packets : ∀ n, MellinPlancherelCriticalLineData MellinWave MellinNorm)
    (realPartReadout : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (hreadout : ∀ n x, realPartReadout n x = (packets n).realPart)
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    stageCriticalDeviation realPartReadout n x = 0 := by
  rw [stageCriticalDeviation_eq_mellinPacket packets realPartReadout hreadout]
  unfold criticalDeviation
  rw [(packets n).realPart_eq_half]
  norm_num

theorem limitCriticalDeviation_eq_zero_of_mellinPacket
    {MellinWave MellinNorm : Type}
    {C : HestenesKreinCone}
    (packets : ∀ n, MellinPlancherelCriticalLineData MellinWave MellinNorm)
    (realPartReadout : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (limitRealPart : DoubledSpace C.LimitBase → ℝ)
    (hstage : ∀ n x, realPartReadout n x = (packets n).realPart)
    (hreadout : ∀ n x, realPartReadout n x = limitRealPart (C.ι n x))
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    limitCriticalDeviation limitRealPart (C.ι n x) = 0 := by
  apply limitCriticalDeviation_eq_zero_of_stage realPartReadout limitRealPart hreadout
  · intro m y
    exact stageCriticalDeviation_eq_zero_of_mellinPacket packets realPartReadout hstage m y

theorem stageCriticalDeviation_eq_zero_of_zeroModePacket
    {ZeroMode NormReadout : Type}
    {C : HestenesKreinCone}
    (packets : ∀ n, MajoranaZeroModeNormalizabilityData ZeroMode NormReadout)
    (realPartReadout : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (hreadout : ∀ n x, realPartReadout n x = (packets n).realPart)
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    stageCriticalDeviation realPartReadout n x = 0 := by
  rw [stageCriticalDeviation]
  rw [hreadout n x]
  unfold criticalDeviation
  rw [(packets n).realPart_eq_half]
  norm_num

theorem limitCriticalDeviation_eq_zero_of_zeroModePacket
    {ZeroMode NormReadout : Type}
    {C : HestenesKreinCone}
    (packets : ∀ n, MajoranaZeroModeNormalizabilityData ZeroMode NormReadout)
    (realPartReadout : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (limitRealPart : DoubledSpace C.LimitBase → ℝ)
    (hstage : ∀ n x, realPartReadout n x = (packets n).realPart)
    (hreadout : ∀ n x, realPartReadout n x = limitRealPart (C.ι n x))
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    limitCriticalDeviation limitRealPart (C.ι n x) = 0 := by
  apply limitCriticalDeviation_eq_zero_of_stage realPartReadout limitRealPart hreadout
  · intro m y
    exact stageCriticalDeviation_eq_zero_of_zeroModePacket packets realPartReadout hstage m y

theorem stageCriticalDeviation_bondIterate_eq_of_readout
    {C : HestenesKreinCone}
    (realPartReadout : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (hreadout : ∀ n m x,
      realPartReadout (n + m)
          (FilteredPhaseCone.bondIterate C.toFilteredPhaseCone n m x) =
        realPartReadout n x)
    (n m : ℕ) (x : DoubledSpace (C.Base n)) :
    stageCriticalDeviation realPartReadout (n + m)
        (FilteredPhaseCone.bondIterate C.toFilteredPhaseCone n m x) =
      stageCriticalDeviation realPartReadout n x := by
  unfold stageCriticalDeviation
  rw [hreadout n m x]

end InfoGeometry.Canonical.HestenesKreinMajoranaSourceBridge

end noncomputable section
