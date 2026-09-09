import Mathlib.Tactic
import InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
import InfoGeometry.Canonical.PrimeLeeYangFerromagneticChain

namespace InfoGeometry.Canonical.PrimeLeeYangRHBridge

open Complex
open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
open InfoGeometry.Canonical.PrimeLeeYangFerromagneticChain

theorem partitionRoot_mapsToCriticalLine
    (partitionPolynomial : Polynomial ℂ)
    (hLeeYang : ∀ z : ℂ, partitionPolynomial.IsRoot z → OnLeeYangCircle z)
    {z : ℂ} (hz : partitionPolynomial.IsRoot z) (hpole : z.re ≠ -1) :
    OnCriticalLine (cayleyToTemperature z) := by
  exact cayleyToTemperature_mem_criticalLine_of_unitCircle z
    (hLeeYang z hz) hpole

theorem partitionRoot_cayleyRoundTrip
    (partitionPolynomial : Polynomial ℂ)
    (hLeeYang : ∀ z : ℂ, partitionPolynomial.IsRoot z → OnLeeYangCircle z)
    {z : ℂ} (hz : partitionPolynomial.IsRoot z) (hpole : z.re ≠ -1) :
    OnCriticalLine (cayleyToTemperature z) ∧
      cayleyToFugacity (cayleyToTemperature z) = z := by
  constructor
  · exact partitionRoot_mapsToCriticalLine partitionPolynomial hLeeYang hz hpole
  · apply cayleyToFugacity_cayleyToTemperature
    intro hzero
    apply hpole
    have hre : (1 + z).re = 0 := by rw [hzero]; simp
    calc z.re = (1 + z).re - 1 := by simp
      _ = 0 - 1 := by rw [hre]
      _ = -1 := by ring

end InfoGeometry.Canonical.PrimeLeeYangRHBridge
