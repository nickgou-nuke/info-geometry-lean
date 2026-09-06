import InfoGeometry.Analysis.FiniteSpectralHeatMellin

namespace InfoGeometry.Analysis.FiniteSpectralHeatMellin

open Finset
open InfoGeometry.Analysis.FiniteSpectralMellinTaylor

variable {ι : Type*} [Fintype ι]

theorem continuous_heatTaylorCoeff (k : ℕ) :
    Continuous (fun t : ℂ => heatTaylorCoeff t k) := by
  unfold heatTaylorCoeff
  fun_prop

theorem continuous_scalarHeatTaylorPrefix
    (lam : ℂ) (N : ℕ) :
    Continuous (fun t : ℂ => scalarHeatTaylorPrefix t lam N) := by
  unfold scalarHeatTaylorPrefix
  apply continuous_finset_sum
  intro k hk
  exact (continuous_heatTaylorCoeff k).mul continuous_const

theorem continuous_heatTaylorReadout
    (D : FiniteSpectralData ι ℂ) (N : ℕ) :
    Continuous (fun t : ℂ => heatTaylorReadout D t N) := by
  unfold heatTaylorReadout
  apply continuous_finset_sum (s := (Finset.univ : Finset ι))
  intro i hi
  exact continuous_const.mul
    (continuous_scalarHeatTaylorPrefix (D.spectralValue i) N)

theorem heatTaylorReadout_fiber_isClosed
    (D : FiniteSpectralData ι ℂ) (N : ℕ) (level : ℂ) :
    IsClosed {t : ℂ | heatTaylorReadout D t N = level} := by
  change IsClosed
    ((fun t : ℂ => heatTaylorReadout D t N) ⁻¹' ({level} : Set ℂ))
  exact isClosed_singleton.preimage (continuous_heatTaylorReadout D N)

theorem isCompact_heatTaylorReadout_image
    (D : FiniteSpectralData ι ℂ) (N : ℕ)
    (s : Set ℂ) (hs : IsCompact s) :
    IsCompact ((fun t : ℂ => heatTaylorReadout D t N) '' s) :=
  hs.image (continuous_heatTaylorReadout D N)

end InfoGeometry.Analysis.FiniteSpectralHeatMellin
