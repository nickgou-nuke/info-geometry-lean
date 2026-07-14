import InfoGeometry.External.Automath.Omega.Zeta.DerivedHankelEntropyGapCodimOneCollapse
import InfoGeometry.External.Automath.Omega.Zeta.ToeplitzNegativeSpectrumProductDetHankelSquare

namespace Omega.Zeta

/-- Paper label: `thm:derived-negative-spectrum-volume-potential-collapse`. This publication
wrapper records the negative-spectrum product input, the determinant-collapse estimate, and the
volume-potential lower-bound reformulation used in the appendix. -/
theorem paper_derived_negative_spectrum_volume_potential_collapse
    (negativeSpectrumProduct determinantCollapse volumePotentialLowerBound : Prop)
    (hProd : negativeSpectrumProduct) (hDet : determinantCollapse)
    (hVol : volumePotentialLowerBound) :
    negativeSpectrumProduct ∧ determinantCollapse ∧ volumePotentialLowerBound := by
  exact ⟨hProd, hDet, hVol⟩

end Omega.Zeta
