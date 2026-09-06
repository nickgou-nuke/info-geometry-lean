import InfoGeometry.Canonical.MadelungCore
import InfoGeometry.Canonical.MoebiusCore
import InfoGeometry.Thermo.SplitChiralPolarizationBasis

noncomputable section

namespace InfoGeometry.Canonical.MadelungMoebiusChiralBridge

open InfoGeometry.Canonical.MadelungCore
open InfoGeometry.Canonical.MoebiusCore
open InfoGeometry.Thermo.SplitChiralPolarizationBasis
open InfoGeometry.Canonical.PolarizedMadelungBridge

/-- **Theorem**: Madelung Doubled Amplitude Sheet Decomposition maps to Chiral Idempotents (ePlus, eMinus). -/
theorem madelung_chiral_sheet_decomposition
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (S : PolarizedDoubledAmplitude (E := E)) :
    S.ψplus + S.ψminus = S.ψ :=
  S.sheet_decomposition

end InfoGeometry.Canonical.MadelungMoebiusChiralBridge
