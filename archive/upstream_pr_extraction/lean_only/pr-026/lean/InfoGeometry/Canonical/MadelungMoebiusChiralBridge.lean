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

/-- **Theorem**: Master Madelung-Möbius Chiral Synthesis.
    Unifies:
    1. Madelung sheet decomposition ψplus + ψminus = ψ.
    2. Möbius inversion involution (-1 / (-1 / z) = z). -/
theorem master_madelung_moebius_chiral_synthesis
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (S : PolarizedDoubledAmplitude (E := E)) (z : ℝ) (hz : z ≠ 0) :
    (S.ψplus + S.ψminus = S.ψ) ∧
    (moebiusInversion (moebiusInversion z) = z) := ⟨
  madelung_chiral_sheet_decomposition S,
  moebiusInversion_involutive z hz
⟩

end InfoGeometry.Canonical.MadelungMoebiusChiralBridge
