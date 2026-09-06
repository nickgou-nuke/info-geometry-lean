import InfoGeometry.Automorphic.LanglandsFunctorialityNuclearBridge

namespace InfoGeometry.Canonical.LanglandsFunctorialityNuclearCapstone

open InfoGeometry.Automorphic.LanglandsFunctorialityNuclearBridge
open InfoGeometry.Nuclear.ChiralPRM

theorem langlands_functoriality_nuclear_canonical_capstone
    {CuspH CuspG : Type*}
    (galois : GaloisRepresentationDatum)
    (B : NuclearIsotopeFunctorialBridge CuspH CuspG)
    (f : CuspH) :
    (∀ p : ℕ, galois.frobeniusTrace p = galois.satakeParameter p) ∧
    (∃ q : ℚ, B.functorialPacket.datumG.normalizedSpecialValue
        (B.functorialPacket.transferMap f) = (q : ℝ)) ∧
    (energyMinus B.stateG - energyPlus B.stateG =
      energyMinus B.stateH - energyPlus B.stateH) ∧
    (B.stateH.Delta = 0 → energyPlus B.stateG = energyMinus B.stateG) := by
  refine ⟨galois.langlands_reciprocity,
    (B.functorialPacket.transfer_rational_equiv f).mp
      (B.functorialPacket.datumH.normalizedSpecialValue_is_rational f),
    nuclear_isotope_doublet_gap_preserved B,
    nuclear_isotope_static_degeneracy_transferred B⟩

end InfoGeometry.Canonical.LanglandsFunctorialityNuclearCapstone
