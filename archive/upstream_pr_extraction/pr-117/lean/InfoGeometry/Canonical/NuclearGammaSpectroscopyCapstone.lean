import InfoGeometry.Nuclear.NuclearGammaSpectroscopy

namespace InfoGeometry.Canonical.NuclearGammaSpectroscopyCapstone

open InfoGeometry.Nuclear.GammaSpectroscopy
open InfoGeometry.Nuclear.ChiralPRM

/--
🏆 **CAPSTONE: Canonical Nuclear Gamma Spectroscopy & Chiral Quasiparticle Verification**
-/
theorem nuclear_gamma_spectroscopy_canonical_capstone
    (H : HydrodynamicInertia)
    (bcs : NuclearBCSPairing)
    (state : ChiralDoubletState) :
    (∀ k : Fin 3, 0 ≤ momentOfInertia H k) ∧
    (bcs.pairingGap ≤ quasiparticleEnergy bcs) ∧
    ((bcsPairingPfaffian bcs).pfaffianAmplitude ^ 2 = bcs.pairingGap ^ 2) ∧
    (energyMinus state - energyPlus state = 2 * state.Delta) ∧
    (state.Delta = 0 → energyPlus state = energyMinus state) := by
  refine ⟨momentOfInertia_nonneg H,
          quasiparticleEnergy_ge_gap bcs,
          bcs_pfaffian_sq_eq_gap_sq bcs,
          chiral_doublet_energy_splitting state,
          chiral_partner_energies_identical state⟩

end InfoGeometry.Canonical.NuclearGammaSpectroscopyCapstone
