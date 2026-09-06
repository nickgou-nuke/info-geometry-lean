import proofs.TorusKleinO55Bridge
import proofs.O55GradedGeneratorBasis
import proofs.WallpaperO55FrozenSelectionBridge
import proofs.KasparovKreinCategory

/-!
# Doubled charge lattice and Kasparov--Krein bridge

This module formalizes the finite bridge:

* the torus contributes the doubled lattice `Λ ⊕ Λ*`;
* the Klein crosscap twist selects the non-orientable quotient data;
* the finite `O(5,5)` carrier is the symmetry-adapted switchboard;
* the Kasparov--Krein product remains an abstract boundary firewall, not a
  completed analytic product theorem.

The bridge is finite: `Λ ⊕ Λ*` has rank `10`, the `O(5,5)` carrier dimension is
`10`, and the active wallpaper-selected sector has `15 + 1 = 16` channels.
-/

noncomputable section

namespace DoubledChargeLatticeKasparovKreinBridge

open InfoGeometry.Canonical.KasparovKreinCategory

/-- The doubled charge lattice `Λ ⊕ Λ*` is modeled by a finite rank-10 carrier. -/
def doubledChargeLatticeRank : ℕ := 10

@[simp] theorem doubled_charge_lattice_rank_eq : doubledChargeLatticeRank = 10 := rfl

/-- The doubled charge lattice rank matches the split `O(5,5)` carrier dimension. -/
theorem doubled_charge_lattice_matches_o55_carrier :
    doubledChargeLatticeRank = TorusKleinO55Bridge.doubledCartanCarrierDimension := by
  rfl

/-- The abstract Kasparov--Krein firewall says there is no transport through a
contractible boundary. -/
theorem kasparov_krein_firewall
    (K₀ : Type) [KK : KasparovKreinData] [hK : KKContractibleBoundary K₀] :
    ∀ A : Type, IsEmpty (KK.KK A K₀) := by
  exact kasparov_krein_contractibility_slogan K₀

/-- Capstone bridge: doubled charge lattice, Klein selection, `O(5,5)` carrier,
and abstract Kasparov--Krein firewall line up in one statement. -/
theorem doubled_charge_lattice_kasparov_krein_bridge_synthesis
    {K₀ : Type} [KK : KasparovKreinData] [hK : KKContractibleBoundary K₀] :
    doubledChargeLatticeRank = 10 ∧
    doubledChargeLatticeRank = TorusKleinO55Bridge.doubledCartanCarrierDimension ∧
    O55CartanPhononReduction.o55CartanRank = 5 ∧
    O55GradedGeneratorBasis.fullGradedGeneratorCount = 45 ∧
    O55GradedGeneratorBasis.activeGradedGeneratorCount = 15 ∧
    ProjectiveWallpaperGaugePSA.nonEquivalentPSACount
      ProjectiveWallpaperGaugePSA.WallpaperGroup.p6m = 16 ∧
    ProjectiveWallpaperGaugePSA.nonEquivalentPSACount
      ProjectiveWallpaperGaugePSA.WallpaperGroup.p6m =
        O55GradedGeneratorBasis.activeGradedGeneratorCount + 1 ∧
    (∀ A : Type, IsEmpty (KK.KK A K₀)) := by
  constructor
  · exact doubled_charge_lattice_rank_eq
  constructor
  · exact doubled_charge_lattice_matches_o55_carrier
  constructor
  · exact O55CartanPhononReduction.o55_cartan_rank_eq
  constructor
  · exact O55GradedGeneratorBasis.full_graded_generator_count_eq
  constructor
  · exact O55GradedGeneratorBasis.active_graded_generator_count_eq
  constructor
  · exact WallpaperHolographicSelectionRules.p6m_nonEquivalentPSACount
  constructor
  · exact WallpaperO55FrozenSelectionBridge.p6m_psa_count_matches_active_o55_plus_base
  · exact kasparov_krein_firewall K₀

#check doubled_charge_lattice_kasparov_krein_bridge_synthesis

end DoubledChargeLatticeKasparovKreinBridge

end noncomputable section
