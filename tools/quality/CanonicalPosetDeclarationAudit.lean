/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys
import InfoGeometry.OperatorAlgebra.PeirceSpine.GravitoElectromagneticBridge
import InfoGeometry.OperatorAlgebra.OntologyRing
import InfoGeometry.OperatorAlgebra.SymmetryInvariants
import InfoGeometry.Canonical.GrothendieckElementaryExpansionOperatorCalculus
import InfoGeometry.Canonical.GrothendieckElementaryExpansionPoset
import InfoGeometry.Canonical.GrothendieckElementaryExpansionPeirceCylinderPoset
import InfoGeometry.Canonical.WheelerQuantumFoamPlanckPopperPoset
import InfoGeometry.Canonical.DoubledPlabicTwistedAmplituhedronFoam
import InfoGeometry.Canonical.FriedmanFoundationsUltrafilterPoset
import InfoGeometry.Canonical.WheelerGodelQuantumExistencePoset
import InfoGeometry.Canonical.WheelerGodelRotatingUniverseChronologyPoset
import InfoGeometry.Canonical.TwelveRungMasterPeirceKreinZornColimitPoset
import InfoGeometry.Canonical.KitaevCliffordShiftHigherBerryE8Mod24Poset
import InfoGeometry.Canonical.KitaevSYKHolographyScramblonPoset
import InfoGeometry.Parafermion.ParafermionCondensationGaloisCharacterPoset
import InfoGeometry.Canonical.EpistemicCompilerSelfBootstrapPoset
import InfoGeometry.Canonical.GolayLeechPerfectCodesPoset
import InfoGeometry.Canonical.LanguageStatisticsCirculantBirkhoffYangianPeircePoset
import InfoGeometry.Canonical.LanguageSymmetryCirculantToeplitzBirkhoffPeircePoset
import InfoGeometry.Canonical.SYKQuantumChaosMSSBoundCapstone
import InfoGeometry.Canonical.SYKTwoCopyInterface
import InfoGeometry.Canonical.RelativeDeterminantScatteringSocket
import InfoGeometry.Synthesis.ShirokovTernaryCliffordUnitarySU3Synthesis
import InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon
import InfoGeometry.Archetypes.SouriauKaluzaNativeMatrixBridge
import InfoGeometry.Canonical.AnalogGravityPoset
import InfoGeometry.Canonical.DualBruhatHalmosKleinSeamColimitAnalyticPoset
import InfoGeometry.Canonical.ModularSurprisalVolumeClockingBKMClosurePoset
import InfoGeometry.Canonical.HestenesKreinGaussBonnetAnalyticDerivationPoset
import InfoGeometry.Canonical.EinsteinCartanChiralAnomalyFrameDraggingPoset
import InfoGeometry.Canonical.JaynesianNilpotentInductiveColimitContinuumPoset
import InfoGeometry.Canonical.SouriauKaluzaJanusBimetricPoset
import InfoGeometry.Canonical.ChiralCondensateGMORBanksCasherNJLPoset
import InfoGeometry.Canonical.SouriauChernFourierCharpolyCyclotomicPoset
import InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset
import InfoGeometry.GaloisQuotient.GaloisQuotientNonAbelianFourierPoset
import InfoGeometry.Canonical.FiniteCharacterMatrixOrder
import InfoGeometry.Canonical.GaloisQuotientDihedralL8ClosureBridge
import InfoGeometry.CliffordBottKTheoryWignerS4.CliffordBottKTheoryWignerS4Poset
import InfoGeometry.WignerHurwitzAdamsKTheory.WignerHurwitzAdamsKTheoryPoset
import InfoGeometry.PinMinus88Triality.PinMinus88TrialityPoset
import InfoGeometry.Canonical.KitaevLocalGapOmegaSpectrumKOPoset
import InfoGeometry.CondensedMatter.KitaevFreeFermionKOSpectrumLocalGapPoset
import InfoGeometry.KitaevLocalGapOmegaSpectrum.KitaevLocalGapOmegaSpectrumPoset
import InfoGeometry.Kitaev.KitaevLocalGapOmegaSpectrumPoset
import InfoGeometry.Canonical.KitaevCliffordBottHurwitzKTheoryBridge
import InfoGeometry.Canonical.TypedCategoryInductiveColimitInverseLimitPoset
import InfoGeometry.Canonical.ColimitInverseLimitOntologyTaxonomyPhylogenesisPoset
import InfoGeometry.Canonical.InductiveCategoricalColimitInverseLimitUnificationPoset
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.Data.Json

/-!
# Canonical Poset & Peirce–Bruhat Declaration + Heartbeat Audit

Reuses the kernel environment inspection pattern from
`tools/quality/OperatorGeometryDeclarationAudit.lean` to audit every declaration owned by the
canonical poset modules and `InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys`:
1. Verifies that no declaration is `unsafe`, `partial`, `opaque`, or a local `axiom`.
2. Verifies that all transitive axioms are restricted to the standard Lean whitelist
   `#[propext, Classical.choice, Quot.sound]`, and that all constructive/choice-free theorems
   (Lawvere diagonal, Gödel incompleteness, DP-NEP, Cantor diagonal, Kruskal `TREE(1)=1` and
   `TREE(2)=3`, Peirce–Bruhat mirror, and Choice-Free Definable Angel) do not depend on
   `Classical.choice`.
3. Runs `#count_heartbeats` guards on hot non-commutative `peirce_nf` operator-algebra paths.
-/

open Lean Elab Command
open InfoGeometry.OperatorAlgebra.PeirceSpine

namespace CanonicalPosetDeclarationAudit

section HeartbeatGuards

variable {B : Type*} [Ring B]

-- Heartbeat guard on degree-3 Bruhat idempotency normalization via `peirce_nf`.
#count_heartbeats in
example (P A C : B) (hP : P * P = P) :
    dressedPeirceProjector P A C * dressedPeirceProjector P A C =
      dressedPeirceProjector P A C := by
  dsimp [dressedPeirceProjector]
  peirce_nf hP

-- Heartbeat guard on inner Gödel / outer Friedman Bruhat projector orthogonality via `peirce_nf`.
#count_heartbeats in
example (P A D : B) (hP : P * P = P) :
    (P - genPhi P A D - genSig P A D + genV P A D * conePlus P A) *
      ((1 - P) + genPhi P A D + genSig P A D - genV P A D * conePlus P A) = 0 := by
  peirce_nf hP

-- Heartbeat guard on constructive elementary expansion 4-term word and commutator shift via `peirce_nf`.
#count_heartbeats in
example (P g X : B) (hP : P * P = P) :
    evenGrade P
        (InfoGeometry.Canonical.GrothendieckElementaryExpansionOperatorCalculus.cornerConjugation P g g (P * X * P) -
          P * X * P) =
      - comm (conePlus P g) (coneMinus P g * (P * X * P)) := by
  dsimp only [InfoGeometry.Canonical.GrothendieckElementaryExpansionOperatorCalculus.cornerConjugation,
    InfoGeometry.Canonical.GrothendieckElementaryExpansionOperatorCalculus.cornerConjugator,
    InfoGeometry.Canonical.GrothendieckElementaryExpansionOperatorCalculus.cornerConjugatorInv]
  peirce_nf hP

-- Heartbeat guard on SYK two-shockwave right-sheet readout and intra-corner commutator correction via `peirce_nf`.
#count_heartbeats in
example (P X Y Z : B) (hP : P * P = P) :
    evenGrade P
        (InfoGeometry.Canonical.GrothendieckElementaryExpansionOperatorCalculus.cornerConjugation P X Y (P * Z * P) -
          P * Z * P) =
      - comm (P * Z * P * conePlus P X) (coneMinus P Y) +
        comm (P * Z * P) (conePlus P X * coneMinus P Y) := by
  dsimp only [InfoGeometry.Canonical.GrothendieckElementaryExpansionOperatorCalculus.cornerConjugation,
    InfoGeometry.Canonical.GrothendieckElementaryExpansionOperatorCalculus.cornerConjugator,
    InfoGeometry.Canonical.GrothendieckElementaryExpansionOperatorCalculus.cornerConjugatorInv]
  peirce_nf hP

end HeartbeatGuards

private def owners : Array Name := #[
  `InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys,
  `InfoGeometry.Canonical.GrothendieckElementaryExpansionOperatorCalculus,
  `InfoGeometry.Canonical.GrothendieckElementaryExpansionPoset,
  `InfoGeometry.Canonical.GrothendieckElementaryExpansionPeirceCylinderPoset,
  `InfoGeometry.Canonical.WheelerQuantumFoamPlanckPopperPoset,
  `InfoGeometry.Canonical.DoubledPlabicTwistedAmplituhedronFoam,
  `InfoGeometry.Canonical.FriedmanFoundationsUltrafilterPoset,
  `InfoGeometry.Canonical.WheelerGodelQuantumExistencePoset,
  `InfoGeometry.Canonical.TwelveRungMasterPeirceKreinZornColimitPoset,
  `InfoGeometry.Canonical.KitaevCliffordShiftHigherBerryE8Mod24Poset,
  `InfoGeometry.Canonical.KitaevSYKHolographyScramblonPoset,
  `InfoGeometry.Canonical.AnalogGravityPoset,
  `InfoGeometry.Canonical.DualBruhatHalmosKleinSeamColimitAnalyticPoset,
  `InfoGeometry.Canonical.ModularSurprisalVolumeClockingBKMClosurePoset,
  `InfoGeometry.Canonical.HestenesKreinGaussBonnetAnalyticDerivationPoset,
  `InfoGeometry.Canonical.EinsteinCartanChiralAnomalyFrameDraggingPoset,
  `InfoGeometry.Canonical.JaynesianNilpotentInductiveColimitContinuumPoset,
  `InfoGeometry.Canonical.SouriauKaluzaJanusBimetricPoset,
  `InfoGeometry.Canonical.ChiralCondensateGMORBanksCasherNJLPoset,
  `InfoGeometry.Canonical.SouriauChernFourierCharpolyCyclotomicPoset,
  `InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset,
  `InfoGeometry.OperatorAlgebra.PeirceSpine.GravitoElectromagneticBridge,
  `InfoGeometry.OperatorAlgebra.OntologyRing,
  `InfoGeometry.OperatorAlgebra.SymmetryInvariants,
  `InfoGeometry.Canonical.WheelerGodelRotatingUniverseChronologyPoset,
  `InfoGeometry.Canonical.SYKQuantumChaosMSSBoundCapstone,
  `InfoGeometry.Canonical.SYKTwoCopyInterface,
  `InfoGeometry.Canonical.RelativeDeterminantScatteringSocket,
  `InfoGeometry.Synthesis.ShirokovTernaryCliffordUnitarySU3Synthesis,
  `InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon,
  `InfoGeometry.Archetypes.SouriauKaluzaNativeMatrixBridge,
  `InfoGeometry.Parafermion.ParafermionCondensationGaloisCharacterPoset,
  `InfoGeometry.Canonical.EpistemicCompilerSelfBootstrapPoset,
  `InfoGeometry.Canonical.GolayLeechPerfectCodesPoset,
  `InfoGeometry.Canonical.LanguageStatisticsCirculantBirkhoffYangianPeircePoset,
  `InfoGeometry.Canonical.LanguageSymmetryCirculantToeplitzBirkhoffPeircePoset,
  `InfoGeometry.GaloisQuotient.GaloisQuotientNonAbelianFourierPoset,
  `InfoGeometry.Canonical.FiniteCharacterMatrixOrder,
  `InfoGeometry.Canonical.GaloisQuotientDihedralL8ClosureBridge,
  `InfoGeometry.CliffordBottKTheoryWignerS4.CliffordBottKTheoryWignerS4Poset,
  `InfoGeometry.WignerHurwitzAdamsKTheory.WignerHurwitzAdamsKTheoryPoset,
  `InfoGeometry.PinMinus88Triality.PinMinus88TrialityPoset,
  `InfoGeometry.Canonical.KitaevLocalGapOmegaSpectrumKOPoset,
  `InfoGeometry.CondensedMatter.KitaevFreeFermionKOSpectrumLocalGapPoset,
  `InfoGeometry.KitaevLocalGapOmegaSpectrum.KitaevLocalGapOmegaSpectrumPoset,
  `InfoGeometry.Kitaev.KitaevLocalGapOmegaSpectrumPoset,
  `InfoGeometry.Canonical.KitaevCliffordBottHurwitzKTheoryBridge,
  `InfoGeometry.Canonical.TypedCategoryInductiveColimitInverseLimitPoset,
  `InfoGeometry.Canonical.ColimitInverseLimitOntologyTaxonomyPhylogenesisPoset,
  `InfoGeometry.Canonical.InductiveCategoricalColimitInverseLimitUnificationPoset
]

private def choiceFreeTheorems : Array Name := #[
  `InfoGeometry.Canonical.FriedmanFoundationsUltrafilterPoset.lawvere_universal_diagonal_duality,
  `InfoGeometry.Canonical.FriedmanFoundationsUltrafilterPoset.godel_second_incompleteness_reverse_math_amplifier,
  `InfoGeometry.Canonical.FriedmanFoundationsUltrafilterPoset.friedman_dp_implies_bounded_nep_compiler,
  `InfoGeometry.Canonical.FriedmanFoundationsUltrafilterPoset.bitwise_peirce_dp_tree_compiler,
  `InfoGeometry.Canonical.FriedmanFoundationsUltrafilterPoset.cantor_diagonal_escapes_all,
  `InfoGeometry.Canonical.FriedmanFoundationsUltrafilterPoset.tree_one_no_length_two,
  `InfoGeometry.Canonical.FriedmanFoundationsUltrafilterPoset.tree_two_no_length_four,
  `InfoGeometry.Canonical.FriedmanFoundationsUltrafilterPoset.inner_godel_outer_friedman_bruhat_mirror,
  `InfoGeometry.Canonical.FriedmanFoundationsUltrafilterPoset.socratic_aporia_outer_identity_defect,
  `InfoGeometry.Canonical.FriedmanFoundationsUltrafilterPoset.principal_god_lump_collapse,
  `InfoGeometry.Canonical.FriedmanFoundationsUltrafilterPoset.choice_free_definable_angel_homomorphism,
  `InfoGeometry.Canonical.FriedmanFoundationsUltrafilterPoset.angel_singleton_not_definable_of_nonprincipal,
  `InfoGeometry.Canonical.WheelerGodelQuantumExistencePoset.wheeler_how_come_quantum_iff_how_come_existence,
  `InfoGeometry.Canonical.DoubledPlabicTwistedAmplituhedronFoam.peirce_bruhat_positroid_idempotent_and_annihilator,
  `InfoGeometry.Canonical.WheelerQuantumFoamPlanckPopperPoset.popper_survival_implies_surprise,
  `InfoGeometry.OperatorAlgebra.PeirceSpine.internal_globular_boundary_squared_zero,
  `InfoGeometry.OperatorAlgebra.PeirceSpine.coherator_weak_vs_strict_socratic_defect,
  `InfoGeometry.OperatorAlgebra.PeirceSpine.constructive_elementary_expansion_word_and_commutator_shift,
  `InfoGeometry.OperatorAlgebra.PeirceSpine.constructive_elementary_expansion_retraction_isomorphism,
  `InfoGeometry.Canonical.GrothendieckElementaryExpansionOperatorCalculus.internal_globular_boundary_squared_zero,
  `InfoGeometry.Canonical.GrothendieckElementaryExpansionOperatorCalculus.eckmann_hilton_strict_commutativity,
  `InfoGeometry.Canonical.GrothendieckElementaryExpansionOperatorCalculus.coherator_weak_vs_strict_socratic_defect,
  `InfoGeometry.Canonical.GrothendieckElementaryExpansionOperatorCalculus.cornerConjugator_mul_inverse,
  `InfoGeometry.Canonical.GrothendieckElementaryExpansionOperatorCalculus.cornerConjugation_base_left_inverse,
  `InfoGeometry.Canonical.GrothendieckElementaryExpansionOperatorCalculus.cornerConjugation_expanded_right_inverse,
  `InfoGeometry.Canonical.GrothendieckElementaryExpansionOperatorCalculus.cornerConjugation_mul,
  `InfoGeometry.Canonical.GrothendieckElementaryExpansionOperatorCalculus.cornerConjugation_base_expansion,
  `InfoGeometry.Canonical.GrothendieckElementaryExpansionOperatorCalculus.cornerConjugation_even_shift,
  `InfoGeometry.Canonical.GrothendieckElementaryExpansionOperatorCalculus.cornerConjugation_even_shift_commutator_correction,
  `InfoGeometry.Canonical.GrothendieckElementaryExpansionOperatorCalculus.cornerConjugation_even_shift_eq_commutator,
  `InfoGeometry.Canonical.GrothendieckElementaryExpansionOperatorCalculus.cornerConjugation_even_shift_eq_reverse_commutator,
  `InfoGeometry.Canonical.GrothendieckElementaryExpansionOperatorCalculus.cornerConjugation_projection_retraction_isomorphism,
  `InfoGeometry.Canonical.KitaevSYKHolographyScramblonPoset.sl2_rindler_wedge_and_tfd_scramblon_excitation,
  `InfoGeometry.Canonical.KitaevSYKHolographyScramblonPoset.peirce_horizon_bracket_matches_boost_iff_unit_foam,
  `InfoGeometry.Canonical.KitaevSYKHolographyScramblonPoset.syk_probe_bath_integer_dimension_lock,
  `InfoGeometry.Canonical.KitaevSYKHolographyScramblonPoset.wick_scramblon_ladder_and_shockwave_entanglement_action,
  `InfoGeometry.Canonical.KitaevSYKHolographyScramblonPoset.two_corner_shockwave_sheet_transfer_round_trip,
  `InfoGeometry.Canonical.KitaevSYKHolographyScramblonPoset.finite_rindler_boost_scramblon_scaling_and_schwarzian_moebius_jet,
  `InfoGeometry.Canonical.GrothendieckElementaryExpansionPoset.eckmann_hilton_strict_commutativity,
  `InfoGeometry.Canonical.GrothendieckElementaryExpansionPoset.ara_two_out_of_three_dimensionwise_bijective,
  `InfoGeometry.Canonical.KitaevCliffordShiftHigherBerryE8Mod24Poset.finite_rindler_boost_scramblon_scaling_and_schwarzian_moebius_jet,
  `InfoGeometry.Canonical.KitaevCliffordShiftHigherBerryE8Mod24Poset.syk7_kitaev_holography_scramblon_and_grothendieck_shockwave_expansion_synthesis,
  `InfoGeometry.Canonical.KitaevCliffordShiftHigherBerryE8Mod24Poset.kitaev_local_gap_centered_band_square_identity,
  `ParafermionCondensationGaloisCharacterPoset.zfSpinNum_charge_conjugation,
  `ParafermionCondensationGaloisCharacterPoset.zfSpinNum_half_period_even,
  `ParafermionCondensationGaloisCharacterPoset.parafermion_and_vortex_spin_numerator_examples,
  `ParafermionCondensationGaloisCharacterPoset.negation_action_fixes_iff_two_mul_eq_zero,
  `ParafermionCondensationGaloisCharacterPoset.scalar_action_invariant_of_unit_sq_eq_one,
  `ParafermionCondensationGaloisCharacterPoset.finite_unit_action_fixed_residues,
  `ParafermionCondensationGaloisCharacterPoset.quadratic_residue_invariance_selected_moduli,
  `ParafermionCondensationGaloisCharacterPoset.spin_numerator_remainder_zero_iff_zero_remainder,
  `ParafermionCondensationGaloisCharacterPoset.cyclic_character_sum_ring_identities,
  `InfoGeometry.Canonical.EpistemicCompilerSelfBootstrapPoset.twistedCoagulaDefect_one,
  `InfoGeometry.Canonical.EpistemicCompilerSelfBootstrapPoset.primordial_binary_cut_and_noncommutative_asymmetry,
  `InfoGeometry.Canonical.EpistemicCompilerSelfBootstrapPoset.fourfold_relational_anatomy_decomposition,
  `InfoGeometry.Canonical.EpistemicCompilerSelfBootstrapPoset.transcendent_function_ignition_laws,
  `InfoGeometry.Canonical.EpistemicCompilerSelfBootstrapPoset.socratic_aporia_thesis_square_defect,
  `InfoGeometry.Canonical.EpistemicCompilerSelfBootstrapPoset.quine_self_compilation_shadow_necessity,
  `InfoGeometry.Canonical.EpistemicCompilerSelfBootstrapPoset.meta_cognitive_horizon_expansion_idempotence,
  `InfoGeometry.Canonical.EpistemicCompilerSelfBootstrapPoset.epistemic_compiler_grand_unified_coagulation,
  `InfoGeometry.Canonical.GolayLeechPerfectCodesPoset.hammingBallVol_one,
  `InfoGeometry.Canonical.GolayLeechPerfectCodesPoset.perfect_code_sphere_packing_trinity,
  `InfoGeometry.Canonical.GolayLeechPerfectCodesPoset.witt_steiner_design_block_counts,
  `InfoGeometry.Canonical.GolayLeechPerfectCodesPoset.gleason_golay_w24_polynomial_identity,
  `InfoGeometry.Canonical.GolayLeechPerfectCodesPoset.leech_lattice_root_annihilation_and_theta_series,
  `InfoGeometry.Canonical.GolayLeechPerfectCodesPoset.conway_threefold_leech_decomposition_and_monster_griess,
  `InfoGeometry.Canonical.GolayLeechPerfectCodesPoset.golay_leech_perfect_codes_parafermion_peirce_master_synthesis,
  `InfoGeometry.Canonical.LanguageStatisticsCirculantBirkhoffYangianPeircePoset.LanguageStatisticsPeirceStage.causalEdge_acyclic,
  `InfoGeometry.Canonical.LanguageStatisticsCirculantBirkhoffYangianPeircePoset.involution_quotient_second_order_variance,
  `InfoGeometry.Canonical.LanguageStatisticsCirculantBirkhoffYangianPeircePoset.peirce_rotor_conjugation_and_commutator,
  `InfoGeometry.Canonical.LanguageStatisticsCirculantBirkhoffYangianPeircePoset.conditional_involution_compression_variance,
  `InfoGeometry.Canonical.LanguageSymmetryCirculantToeplitzBirkhoffPeircePoset.LanguageSymmetryPeirceStage.rank_injective,
  `InfoGeometry.Canonical.LanguageSymmetryCirculantToeplitzBirkhoffPeircePoset.LanguageSymmetryPeirceStage.causalEdge_acyclic,
  `InfoGeometry.Canonical.LanguageSymmetryCirculantToeplitzBirkhoffPeircePoset.helper_word_ablation_resilience_and_shift_equivariance,
  `InfoGeometry.Canonical.LanguageSymmetryCirculantToeplitzBirkhoffPeircePoset.binary_involution_spectral_linearization,
  `GaloisQuotientNonAbelianFourierPoset.GaloisQuotientFourierStage.coverEdge_acyclic,
  `GaloisQuotientNonAbelianFourierPoset.ramanujanSum12_divisor_shells_and_fourier_orthogonality,
  `GaloisQuotientNonAbelianFourierPoset.dihedral_peter_weyl_2x2_peirce_representation,
  `GaloisQuotientNonAbelianFourierPoset.dihedral_reflected_rotor_involution_and_two_reflection_rotation,
  `GaloisQuotientNonAbelianFourierPoset.quotient_surprisal_normal_form_and_second_order_survival,
  `GaloisQuotientNonAbelianFourierPoset.peirce_off_diagonal_involution_is_micro_attribute,
  `CliffordBottKTheoryWignerS4Poset.CliffordBottWignerS4Stage.rank_injective,
  `CliffordBottKTheoryWignerS4Poset.CliffordBottWignerS4Stage.coverEdge_acyclic,
  `WignerHurwitzAdamsKTheoryPoset.WignerHurwitzAdamsStage.rank_injective,
  `WignerHurwitzAdamsKTheoryPoset.WignerHurwitzAdamsStage.coverEdge_acyclic,
  `PinMinus88TrialityPoset.PinMinus88TrialityStage.rank_injective,
  `PinMinus88TrialityPoset.PinMinus88TrialityStage.coverEdge_acyclic,
  `PinMinus88TrialityPoset.Quat.toWHQuat_bridge,
  `PinMinus88TrialityPoset.pin_minus_abk_triality_cyclotomic_bridge,
  `InfoGeometry.Canonical.KitaevLocalGapOmegaSpectrumKOPoset.KitaevKOSpectrumStage.rank_injective,
  `InfoGeometry.Canonical.KitaevLocalGapOmegaSpectrumKOPoset.KitaevKOSpectrumStage.coverEdge_acyclic,
  `InfoGeometry.Canonical.KitaevLocalGapOmegaSpectrumKOPoset.kitaev_local_gap_centered_band_square_identity,
  `InfoGeometry.Canonical.KitaevLocalGapOmegaSpectrumKOPoset.ims_single_double_commutator_identity,
  `InfoGeometry.Canonical.KitaevLocalGapOmegaSpectrumKOPoset.kitaev_soft_diagonal_restriction_and_dimer_loop_shift,
  `InfoGeometry.CondensedMatter.KitaevFreeFermionKOSpectrumLocalGapPoset.KitaevFreeFermionKOSpectrumStage.rank_injective,
  `InfoGeometry.CondensedMatter.KitaevFreeFermionKOSpectrumLocalGapPoset.KitaevFreeFermionKOSpectrumStage.coverEdge_acyclic,
  `KitaevLocalGapOmegaSpectrumPoset.KitaevLocalGapStage.rank_injective,
  `KitaevLocalGapOmegaSpectrumPoset.KitaevLocalGapStage.coverEdge_acyclic,
  `KitaevLocalGapOmegaSpectrumPoset.convex_hamiltonian_fiber_ground_state_invariance,
  `KitaevLocalGapOmegaSpectrumPoset.energy_gap_annulus_midpoint_centering,
  `KitaevLocalGapOmegaSpectrumPoset.n_plus_minus_eq_centralizer_cones,
  `KitaevLocalGapOmegaSpectrumPoset.square_first_local_bulk_gap_collar_healing,
  `InfoGeometry.Kitaev.KitaevLocalGapOmegaSpectrumPoset.KitaevLocalGapOmegaSpectrumStage.rank_injective,
  `InfoGeometry.Kitaev.KitaevLocalGapOmegaSpectrumPoset.KitaevLocalGapOmegaSpectrumStage.coverEdge_acyclic,
  `InfoGeometry.Kitaev.KitaevLocalGapOmegaSpectrumPoset.convex_hamiltonian_fiber_ground_state_invariance,
  `InfoGeometry.Kitaev.KitaevLocalGapOmegaSpectrumPoset.energy_gap_annulus_midpoint_centering,
  `InfoGeometry.Kitaev.KitaevLocalGapOmegaSpectrumPoset.square_first_local_bulk_gap_collar_healing,
  `InfoGeometry.Canonical.TypedCategoryInductiveColimitInverseLimitPoset.TypedCategoryLimitColimitStage.rank_injective,
  `InfoGeometry.Canonical.TypedCategoryInductiveColimitInverseLimitPoset.TypedCategoryLimitColimitStage.causalEdge_acyclic,
  `InfoGeometry.Canonical.TypedCategoryInductiveColimitInverseLimitPoset.tc1_typed_inductive_and_inverse_diagram_functoriality_and_retraction_section,
  `InfoGeometry.Canonical.InductiveCategoricalColimitInverseLimitUnificationPoset.ColimitDevelopmentStratum.rank_injective,
  `InfoGeometry.Canonical.InductiveCategoricalColimitInverseLimitUnificationPoset.ColimitDevelopmentStratum.rankEdge_acyclic,
  `InfoGeometry.Canonical.InductiveCategoricalColimitInverseLimitUnificationPoset.ColimitInverseLimitUnificationStage.rank_injective,
  `InfoGeometry.Canonical.InductiveCategoricalColimitInverseLimitUnificationPoset.ColimitInverseLimitUnificationStage.causalEdge_acyclic
]

private def kindOf : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "definition"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quotient"

run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut names : Array Name := #[]
  for ownerMod in owners do
    if let some modIdx := env.getModuleIdx? ownerMod then
      if _h : modIdx.toNat < env.header.moduleData.size then
        for n in env.header.moduleData[modIdx.toNat].constNames do
          if !n.isInternal then
            names := names.push n
  names := names.qsort Name.lt
  if names.isEmpty then
    throwError "No declarations found in requested canonical poset owner modules"
  let mut thmCount : Nat := 0
  for name in names do
    let some info := env.find? name | throwError "Missing declaration {name}"
    let axioms ← collectAxioms name
    if info.isUnsafe || info.isPartial || kindOf info == "axiom" then
      throwError "Rejected declaration {name}: unsafe, partial, or local axiom"
    for ax in axioms do
      if !allowed.contains ax then
        throwError "Rejected axiom {ax} in declaration {name}"
    if kindOf info == "theorem" then
      thmCount := thmCount + 1
  for thmName in choiceFreeTheorems do
    let some _ := env.find? thmName | throwError "Missing choice-free target theorem {thmName}"
    let axioms ← collectAxioms thmName
    if axioms.contains `Classical.choice then
      throwError "Rejected Classical.choice dependency in constructive theorem {thmName}"
  liftIO <| IO.println (Json.mkObj [
    ("record", toJson "summary"),
    ("declarations", toJson names.size),
    ("theorem_declarations", toJson thmCount),
    ("choice_free_verified", toJson choiceFreeTheorems.size),
    ("modules", toJson (owners.map Name.toString)),
    ("axiom_whitelist", toJson (allowed.map Name.toString)),
    ("status", toJson "PASS")
  ]).compress

end CanonicalPosetDeclarationAudit
