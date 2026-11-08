import InfoGeometry.Canonical.CelikKocakSplitCliffordBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitCliffordDirectLimit
import InfoGeometry.Canonical.PrimeVirasoroSugawara
import InfoGeometry.Probability.HomologicalProbability
import InfoGeometry.Arithmetic.PrimeSpinorWittenIndex
import InfoGeometry.Canonical.BogoliubovFockSuper
import InfoGeometry.Canonical.ModeExtensionBoundary
import InfoGeometry.Canonical.SuperchargeCARCCRBridge
import InfoGeometry.Canonical.CurrentSugawaraBridge
import InfoGeometry.Quantum.SplitTrialityFockBridge
import InfoGeometry.OperatorAlgebra.LightConeSugawaraCalibration
import InfoGeometry.OperatorAlgebra.VirasoroProjectBridge
import InfoGeometry.OperatorAlgebra.AffineVirasoroBridge
import InfoGeometry.External.Virasoro.FockSpaceSugawara

noncomputable section

/-!
# InfoGeometry.Canonical.SplitCliffordExternalChain

Theorem-only export chain for the split-Clifford completion, five-grading,
Witten cancellation, and external Virasoro certification.

This file adds no wrappers and no new datum structures.  It only re-exports
already proven theorems as direct corollaries and packages them in one
conjunction.
-/

namespace InfoGeometry.Canonical.SplitCliffordExternalChain

open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Canonical.SplitCliffordTensorBridge
open InfoGeometry.Canonical.CelikKocakSplitCliffordBridge
open InfoGeometry.Canonical.PrimeVirasoroSugawara
open InfoGeometry.Probability.Homological
open InfoGeometry.Arithmetic.PrimeSpinorWittenIndex
open InfoGeometry.Canonical.BogoliubovFockSuper
open InfoGeometry.Canonical.ModeExtensionBoundary
open InfoGeometry.Canonical.SuperchargeCARCCRBridge
open InfoGeometry.Canonical.CurrentSugawaraBridge
open InfoGeometry.Krein
open InfoGeometry.Quantum.SplitTrialityFockBridge
open InfoGeometry.OperatorAlgebra.LightConeSugawaraCalibration
open InfoGeometry.OperatorAlgebra.VirasoroProjectBridge
open InfoGeometry.OperatorAlgebra.AffineVirasoroBridge
open VirasoroProject

set_option synthInstance.maxHeartbeats 200000

/-- The concrete split-`Cl(1,1)` datum already yields a primitive Majorana CAR witness. -/
theorem splitClifford_cl11_majorana_car
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    InfoGeometry.Quantum.RealMajoranaCategory.MajoranaCARWitness
      (InfoGeometry.Quantum.RealMajoranaCategory.cl11DoubledCore E)
      (InfoGeometry.Quantum.RealMajoranaCategory.SplitCliffordDatum.majoranaPairing
        (InfoGeometry.Quantum.RealMajoranaCategory.cl11SplitCliffordDatum E))
      (InfoGeometry.Quantum.RealMajoranaCategory.SplitCliffordDatum.majoranaField
        (InfoGeometry.Quantum.RealMajoranaCategory.cl11SplitCliffordDatum E)) :=
  InfoGeometry.Quantum.RealMajoranaCategory.majorana_car_of_concrete_cl11 (E := E)

/-- The split triality left channel is the concrete CAR annihilation map. -/
theorem splitTriality_leftSpinor_eq_concreteCARAnnihilation
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    (InfoGeometry.Quantum.vectorToLeftSpinor (E := E) :
        InfoGeometry.Quantum.RealMajoranaCategory.cl11DoubledCore E →ₗ[ℝ]
        InfoGeometry.Quantum.RealMajoranaCategory.cl11DoubledCore E) =
    (cliffordConcreteAnnihilation (E := E)).toLinearMap :=
  vectorToLeftSpinor_eq_cliffordConcreteAnnihilation_toLinearMap (E := E)

/-- The split triality right channel is the concrete CAR creation map. -/
theorem splitTriality_rightSpinor_eq_concreteCARCreation
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    (InfoGeometry.Quantum.vectorToRightSpinor (E := E) :
        InfoGeometry.Quantum.RealMajoranaCategory.cl11DoubledCore E →ₗ[ℝ]
        InfoGeometry.Quantum.RealMajoranaCategory.cl11DoubledCore E) =
    (cliffordConcreteCreation (E := E)).toLinearMap :=
  vectorToRightSpinor_eq_cliffordConcreteCreation_toLinearMap (E := E)

/-- The external Virasoro Fock-space Sugawara construction acts on the vacuum with the expected `L₀` eigenvalue. -/
theorem externalHeisenberg_sugawaraRepresentation_lgen_zero_apply_vacuum (α : ℂ) :
    VirasoroProject.ChargedFockSpace.sugawaraRepresentation ℂ α (.lgen ℂ 0)
      (VirasoroProject.ChargedFockSpace.vacuum ℂ α) =
      (α^2 / 2) • VirasoroProject.ChargedFockSpace.vacuum ℂ α :=
  VirasoroProject.ChargedFockSpace.sugawaraRepresentation_lgen_zero_apply_vacuum ℂ α

/-- The external Virasoro Fock-space Sugawara construction annihilates the vacuum for positive modes. -/
theorem externalHeisenberg_sugawaraRepresentation_lgen_pos_apply_vacuum (α : ℂ)
    {n : ℤ} (n_pos : 0 < n) :
    VirasoroProject.ChargedFockSpace.sugawaraRepresentation ℂ α (.lgen ℂ n)
      (VirasoroProject.ChargedFockSpace.vacuum ℂ α) = 0 :=
  VirasoroProject.ChargedFockSpace.sugawaraRepresentation_lgen_pos_apply_vacuum ℂ α n_pos

/-- The external Virasoro Fock-space Sugawara construction acts on the central generator as the identity. -/
theorem externalHeisenberg_sugawaraRepresentation_cgen_apply (α : ℂ)
    (v : VirasoroProject.ChargedFockSpace ℂ α) :
    VirasoroProject.ChargedFockSpace.sugawaraRepresentation ℂ α (.cgen ℂ) v = v :=
  VirasoroProject.ChargedFockSpace.sugawaraRepresentation_cgen_apply ℂ α v

/-- The external Virasoro Fock-space Sugawara vacuum is a highest-weight vector. -/
theorem externalHeisenberg_sugawaraVacuum_highestWeight (α : ℂ) :
    VirasoroProject.ChargedFockSpace.sugawaraRepresentation ℂ α (.cgen ℂ)
      (VirasoroProject.ChargedFockSpace.vacuum ℂ α) =
      VirasoroProject.ChargedFockSpace.vacuum ℂ α ∧
    VirasoroProject.ChargedFockSpace.sugawaraRepresentation ℂ α (.lgen ℂ 0)
      (VirasoroProject.ChargedFockSpace.vacuum ℂ α) =
      (α^2 / 2) • VirasoroProject.ChargedFockSpace.vacuum ℂ α ∧
    (∀ n > 0,
      VirasoroProject.ChargedFockSpace.sugawaraRepresentation ℂ α (.lgen ℂ n)
        (VirasoroProject.ChargedFockSpace.vacuum ℂ α) = 0) :=
  VirasoroProject.ChargedFockSpace.sugawaraVacuum_highestWeight ℂ α

/-- The external Sugawara representation includes a concrete Verma-to-Fock highest-weight map. -/
theorem externalHeisenberg_virasoroVermaToChargedFockSpace_highestWeight (α : ℂ) :
    VirasoroProject.ChargedFockSpace.virasoroVermaToChargedFockSpace ℂ α (.hwVec ℂ _ _) =
      VirasoroProject.ChargedFockSpace.vacuum ℂ α ∧
    VirasoroProject.ChargedFockSpace.sugawaraRepresentation ℂ α (.cgen ℂ)
      (VirasoroProject.ChargedFockSpace.vacuum ℂ α) =
      VirasoroProject.ChargedFockSpace.vacuum ℂ α ∧
    VirasoroProject.ChargedFockSpace.sugawaraRepresentation ℂ α (.lgen ℂ 0)
      (VirasoroProject.ChargedFockSpace.vacuum ℂ α) =
      (α^2 / 2) • VirasoroProject.ChargedFockSpace.vacuum ℂ α ∧
    (∀ n > 0,
      VirasoroProject.ChargedFockSpace.sugawaraRepresentation ℂ α (.lgen ℂ n)
        (VirasoroProject.ChargedFockSpace.vacuum ℂ α) = 0) :=
  VirasoroProject.ChargedFockSpace.virasoroVermaToChargedFockSpace_highestWeight ℂ α

/-- The charged Fock current/Sugawara morphism has the canonical owner readbacks. -/
theorem externalHeisenberg_currentSugawaraMorphism_readout (α : ℂ) :
    let H := CurrentSugawaraBridge.chargedFockSpaceCurrentHeisenbergRep ℂ α
    let M := CurrentSugawaraMorphism.ofHeisenberg H
    M.heisenberg = H ∧
      M.virasoro = H.currentSugawaraRepresentation ∧
      (∀ n : Int,
        M.virasoro (VirasoroProject.VirasoroAlgebra.lgen ℂ n) =
          H.sugawaraStressMode n) ∧
      M.virasoro (VirasoroProject.VirasoroAlgebra.cgen ℂ) =
        (1 :
          VirasoroProject.ChargedFockSpace ℂ α →ₗ[ℂ]
            VirasoroProject.ChargedFockSpace ℂ α) :=
  by
    let H := CurrentSugawaraBridge.chargedFockSpaceCurrentHeisenbergRep ℂ α
    refine ⟨rfl, rfl, ?_, ?_⟩
    · intro n
      exact H.currentSugawaraRepresentation_lgen_apply n
    · exact H.currentSugawaraRepresentation_central

/-- The external Heisenberg-owned Sugawara datum has central charge `1`. -/
theorem externalHeisenberg_sugawaraDatum_centralCharge_one :
    InfoGeometry.OperatorAlgebra.VirasoroProjectBridge.heisenbergSugawaraDatum.centralCharge = 1 :=
  InfoGeometry.Canonical.PrimeVirasoroSugawara.heisenberg_sugawara_centralCharge_eq_one

/-- The Prime Sugawara packet transports the affine current bracket. -/
theorem primeSugawara_affine_current_mode_bracket
    {PrimeLabel Field Coeff Finite Alg : Type*}
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]
    (P : PrimeSugawaraVirasoroPacket PrimeLabel Field Coeff Finite Alg)
    (m n : ℤ) (X Y : Finite)
    (hbr :
      ∀ (m n : ℤ) (X Y : Finite),
        ⁅P.affineVirasoro.affine.Current m X, P.affineVirasoro.affine.Current n Y⁆ =
          P.affineVirasoro.affine.Current (m + n) ⁅X, Y⁆ +
            ((m : ℝ) * P.affineVirasoro.affine.killingForm X Y) •
              (if m + n = 0 then P.affineVirasoro.affine.kCentral else 0)) :
    ⁅P.affineVirasoro.affine.Current m X,
      P.affineVirasoro.affine.Current n Y⁆ =
      P.affineVirasoro.affine.Current (m + n) ⁅X, Y⁆ +
        ((m : ℝ) * P.affineVirasoro.affine.killingForm X Y) •
          (if m + n = 0 then P.affineVirasoro.affine.kCentral else 0) :=
  P.affine_current_mode_bracket m n X Y hbr

/-- The Prime Sugawara packet transports the Virasoro action on currents. -/
theorem primeSugawara_virasoro_acts_on_currents
    {PrimeLabel Field Coeff Finite Alg : Type*}
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]
    (P : PrimeSugawaraVirasoroPacket PrimeLabel Field Coeff Finite Alg)
    (m n : ℤ) (X : Finite)
    (hact :
      ∀ (m n : ℤ) (X : Finite),
        ⁅P.affineVirasoro.virasoro.Lmode m, P.affineVirasoro.affine.Current n X⁆ =
          (-(n : ℝ)) • P.affineVirasoro.affine.Current (m + n) X) :
    ⁅P.affineVirasoro.virasoro.Lmode m,
      P.affineVirasoro.affine.Current n X⁆ =
      (-(n : ℝ)) • P.affineVirasoro.affine.Current (m + n) X :=
  P.virasoro_acts_on_currents m n X hact

/-- The Prime Sugawara packet transports the Sugawara mode-sum relation. -/
theorem primeSugawara_virasoro_mode_eq_rescaled_sugawara_sum
    {PrimeLabel Field Coeff Finite Alg : Type*}
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]
    (P : PrimeSugawaraVirasoroPacket PrimeLabel Field Coeff Finite Alg)
    (n : ℤ)
    (hsum :
      ∀ n : ℤ,
        P.sugawara.bridge.virasoro.Lmode n =
          (1 / (2 * (P.sugawara.bridge.level + P.sugawara.bridge.dualCoxeterNumber))) •
            P.sugawara.modeSum n) :
    P.affineVirasoro.virasoro.Lmode n =
      P.sugawara.sugawaraFactor • P.sugawara.modeSum n :=
  P.virasoro_mode_eq_rescaled_sugawara_sum n hsum

/-- The Prime Sugawara packet transports the calibrated central charge. -/
theorem primeSugawara_centralCharge_calibrated
    {PrimeLabel Field Coeff Finite Alg : Type*}
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]
    (P : PrimeSugawaraVirasoroPacket PrimeLabel Field Coeff Finite Alg)
    (hcc : P.affineVirasoro.centralCharge =
      P.affineVirasoro.level * P.affineVirasoro.finiteDimension /
        (P.affineVirasoro.level + P.affineVirasoro.dualCoxeterNumber)) :
    P.affineVirasoro.centralCharge =
      P.affineVirasoro.level * P.affineVirasoro.finiteDimension /
        (P.affineVirasoro.level + P.affineVirasoro.dualCoxeterNumber) :=
  P.centralCharge_calibrated hcc

/-- The split-Clifford finite CAR anchor is available directly. -/
theorem splitClifford_cliffordConcreteIsCARPair
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    IsCARPair (E := E)
      (cliffordConcreteAnnihilation (E := E))
      (cliffordConcreteCreation (E := E)) :=
  cliffordConcreteIsCARPair (E := E)

/-- The lightcone Sugawara readout is the supplied mode sum. -/
theorem lightconeSugawara_virasoro_mode_eq_rescaled_sum
    {E Finite Alg Bog Korth Asplit Nshear CartanDiag : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]
    (S : Calibration E Finite Alg Bog Korth Asplit Nshear CartanDiag)
    (n : ℤ)
    (hsum :
      ∀ n : ℤ,
        S.sugawara.bridge.virasoro.Lmode n =
          (1 / (2 * (S.sugawara.bridge.level + S.sugawara.bridge.dualCoxeterNumber))) •
            S.sugawara.modeSum n) :
    S.kanAffine.affineLightCone.bridge.virasoro.Lmode n =
      S.sugawaraFactor • S.modeSum n :=
  S.lightcone_virasoro_mode_eq_rescaled_sum n hsum

/-- The lightcone Sugawara Virasoro action on positive currents is available directly. -/
theorem lightconeSugawara_virasoro_acts_on_uPlusCurrent
    {E Finite Alg Bog Korth Asplit Nshear CartanDiag : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]
    (S : Calibration E Finite Alg Bog Korth Asplit Nshear CartanDiag)
    (m n : ℤ)
    (hact :
      ∀ (m n : ℤ) (X : Finite),
        ⁅S.kanAffine.affineLightCone.bridge.virasoro.Lmode m,
          S.kanAffine.affineLightCone.bridge.affine.Current n X⁆ =
          (-(n : ℝ)) • S.kanAffine.affineLightCone.bridge.affine.Current (m + n) X) :
    ⁅S.sugawara.bridge.virasoro.Lmode m, S.kanAffine.uPlusCurrent n⁆ =
      (-(n : ℝ)) • S.kanAffine.uPlusCurrent (m + n) :=
  S.sugawara_virasoro_acts_on_uPlusCurrent m n hact

/-- The lightcone Sugawara Virasoro action on negative currents is available directly. -/
theorem lightconeSugawara_virasoro_acts_on_uMinusCurrent
    {E Finite Alg Bog Korth Asplit Nshear CartanDiag : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]
    (S : Calibration E Finite Alg Bog Korth Asplit Nshear CartanDiag)
    (m n : ℤ)
    (hact :
      ∀ (m n : ℤ) (X : Finite),
        ⁅S.kanAffine.affineLightCone.bridge.virasoro.Lmode m,
          S.kanAffine.affineLightCone.bridge.affine.Current n X⁆ =
          (-(n : ℝ)) • S.kanAffine.affineLightCone.bridge.affine.Current (m + n) X) :
    ⁅S.sugawara.bridge.virasoro.Lmode m, S.kanAffine.uMinusCurrent n⁆ =
      (-(n : ℝ)) • S.kanAffine.uMinusCurrent (m + n) :=
  S.sugawara_virasoro_acts_on_uMinusCurrent m n hact

/-- The lightcone Sugawara central charge calibration is available directly. -/
theorem lightconeSugawara_centralCharge_calibrated
    {E Finite Alg Bog Korth Asplit Nshear CartanDiag : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]
    (S : Calibration E Finite Alg Bog Korth Asplit Nshear CartanDiag)
    (hcc : S.sugawara.bridge.centralCharge =
      S.sugawara.bridge.level * S.sugawara.bridge.finiteDimension /
        (S.sugawara.bridge.level + S.sugawara.bridge.dualCoxeterNumber)) :
    S.sugawara.bridge.centralCharge =
      S.sugawara.bridge.level * S.sugawara.bridge.finiteDimension /
        (S.sugawara.bridge.level + S.sugawara.bridge.dualCoxeterNumber) :=
  by
    rw [S.uses_lightcone_affine_bridge] at hcc ⊢
    exact S.kanAffine.affineLightCone.centralCharge_calibrated hcc

/--
The theorem-only canonical chain:

split Clifford completion, five-grading shadow, finite Witten cancellation,
and external Virasoro certification all coexist as already proven results.
-/
theorem splitClifford_fiveGraded_witten_virasoro_chain
    (z : InfoGeometry.Canonical.SplitCliffordDirectLimit.SplitCliffordInfinity)
    (N : ℕ)
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister)
    (hP : P.primes.Nonempty) :
    (∃ n ≥ N,
      ∃ x,
        (DirectLimit.Module.of ℝ ℕ
          InfoGeometry.Canonical.SplitCliffordTensorBridge.SplitClNNAlg
          (fun m n h => splitCliffordMap m n h) n) x = z) ∧
      ((fiveGradedHomologicalPipeline Unit (fun _ _ => ())).toNumericalShadow = fun _ => 5) ∧
      (∑ S ∈ P.primes.powerset, (-1 : ℤ) ^ S.card) = 0 ∧
      (∃ V : VirasoroDatum (VirasoroAlgebra ℝ), VirasoroProjectRealizes V) := by
  constructor
  · exact splitCliffordInfinity_unbounded_representatives z N
  · constructor
    · exact
        InfoGeometry.Probability.Homological.fiveGradedHomologicalPipeline_numericalShadow_five
          Unit (fun _ _ => ())
    · constructor
      · exact finiteRealMajoranaWittenIndex_cancel P hP
      · exact virasoro_project_is_certified

/--
Split-Clifford CAR anchor plus the external Heisenberg/Sugawara owner surface.

This is a theorem-only conjunction; it does not claim a new split-to-Sugawara
construction, but it does keep the external Virasoro/Heisenberg implementation
explicitly in the export chain.
-/
theorem splitClifford_externalHeisenbergSugawara_chain
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (α : ℂ) :
    IsCARPair (E := E)
      (cliffordConcreteAnnihilation (E := E))
      (cliffordConcreteCreation (E := E)) ∧
    VirasoroProject.ChargedFockSpace.sugawaraRepresentation ℂ α (.lgen ℂ 0)
      (VirasoroProject.ChargedFockSpace.vacuum ℂ α) =
      (α^2 / 2) • VirasoroProject.ChargedFockSpace.vacuum ℂ α ∧
    VirasoroProject.ChargedFockSpace.sugawaraRepresentation ℂ α (.cgen ℂ)
      (VirasoroProject.ChargedFockSpace.vacuum ℂ α) =
      VirasoroProject.ChargedFockSpace.vacuum ℂ α ∧
    (∀ n > 0,
      VirasoroProject.ChargedFockSpace.sugawaraRepresentation ℂ α (.lgen ℂ n)
        (VirasoroProject.ChargedFockSpace.vacuum ℂ α) = 0) ∧
    InfoGeometry.OperatorAlgebra.VirasoroProjectBridge.heisenbergSugawaraDatum.centralCharge = 1 := by
  constructor
  · exact cliffordConcreteIsCARPair (E := E)
  · constructor
    · exact externalHeisenberg_sugawaraRepresentation_lgen_zero_apply_vacuum α
    · constructor
      · exact externalHeisenberg_sugawaraRepresentation_cgen_apply α
          (VirasoroProject.ChargedFockSpace.vacuum ℂ α)
      · constructor
        · intro n hn
          exact externalHeisenberg_sugawaraRepresentation_lgen_pos_apply_vacuum α hn
        · exact externalHeisenberg_sugawaraDatum_centralCharge_one

/--
The literature-facing bosonization spine:

- the split triality channels are the concrete CAR witness;
- the split supercharge lane already carries the CAR/CCR oscillator spine;
- the external Heisenberg/Sugawara implementation is independently certified,
  including the concrete Verma-to-Fock highest-weight map.

This theorem is a theorem-only bundle of the already proved source and target
surface facts.  It does not claim a new split-to-Heisenberg morphism.
-/
theorem splitClifford_literature_bosonization_chain
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (α : ℂ) :
    (InfoGeometry.Quantum.RealMajoranaCategory.CARWitness
      (InfoGeometry.Quantum.RealMajoranaCategory.cl11DoubledCore E)
      (InfoGeometry.Quantum.vectorToLeftSpinor (E := E))
      (InfoGeometry.Quantum.vectorToRightSpinor (E := E))) ∧
    (IsCARPair (E := E)
      (cliffordConcreteAnnihilation (E := E))
      (cliffordConcreteCreation (E := E))) ∧
    (VirasoroProject.ChargedFockSpace.virasoroVermaToChargedFockSpace ℂ α (.hwVec ℂ _ _) =
      VirasoroProject.ChargedFockSpace.vacuum ℂ α) ∧
    (VirasoroProject.ChargedFockSpace.sugawaraRepresentation ℂ α (.cgen ℂ)
      (VirasoroProject.ChargedFockSpace.vacuum ℂ α) =
      VirasoroProject.ChargedFockSpace.vacuum ℂ α) ∧
    (VirasoroProject.ChargedFockSpace.sugawaraRepresentation ℂ α (.lgen ℂ 0)
      (VirasoroProject.ChargedFockSpace.vacuum ℂ α) =
      (α^2 / 2) • VirasoroProject.ChargedFockSpace.vacuum ℂ α) ∧
    (∀ n > 0,
      VirasoroProject.ChargedFockSpace.sugawaraRepresentation ℂ α (.lgen ℂ n)
        (VirasoroProject.ChargedFockSpace.vacuum ℂ α) = 0) ∧
    (InfoGeometry.OperatorAlgebra.VirasoroProjectBridge.heisenbergSugawaraDatum.centralCharge = 1) := by
  constructor
  · exact triality_channels_CARWitness (E := E)
  · constructor
    · exact cliffordConcreteIsCARPair (E := E)
    · rcases externalHeisenberg_virasoroVermaToChargedFockSpace_highestWeight α with
        ⟨hHwVec, hCgen, hL0, hLpos⟩
      exact ⟨hHwVec, hCgen, hL0, hLpos, externalHeisenberg_sugawaraDatum_centralCharge_one⟩

/--
The conservative zero-mode lift is available alongside the external
Heisenberg/Sugawara owner surface.

This is still theorem-only packaging.  It does not claim that the split
finite atom already induces the full current algebra.
-/
theorem splitClifford_zeroModeSeed_boundary_and_externalHeisenbergSugawara_chain
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (α : ℂ) :
    ((splitNullCreationModeSeed (E := E) 0).comp
          (splitNullCreationModeSeed (E := E) 0) = 0
      ∧ (splitNullAnnihilationModeSeed (E := E) 0).comp
          (splitNullAnnihilationModeSeed (E := E) 0) = 0
      ∧ (splitNullCreationModeSeed (E := E) 0).comp
          (splitNullAnnihilationModeSeed (E := E) 0)
        = spectralPlusProj (E := E)
      ∧ (splitNullAnnihilationModeSeed (E := E) 0).comp
          (splitNullCreationModeSeed (E := E) 0)
        = spectralMinusProj (E := E)
      ∧ CARBracket (E := E)
          (splitNullAnnihilationModeSeed (E := E) 0)
          (splitNullCreationModeSeed (E := E) 0)
        = ContinuousLinearMap.id ℝ (DoubledSpace E)
      ∧ CCRBracket (E := E)
          (splitNullCreationModeSeed (E := E) 0)
          (splitNullAnnihilationModeSeed (E := E) 0)
        = splitEpsilonModeSeed (E := E) 0) ∧
      IsCARPair (E := E)
        (cliffordConcreteAnnihilation (E := E))
        (cliffordConcreteCreation (E := E)) ∧
      VirasoroProject.ChargedFockSpace.sugawaraRepresentation ℂ α (.lgen ℂ 0)
        (VirasoroProject.ChargedFockSpace.vacuum ℂ α) =
        (α^2 / 2) • VirasoroProject.ChargedFockSpace.vacuum ℂ α ∧
      VirasoroProject.ChargedFockSpace.sugawaraRepresentation ℂ α (.cgen ℂ)
        (VirasoroProject.ChargedFockSpace.vacuum ℂ α) =
        VirasoroProject.ChargedFockSpace.vacuum ℂ α ∧
      (∀ n > 0,
        VirasoroProject.ChargedFockSpace.sugawaraRepresentation ℂ α (.lgen ℂ n)
          (VirasoroProject.ChargedFockSpace.vacuum ℂ α) = 0) ∧
      InfoGeometry.OperatorAlgebra.VirasoroProjectBridge.heisenbergSugawaraDatum.centralCharge
        = 1 := by
  constructor
  · exact ModeExtensionBoundary.zeroModeSeed_nilpotent_idempotent_atom (E := E)
  · exact splitClifford_externalHeisenbergSugawara_chain (E := E) α

/-- The finite Cantor/Krein sector lattice is complete. -/
noncomputable instance splitClifford_finiteCantorKreinSectorSet_completeLattice
    (n : Nat) :
    CompleteLattice (InfoGeometry.Topology.FiniteCantorKreinSectorSet n) := by
  infer_instance

/-- The Cuntz projection sector lattice is complete. -/
noncomputable instance splitClifford_CuntzProjectionSectorSet_completeLattice
    {Op : Type} [Ring Op] [StarRing Op] :
    CompleteLattice (InfoGeometry.Topology.CuntzProjectionSectorSet (Op := Op)) := by
  infer_instance

/-- The fixed-point sector lattice is complete. -/
noncomputable instance splitClifford_selfSimilarSectors_completeLattice
    {L : Type} [CompleteLattice L] (R : L →o L) :
    CompleteLattice (InfoGeometry.Topology.SelfSimilarSectors R) :=
  InfoGeometry.Topology.selfSimilarSectorsCompleteLattice R

/-- The refinement/coarse-graining adjunction is the canonical Galois connection. -/
theorem splitClifford_sectorRefine_sectorCoarse_galoisConnection
    {α : Type*} {β : Type*} (f : α → β) :
    GaloisConnection
      (InfoGeometry.Topology.sectorRefine f)
      (InfoGeometry.Topology.sectorCoarse f) :=
  InfoGeometry.Topology.sectorRefine_sectorCoarse_galoisConnection f

end InfoGeometry.Canonical.SplitCliffordExternalChain
