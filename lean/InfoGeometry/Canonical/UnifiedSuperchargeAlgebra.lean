import InfoGeometry.Quantum.SuperchargeMultiplet
import InfoGeometry.Canonical.SuperchargeTransportBridge
import InfoGeometry.Canonical.DrazinSupercharge
import InfoGeometry.Canonical.DrazinCentralChargeBridge
import InfoGeometry.Canonical.OperatorialCentralCharge
import InfoGeometry.Canonical.KKTClosureSymmetry
import InfoGeometry.Canonical.KramersSuperchargeBridge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

namespace InfoGeometry.Canonical.UnifiedSuperchargeAlgebra

open InfoGeometry.Krein
open InfoGeometry.Quantum
open InfoGeometry.Canonical
open InfoGeometry.Canonical.SuperchargeTransportBridge
open InfoGeometry.Canonical.OperatorialCentralCharge

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "Xc" => InfoGeometry.Quantum.RealMajoranaCategory.cl11DoubledCore E
local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
noncomputable local instance : NormedAlgebra ℚ EndH :=
  NormedAlgebra.restrictScalars ℚ ℝ EndH
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance
local instance : SMulCommClass ℝ EndH EndH := inferInstance
local instance : IsScalarTower ℝ EndH EndH := inferInstance

/--
Repo-specific unified supercharge package.

This fuses:
1. primitive doubled-carrier supercharges `(QΠ, QJ)`,
2. transported supercharges on the quasilattice lane,
3. projected Drazin/Penrose odd supercharge `QD`,
4. and the external topological central charge lane.
-/
@[rep_depth transport]
structure UnifiedSuperchargePackage where
  primitive : InfoGeometry.Quantum.SuperchargeMultiplet (E := E)
  kernel : CertifiedInverseKernel H₂

namespace UnifiedSuperchargePackage

variable (U : UnifiedSuperchargePackage (E := E))

/-- Primitive parity/triality supercharge `QΠ`. -/
abbrev QPi : Xc →ₗ[ℝ] Xc := U.primitive.parity.Q

/-- Primitive modular supercharge `QJ`. -/
abbrev QJ : H₂ →L[ℝ] H₂ := U.primitive.modular.Q

/-- Primitive phase channel `K = QΠ QJ = J ε`. -/
noncomputable abbrev phaseChannel : Xc →ₗ[ℝ] Xc := U.primitive.phaseChannel

/-- Projected Drazin odd supercharge `QD = χ_R - χ_L`. -/
noncomputable abbrev QD : EndH :=
  InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.supercharge U.kernel

/-- Projected left chiral supercharge `Q_L = χ_L = [P_D, P_L]`. -/
noncomputable abbrev QL : EndH := U.kernel.chiralAnomaly

/-- Projected right chiral supercharge `Q_R = χ_R = [P_D, P_R]`. -/
noncomputable abbrev QR : EndH := U.kernel.rightChiralAnomaly

/-- Projected Drazin spectral projector `P_D`. -/
noncomputable abbrev PD : EndH := U.kernel.spectralProjector

/-- Projected Moore–Penrose left projector `P_L`. -/
noncomputable abbrev PL : EndH := U.kernel.metricProjector

/-- Projected Moore–Penrose right projector `P_R`. -/
noncomputable abbrev PR : EndH := U.kernel.mpRangeProjector

/-- Projected Drazin even Hamiltonian candidate `HD = QD²`. -/
noncomputable abbrev HD : EndH :=
  InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK U.kernel

/-- Spectral grading of the projected lane. -/
noncomputable abbrev GammaS : EndH := U.kernel.toInformationCartanTriple.GammaS

/-- Primitive parity/modular anticommutator vanishes. -/
theorem primitive_anticommutator_eq_zero :
    InfoGeometry.Quantum.RealMajoranaCategory.anticommutator
      (QPi U) ((QJ U).toLinearMap) = 0 := by
  exact InfoGeometry.Quantum.SuperchargeMultiplet.parity_modular_anticommutator_eq_zero
    (E := E) U.primitive

/-- Primitive phase channel as the internal doubled real phase axis `K = J ∘ ε`. -/
theorem primitive_phaseChannel_eq_phaseAxis :
    phaseChannel U =
      ((modular_j (E := E)).toLinearMap).comp ((spectral_epsilon (E := E)).toLinearMap) := by
  have hComplex :
      phaseChannel U = (complex_i (E := E)).toLinearMap := by
    exact InfoGeometry.Quantum.SuperchargeMultiplet.phaseChannel_eq_complexI
      (E := E) U.primitive
  calc
    phaseChannel U = (complex_i (E := E)).toLinearMap := hComplex
    _ =
      ((modular_j (E := E)).toLinearMap).comp ((spectral_epsilon (E := E)).toLinearMap) := by
        rfl

/--
Legacy compatibility alias:
the internal phase axis `K = J ∘ ε` coincides with the historical `complex_i`
surface.
-/
theorem primitive_phaseChannel_eq_complexI :
    phaseChannel U = (complex_i (E := E)).toLinearMap := by
  exact InfoGeometry.Quantum.SuperchargeMultiplet.phaseChannel_eq_complexI
    (E := E) U.primitive

/-- Primitive phase channel squares to `-Id`. -/
theorem primitive_phaseChannel_sq_eq_neg_id :
    (phaseChannel U).comp (phaseChannel U) = -((LinearMap.id : Xc →ₗ[ℝ] Xc)) := by
  exact InfoGeometry.Quantum.SuperchargeMultiplet.phaseChannel_sq_eq_neg_id
    (E := E) U.primitive

/-- The projected supercharge is odd in the Drazin spectral grading. -/
theorem projected_supercharge_is_odd :
    InfoGeometry.Canonical.DrazinSupercharge.anticommutatorK (GammaS U) (QD U) = 0 := by
  simpa [QD, GammaS] using
    (InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.supercharge_is_oddK
      (CIK := U.kernel))

/-- The projected kinetic operator is even/compact in the Drazin grading. -/
theorem projected_hamiltonian_is_even :
    let T := U.kernel.toInformationCartanTriple
    T.IsSpectralCompact (HD U) := by
  simpa [HD] using
    (InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK_isSpectralCompact
      (CIK := U.kernel))

/-- The projected supercharge admits the exact dilation-gap commutator presentation. -/
theorem projected_supercharge_eq_two_commutator :
    QD U = (2 : ℝ) •
      InfoGeometry.Canonical.DrazinSupercharge.commutatorK U.kernel.spectralProjector U.kernel.dilationGap := by
  simpa [QD] using
    (InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.supercharge_eq_two_smul_commutatorK_spectralProjector_dilationGap
      (CIK := U.kernel))

/-- Projected right/left decomposition `Q_D = Q_R - Q_L`. -/
theorem projected_supercharge_eq_sub_chiral :
    QD U = QR U - QL U := by
  rfl

/-- Left projected supercharge as commutator `[P_D, P_L]`. -/
theorem projected_left_eq_commutator_PD_PL :
    QL U =
      InfoGeometry.Canonical.DrazinSupercharge.commutator (PD U) (PL U) := by
  rfl

/-- Right projected supercharge as commutator `[P_D, P_R]`. -/
theorem projected_right_eq_commutator_PD_PR :
    QR U =
      InfoGeometry.Canonical.DrazinSupercharge.commutator (PD U) (PR U) := by
  rfl

/-- Projected even Hamiltonian as a square `H_D = Q_D²`. -/
theorem projected_hamiltonian_eq_square :
    HD U = (QD U) * (QD U) := by
  rfl

/--
Scaled kinetic lane extracted from the projected odd-odd Drazin bracket.

This is the repo-native translation candidate on the chiral-charge / Drazin lane:
the canonical kinetic remainder in the internal split of `Q_D²`.
-/
@[rep_depth transport]
noncomputable def drazinTranslationCandidate : EndH :=
  InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.canonicalKineticPartK U.kernel

/--
Scaled central lane carried by the KKT packet notation `Z_D`.

We package the odd-odd bracket in the direct form
`{Q_D, Q_D} = 2 • translationCandidate + centralCandidate`,
so the central candidate is stored with the factor of `2` absorbed.
-/
@[rep_depth transport]
noncomputable def drazinCentralCandidate : EndH :=
  (2 : ℝ) • InfoGeometry.Canonical.KKTClosure.ZD U.kernel

/--
Scaled defect-supported channel on the direct Drazin owner lane.

This is definitionally the same channel as the KKT-side central candidate,
written in the underlying Drazin owner vocabulary.
-/
@[rep_depth transport]
noncomputable def drazinDefectCandidate : EndH :=
  (2 : ℝ) •
    InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.canonicalDefectCentralK U.kernel

/--
Minimal pair readout of the new Drazin-lane packet: translation and central
channels.  The defect witness is carried separately and proved equal to the
central readout below.
-/
@[rep_depth transport]
noncomputable def drazinTranslationCentralDefectPacket : EndH × EndH :=
  (drazinTranslationCandidate U, drazinCentralCandidate U)

@[rep_depth transport]
theorem drazinTranslationCentralDefectPacket_fst :
    (drazinTranslationCentralDefectPacket U).1 = drazinTranslationCandidate U := by
  rfl

@[rep_depth transport]
theorem drazinTranslationCentralDefectPacket_snd :
    (drazinTranslationCentralDefectPacket U).2 = drazinCentralCandidate U := by
  rfl

/--
Repo-native supergraded packet on the projected Drazin lane.

This does not yet formalize a distinct conjugate odd generator `Q̄_D`; instead it
records the owner decomposition of the realized odd-odd Drazin bracket
`{Q_D, Q_D}` into translation, central, and defect readouts.
-/
@[rep_depth transport]
structure DrazinSupergradedTranslationPacket where
  oddOddBracket : EndH
  translationCandidate : EndH
  centralCandidate : EndH
  defectCandidate : EndH
  oddOdd_bracket_eq_two_smul_translation_plus_central :
    oddOddBracket = (2 : ℝ) • translationCandidate + centralCandidate
  central_eq_defect : centralCandidate = defectCandidate

/-- KKT-central and direct Drazin-defect channels coincide definitionally. -/
@[rep_depth transport]
theorem drazinCentralCandidate_eq_defectCandidate :
    drazinCentralCandidate U = drazinDefectCandidate U := by
  rfl

/--
Projected odd-odd Drazin bracket in repo-native split form:
`{Q_D, Q_D} = 2 • translationCandidate + centralCandidate`.
-/
@[rep_depth transport]
theorem projected_oddOdd_bracket_eq_two_smul_translation_plus_central :
    InfoGeometry.Canonical.DrazinSupercharge.anticommutatorK (QD U) (QD U)
      = (2 : ℝ) • drazinTranslationCandidate U + drazinCentralCandidate U := by
  calc
    InfoGeometry.Canonical.DrazinSupercharge.anticommutatorK (QD U) (QD U)
        = (2 : ℝ) • (HD U) := by
            simp [InfoGeometry.Canonical.DrazinSupercharge.anticommutatorK,
              InfoGeometry.Canonical.DrazinSupercharge.anticommutator,
              QD, HD, two_smul,
              InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK,
              InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.superHamiltonian]
    _ = (2 : ℝ) •
          (drazinTranslationCandidate U
            + InfoGeometry.Canonical.KKTClosure.ZD U.kernel) := by
          have hSplit :=
            InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK_eq_canonicalKineticPartK_plus_canonicalDefectCentralK
              (CIK := U.kernel)
          exact congrArg (fun X => (2 : ℝ) • X) (by simpa [HD, drazinTranslationCandidate, InfoGeometry.Canonical.KKTClosure.ZD] using hSplit)
    _ = (2 : ℝ) • drazinTranslationCandidate U + drazinCentralCandidate U := by
          simp [drazinCentralCandidate, smul_add]

/--
Equivalent defect-language readout of the same odd-odd Drazin bracket.
-/
@[rep_depth transport]
theorem projected_oddOdd_bracket_eq_two_smul_translation_plus_defect :
    InfoGeometry.Canonical.DrazinSupercharge.anticommutatorK (QD U) (QD U)
      = (2 : ℝ) • drazinTranslationCandidate U + drazinDefectCandidate U := by
  rw [projected_oddOdd_bracket_eq_two_smul_translation_plus_central]
  rw [drazinCentralCandidate_eq_defectCandidate]

/--
Canonical owner packet witnessing the lift from the primitive transported
translation seed into the projected chiral-charge / Drazin lane.
-/
@[rep_depth transport]
theorem drazinSupergradedTranslationPacket_ofOwners :
    ∃ P : DrazinSupergradedTranslationPacket,
      P.oddOddBracket = InfoGeometry.Canonical.DrazinSupercharge.anticommutatorK (QD U) (QD U)
        ∧ P.translationCandidate = drazinTranslationCandidate U
        ∧ P.centralCandidate = drazinCentralCandidate U
        ∧ P.defectCandidate = drazinDefectCandidate U := by
  refine ⟨{
    oddOddBracket := InfoGeometry.Canonical.DrazinSupercharge.anticommutatorK (QD U) (QD U)
    translationCandidate := drazinTranslationCandidate U
    centralCandidate := drazinCentralCandidate U
    defectCandidate := drazinDefectCandidate U
    oddOdd_bracket_eq_two_smul_translation_plus_central :=
      projected_oddOdd_bracket_eq_two_smul_translation_plus_central (U := U)
    central_eq_defect := drazinCentralCandidate_eq_defectCandidate (U := U)
  }, rfl, rfl, rfl, rfl⟩

/--
Best available repo-native paired odd candidate on the Drazin lane.

At present this is a Majorana-conjugate witness rather than a fully independent
owner-defined `Q̄_D`: it is `Q_D` viewed through the Majorana fixed-sector bridge.
-/
@[rep_depth transport]
noncomputable def drazinMajoranaConjugateCandidate : EndH :=
  QD U

/--
Under Majorana compatibility with both anomaly channels, the current paired odd
candidate collapses to the owned Drazin supercharge itself.
-/
@[rep_depth transport]
theorem drazinMajoranaConjugateCandidate_eq_QD_of_commute_chi
    (M : InfoGeometry.Canonical.HestenesRealStructures.MajoranaRealStructure (E := E))
    (_hCL : Commute M.C (U.kernel.chiralAnomaly))
    (_hCR : Commute M.C (U.kernel.rightChiralAnomaly)) :
    drazinMajoranaConjugateCandidate U = QD U := by
  rfl

/--
For the current Majorana-paired candidate, the paired odd-odd bracket reduces to
the already owned self-bracket of `Q_D`.
-/
@[rep_depth transport]
theorem paired_oddOdd_majoranaBracket_eq_selfBracket_of_commute_chi
    (M : InfoGeometry.Canonical.HestenesRealStructures.MajoranaRealStructure (E := E))
    (hCL : Commute M.C (U.kernel.chiralAnomaly))
    (hCR : Commute M.C (U.kernel.rightChiralAnomaly)) :
    InfoGeometry.Canonical.DrazinSupercharge.anticommutatorK
        (QD U) (drazinMajoranaConjugateCandidate U)
      =
    InfoGeometry.Canonical.DrazinSupercharge.anticommutatorK (QD U) (QD U) := by
  rw [drazinMajoranaConjugateCandidate_eq_QD_of_commute_chi (U := U) (M := M) hCL hCR]

/--
Conditional paired-bracket translation/central readout.

This is the strongest current owner-safe statement: once the paired odd candidate
is identified with `Q_D` through the Majorana-compatible anomaly corridor, the
paired bracket inherits the already proved Drazin split.
-/
@[rep_depth transport]
theorem paired_oddOdd_majoranaBracket_eq_two_smul_translation_plus_central_of_commute_chi
    (M : InfoGeometry.Canonical.HestenesRealStructures.MajoranaRealStructure (E := E))
    (hCL : Commute M.C (U.kernel.chiralAnomaly))
    (hCR : Commute M.C (U.kernel.rightChiralAnomaly)) :
    InfoGeometry.Canonical.DrazinSupercharge.anticommutatorK
        (QD U) (drazinMajoranaConjugateCandidate U)
      =
    (2 : ℝ) • drazinTranslationCandidate U + drazinCentralCandidate U := by
  rw [paired_oddOdd_majoranaBracket_eq_selfBracket_of_commute_chi (U := U) (M := M) hCL hCR]
  exact projected_oddOdd_bracket_eq_two_smul_translation_plus_central (U := U)

/--
Equivalent defect-language version of the conditional paired-bracket readout.
-/
@[rep_depth transport]
theorem paired_oddOdd_majoranaBracket_eq_two_smul_translation_plus_defect_of_commute_chi
    (M : InfoGeometry.Canonical.HestenesRealStructures.MajoranaRealStructure (E := E))
    (hCL : Commute M.C (U.kernel.chiralAnomaly))
    (hCR : Commute M.C (U.kernel.rightChiralAnomaly)) :
    InfoGeometry.Canonical.DrazinSupercharge.anticommutatorK
        (QD U) (drazinMajoranaConjugateCandidate U)
      =
    (2 : ℝ) • drazinTranslationCandidate U + drazinDefectCandidate U := by
  rw [paired_oddOdd_majoranaBracket_eq_selfBracket_of_commute_chi (U := U) (M := M) hCL hCR]
  exact projected_oddOdd_bracket_eq_two_smul_translation_plus_defect (U := U)

/--
Nontrivial Kramers-conjugated odd candidate on the Drazin lane.

Unlike the Majorana witness above, this really uses an external symmetry action:
`Θ * Q_D * Θ`.
-/
@[rep_depth transport]
noncomputable def drazinKramersConjugateCandidate
    (S : InfoGeometry.Canonical.HestenesRealStructures.KramersSymmetry (E := E)) : EndH :=
  S.Θ * QD U * S.Θ

/-- Paired odd-odd bracket using the Kramers-conjugated Drazin candidate. -/
@[rep_depth transport]
noncomputable def pairedOddOddKramersBracket
    (S : InfoGeometry.Canonical.HestenesRealStructures.KramersSymmetry (E := E)) : EndH :=
  InfoGeometry.Canonical.DrazinSupercharge.anticommutatorK
    (QD U) (drazinKramersConjugateCandidate U S)

/--
If the Kramers symmetry commutes with `Γ_S`, the Kramers-conjugated Drazin odd
candidate remains odd.
-/
@[rep_depth transport]
theorem drazinKramersConjugateCandidate_is_odd_of_commute_GammaS
    (S : InfoGeometry.Canonical.HestenesRealStructures.KramersSymmetry (E := E))
    (hThetaGamma : Commute S.Θ (GammaS U)) :
    InfoGeometry.Canonical.DrazinSupercharge.anticommutator
      (GammaS U) (drazinKramersConjugateCandidate U S) = 0 := by
  simpa [drazinKramersConjugateCandidate, GammaS, QD] using
    (InfoGeometry.Canonical.KramersSuperchargeBridge.kramers_conjugated_qD_is_odd_of_commute_GammaS
      (E := E) (CIK := U.kernel) (S := S) hThetaGamma)

/--
Owner-readout transfer for the Kramers-paired bracket.

This is the strongest current owner-safe theorem: if a concrete Kramers symmetry
is additionally shown to identify its conjugated odd lane with the owner `Q_D`,
then the bracket inherits the already formalized Drazin translation/central split.
-/
@[rep_depth transport]
theorem pairedOddOddKramersBracket_eq_ownerReadout
    (S : InfoGeometry.Canonical.HestenesRealStructures.KramersSymmetry (E := E))
    (hPair : drazinKramersConjugateCandidate U S = QD U) :
    pairedOddOddKramersBracket U S
      = (2 : ℝ) • drazinTranslationCandidate U + drazinCentralCandidate U := by
  unfold pairedOddOddKramersBracket
  rw [hPair]
  exact projected_oddOdd_bracket_eq_two_smul_translation_plus_central (U := U)

/-- Projected odd/even closure package under the spectral grading `Γ_S`. -/
theorem projected_odd_even_closure :
    InfoGeometry.Canonical.DrazinSupercharge.anticommutator (GammaS U) (QD U) = 0
      ∧
    (let T := U.kernel.toInformationCartanTriple;
      T.IsSpectralCompact (HD U))
      ∧
    (let T := U.kernel.toInformationCartanTriple;
      T.spectralAdjointFlow T.GammaS 0 (HD U) = HD U) := by
  refine ⟨projected_supercharge_is_odd U, ?_, ?_⟩
  · exact projected_hamiltonian_is_even U
  ·
    have hFix :=
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.superHamiltonian_fixed_under_spectralGradingFlow
        (CIK := U.kernel) 0
    simpa [HD] using hFix

end UnifiedSuperchargePackage

end Core

section Transported

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/--
Transport package for the primitive supercharges on the quasilattice lane.
-/
@[rep_depth transport]
structure TransportedSuperchargePackage where
  V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)

namespace TransportedSuperchargePackage

variable (T : TransportedSuperchargePackage (E := E))

/-- Transported parity supercharge `QΠ(t)`. -/
noncomputable abbrev QPi_t (t : ℝ) : EndH :=
  transportedParitySupercharge (E := E) T.V t

/-- Transported modular supercharge `QJ(t)`. -/
noncomputable abbrev QJ_t (t : ℝ) : EndH :=
  transportedModularSupercharge (E := E) T.V t

/-- Primitive transported anticommutator vanishes at time zero. -/
theorem transported_primitive_anticommutator_zero :
    InfoGeometry.Canonical.BogoliubovFockSuper.fockAnticommutator
      (E := E) (modular_j (E := E)) (spectral_epsilon (E := E)) = 0 := by
  exact parity_modular_anticommutator_eq_zero (E := E)

/-- The transported parity supercharge satisfies the quasilattice commutator law. -/
theorem deriv_QPi_t (t : ℝ) :
    deriv (fun s => QPi_t T s) t
      =
    InfoGeometry.Canonical.BogoliubovTransport.transportCommutator
      (E := E) T.V.connectionGenerator (QPi_t T t) := by
  simpa [QPi_t] using deriv_transportedParitySupercharge (E := E) T.V t

/-- The transported modular supercharge satisfies the quasilattice commutator law. -/
theorem deriv_QJ_t (t : ℝ) :
    deriv (fun s => QJ_t T s) t
      =
    InfoGeometry.Canonical.BogoliubovTransport.transportCommutator
      (E := E) T.V.connectionGenerator (QJ_t T t) := by
  simpa [QJ_t] using deriv_transportedModularSupercharge (E := E) T.V t

/-- Second derivative of the transported parity supercharge lands in the weak-owner Lichnerowicz Hessian. -/
theorem deriv2_QPi_t_eq_operatorInformationHessian :
    let X := T.V.connectionGenerator
    deriv (fun t => deriv (fun s => QPi_t T s) t) 0
      =
    InfoGeometry.Canonical.RelationalInformationDynamics.operatorInformationHessian
      (E := E) X (modular_j (E := E)) := by
  simpa [QPi_t] using
    deriv2_transportedParitySupercharge_at_zero_eq_operatorInformationHessian (E := E) T.V

/-- Second derivative of the transported parity supercharge splits into metric and curvature parts. -/
theorem deriv2_QPi_t_eq_metricPart_add_half_curvaturePart :
    let X := T.V.connectionGenerator
    deriv (fun t => deriv (fun s => QPi_t T s) t) 0
      =
    InfoGeometry.Canonical.RelationalInformationDynamics.operatorInformationMetricPart
      (E := E) X X (modular_j (E := E))
      + ((2 : ℝ)⁻¹) •
        InfoGeometry.Canonical.RelationalInformationDynamics.operatorInformationCurvaturePart
          (E := E) X X (modular_j (E := E)) := by
  simpa [QPi_t] using
    deriv2_transportedParitySupercharge_at_zero_eq_metricPart_add_half_curvaturePart
      (E := E) T.V

end TransportedSuperchargePackage

end Transported

section TopologicalCentralCharge

open InfoGeometry.KK
open InfoGeometry.KK.RealSplitKreinKasparovCycle
open InfoGeometry.Krein
open InfoGeometry.Canonical.OperatorialCentralCharge

variable {A B E : Type}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [KreinSpace (DoubledSpace E)] [KreinGradedModule (DoubledSpace E)]

local notation "H₂" => DoubledSpace E

/--
Topological central charge package:
the external central supercharge is the analytical index already owned by the repo.
-/
@[rep_depth transport]
structure TopologicalCentralChargePackage where
  X : RealSplitKreinDiracFredholmModule A B H₂
  hX : ChiralFredholmSurface X
  Zop : ℤ
  hZop :
    Zop = operatorialCentralCharge (A := A) (B := B) (E := E) X hX

namespace TopologicalCentralChargePackage

variable (Z : TopologicalCentralChargePackage (A := A) (B := B) (E := E))

/-- The external central supercharge is exactly the repo-owned analytical index. -/
theorem Zop_eq_analyticIndex :
    Z.Zop = operatorialCentralCharge (A := A) (B := B) (E := E) Z.X Z.hX :=
  Z.hZop

/-- The external central supercharge is transport invariant. -/
theorem Zop_transport_invariant
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (s t : ℝ) :
    quasilatticeAnalyticalIndex V Z.X s
        (quasilatticeChiralFredholmSurfaceOf (E := E) V Z.X Z.hX hEven s)
      =
    quasilatticeAnalyticalIndex V Z.X t
        (quasilatticeChiralFredholmSurfaceOf (E := E) V Z.X Z.hX hEven t) := by
  simpa using
    operatorialCentralCharge_transport_invariant
      (A := A) (B := B) (E := E) V Z.X Z.hX hEven s t

end TopologicalCentralChargePackage

end TopologicalCentralCharge

section Fusion

open InfoGeometry.Canonical.SuperchargeCentralChargeClosure
open InfoGeometry.KK
open InfoGeometry.KK.RealSplitKreinKasparovCycle
open InfoGeometry.Krein

variable {A B F : Type}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable [KreinSpace (DoubledSpace F)] [KreinGradedModule (DoubledSpace F)]

local notation "H₂" => DoubledSpace F

/--
Unified central supercharge theorem:
combines projected Drazin evenness/flow invariance with the root transported
supercharge Lichnerowicz/central-charge closure package.
-/
@[rep_depth transport]
theorem unified_central_supercharge_theorem
    (U : UnifiedSuperchargePackage (E := F))
    (Tpkg : TransportedSuperchargePackage (E := F))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) Tpkg.V.connectionGenerator)
    (τ t : ℝ) :
    (let T := U.kernel.toInformationCartanTriple;
      T.IsSpectralCompact
          (InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK U.kernel)
        ∧
      T.spectralAdjointFlow T.GammaS τ
          (InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK U.kernel)
        =
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK U.kernel)
      ∧
    rootGapHessianClosure (E := F) Tpkg.V
      ∧
    (quasilatticeAnalyticalIndex Tpkg.V X t
        (quasilatticeChiralFredholmSurfaceOf (E := F) Tpkg.V X hX hEven t)
      =
    operatorialCentralCharge (A := A) (B := B) (E := F) X hX)
      ∧
    (operatorialCentralCharge (A := A) (B := B) (E := F) X hX ≠ 0 →
      quasilatticeAnalyticalIndex Tpkg.V X t
          (quasilatticeChiralFredholmSurfaceOf (E := F) Tpkg.V X hX hEven t)
        ≠ 0) := by
  exact InfoGeometry.Canonical.DrazinSupercharge.central_supercharge_theorem_with_drazin_evenness
    (A := A) (B := B) (F := F) U.kernel Tpkg.V X hX hEven τ t

/--
Cross-family compatibility packet:
projected odd/even closure, transported second-order Lichnerowicz landing, and
topological central-charge closure on the same transport slice.
-/
@[rep_depth transport]
theorem unified_cross_family_compatibility
    (U : UnifiedSuperchargePackage (E := F))
    (Tpkg : TransportedSuperchargePackage (E := F))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) Tpkg.V.connectionGenerator)
    (τ t : ℝ) :
    (InfoGeometry.Canonical.DrazinSupercharge.anticommutatorK
        (UnifiedSuperchargePackage.GammaS U)
        (UnifiedSuperchargePackage.QD U)
      = 0)
      ∧
    (let X := Tpkg.V.connectionGenerator;
      deriv (fun t => deriv (fun s => TransportedSuperchargePackage.QPi_t Tpkg s) t) 0
        =
      InfoGeometry.Canonical.RelationalInformationDynamics.operatorInformationMetricPart
        (E := F) X X (modular_j (E := F))
        + ((2 : ℝ)⁻¹) •
          InfoGeometry.Canonical.RelationalInformationDynamics.operatorInformationCurvaturePart
            (E := F) X X (modular_j (E := F)))
      ∧
    rootGapHessianClosure (E := F) Tpkg.V
      ∧
    (quasilatticeAnalyticalIndex Tpkg.V X t
        (quasilatticeChiralFredholmSurfaceOf (E := F) Tpkg.V X hX hEven t)
      =
    operatorialCentralCharge (A := A) (B := B) (E := F) X hX)
      ∧
    (operatorialCentralCharge (A := A) (B := B) (E := F) X hX ≠ 0 →
      quasilatticeAnalyticalIndex Tpkg.V X t
          (quasilatticeChiralFredholmSurfaceOf (E := F) Tpkg.V X hX hEven t)
        ≠ 0) := by
  refine ⟨UnifiedSuperchargePackage.projected_supercharge_is_odd U, ?_, ?_, ?_, ?_⟩
  · exact TransportedSuperchargePackage.deriv2_QPi_t_eq_metricPart_add_half_curvaturePart Tpkg
  · exact (unified_central_supercharge_theorem
      (A := A) (B := B) (F := F) U Tpkg X hX hEven τ t).2.1
  · exact (unified_central_supercharge_theorem
      (A := A) (B := B) (F := F) U Tpkg X hX hEven τ t).2.2.1
  · exact (unified_central_supercharge_theorem
      (A := A) (B := B) (F := F) U Tpkg X hX hEven τ t).2.2.2

omit [KreinSpace H₂] [KreinGradedModule H₂] in
/--
Sources/sinks + Onsager packet on the unified lane:

1. internal Drazin canonical split `Q_D² = H + Z` with `Z` spectrally central
   and defect-supported,
2. projected left/right anomaly channels and net divergence channel
   `Q_D = Q_R - Q_L`,
3. divergence identity `[P_D, G] = (1/2)•Q_D`,
4. first-order Lie-derivation transport laws for `Q_Π(t), Q_J(t)`,
5. second-order transported metric/curvature (Lichnerowicz/Onsager) split.
-/
@[rep_depth transport]
theorem unified_sources_sinks_onsager_with_internal_central_split
    (U : UnifiedSuperchargePackage (E := F))
    (Tpkg : TransportedSuperchargePackage (E := F))
    (t : ℝ) :
    (∃ H Z : H₂ →L[ℝ] H₂,
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.IsDrazinLaneCentralK
        U.kernel Z
        ∧
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.IsDefectSupportedK U.kernel Z
        ∧
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.HasVanishingDefectBlockK
        U.kernel H
        ∧
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK U.kernel
        = H + Z)
      ∧
    (UnifiedSuperchargePackage.QD U
      =
      UnifiedSuperchargePackage.QR U - UnifiedSuperchargePackage.QL U)
      ∧
    (InfoGeometry.Canonical.DrazinSupercharge.commutatorK
        U.kernel.spectralProjector U.kernel.dilationGap
      =
      ((2 : ℝ)⁻¹) • UnifiedSuperchargePackage.QD U)
      ∧
    (deriv (fun s => TransportedSuperchargePackage.QPi_t Tpkg s) t
      =
      InfoGeometry.Canonical.BogoliubovTransport.transportCommutator
        (E := F) Tpkg.V.connectionGenerator (TransportedSuperchargePackage.QPi_t Tpkg t))
      ∧
    (deriv (fun s => TransportedSuperchargePackage.QJ_t Tpkg s) t
      =
      InfoGeometry.Canonical.BogoliubovTransport.transportCommutator
        (E := F) Tpkg.V.connectionGenerator (TransportedSuperchargePackage.QJ_t Tpkg t))
      ∧
    (let X0 := Tpkg.V.connectionGenerator;
      deriv (fun τ => deriv (fun s => TransportedSuperchargePackage.QPi_t Tpkg s) τ) 0
        =
      InfoGeometry.Canonical.RelationalInformationDynamics.operatorInformationMetricPart
        (E := F) X0 X0 (modular_j (E := F))
        + ((2 : ℝ)⁻¹) •
          InfoGeometry.Canonical.RelationalInformationDynamics.operatorInformationCurvaturePart
            (E := F) X0 X0 (modular_j (E := F))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.exists_superHamiltonian_canonical_split_with_drazin_lane_centralityK
        (CIK := U.kernel)
  · exact UnifiedSuperchargePackage.projected_supercharge_eq_sub_chiral U
  · have hQ := UnifiedSuperchargePackage.projected_supercharge_eq_two_commutator (U := U)
    have hHalf :
        ((2 : ℝ)⁻¹) • UnifiedSuperchargePackage.QD U
          =
        InfoGeometry.Canonical.DrazinSupercharge.commutatorK
          U.kernel.spectralProjector U.kernel.dilationGap := by
      calc
        ((2 : ℝ)⁻¹) • UnifiedSuperchargePackage.QD U
            = ((2 : ℝ)⁻¹) •
              ((2 : ℝ) •
                InfoGeometry.Canonical.DrazinSupercharge.commutatorK
                  U.kernel.spectralProjector U.kernel.dilationGap) := by
                  rw [hQ]
        _ =
            InfoGeometry.Canonical.DrazinSupercharge.commutatorK
              U.kernel.spectralProjector U.kernel.dilationGap := by
                simp [smul_smul]
    exact hHalf.symm
  · exact TransportedSuperchargePackage.deriv_QPi_t Tpkg t
  · exact TransportedSuperchargePackage.deriv_QJ_t Tpkg t
  · exact TransportedSuperchargePackage.deriv2_QPi_t_eq_metricPart_add_half_curvaturePart Tpkg

/--
Integrated internal split + transported operatorial-shadow theorem.

This strengthens the unified lane with the bridge that packages:
1. internal Drazin split `Q_D² = H + Z`,
2. Drazin-lane centrality of the transported operatorial central-charge scalar shadow,
3. transported analytical-index equality on the same slice.
-/
@[rep_depth transport]
theorem unified_internal_split_with_operatorial_shadow
    (U : UnifiedSuperchargePackage (E := F))
    (Tpkg : TransportedSuperchargePackage (E := F))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) Tpkg.V.connectionGenerator)
    (t : ℝ) :
    ∃ H Z : H₂ →L[ℝ] H₂,
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.IsDrazinLaneCentralK
          U.kernel Z
        ∧
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.IsDefectSupportedK
          U.kernel Z
        ∧
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.HasVanishingDefectBlockK
          U.kernel H
        ∧
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK
          U.kernel
        = H + Z
        ∧
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.IsDrazinLaneCentralK
          U.kernel
          (InfoGeometry.Canonical.DrazinCentralChargeBridge.DrazinLane.operatorialCentralScalar
            (A := A) (B := B) X hX)
        ∧
      quasilatticeAnalyticalIndex Tpkg.V X t
          (quasilatticeChiralFredholmSurfaceOf (E := F) Tpkg.V X hX hEven t)
        =
      operatorialCentralCharge (A := A) (B := B) (E := F) X hX := by
  simpa using
    InfoGeometry.Canonical.DrazinCentralChargeBridge.DrazinLane.exists_internal_split_with_operatorial_shadow
      (A := A) (B := B) (F := F) (CIK := U.kernel) (V := Tpkg.V) X hX hEven t

end Fusion

end InfoGeometry.Canonical.UnifiedSuperchargeAlgebra
