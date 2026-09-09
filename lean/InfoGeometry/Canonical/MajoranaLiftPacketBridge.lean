import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Core.MajoranaLiftPacket
import InfoGeometry.Canonical.RealBdGDIIIAtom
import InfoGeometry.Canonical.UnifiedSuperchargeAlgebra
import InfoGeometry.Canonical.OnsagerCasimirJ
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.MajoranaLiftPacketBridge

Owner-respecting bridge:

- identifies the canonical DIII proxy with the doubled-core Majorana operators,
- exposes projected fermionic odd/even closure from the unified supercharge lane,
- and exports the operatorial Onsager phase sign-flip law.

This file is a translator surface over existing owners; it does not introduce a
second ontology.
-/

namespace InfoGeometry.Canonical.MajoranaLiftPacketBridge

open InfoGeometry.Krein
open InfoGeometry.Core
open InfoGeometry.Canonical.RealBdGDIIIAtom
open InfoGeometry.Canonical.UnifiedSuperchargeAlgebra
open InfoGeometry.Canonical.OnsagerCasimirJ

section Core

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

@[rep_depth transport]
theorem canonicalDIIIProxy_majorana_root_laws :
    (canonicalDIIIProxy (E := E)).C = modular_j (E := E)
      ∧ -((canonicalDIIIProxy (E := E)).S) = spectral_epsilon (E := E)
      ∧ (canonicalDIIIProxy (E := E)).T = complex_i (E := E)
      ∧ (canonicalDIIIProxy (E := E)).T.comp
          (canonicalDIIIProxy (E := E)).T =
            -(ContinuousLinearMap.id ℝ H₂) := by
  refine ⟨by simp, by simp, canonicalDIIIProxy_T_eq_complex_i (E := E), ?_⟩
  rw [canonicalDIIIProxy_T_eq_complex_i]
  exact complex_i_sq (E := E)

/-- The DIII translator preserves the concrete doubled-core CAR realization. -/
@[rep_depth transport]
theorem packetOfCanonicalDIIIProxy_concreteCAR :
    InfoGeometry.Canonical.BogoliubovFockSuper.IsCARPair
      (InfoGeometry.Canonical.SuperchargeCARCCRBridge.concreteCARAnnihilation (E := E))
      (InfoGeometry.Canonical.SuperchargeCARCCRBridge.concreteCARCreation (E := E)) := by
  exact canonicalDIIIProxy_concreteCARPair (E := E)

/--
Projected fermionic closure from the unified package:
odd projected supercharge plus even projected Hamiltonian.
-/
@[rep_depth transport]
theorem unifiedPackage_projected_fermionic_closure
    (U : UnifiedSuperchargePackage (E := E)) :
    InfoGeometry.Canonical.DrazinSupercharge.anticommutatorK
        (UnifiedSuperchargePackage.GammaS U)
        (UnifiedSuperchargePackage.QD U) = 0
      ∧
    (let T := U.kernel.toInformationCartanTriple;
      T.IsSpectralCompact (UnifiedSuperchargePackage.HD U)) := by
  refine ⟨?_, ?_⟩
  · exact UnifiedSuperchargePackage.projected_supercharge_is_odd (U := U)
  · exact UnifiedSuperchargePackage.projected_hamiltonian_is_even (U := U)

/--
Onsager/Casimir phase law:
`J`-conjugation flips the sign of the `K`-twisted response channel.
-/
@[rep_depth transport]
theorem onsager_phaseChannel_signFlip
    (X : InfoGeometry.Canonical.RelationalInformationCore.PerturbationChannel E) :
    JConjugate (InfoGeometry.Canonical.RelationalInformationCore.channelPhaseAxis X)
      =
    -(InfoGeometry.Canonical.RelationalInformationCore.channelPhaseAxis (JConjugate X)) := by
  exact JConjugate_channelPhaseAxis_eq_neg_channelPhaseAxis_JConjugate (E := E) X

/-- Compatibility name for the canonical DIII proxy Majorana root laws. -/
@[rep_depth transport]
theorem packetOfCanonicalDIIIProxy_root_laws :
    (canonicalDIIIProxy (E := E)).C = modular_j (E := E)
      ∧ -((canonicalDIIIProxy (E := E)).S) = spectral_epsilon (E := E)
      ∧ (canonicalDIIIProxy (E := E)).T = complex_i (E := E)
      ∧ (canonicalDIIIProxy (E := E)).T.comp
          (canonicalDIIIProxy (E := E)).T =
            -(ContinuousLinearMap.id ℝ H₂) :=
  canonicalDIIIProxy_majorana_root_laws (E := E)

/-- The canonical Majorana conjugation is the DIII particle-hole operator. -/
@[rep_depth transport]
theorem packetOfCanonicalDIIIProxy_J_eq_C :
    canonicalMajoranaJ (E := E) =
      (canonicalDIIIProxy (E := E)).C := by
  symm
  exact canonicalDIIIProxy_C_eq_modular_j (E := E)

/-- The canonical Majorana spectral sign is the DIII chiral sign `-S`. -/
@[rep_depth transport]
theorem packetOfCanonicalDIIIProxy_eps_eq_neg_S :
    canonicalMajoranaEps (E := E) =
      -((canonicalDIIIProxy (E := E)).S) := by
  symm
  simpa using congrArg Neg.neg
    (canonicalDIIIProxy_S_eq_neg_spectral_epsilon (E := E))

/-- The canonical Majorana phase axis is the DIII time-reversal operator. -/
@[rep_depth transport]
theorem packetOfCanonicalDIIIProxy_K_eq_T :
    canonicalMajoranaK (E := E) =
      (canonicalDIIIProxy (E := E)).T :=
  (canonicalDIIIProxy_T_eq_complex_i (E := E)).symm

/-- The DIII chiral sign `-S`, identified with the canonical Majorana
spectral sign, is involutive. -/
@[rep_depth transport]
theorem packetOfCanonicalDIIIProxy_eps_sq :
    (-((canonicalDIIIProxy (E := E)).S)).comp
        (-((canonicalDIIIProxy (E := E)).S)) =
      ContinuousLinearMap.id ℝ H₂ := by
  rw [← packetOfCanonicalDIIIProxy_eps_eq_neg_S (E := E)]
  exact canonicalMajoranaEps_sq (E := E)

/-- The DIII particle-hole operator and chiral sign satisfy the canonical
Majorana anticommutation law. -/
@[rep_depth transport]
theorem packetOfCanonicalDIIIProxy_J_eps_anticommute :
    (canonicalDIIIProxy (E := E)).C.comp
        (-((canonicalDIIIProxy (E := E)).S)) =
      -((-((canonicalDIIIProxy (E := E)).S)).comp
        (canonicalDIIIProxy (E := E)).C) := by
  rw [← packetOfCanonicalDIIIProxy_J_eq_C (E := E),
    ← packetOfCanonicalDIIIProxy_eps_eq_neg_S (E := E)]
  exact canonicalMajoranaJ_Eps_anticommute (E := E)

/-- The DIII time-reversal phase axis is the composite of particle-hole and
chiral-sign operators. -/
@[rep_depth transport]
theorem packetOfCanonicalDIIIProxy_K_eq_J_comp_eps :
    (canonicalDIIIProxy (E := E)).T =
      (canonicalDIIIProxy (E := E)).C.comp
        (-((canonicalDIIIProxy (E := E)).S)) := by
  rw [← packetOfCanonicalDIIIProxy_K_eq_T (E := E),
    ← packetOfCanonicalDIIIProxy_J_eq_C (E := E),
    ← packetOfCanonicalDIIIProxy_eps_eq_neg_S (E := E)]
  exact canonicalMajoranaK_eq_J_comp_Eps (E := E)

/-- Complete theorem-level recovery of the former DIII Majorana packet
fields.  Every law is derived from the doubled-core owner. -/
@[rep_depth transport]
theorem packetOfCanonicalDIIIProxy_complete_root_laws :
    (canonicalDIIIProxy (E := E)).C.comp
        (canonicalDIIIProxy (E := E)).C =
        ContinuousLinearMap.id ℝ H₂
      ∧
    (-((canonicalDIIIProxy (E := E)).S)).comp
        (-((canonicalDIIIProxy (E := E)).S)) =
        ContinuousLinearMap.id ℝ H₂
      ∧
    (canonicalDIIIProxy (E := E)).C.comp
        (-((canonicalDIIIProxy (E := E)).S)) =
        -((-((canonicalDIIIProxy (E := E)).S)).comp
          (canonicalDIIIProxy (E := E)).C)
      ∧
    (canonicalDIIIProxy (E := E)).T =
        (canonicalDIIIProxy (E := E)).C.comp
          (-((canonicalDIIIProxy (E := E)).S))
      ∧
    (canonicalDIIIProxy (E := E)).T.comp
        (canonicalDIIIProxy (E := E)).T =
        -(ContinuousLinearMap.id ℝ H₂) := by
  refine ⟨(canonicalDIIIProxy (E := E)).C_sq,
    packetOfCanonicalDIIIProxy_eps_sq (E := E),
    packetOfCanonicalDIIIProxy_J_eps_anticommute (E := E),
    packetOfCanonicalDIIIProxy_K_eq_J_comp_eps (E := E), ?_⟩
  rw [canonicalDIIIProxy_T_eq_complex_i]
  exact canonicalMajoranaK_sq_eq_neg_id (E := E)

end Core

end InfoGeometry.Canonical.MajoranaLiftPacketBridge
