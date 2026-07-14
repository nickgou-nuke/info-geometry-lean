import InfoGeometry.Core.MajoranaLiftPacket
import InfoGeometry.Canonical.RealBdGDIIIAtom
import InfoGeometry.Canonical.UnifiedSuperchargeAlgebra
import InfoGeometry.Canonical.OnsagerCasimirJ
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.MajoranaLiftPacketBridge

Owner-respecting bridge:

- reifies the canonical DIII proxy into the root `MajoranaLiftPacket`,
- exposes projected fermionic odd/even closure from the unified supercharge lane,
- and exports the operatorial Onsager phase sign-flip law.

This file is a translator surface over existing owners; it does not introduce a
second ontology.
-/

namespace MajoranaLiftPacketBridge

open InfoGeometry.Core
open InfoGeometry.Krein
open InfoGeometry.Canonical.RealBdGDIIIAtom
open InfoGeometry.Canonical.UnifiedSuperchargeAlgebra
open InfoGeometry.Canonical.OnsagerCasimirJ

section Core

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/--
Translator: canonical DIII proxy induces the root doubled-core Majorana packet.
-/
@[rep_depth transport]
noncomputable def packetOfCanonicalDIIIProxy : MajoranaLiftPacket (E := E) where
  J := (canonicalDIIIProxy (E := E)).C
  eps := -((canonicalDIIIProxy (E := E)).S)
  K := (canonicalDIIIProxy (E := E)).T
  hJ_sq := by
    exact (canonicalDIIIProxy (E := E)).C_sq
  hEps_sq := by
    calc
      (-(canonicalDIIIProxy (E := E)).S).comp (-(canonicalDIIIProxy (E := E)).S)
          = (spectral_epsilon (E := E)).comp (spectral_epsilon (E := E)) := by simp
      _ = ContinuousLinearMap.id ℝ H₂ := spectral_epsilon_involution (E := E)
  hJ_eps_anticomm := by
    calc
      (canonicalDIIIProxy (E := E)).C.comp (-(canonicalDIIIProxy (E := E)).S)
          = (modular_j (E := E)).comp (spectral_epsilon (E := E)) := by simp
      _ = -((spectral_epsilon (E := E)).comp (modular_j (E := E))) := by
            exact modular_j_spectral_epsilon_anticommute (E := E)
      _ = -((-(canonicalDIIIProxy (E := E)).S).comp (canonicalDIIIProxy (E := E)).C) := by simp
  hK_eq_J_comp_eps := by
    calc
      (canonicalDIIIProxy (E := E)).T = complex_i (E := E) := by
            exact canonicalDIIIProxy_T_eq_complex_i (E := E)
      _ = (modular_j (E := E)).comp (spectral_epsilon (E := E)) := rfl
      _ = (canonicalDIIIProxy (E := E)).C.comp (-(canonicalDIIIProxy (E := E)).S) := by simp

@[rep_depth transport]
theorem packetOfCanonicalDIIIProxy_root_laws :
    let P := packetOfCanonicalDIIIProxy (E := E)
    P.J = modular_j (E := E)
      ∧ P.eps = spectral_epsilon (E := E)
      ∧ P.K = complex_i (E := E) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [packetOfCanonicalDIIIProxy]

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

end Core

end MajoranaLiftPacketBridge
