import InfoGeometry.Canonical.VectorScoreBridge
import InfoGeometry.Krein.KreinSpace
import InfoGeometry.Krein.HestenesModularKMSBridge
import InfoGeometry.Canonical.RealCl55NativeIntegratedActionBridge
import InfoGeometry.Canonical.RealCl55NativeKreinPairingBridge
import InfoGeometry.Canonical.G2IntegratedKasparovEquivarianceBridge

namespace InfoGeometry.Canonical.PositionalDynamicsRegimeBridge

open InfoGeometry.Krein

/-! A native interface for Krein-isometric positional actions. -/

structure KreinRotorRepresentation
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [KreinSpace H] (G : Type*) [AddGroup G] where
  action : G → H →L[ℝ] H
  action_zero : action 0 = ContinuousLinearMap.id ℝ H
  action_add : ∀ s t, action (s + t) = (action t).comp (action s)
  krein_isometry : ∀ t, KreinSpace.IsKreinIsometry (action t)
  krein_adjoint : ∀ t, KreinSpace.kreinAdjoint (action t) = action (-t)

namespace KreinRotorRepresentation

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [KreinSpace H] [AddGroup G]

theorem relative_score (R : KreinRotorRepresentation H G)
    (q k : H) (t s : G) :
    KreinSpace.kreinInner (R.action t q) (R.action s k) =
      KreinSpace.kreinInner q (R.action (s - t) k) := by
  have hs : (s - t) + t = s := sub_add_cancel s t
  have hsaction : R.action s k = R.action t (R.action (s - t) k) := by
    calc
      R.action s k = R.action ((s - t) + t) k := by rw [hs]
      _ = ((R.action t).comp (R.action (s - t))) k := by rw [R.action_add]
      _ = R.action t (R.action (s - t) k) := rfl
  rw [hsaction]
  exact R.krein_isometry t q (R.action (s - t) k)

theorem adjoint_score (R : KreinRotorRepresentation H G)
    (q k : H) (t : G) :
    KreinSpace.kreinInner (R.action t q) k =
      KreinSpace.kreinInner q (R.action (-t) k) := by
  rw [KreinSpace.kreinInner_kreinAdjoint, R.krein_adjoint]

end KreinRotorRepresentation

/-! Multiplicative form for discrete group actions such as the native Cl55
action. -/

structure KreinGroupRepresentation
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [KreinSpace H] (G : Type*) [Group G] where
  action : G → H →L[ℝ] H
  action_one : action 1 = ContinuousLinearMap.id ℝ H
  action_mul : ∀ g h, action (g * h) = (action g).comp (action h)
  krein_isometry : ∀ g, KreinSpace.IsKreinIsometry (action g)
  krein_adjoint : ∀ g, KreinSpace.kreinAdjoint (action g) = action g⁻¹

namespace KreinGroupRepresentation

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [KreinSpace H] [Group G]

  theorem relative_score (R : KreinGroupRepresentation H G)
    (q k : H) (g h : G) :
    KreinSpace.kreinInner (R.action g q) (R.action h k) =
      KreinSpace.kreinInner q (R.action (g⁻¹ * h) k) := by
  have hfactor : g * (g⁻¹ * h) = h := by simp
  have haction : R.action h k =
      R.action g (R.action (g⁻¹ * h) k) := by
    calc
      R.action h k = R.action (g * (g⁻¹ * h)) k := by rw [hfactor]
      _ = R.action g (R.action (g⁻¹ * h) k) := by
        rw [R.action_mul]
        rfl
  rw [haction]
  exact R.krein_isometry g q (R.action (g⁻¹ * h) k)

theorem adjoint_score (R : KreinGroupRepresentation H G)
    (q k : H) (g : G) :
    KreinSpace.kreinInner (R.action g q) k =
      KreinSpace.kreinInner q (R.action g⁻¹ k) := by
  rw [KreinSpace.kreinInner_kreinAdjoint, R.krein_adjoint]

end KreinGroupRepresentation

/-! A pairing-polymorphic group action, for concrete carriers whose pairing is
owned independently of a `KreinSpace` instance. -/

structure PairingGroupRepresentation
    (H : Type*) (G : Type*) [Group G] where
  pairing : H → H → ℝ
  action : G → H → H
  action_one : action 1 = id
  action_mul : ∀ g h, action (g * h) = action g ∘ action h
  pairing_isometry : ∀ g x y, pairing (action g x) (action g y) = pairing x y

namespace PairingGroupRepresentation

variable {H G : Type*} [Group G]

theorem relative_score (R : PairingGroupRepresentation H G)
    (q k : H) (g h : G) :
    R.pairing (R.action g q) (R.action h k) =
      R.pairing q (R.action (g⁻¹ * h) k) := by
  have hfactor : g * (g⁻¹ * h) = h := by simp
  have haction : R.action h k =
      R.action g (R.action (g⁻¹ * h) k) := by
    calc
      R.action h k = R.action (g * (g⁻¹ * h)) k := by rw [hfactor]
      _ = R.action g (R.action (g⁻¹ * h) k) := by
        rw [R.action_mul]
        rfl
  rw [haction]
  exact R.pairing_isometry g q (R.action (g⁻¹ * h) k)

end PairingGroupRepresentation

namespace RealCl55NativeKreinPairingBridge

open InfoGeometry.Canonical.G2IntegratedKasparovEquivarianceBridge
open InfoGeometry.Canonical.RealCl55FiniteModuleEndBridge
open InfoGeometry.Canonical.RealCl55NativeIntegratedActionBridge
open InfoGeometry.Canonical.RealCl55NativeKreinPairingBridge
open InfoGeometry.Canonical.RealCl55NativeKreinTransportBridge

variable {G : Type*} [Group G]

noncomputable def nativeIntegratedAction_pairingGroupRepresentation
    (act : G2IntegratedAction G)
    (hK : MatrixKreinUnitaryIntegratedAction act) :
    PairingGroupRepresentation RealCl55FiniteModuleEndBridge.NativeSpinorCarrier G :=
  { pairing := nativeKreinPairing
    action := fun g x => nativeIntegratedAction act g x
    action_one := by
      funext x
      simpa using congrArg
        (fun T : RealCl55NativeIntegratedActionBridge.NativeSpinorCLM => T x)
        (nativeIntegratedAction act).map_one
    action_mul := by
      intro g h
      funext x
      simpa [Function.comp_def] using congrArg
        (fun T : RealCl55NativeIntegratedActionBridge.NativeSpinorCLM => T x)
        ((nativeIntegratedAction act).map_mul g h)
    pairing_isometry := by
      intro g x y
      exact nativeIntegratedAction_preserves_kreinPairing act hK g x y }

theorem nativeCl55_relative_pairing_score
    (act : G2IntegratedAction G)
    (hK : MatrixKreinUnitaryIntegratedAction act)
    (q k : RealCl55FiniteModuleEndBridge.NativeSpinorCarrier) (g h : G) :
    nativeKreinPairing (nativeIntegratedAction act g q)
        (nativeIntegratedAction act h k) =
      nativeKreinPairing q
        (nativeIntegratedAction act (g⁻¹ * h) k) := by
  exact (nativeIntegratedAction_pairingGroupRepresentation act hK).relative_score q k g h

end RealCl55NativeKreinPairingBridge

/-! Relative scores for a Krein-isometric positional flow. -/

theorem kreinInner_flow_relative
    {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [KreinSpace H] [AddGroup G]
    (U : G → H →L[ℝ] H)
    (hadd : ∀ s t, U (s + t) = (U t).comp (U s))
    (hiso : ∀ t, KreinSpace.IsKreinIsometry (U t))
    (q k : H) (t s : G) :
    KreinSpace.kreinInner (U t q) (U s k) =
      KreinSpace.kreinInner q (U (s - t) k) := by
  have hs : (s - t) + t = s := sub_add_cancel s t
  have hsflow : U s k = U t (U (s - t) k) := by
    calc
      U s k = U ((s - t) + t) k := by rw [hs]
      _ = ((U t).comp (U (s - t))) k := by rw [hadd]
      _ = U t (U (s - t) k) := rfl
  rw [hsflow]
  exact hiso t q (U (s - t) k)

/-! The same transport written through the native Krein adjoint. -/

theorem kreinInner_flow_via_kreinAdjoint
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [KreinSpace H]
    (U : ℝ → H →L[ℝ] H)
    (hAdj : ∀ t, KreinSpace.kreinAdjoint (U t) = U (-t))
    (q k : H) (t : ℝ) :
    KreinSpace.kreinInner (U t q) k =
      KreinSpace.kreinInner q (U (-t) k) := by
  rw [KreinSpace.kreinInner_kreinAdjoint, hAdj]

theorem kreinInner_flow_relative_via_kreinAdjoint
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [KreinSpace H]
    (U : ℝ → H →L[ℝ] H)
    (hadd : ∀ a b, U (a + b) = (U b).comp (U a))
    (hAdj : ∀ t, KreinSpace.kreinAdjoint (U t) = U (-t))
    (q k : H) (t s : ℝ) :
    KreinSpace.kreinInner (U t q) (U s k) =
      KreinSpace.kreinInner q (U (s - t) k) := by
  rw [KreinSpace.kreinInner_kreinAdjoint, hAdj]
  have hcomp : (U (-t)).comp (U s) = U (s - t) := by
    rw [← hadd s (-t), sub_eq_add_neg]
  rw [← hcomp]
  rfl

end InfoGeometry.Canonical.PositionalDynamicsRegimeBridge

namespace InfoGeometry.Krein.HestenesModularKMSBridge

open InfoGeometry.Krein

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [KreinSpace E]

namespace HestenesKreinKMSPacket

/--
The positional relative-pairing law for a Hestenes rotor.

The KMS packet supplies Krein-isometry of each rotor, while the additive
composition law is an additional dynamical hypothesis: it is not asserted by
the packet merely from its observable-side conjugation data.
-/
theorem rotor_relative
    (P : HestenesKreinKMSPacket (E := E))
    (hadd : ∀ s t, P.rotor (s + t) = (P.rotor t).comp (P.rotor s))
    (q k : E) (t s : ℝ) :
    KreinSpace.kreinInner (P.rotor t q) (P.rotor s k) =
      KreinSpace.kreinInner q (P.rotor (s - t) k) := by
  apply InfoGeometry.Canonical.PositionalDynamicsRegimeBridge.kreinInner_flow_relative
      P.rotor hadd
  intro u
  exact P.rotor_preserves_kreinInner u

/-- Package a Hestenes rotor as the unified native Krein positional action. -/
def toKreinRotorRepresentation
    (P : HestenesKreinKMSPacket (E := E))
    (hzero : P.rotor 0 = ContinuousLinearMap.id ℝ E)
    (hadd : ∀ s t, P.rotor (s + t) = (P.rotor t).comp (P.rotor s))
    (hAdj : ∀ t, KreinSpace.kreinAdjoint (P.rotor t) = P.rotor (-t)) :
    InfoGeometry.Canonical.PositionalDynamicsRegimeBridge.KreinRotorRepresentation E ℝ :=
  { action := P.rotor
    action_zero := hzero
    action_add := hadd
    krein_isometry := P.rotor_preserves_kreinInner
    krein_adjoint := hAdj }

theorem toKreinRotorRepresentation_relative_score
    (P : HestenesKreinKMSPacket (E := E))
    (hzero : P.rotor 0 = ContinuousLinearMap.id ℝ E)
    (hadd : ∀ s t, P.rotor (s + t) = (P.rotor t).comp (P.rotor s))
    (hAdj : ∀ t, KreinSpace.kreinAdjoint (P.rotor t) = P.rotor (-t))
    (q k : E) (t s : ℝ) :
    KreinSpace.kreinInner (P.rotor t q) (P.rotor s k) =
      KreinSpace.kreinInner q (P.rotor (s - t) k) := by
  exact (toKreinRotorRepresentation P hzero hadd hAdj).relative_score q k t s

end HestenesKreinKMSPacket

end InfoGeometry.Krein.HestenesModularKMSBridge
