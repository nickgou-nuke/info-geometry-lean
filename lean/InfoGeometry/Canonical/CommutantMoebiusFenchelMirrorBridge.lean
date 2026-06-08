import InfoGeometry.Canonical.HestenesCommutantGeometry
import InfoGeometry.Canonical.SouriauDiracHodgeCoupling
import InfoGeometry.Canonical.SouriauFenchelOnsagerBridge
import InfoGeometry.Canonical.TypeIIIModularCantorSystem
import InfoGeometry.Clifford.SplitCartanHopWittBridge
import InfoGeometry.Krein.HestenesAffineO55ClosureBridge
import InfoGeometry.Krein.HestenesMoebiusClosureBridge

/-!
# Commutant, Möbius, Fenchel, and Modular-Mirror Finite Window

This file packages four existing owner surfaces into one theorem-safe finite
window:

* the Hestenes phase-axis commutant is closed under multiplication;
* the witness-gated Möbius socket fixes the Hestenes phase axis;
* the scalar Fenchel gap is invariant under paired primal/dual symmetries;
* the Tomita/Cartan mirror is involutive;
* the `Cl(5,5)` head anti-diagonal Cartan hop realizes the Witt/CAR pair.
* the supplied `O(5,5)` socket preserves the natural cone, null cone, and
  Ω-volume readout;
* the real Dirac-Hodge lane proves J-gated twisted-index vanishing and the
  Hodge-star phase-axis flip.

It deliberately does **not** prove the infinite commutant of `Cl(∞,∞)`, a
global `SL(2,ℝ)` completion of the Cuntz map, or an equality between those
global structures.  Those remain separate closure targets unless supplied by
native Lean owner theorems.
-/

open scoped InnerProductSpace

noncomputable section

namespace InfoGeometry.Canonical.CommutantMoebiusFenchelMirrorBridge

open InfoGeometry.Clifford.ClNN
open InfoGeometry.Clifford.SplitCartanHopWittBridge

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable {Word : Type*} [Fintype Word] [DecidableEq Word]

local notation "H₂" => InfoGeometry.Krein.DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

variable {Left Right : Type*}
variable [AddCommGroup Left] [Module ℝ Left]
variable [AddCommGroup Right] [Module ℝ Right]

/--
Finite commutant/Möbius/Fenchel/mirror/Cartan-hop bridge.

This is the precise kernel-checked content currently available from the owner
files.  It packages compatible finite-window readouts, not a global
identification theorem for the infinite CAR commutant or a global Cuntz
`SL(2,ℝ)` completion.
-/
@[rep_depth krein]
theorem finite_commutant_moebius_fenchel_mirror_o55_window
    (M :
      InfoGeometry.Krein.HestenesMoebiusClosureBridge.HestenesMoebiusClosureBridge
        (E := E) Word)
    (mobius :
      InfoGeometry.Krein.HestenesMoebiusClosureBridge.MoebiusParameter)
    (A B : EndH)
    (hA :
      InfoGeometry.Canonical.HestenesCommutantGeometry.CommutesWithHestenesK
        (E := E) A)
    (hB :
      InfoGeometry.Canonical.HestenesCommutantGeometry.CommutesWithHestenesK
        (E := E) B)
    (L : InfoGeometry.LogPotential.LegendreModel)
    {G : Type*} [Group G]
    (actθ : G → ℝ → ℝ)
    (actη : G → ℝ → ℝ)
    (hψ :
      ∀ g θ,
        L.massieu (actθ g θ) = L.massieu θ)
    (hφ :
      ∀ g η,
        L.φ (actη g η) = L.φ η)
    (hpair :
      ∀ g θ η,
        actθ g θ * actη g η = θ * η)
    (fenchelSym : G)
    (θ η : ℝ)
    (T :
      InfoGeometry.Canonical.TypeIIIModularCantorSystem.ModularMirror Left Right)
    (z : T.Doubled) :
    InfoGeometry.Canonical.HestenesCommutantGeometry.CommutesWithHestenesK
        (E := E) (A * B) ∧
    M.operatorAction mobius (InfoGeometry.Krein.clockAxis (E := E)) =
        InfoGeometry.Krein.clockAxis (E := E) ∧
    L.fenchelGap (actθ fenchelSym θ) (actη fenchelSym η) =
        L.fenchelGap θ η ∧
    T.theta (T.theta z) = z ∧
    headCartanHop 4 (headNullMinus 4) = headNullMinus 4 ∧
    headCartanHop 4 (headNullPlus 4) = -headNullPlus 4 ∧
    gammaHeadNullMinus 4 * gammaHeadNullMinus 4 = 0 ∧
    gammaHeadNullPlus 4 * gammaHeadNullPlus 4 = 0 ∧
    gammaHeadNullMinus 4 * gammaHeadNullPlus 4 +
        gammaHeadNullPlus 4 * gammaHeadNullMinus 4 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact
      InfoGeometry.Canonical.HestenesCommutantGeometry.CommutesWithHestenesK.mul
        (E := E) hA hB
  · exact M.moebius_phaseAxis_fixed mobius
  · exact
      InfoGeometry.LogPotential.LegendreModel.fenchelGap_invariant_of_preserves_potentials_and_pairing
        L actθ actη hψ hφ hpair fenchelSym θ η
  · exact
      InfoGeometry.Canonical.TypeIIIModularCantorSystem.ModularMirror.theta_sq T z
  · exact
      o55_antidiagonal_cartan_hop_realizes_split_clifford_witt_pair.1
  · exact
      o55_antidiagonal_cartan_hop_realizes_split_clifford_witt_pair.2.1
  · exact
      o55_antidiagonal_cartan_hop_realizes_split_clifford_witt_pair.2.2.1
  · exact
      o55_antidiagonal_cartan_hop_realizes_split_clifford_witt_pair.2.2.2.1
  · exact
      o55_antidiagonal_cartan_hop_realizes_split_clifford_witt_pair.2.2.2.2

/--
Supplied `O(5,5)` closure and real Dirac-Hodge trace window.

This packages the exact owner-level consequences from
`HestenesAffineO55ClosureBridge` and `SouriauDiracHodgeCoupling`: a supplied
`O(5,5)` action preserves the natural cone, null cone, and Ω-volume state, and
a supplied real Krein trace satisfying the J-invariance hypotheses has vanishing
twisted index.
-/
@[rep_depth krein]
theorem supplied_o55_and_dirac_hodge_trace_window
    [InfoGeometry.Krein.KreinSpace H₂]
    (B :
      InfoGeometry.Krein.HestenesAffineO55ClosureBridge.HestenesAffineO55ClosureBridge
        (E := E))
    (ξ : H₂)
    (hNatural :
      ξ ∈
        B.duality.arithmetic.moebius.wilson.kmsPacket.HestenesNaturalCone)
    (hNull :
      ξ ∈
        InfoGeometry.Krein.HestenesMoebiusClosureBridge.HestenesNullCone
          B.duality.arithmetic.moebius.wilson.kmsPacket)
    (A : EndH)
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [InfoGeometry.Krein.KreinSpace H]
    (D : InfoGeometry.Dynamics.SouriauDiracHodge.KreinOperatorData H)
    (trace : (H →L[ℝ] H) → ℝ)
    (hTraceLinear : ∀ (c : ℝ) (T : H →L[ℝ] H), trace (c • T) = c * trace T)
    (hTraceJ : ∀ T, trace (D.J * T * D.J) = trace T)
    (hProjJ : D.twistedSectorProjection * D.J = D.J * D.twistedSectorProjection) :
    B.o55VectorAction ξ ∈
        B.duality.arithmetic.moebius.wilson.kmsPacket.HestenesNaturalCone ∧
    B.o55VectorAction ξ ∈
        InfoGeometry.Krein.HestenesMoebiusClosureBridge.HestenesNullCone
          B.duality.arithmetic.moebius.wilson.kmsPacket ∧
    B.duality.arithmetic.moebius.wilson.volume.volumeState (B.o55OperatorAction A) =
        B.duality.arithmetic.moebius.wilson.volume.volumeState A ∧
    D.indexPairing trace = 0 ∧
    D.J * D.chiralChargeOperator * D.J = -D.chiralChargeOperator := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact B.o55_preserves_naturalCone hNatural
  · exact B.o55_preserves_nullCone hNull
  · exact B.volumeState_o55_invariant A
  · exact
      InfoGeometry.Canonical.SouriauDiracHodgeCoupling.krein_operator_twisted_index_vanishing
        H D trace hTraceLinear hTraceJ hProjJ
  · exact D.hodge_star_executes_legendre_transform

end Core

end InfoGeometry.Canonical.CommutantMoebiusFenchelMirrorBridge
