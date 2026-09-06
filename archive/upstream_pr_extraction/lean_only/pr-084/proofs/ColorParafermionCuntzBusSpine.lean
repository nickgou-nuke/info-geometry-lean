import proofs.GellMannParafermionRealizationRoutesSynthesis

/-!
# Color--parafermion--Cuntz bus spine

This module records one finite conjunction of existing algebraic results for
the SU(3), parafermion, BdG, and Cuntz components.
-/

noncomputable section

namespace ColorParafermionCuntzBusSpine

open AlgebraicCuntzQuotient
open BogoliubovSU3ParafermionProofChain
open BogoliubovSU3ParafermionWeld
open BogoliubovWeylChemicalPotential
open CantorBoundaryCuntzFamily
open GellMannParafermionRealizationRoutesSynthesis
open GellMannParafermionSolder
open GellMannSU3
open ParafermionIdentityRealization
open SupergradedCuntzBdG
open WeylSU3ColorSymmetry

/-- The SU(3) color commutator proposition used by the imported chain. -/
abbrev su3ColorCommutators
    {V : Type*} [AddCommGroup V] [Module ℂ V] (ψ : ColorSpinor4 V) : Prop :=
    colorLieAction4 ((2 * Complex.I) • gl3) ψ =
      colorLieAction4 gl1 (colorLieAction4 gl2 ψ) -
        colorLieAction4 gl2 (colorLieAction4 gl1 ψ) ∧
    colorLieAction4 ((-2 * Complex.I) • gl2) ψ =
      colorLieAction4 gl1 (colorLieAction4 gl3 ψ) -
        colorLieAction4 gl3 (colorLieAction4 gl1 ψ) ∧
    colorLieAction4 ((2 * Complex.I) • gl1) ψ =
      colorLieAction4 gl2 (colorLieAction4 gl3 ψ) -
        colorLieAction4 gl3 (colorLieAction4 gl2 ψ) ∧
    colorLieAction4 (Complex.I • gl5) ψ =
      colorLieAction4 gl1 (colorLieAction4 gl6 ψ) -
        colorLieAction4 gl6 (colorLieAction4 gl1 ψ) ∧
    colorLieAction4 ((-Complex.I) • gl4) ψ =
      colorLieAction4 gl1 (colorLieAction4 gl7 ψ) -
        colorLieAction4 gl7 (colorLieAction4 gl1 ψ) ∧
    colorLieAction4 ((-Complex.I) • gl4) ψ =
      colorLieAction4 gl2 (colorLieAction4 gl6 ψ) -
        colorLieAction4 gl6 (colorLieAction4 gl2 ψ) ∧
    colorLieAction4 ((-Complex.I) • gl5) ψ =
      colorLieAction4 gl2 (colorLieAction4 gl7 ψ) -
        colorLieAction4 gl7 (colorLieAction4 gl2 ψ) ∧
    colorLieAction4 (Complex.I • gl5) ψ =
      colorLieAction4 gl3 (colorLieAction4 gl4 ψ) -
        colorLieAction4 gl4 (colorLieAction4 gl3 ψ) ∧
    colorLieAction4 ((-Complex.I) • gl4) ψ =
      colorLieAction4 gl3 (colorLieAction4 gl5 ψ) -
        colorLieAction4 gl5 (colorLieAction4 gl3 ψ) ∧
    colorLieAction4 (Complex.I • gl2) ψ =
      colorLieAction4 gl4 (colorLieAction4 gl6 ψ) -
        colorLieAction4 gl6 (colorLieAction4 gl4 ψ) ∧
    colorLieAction4 (Complex.I • gl1) ψ =
      colorLieAction4 gl4 (colorLieAction4 gl7 ψ) -
        colorLieAction4 gl7 (colorLieAction4 gl4 ψ) ∧
    colorLieAction4 ((-Complex.I) • gl1) ψ =
      colorLieAction4 gl5 (colorLieAction4 gl6 ψ) -
        colorLieAction4 gl6 (colorLieAction4 gl5 ψ) ∧
    colorLieAction4 (Complex.I • gl2) ψ =
      colorLieAction4 gl5 (colorLieAction4 gl7 ψ) -
        colorLieAction4 gl7 (colorLieAction4 gl5 ψ) ∧
    colorLieAction4 gl3 (colorLieAction4 gl8 ψ) =
      colorLieAction4 gl8 (colorLieAction4 gl3 ψ) ∧
    colorLieAction4 ((-3 * Complex.I) • gl5) ψ =
      colorLieAction4 gl4 (colorLieAction4 gl8 ψ) -
        colorLieAction4 gl8 (colorLieAction4 gl4 ψ) ∧
    colorLieAction4 ((3 * Complex.I) • gl4) ψ =
      colorLieAction4 gl5 (colorLieAction4 gl8 ψ) -
        colorLieAction4 gl8 (colorLieAction4 gl5 ψ)

/-- The route proposition with direct commutator conjuncts. -/
abbrev realizationRoutes
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (F : CuntzFamilyOn V)
    (A B C : GellMannParafermionRealizationRoutesSynthesis.M3C)
    (c : ℂ) (Bog : BogoliubovInertialFrame) (δμ : ℝ) : Prop :=
    realizedParafermionColorSpinor4 idRealization = bdgMajoranaPlusColorSpinor4 ∧
    gellMannParafermionSolder idRealization A =
      colorLieAction4 A bdgMajoranaPlusColorSpinor4 ∧
    su3ColorCommutators bdgMajoranaPlusColorSpinor4 ∧
    (∀ i : Fin 4, cuntzFamilyLift V F (S (R := ℂ) i) = F.S i) ∧
    (∀ i : Fin 4, cuntzFamilyLift V F (T (R := ℂ) i) = F.T i) ∧
    (∀ i j : Fin 4, cuntzT i * cuntzS j =
      if i = j then (1 : C4Functions →ₗ[ℂ] C4Functions) else 0) ∧
    (∑ i : Fin 4, cuntzS i * cuntzT i) = (1 : C4Functions →ₗ[ℂ] C4Functions) ∧
    (gellMannParafermionSolder c4Realization A).2 = 0 ∧
    su3ColorCommutators (realizedParafermionColorSpinor4 c4Realization) ∧
    colorLieAction4 (weylAct swap12 A)
        (gellMannParafermionSolder c4Realization (weylAct swap12 B)) -
      colorLieAction4 (weylAct swap12 B)
        (gellMannParafermionSolder c4Realization (weylAct swap12 A)) =
        c • gellMannParafermionSolder c4Realization (weylAct swap12 C) ∧
    colorLieAction4 (weylAct swap23 A)
        (gellMannParafermionSolder c4Realization (weylAct swap23 B)) -
      colorLieAction4 (weylAct swap23 B)
        (gellMannParafermionSolder c4Realization (weylAct swap23 A)) =
        c • gellMannParafermionSolder c4Realization (weylAct swap23 C) ∧
    colorLieAction4 (weylAct swap12 gl1)
        (gellMannParafermionSolder c4Realization (weylAct swap12 gl2)) -
      colorLieAction4 (weylAct swap12 gl2)
        (gellMannParafermionSolder c4Realization (weylAct swap12 gl1)) =
        (2 * Complex.I) • gellMannParafermionSolder c4Realization (weylAct swap12 gl3) ∧
    frameSolderedBraid { Bog with μ := Bog.μ + δμ } bdgMajoranaPlusColorSpinor4 =
      qBraid4 (qRapidity (Bog.β * δμ * Bog.Q))
        (frameSolderedBraid Bog bdgMajoranaPlusColorSpinor4)

/-- The Bogoliubov/SU(3)/parafermion proposition imported from the weld module. -/
abbrev bogoliubovSynthesis
    (F : BogoliubovInertialFrame) (δμ a : ℝ) : Prop :=
    (2 * Real.pi) * unruhTemperature a = a ∧
    frameWeylQ F = qRapidity (frameWeylLogClock F) ∧
    frameBraidingPhase F = frameWeylQ F ∧
    frameBraidingPhase { F with μ := F.μ + δμ } =
      qRapidity (F.β * δμ * F.Q) * frameBraidingPhase F ∧
    affineSuperBracket (frameWeylQ F) Z2Parity.even Z2Parity.even gl1 gl2 =
      (2 * Complex.I) • gl3 ∧
    affineSuperBracket (frameWeylQ F) Z2Parity.even Z2Parity.even gl1 gl3 =
      (-2 * Complex.I) • gl2 ∧
    affineSuperBracket (frameWeylQ F) Z2Parity.even Z2Parity.even gl3 gl8 = 0 ∧
    (∀ i : Fin 4, bdgParafermionPlus4 i * bdgParafermionPlus4 i = hamiltonianAtom i) ∧
    (∀ lane, parafermionBraid 1 lane = lane)

/-- The finite proof-chain proposition with the commutator block named above. -/
abbrev bogoliubovProofChain
    (F : BogoliubovInertialFrame) (δμ : ℝ)
    {V : Type*} [AddCommGroup V] [Module ℂ V] (ψ : ColorSpinor4 V) : Prop :=
    frameBraid4 { F with μ := F.μ + δμ } bdgMajoranaPlusColorSpinor4 =
      qBraid4 (qRapidity (F.β * δμ * F.Q))
        (frameBraid4 F bdgMajoranaPlusColorSpinor4) ∧
    (∀ i : Fin 3,
      bdgMajoranaPlusColorSpinor4.1 i * bdgMajoranaPlusColorSpinor4.1 i =
        hamiltonianAtom (⟨i.1, Nat.lt_trans i.2 (by decide : 3 < 4)⟩ : Fin 4)) ∧
    bdgMajoranaPlusColorSpinor4.2 * bdgMajoranaPlusColorSpinor4.2 =
      hamiltonianAtom (3 : Fin 4) ∧
    su3ColorCommutators ψ

/-- The affine `λ₁,λ₂` bracket proposition. -/
abbrev frameAffineGl1Gl2 (F : BogoliubovInertialFrame) : Prop :=
    affineSuperBracket (frameWeylQ F) Z2Parity.even Z2Parity.even gl1 gl2 =
      (2 * Complex.I) • gl3

/-- The first BdG parafermion square proposition. -/
abbrev bdgParafermionSq0 : Prop :=
    bdgParafermionPlus4 (0 : Fin 4) * bdgParafermionPlus4 (0 : Fin 4) =
      hamiltonianAtom (0 : Fin 4)

/-- The first algebraic Cuntz left inverse proposition. -/
abbrev cuntzLeftInverse00 : Prop :=
    T (R := ℂ) (0 : Fin 4) * S (R := ℂ) (0 : Fin 4) =
      if (0 : Fin 4) = 0 then 1 else 0

/-- The finite algebraic Cuntz partition proposition. -/
abbrev cuntzPartitionOne : Prop :=
    (∑ i : Fin 4, S (R := ℂ) i * T (R := ℂ) i) = 1

/-- `closed_color_parafermion_cuntz_bus_spine` combines the imported finite
SU(3), parafermion, BdG, and Cuntz propositions.
The declaration `closed_color_parafermion_cuntz_bus_spine` is kept stable for
graph references. -/
theorem closed_color_parafermion_cuntz_bus_spine
    (F : BogoliubovInertialFrame) (δμ a : ℝ) :
    realizationRoutes c4CuntzFamily gl1 gl2 gl3 (2 * Complex.I) F δμ ∧
    bogoliubovSynthesis F δμ a ∧
    bogoliubovProofChain F δμ bdgMajoranaPlusColorSpinor4 ∧
    su3ColorCommutators bdgMajoranaPlusColorSpinor4 ∧
    frameAffineGl1Gl2 F ∧
    bdgParafermionSq0 ∧
    cuntzLeftInverse00 ∧
    cuntzPartitionOne := by
  have routePack :=
    gellmann_parafermion_realization_routes_synthesis
      c4CuntzFamily gl1 gl2 gl3 (2 * Complex.I) gl1_comm_gl2 F δμ
  rcases routePack with
    ⟨route_id, route_solder, _,
      liftS, liftT, cantorTS, cantorST, cantor_singlet, _,
      weyl12, weyl23, weyl_gl, route_braid⟩
  have routes : realizationRoutes c4CuntzFamily gl1 gl2 gl3 (2 * Complex.I) F δμ :=
    ⟨route_id, route_solder,
      su3_color_action_all_commutators bdgMajoranaPlusColorSpinor4,
      liftS, liftT, cantorTS, cantorST, cantor_singlet,
      su3_color_action_all_commutators (realizedParafermionColorSpinor4 c4Realization),
      weyl12, weyl23, weyl_gl, route_braid⟩
  have synthesis := bogoliubov_su3_parafermion_synthesis F δμ a
  have chain := bogoliubov_su3_parafermion_proof_chain F δμ bdgMajoranaPlusColorSpinor4
  have commutators := su3_color_action_all_commutators bdgMajoranaPlusColorSpinor4
  have bracket := frame_affine_gl1_gl2 F
  have parafermion_sq := bdgParafermionPlus4_sq (0 : Fin 4)
  have left_inverse := T_mul_S (R := ℂ) (0 : Fin 4) (0 : Fin 4)
  have partition := partition_one (R := ℂ) (ι := Fin 4)
  constructor
  · exact routes
  constructor
  · exact synthesis
  constructor
  · exact chain
  constructor
  · exact commutators
  constructor
  · exact bracket
  constructor
  · exact parafermion_sq
  constructor
  · exact left_inverse
  · exact partition

end ColorParafermionCuntzBusSpine

end noncomputable section
