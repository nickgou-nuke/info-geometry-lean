import proofs.ParafermionIdentityRealization
import proofs.CantorBoundaryCuntzFamily
import proofs.WeylSolderedParafermionSymmetry

/-!
# Cuntz boundary realization of the soldered parafermion color lanes

This module bundles the now-populated realization routes for the
Gell-Mann-to-parafermion soldering map:

* identity/regular realization of `CuntzAlg ℂ (Fin 4)`;
* universal realization from any algebraic Cuntz family on a complex module;
* concrete 4-symbol Cantor-boundary Cuntz family;
* SU(3) commutator soldering and Weyl-transported soldering on those
  realization routes.
-/

noncomputable section

namespace CuntzBoundarySolderRealization

open ParafermionIdentityRealization
open CantorBoundaryCuntzFamily
open GellMannParafermionSolder
open WeylSolderedParafermionSymmetry
open WeylSU3ColorSymmetry
open BogoliubovSU3ParafermionProofChain
open GellMannSU3
open AlgebraicCuntzQuotient

abbrev M3C := Matrix (Fin 3) (Fin 3) ℂ

/-- The identity realization is the regular algebraic representation route. -/
theorem identity_route_recovers_bdg_spinor :
    realizedParafermionColorSpinor4 idRealization = bdgMajoranaPlusColorSpinor4 :=
  idRealization_spinor_eq

/-- The universal Cuntz-family route sends generators to the supplied family
operators. -/
theorem universal_cuntz_family_route
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (F : CuntzFamilyOn V) :
    (∀ i : Fin 4,
      cuntzFamilyLift V F (AlgebraicCuntzQuotient.S (R := ℂ) i) = F.S i) ∧
    (∀ i : Fin 4,
      cuntzFamilyLift V F (AlgebraicCuntzQuotient.T (R := ℂ) i) = F.T i) := by
  exact ⟨cuntzFamilyLift_S V F, cuntzFamilyLift_T V F⟩

/-- The concrete Cantor-boundary family satisfies the algebraic Cuntz relations. -/
theorem cantor_boundary_route_cuntz_relations :
    (∀ i j : Fin 4,
      cuntzT i * cuntzS j =
        if i = j then (1 : C4Functions →ₗ[ℂ] C4Functions) else 0) ∧
    (∑ i : Fin 4, cuntzS i * cuntzT i) = (1 : C4Functions →ₗ[ℂ] C4Functions) := by
  exact ⟨cuntz_ortho, cuntz_partition⟩

/-- The concrete Cantor-boundary realization is obtained from the universal
Cuntz-family realization route. -/
theorem cantor_boundary_realization_eq_family_realization :
    c4Realization = cuntzFamilyRealization C4Functions c4CuntzFamily (fun _ => 0) := rfl

/-- In the identity route, the Gell-Mann solder is exactly the color action on
the abstract BdG/Majorana spinor. -/
theorem identity_route_solder (A : M3C) :
    gellMannParafermionSolder idRealization A =
      colorLieAction4 A bdgMajoranaPlusColorSpinor4 :=
  gellMannSolder_idRealization A

/-- In the Cantor boundary route, the soldered singlet lane is color-neutral. -/
theorem cantor_boundary_solder_singlet_zero (A : M3C) :
    (gellMannParafermionSolder c4Realization A).2 = 0 :=
  gellMannParafermionSolder_singlet_zero c4Realization A

/-- The full SU(3) Gell-Mann commutator table is valid on the Cantor-boundary
realized parafermion color spinor. -/
theorem cantor_boundary_su3_commutators :
    ∃ h, h = su3_color_action_all_commutators
      (realizedParafermionColorSpinor4 c4Realization) :=
  solder_su3_color_action_all_commutators c4Realization

/-- Weyl-transported seed commutators act correctly on the Cantor-boundary
soldered parafermion color lanes. -/
theorem cantor_boundary_weyl_soldered_transport
    (A B C : M3C) (c : ℂ) (h : A * B - B * A = c • C) :
    colorLieAction4 (weylAct swap12 A)
        (gellMannParafermionSolder c4Realization (weylAct swap12 B)) -
      colorLieAction4 (weylAct swap12 B)
        (gellMannParafermionSolder c4Realization (weylAct swap12 A)) =
        c • gellMannParafermionSolder c4Realization (weylAct swap12 C) ∧
    colorLieAction4 (weylAct swap23 A)
        (gellMannParafermionSolder c4Realization (weylAct swap23 B)) -
      colorLieAction4 (weylAct swap23 B)
        (gellMannParafermionSolder c4Realization (weylAct swap23 A)) =
        c • gellMannParafermionSolder c4Realization (weylAct swap23 C) := by
  exact weyl_soldered_parafermion_symmetry_synthesis c4Realization A B C c h

/-- Concrete Cantor-boundary Weyl transport of `[λ₁,λ₂]=2iλ₃`. -/
theorem cantor_boundary_weyl_gl1_gl2 :
    colorLieAction4 (weylAct swap12 gl1)
        (gellMannParafermionSolder c4Realization (weylAct swap12 gl2)) -
      colorLieAction4 (weylAct swap12 gl2)
        (gellMannParafermionSolder c4Realization (weylAct swap12 gl1)) =
        (2 * Complex.I) • gellMannParafermionSolder c4Realization (weylAct swap12 gl3) ∧
    colorLieAction4 (weylAct swap23 gl1)
        (gellMannParafermionSolder c4Realization (weylAct swap23 gl2)) -
      colorLieAction4 (weylAct swap23 gl2)
        (gellMannParafermionSolder c4Realization (weylAct swap23 gl1)) =
        (2 * Complex.I) • gellMannParafermionSolder c4Realization (weylAct swap23 gl3) := by
  exact cantor_boundary_weyl_soldered_transport gl1 gl2 gl3 (2 * Complex.I) gl1_comm_gl2

/-- Synthesis: the identity, universal Cuntz-family, and Cantor-boundary routes
all feed the same soldered SU(3)/Weyl parafermion color action. -/
theorem cuntz_boundary_solder_realization_synthesis
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (F : CuntzFamilyOn V) (A : M3C) :
    realizedParafermionColorSpinor4 idRealization = bdgMajoranaPlusColorSpinor4 ∧
    gellMannParafermionSolder idRealization A =
      colorLieAction4 A bdgMajoranaPlusColorSpinor4 ∧
    (∀ i : Fin 4,
      cuntzFamilyLift V F (AlgebraicCuntzQuotient.S (R := ℂ) i) = F.S i) ∧
    (∀ i : Fin 4,
      cuntzFamilyLift V F (AlgebraicCuntzQuotient.T (R := ℂ) i) = F.T i) ∧
    (∀ i j : Fin 4,
      cuntzT i * cuntzS j =
        if i = j then (1 : C4Functions →ₗ[ℂ] C4Functions) else 0) ∧
    (∑ i : Fin 4, cuntzS i * cuntzT i) = (1 : C4Functions →ₗ[ℂ] C4Functions) ∧
    (gellMannParafermionSolder c4Realization A).2 = 0 ∧
    (∃ h, h = su3_color_action_all_commutators
      (realizedParafermionColorSpinor4 c4Realization)) := by
  exact ⟨identity_route_recovers_bdg_spinor,
    identity_route_solder A,
    (universal_cuntz_family_route F).1,
    (universal_cuntz_family_route F).2,
    cantor_boundary_route_cuntz_relations.1,
    cantor_boundary_route_cuntz_relations.2,
    cantor_boundary_solder_singlet_zero A,
    cantor_boundary_su3_commutators⟩

end CuntzBoundarySolderRealization

end noncomputable section
