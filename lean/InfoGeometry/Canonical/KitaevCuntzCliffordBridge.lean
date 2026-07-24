import DAG.GradedBottInclusion
import InfoGeometry.Canonical.BulkBoundaryZeroModeOwner
import InfoGeometry.Canonical.CelikErlangenBraidBridge
import InfoGeometry.Canonical.SouriauDiracHodgeCoupling
import InfoGeometry.Canonical.SplitCliffordJordanWigner
import InfoGeometry.Tessellation.CantorDiracSeaOperatorGeometry

open scoped InnerProductSpace

noncomputable section

/-!
# InfoGeometry.Canonical.KitaevCuntzCliffordBridge

Repo-owned bridge for the safe part of the Kitaev/Cuntz/Clifford dictionary.

This file does not assert a new analytic physical-equivalence theorem.  It
bundles the existing owner surfaces that already formalize the rigorous
algebraic content:

* split `Cl(1,1)` Majorana CAR on the real doubled carrier;
* local and two-mode Jordan--Wigner parity-string CAR;
* graded Bott inclusion as the recursive Jordan--Wigner string;
* finite Kitaev-chain Pfaffian and `ZMod 2` phase laws;
* boundary zero modes from the topological Kitaev lane;
* Cantor Dirac-sea binary hopping geometry;
* real Krein zero-temperature anomaly cancellation;
* concrete real `Z3` Yang--Baxter upgrade.

The missing physics beyond this bridge remains explicit: full continuum
Kitaev Hamiltonian analysis, many-chain braiding as a complete representation,
and universality/density are not claimed here.
-/

namespace InfoGeometry.Canonical.KitaevCuntzCliffordBridge

open InfoGeometry.Canonical.BulkBoundaryZeroModeOwner
open InfoGeometry.Canonical.CelikErlangenBraidBridge
open InfoGeometry.Canonical.FibonacciParafermionAtoms
open InfoGeometry.Canonical.SouriauDiracHodgeCoupling
open InfoGeometry.Canonical.SplitCliffordJordanWigner
open InfoGeometry.Quantum.BulkBoundary
open InfoGeometry.Quantum.KitaevChain
open InfoGeometry.Quantum.RealMajorana
open InfoGeometry.Quantum.RealMajoranaCategory
open InfoGeometry.Tessellation

universe u v

/-- Local concrete `2 × 2` real matrix carrier from the core package. -/
abbrev M2R := InfoGeometryCore.M2R

/--
The formal owner target for the Kitaev/Cuntz/Clifford dictionary.

Every conjunct delegates to an already compiled owner theorem.  The statement is
therefore a navigation/capstone surface, not a new independent model.
-/
def KitaevCuntzCliffordOwnerTarget : Prop :=
  (∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E],
    InfoGeometry.Quantum.RealMajoranaCategory.MajoranaCARWitness
      (cl11DoubledCore E)
      (SplitCliffordDatum.majoranaPairing (cl11SplitCliffordDatum E))
      (SplitCliffordDatum.majoranaField (cl11SplitCliffordDatum E))) ∧
  (P * P = (1 : InfoGeometry.Canonical.SplitCliffordJordanWigner.M2R)
    ∧ P * InfoGeometry.Canonical.SplitCliffordSourceWickBase.a
        + InfoGeometry.Canonical.SplitCliffordSourceWickBase.a * P = 0
    ∧ P * InfoGeometry.Canonical.SplitCliffordSourceWickBase.aDag
        + InfoGeometry.Canonical.SplitCliffordSourceWickBase.aDag * P = 0
    ∧ TwoMode.a1 * TwoMode.a2 + TwoMode.a2 * TwoMode.a1 = 0
    ∧ TwoMode.a1 * TwoMode.a2Dag + TwoMode.a2Dag * TwoMode.a1 = 0
    ∧ TwoMode.a1Dag * TwoMode.a2 + TwoMode.a2 * TwoMode.a1Dag = 0
    ∧ TwoMode.a1Dag * TwoMode.a2Dag + TwoMode.a2Dag * TwoMode.a1Dag = 0) ∧
  (∀ (n : ℕ)
      (D X : InfoGeometry.Canonical.SplitCliffordTensorBridge.SplitClNNAlg n),
    D * X + X * D = 0 →
      DAG.GradedBottInclusion.bottInclusionEven D *
          DAG.GradedBottInclusion.bottInclusionOdd X
        + DAG.GradedBottInclusion.bottInclusionOdd X *
          DAG.GradedBottInclusion.bottInclusionEven D = 0) ∧
  (∀ chain₁ chain₂ : List (KitaevCell.{u}),
    macroscopicVolume (chain₁ ++ chain₂) =
      macroscopicVolume chain₁ * macroscopicVolume chain₂) ∧
  (∀ chain₁ chain₂ : List (KitaevCell.{u}),
    macroscopicVolume chain₁ ≠ 0 →
      macroscopicVolume chain₂ ≠ 0 →
        topologicalIndexZ2 (chain₁ ++ chain₂) =
          topologicalIndexZ2 chain₁ + topologicalIndexZ2 chain₂) ∧
  (∀ (S : Type v) [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
      (M : RealMajoranaDatum (S := S))
      (P0 : KPolarization (S := S) M)
      (localOp : KitaevCell.{u} → S →L[ℝ] S)
      (chain : List (KitaevCell.{u})),
    topologicalIndexZ2 chain = 1 →
      SimplifiedBoundaryModel (M := M) (P0 := P0) localOp chain →
        HasZeroMode (S := S)
          (globalChainOperatorFromOpenChain (S := S) localOp chain)) ∧
  CantorDiracSeaOperatorGeometryOwnerTarget.{u, u, u, u, u} ∧
  (∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      [InfoGeometry.Krein.KreinSpace H]
      (D : InfoGeometry.Dynamics.SouriauDiracHodge.KreinOperatorData H),
    Filter.Tendsto
      (fun beta : ℝ =>
        ‖D.thermalDensityMatrix beta * D.chiralChargeOperator‖)
      Filter.atTop (nhds 0)) ∧
  ((z3RMatrix : Matrix (Fin 2) (Fin 2) ℝ) * z3BMatrix * z3RMatrix =
    z3BMatrix * z3RMatrix * z3BMatrix)

/--
The safe Kitaev/Cuntz/Clifford dictionary is discharged by owner theorems.
-/
theorem kitaev_cuntz_clifford_owner_target :
    KitaevCuntzCliffordOwnerTarget := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro E _ _ _
    exact majorana_car_of_concrete_cl11 E
  · exact
      ⟨parity_sq_eq_one,
        parity_anticommutes_annihilate,
        parity_anticommutes_create,
        TwoMode.jw_cross_annihilate_anticomm,
        TwoMode.jw_cross_annihilate_create_CAR,
        TwoMode.jw_cross_create_annihilate_CAR,
        TwoMode.jw_cross_create_anticomm⟩
  · intro n D X h
    exact DAG.GradedBottInclusion.graded_anticommutation_preserved D X h
  · intro chain₁ chain₂
    exact macroscopicVolume_append chain₁ chain₂
  · intro chain₁ chain₂ h₁ h₂
    exact topologicalIndexZ2_append_of_macroscopicVolume_ne_zero chain₁ chain₂ h₁ h₂
  · intro S _ _ _ M P0 localOp chain hTopo hSimple
    exact hasZeroMode_of_topologicalIndexZ2_eq_one_of_simplifiedBoundaryModel
      (S := S) M P0 localOp chain hTopo hSimple
  · exact cantorDiracSeaOperatorGeometryOwnerTarget
  · intro H _ _ _ _ D
    exact krein_operator_zero_temperature_anomaly_cancellation H D
  · exact z3_artin_relation_via_atoms

/--
Short downstream theorem name: the Kitaev-chain lane is exactly the finite
Majorana/Pfaffian/Z2 and boundary-zero-mode surface already owned by the repo,
and its Cuntz/Clifford/Jordan--Wigner links are the owner theorems bundled
above.
-/
theorem kitaev_chain_realizes_cuntz_clifford_boundary_dictionary :
    KitaevCuntzCliffordOwnerTarget :=
  kitaev_cuntz_clifford_owner_target

end InfoGeometry.Canonical.KitaevCuntzCliffordBridge
