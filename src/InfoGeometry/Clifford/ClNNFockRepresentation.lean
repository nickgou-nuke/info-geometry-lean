import Mathlib.Algebra.Algebra.Equiv
import InfoGeometry.Clifford.FockSpaceCAR

/-!
# The recursive `Cl(n,n)` action on the primal-sheet exterior Fock space

The recursive split Clifford algebra already acts on the Chevalley spinor
module. This owner transports that native representation to the exterior
algebra of the actual primal sheet, using Mathlib's functorial exterior
algebra map and the proved primal-sheet parametrization.
-/

noncomputable section

namespace InfoGeometry.Clifford.ClNNFockRepresentation

open InfoGeometry.Clifford.ClNNNeutralChevalleyBridge
open InfoGeometry.Clifford.ClNNToDoubledKreinTransport
open InfoGeometry.Clifford.FockSpaceCAR
open InfoGeometry.Clifford.NeutralPhaseSpaceDoubledBridge
open InfoGeometry.Krein

variable (n : ℕ)

/-- The algebra homomorphism induced by the native parametrization of the
primal sheet. -/
def exteriorModeMap :
    ExteriorAlgebra ℝ (Vector n) →ₐ[ℝ]
      ExteriorAlgebra ℝ (PrimalSheet n) :=
  ExteriorAlgebra.map (neutralPrimalSheetParametrization n).toLinearMap

/-- The exterior map induced by a linear equivalence is bijective. -/
theorem exteriorModeMap_bijective :
    Function.Bijective (exteriorModeMap n) := by
  constructor
  · change Function.Injective
      (ExteriorAlgebra.map (neutralPrimalSheetParametrization n).toLinearMap)
    apply ExteriorAlgebra.map_injective
    refine ⟨(neutralPrimalSheetParametrization n).symm.toLinearMap, ?_⟩
    ext x
    simp
  · change Function.Surjective
      (ExteriorAlgebra.map (neutralPrimalSheetParametrization n).toLinearMap)
    exact ExteriorAlgebra.map_surjective_iff.mpr
      (neutralPrimalSheetParametrization n).surjective

/-- Algebra equivalence between the coordinate exterior algebra and the
exterior algebra of the actual primal sheet. -/
def exteriorModeEquiv :
    ExteriorAlgebra ℝ (Vector n) ≃ₐ[ℝ]
      ExteriorAlgebra ℝ (PrimalSheet n) :=
  AlgEquiv.ofBijective (exteriorModeMap n) (exteriorModeMap_bijective n)

@[simp] theorem exteriorModeEquiv_apply_ι (u : Vector n) :
    exteriorModeEquiv n (ExteriorAlgebra.ι ℝ u) =
      ExteriorAlgebra.ι ℝ (neutralPrimalSheetParametrization n u) := by
  simp [exteriorModeEquiv, exteriorModeMap]

/-- The exterior mode equivalence intertwines Mathlib's left contraction
when covectors are transported by the dual equivalence. -/
theorem exteriorModeEquiv_contractLeft
    (φ : Module.Dual ℝ (Vector n))
    (a : InfoGeometry.Clifford.SpinorSpace (Vector n)) :
    exteriorModeEquiv n (CliffordAlgebra.contractLeft φ a) =
      CliffordAlgebra.contractLeft
        ((neutralPrimalSheetParametrization n).dualMap.symm φ)
        (exteriorModeEquiv n a) := by
  induction a using CliffordAlgebra.left_induction with
  | algebraMap r => simp [exteriorModeEquiv, exteriorModeMap]
  | add a b ha hb => simp [ha, hb]
  | ι_mul m a ha =>
      simp only [CliffordAlgebra.contractLeft_ι_mul, map_sub, map_smul,
        map_mul, exteriorModeEquiv_apply_ι, ha,
        CliffordAlgebra.contractLeft_ι_mul]
      congr 1
      have hdual := congrArg (fun ψ : Module.Dual ℝ (Vector n) => ψ a)
        ((neutralPrimalSheetParametrization n).dualMap.apply_symm_apply φ)
      have hpair : φ a =
          ((neutralPrimalSheetParametrization n).dualMap.symm φ)
            ((neutralPrimalSheetParametrization n) a) := by
        simpa only [LinearEquiv.dualMap_apply] using hdual.symm
      exact congrArg (fun c : ℝ => c • exteriorModeEquiv n m) hpair

/-- The existing recursive Chevalley spinor carrier is linearly equivalent
to the Fock space built directly on the native primal sheet. -/
def towerSpinorToFock :
    InfoGeometry.Clifford.SpinorSpace (Vector n) ≃ₗ[ℝ]
      FockSpace (PrimalSheet n) :=
  (exteriorModeEquiv n).toLinearEquiv

/-- Transporting exterior multiplication through the actual primal-sheet
mode equivalence gives the named Fock creation operator. -/
theorem towerSpinorToFock_extAction
    (u : Vector n) (w : InfoGeometry.Clifford.SpinorSpace (Vector n)) :
    towerSpinorToFock n (InfoGeometry.Clifford.extAction u w) =
      sheetCreation n (neutralPrimalSheetParametrization n u)
        (towerSpinorToFock n w) := by
  change exteriorModeEquiv n (extAction u w) =
    creation (neutralPrimalSheetParametrization n u)
      (exteriorModeEquiv n w)
  rw [creation_apply_ι_mul]
  change exteriorModeEquiv n
      (CliffordAlgebra.ι (0 : QuadraticForm ℝ (Vector n)) u * w) =
    ExteriorAlgebra.ι ℝ (neutralPrimalSheetParametrization n u) *
      exteriorModeEquiv n w
  calc
    _ = exteriorModeEquiv n (CliffordAlgebra.ι (0 : QuadraticForm ℝ (Vector n)) u) *
          exteriorModeEquiv n w := (exteriorModeEquiv n).map_mul _ _
    _ = _ := by simp

/-- Transporting contraction through the primal-sheet mode equivalence gives
the named Fock annihilation operator with its dual mode. -/
theorem towerSpinorToFock_intAction
    (φ : Module.Dual ℝ (Vector n))
    (w : InfoGeometry.Clifford.SpinorSpace (Vector n)) :
    towerSpinorToFock n (InfoGeometry.Clifford.intAction φ w) =
      sheetAnnihilation n (neutralVacuumSheetParametrization n φ)
        (towerSpinorToFock n w) := by
  have hdual :
      neutralVacuumSheetDualEquiv n
          (neutralVacuumSheetParametrization n φ) =
        (neutralPrimalSheetParametrization n).dualMap.symm φ := by
    simp [neutralVacuumSheetDualEquiv]
  simpa only [towerSpinorToFock, AlgEquiv.toLinearEquiv_apply,
    sheetAnnihilation, annihilation_apply_contractLeft, intAction, hdual] using
      exteriorModeEquiv_contractLeft n φ w

/-- The recursive `Cl(n,n)` Clifford algebra represented on the exterior
Fock space of its native primal sheet. This is the existing tower spinor
representation conjugated by the explicit carrier equivalence above. -/
def towerFockRep :
    CliffordAlgebra (TowerForm n) →ₐ[ℝ]
      Module.End ℝ (FockSpace (PrimalSheet n)) :=
  ((towerSpinorToFock n).conjAlgEquiv ℝ).toAlgHom.comp
    (towerSpinorRep n)

/-- Pointwise transport law for the represented action on Fock states. -/
theorem towerFockRep_apply
    (A : CliffordAlgebra (TowerForm n)) (ψ : FockSpace (PrimalSheet n)) :
    towerFockRep n A ψ =
      towerSpinorToFock n
        (towerSpinorRep n A ((towerSpinorToFock n).symm ψ)) := by
  simp [towerFockRep, LinearEquiv.conjAlgEquiv_apply,
    LinearMap.comp_apply]

/-- On each Clifford vector generator, the Fock action is the transported
Chevalley creation-plus-contraction action in the neutral split coordinates. -/
theorem towerFockRep_generator
    (x : TowerSpace n) (ψ : FockSpace (PrimalSheet n)) :
    towerFockRep n (CliffordAlgebra.ι (TowerForm n) x) ψ =
      towerSpinorToFock n
        (InfoGeometry.Clifford.spinorAction
          ((neutralToSplit n).symm x)
          ((towerSpinorToFock n).symm ψ)) := by
  rw [towerFockRep_apply, towerSpinorRep_generator]

/-- In the native neutral coordinates, each recursive Clifford generator acts
on the primal-sheet Fock space as creation plus annihilation. -/
theorem towerFockRep_neutral_generator
    (X : Neutral n) (ψ : FockSpace (PrimalSheet n)) :
    towerFockRep n (CliffordAlgebra.ι (TowerForm n) (neutralToSplit n X)) ψ =
      sheetCreation n (neutralPrimalSheetParametrization n X.1) ψ +
        sheetAnnihilation n (neutralVacuumSheetParametrization n X.2) ψ := by
  rw [towerFockRep_generator]
  rw [(neutralToSplit n).symm_apply_apply]
  rw [InfoGeometry.Clifford.spinorAction, LinearMap.add_apply]
  rw [(towerSpinorToFock n).map_add]
  rw [towerSpinorToFock_extAction, towerSpinorToFock_intAction]
  simp

/-- The represented neutral Clifford generator squares to the recursive
quadratic form on every primal-sheet Fock state. -/
theorem towerFockRep_neutral_generator_sq
    (X : Neutral n) (ψ : FockSpace (PrimalSheet n)) :
    towerFockRep n (CliffordAlgebra.ι (TowerForm n) (neutralToSplit n X))
        (towerFockRep n (CliffordAlgebra.ι (TowerForm n) (neutralToSplit n X)) ψ) =
      TowerForm n (neutralToSplit n X) • ψ := by
  simp only [towerFockRep_neutral_generator]
  change
    creation (neutralPrimalSheetParametrization n X.1)
        (creation (neutralPrimalSheetParametrization n X.1) ψ +
          annihilation
            (neutralVacuumSheetDualEquiv n
              (neutralVacuumSheetParametrization n X.2)) ψ) +
      annihilation
        (neutralVacuumSheetDualEquiv n
          (neutralVacuumSheetParametrization n X.2))
        (creation (neutralPrimalSheetParametrization n X.1) ψ +
          annihilation
            (neutralVacuumSheetDualEquiv n
              (neutralVacuumSheetParametrization n X.2)) ψ) =
      TowerForm n (neutralToSplit n X) • ψ
  rw [creation_annihilation_sum_sq]
  have hscalar :
      neutralVacuumSheetDualEquiv n
          (neutralVacuumSheetParametrization n X.2)
          (neutralPrimalSheetParametrization n X.1) =
        TowerForm n (neutralToSplit n X) := by
    rw [neutralVacuumSheetDualEquiv_apply]
    rw [Qsplit_neutralToSplit n X]
    rcases X with ⟨u, φ⟩
    simp [InfoGeometry.Clifford.NeutralPhaseSpaceCore.canonicalNeutralFormUnscaled_apply]
  rw [hscalar]

/-- The anticommutator of two represented neutral Clifford generators is the
polarization of the tower quadratic form. This is the two-generator CAR
normalization on the actual primal-sheet Fock carrier. -/
theorem towerFockRep_neutral_generator_anticommutator
    (X Y : Neutral n) (ψ : FockSpace (PrimalSheet n)) :
    towerFockRep n
        (CliffordAlgebra.ι (TowerForm n) (neutralToSplit n X))
        (towerFockRep n
          (CliffordAlgebra.ι (TowerForm n) (neutralToSplit n Y)) ψ) +
      towerFockRep n
        (CliffordAlgebra.ι (TowerForm n) (neutralToSplit n Y))
        (towerFockRep n
          (CliffordAlgebra.ι (TowerForm n) (neutralToSplit n X)) ψ) =
      QuadraticMap.polar (TowerForm n)
        (neutralToSplit n X) (neutralToSplit n Y) • ψ := by
  have hcl := CliffordAlgebra.ι_mul_ι_add_swap
    (Q := TowerForm n) (neutralToSplit n X) (neutralToSplit n Y)
  have hrep := congrArg (towerFockRep n) hcl
  have hpoint := congrArg (fun T : Module.End ℝ (FockSpace (PrimalSheet n)) => T ψ) hrep
  simpa using hpoint

/-- In neutral coordinates, the represented Clifford anticommutator is the
canonical symmetric primal/covector pairing. This is the finite-stage CAR
readout on the native primal-sheet Fock space. -/
theorem towerFockRep_neutral_generator_CAR
    (X Y : Neutral n) (ψ : FockSpace (PrimalSheet n)) :
    towerFockRep n
        (CliffordAlgebra.ι (TowerForm n) (neutralToSplit n X))
        (towerFockRep n
          (CliffordAlgebra.ι (TowerForm n) (neutralToSplit n Y)) ψ) +
      towerFockRep n
        (CliffordAlgebra.ι (TowerForm n) (neutralToSplit n Y))
        (towerFockRep n
          (CliffordAlgebra.ι (TowerForm n) (neutralToSplit n X)) ψ) =
      InfoGeometry.Clifford.NeutralPhaseSpaceCore.canonicalNeutralBilin
        (E := Vector n) X Y • ψ := by
  rw [towerFockRep_neutral_generator_anticommutator]
  rw [neutralToSplit_polar, chevelleyQsplit_eq_neutralForm,
    InfoGeometry.Clifford.NeutralPhaseSpaceCore.canonicalNeutralFormUnscaled_polar]

/-- The canonically normalized head null directions satisfy the unit CAR in
the Fock representation: their split bilinear pairing is `1/2`, hence the
Clifford polarization and represented anticommutator are `1`. -/
theorem towerFockRep_headNull_CAR
    (n : ℕ) (ψ : FockSpace (PrimalSheet (n + 1))) :
    towerFockRep (n + 1)
        (CliffordAlgebra.ι (TowerForm (n + 1))
          (InfoGeometry.Clifford.ClNN.headNullMinus n))
        (towerFockRep (n + 1)
          (CliffordAlgebra.ι (TowerForm (n + 1))
            (InfoGeometry.Clifford.ClNN.headNullPlus n)) ψ) +
      towerFockRep (n + 1)
        (CliffordAlgebra.ι (TowerForm (n + 1))
          (InfoGeometry.Clifford.ClNN.headNullPlus n))
        (towerFockRep (n + 1)
          (CliffordAlgebra.ι (TowerForm (n + 1))
            (InfoGeometry.Clifford.ClNN.headNullMinus n)) ψ) = ψ := by
  let X : Neutral (n + 1) := (neutralToSplit (n + 1)).symm
    (InfoGeometry.Clifford.ClNN.headNullMinus n)
  let Y : Neutral (n + 1) := (neutralToSplit (n + 1)).symm
    (InfoGeometry.Clifford.ClNN.headNullPlus n)
  have hcar := towerFockRep_neutral_generator_anticommutator
    (n + 1) X Y ψ
  have hpolar : QuadraticMap.polar (TowerForm (n + 1))
      (InfoGeometry.Clifford.ClNN.headNullMinus n)
      (InfoGeometry.Clifford.ClNN.headNullPlus n) = 1 := by
    change QuadraticMap.polar (InfoGeometry.Clifford.ClNN.Quad (n + 1))
        (InfoGeometry.Clifford.ClNN.headNullMinus n)
        (InfoGeometry.Clifford.ClNN.headNullPlus n) = 1
    exact InfoGeometry.Clifford.ClNN.polar_headNullMinus_headNullPlus n
  simpa only [X, Y, LinearEquiv.apply_symm_apply, hpolar, one_smul] using hcar

/-- The represented recursive Clifford generator squares to one half of the
quadratic form on the explicitly realized doubled real Krein carrier. The
factor is the unscaled neutral-form normalization used by `TowerForm`. -/
theorem towerFockRep_neutral_generator_sq_eq_doubledKrein
    (X : Neutral n) (ψ : FockSpace (PrimalSheet n)) :
    towerFockRep n (CliffordAlgebra.ι (TowerForm n) (neutralToSplit n X))
        (towerFockRep n (CliffordAlgebra.ι (TowerForm n) (neutralToSplit n X)) ψ) =
      ((1 / 2 : ℝ) * hessian_indefinite_form
        (realizeToDoubledRho (E := EucVector n) (rieszEquiv n)
          (toEuclideanPhase n X))
        (realizeToDoubledRho (E := EucVector n) (rieszEquiv n)
          (toEuclideanPhase n X))) • ψ := by
  rw [towerFockRep_neutral_generator_sq]
  rw [Qsplit_eq_doubledKrein_form]

end InfoGeometry.Clifford.ClNNFockRepresentation
