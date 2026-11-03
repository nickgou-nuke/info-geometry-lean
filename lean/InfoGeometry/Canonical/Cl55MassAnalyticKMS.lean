/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.Cl55AllModeMassCoercivity
import InfoGeometry.Canonical.Cl55CARRepresentationCalibration
import InfoGeometry.Canonical.Cl55ChiralAnalyticKMS
import InfoGeometry.Clifford.Cl55WittCalibratedHermitian
import Mathlib.LinearAlgebra.Eigenspace.Matrix

/-!
# The finite CAR mass as a Hamiltonian of the represented analytic KMS state

The five-mode Majorana mass is first proved on its real finite CAR matrix
carrier. The existing coherent complexification maps that same operator into
the complex matrix stage used by the represented finite-seed KMS construction.
This owner proves that the transported operator remains self-adjoint, retains
its exact quadratic mass relation, and constrains every finite spectral value.
The existing `finiteSeedKMSState` construction can be applied directly to this
Hamiltonian; no second KMS-state wrapper is introduced here.
-/

noncomputable section
open scoped ComplexOrder
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 500000
set_option autoImplicit false

namespace InfoGeometry.Canonical.Cl55MassAnalyticKMS

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl55WittCalibratedHermitian
open InfoGeometry.Canonical.Cl11CuntzCoherentIndexTopologicalBridge
open InfoGeometry.Canonical.Cl55AllModeMassCoercivity
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.FiniteSeedRepresentedAnalyticKMS
open InfoGeometry.Canonical.FiniteSeedRepresentedKMS
open InfoGeometry.Canonical.FiniteSeedRepresentedRealTime
open InfoGeometry.Canonical.FiniteMatrixGibbsFunctional
open InfoGeometry.Canonical.AlgebraicKMSStateColimit
open InfoGeometry.Canonical.CantorBernoulliCStarMatrixTraceState
open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredStarAlgebraDirectLimit
open CStarStateColimit.Native.FilteredGNSRepresentedCStarClosure
open CStarStateColimit.Native.FilteredGNSVacuumReadback
open CStarStateColimit.Native.FilteredGNSMatrixAnalyticKMS
open CStarStateColimit.Native.FilteredGNSMatrixRealTime
open CStarStateColimit.Native.FilteredGNSAlgebraicColimitRepresentation
open CStarStateColimit.Native.FilteredGNSGlobalStageRepresentation

private abbrev matrixStageCStarFamily : ∀ n, CStarAlgebra (CStarMatrixStage n) :=
  fun n => (inferInstance : CStarAlgebra (CStarMatrixStage n))
private abbrev matrixStageOrderFamily : ∀ n, PartialOrder (CStarMatrixStage n) :=
  fun n => (inferInstance : PartialOrder (CStarMatrixStage n))
private abbrev matrixStageStarOrderFamily : ∀ n, StarOrderedRing (CStarMatrixStage n) :=
  fun n => (inferInstance : StarOrderedRing (CStarMatrixStage n))
attribute [local instance] matrixStageCStarFamily matrixStageOrderFamily matrixStageStarOrderFamily

/-- The five-mode Majorana interaction, transported from the real CAR stage
to the complex finite matrix stage used by the KMS construction. -/
def massHamiltonian : MatrixStage 5 :=
  coherentComplexifyClStage 5 fiveModeMajorana

/-- The three-mode color component of the Majorana mass on the same complex
matrix carrier used by the finite KMS construction. -/
def colorMassHamiltonian : MatrixStage 5 :=
  coherentComplexifyClStage 5 threeColorModeMajorana

/-- The complementary two-mode component of the Majorana mass on the same
complex matrix carrier. -/
def complementaryMassHamiltonian : MatrixStage 5 :=
  coherentComplexifyClStage 5 twoComplementModeMajorana

/-- The Hamiltonian used by the represented finite-seed KMS construction is
the complexification of the native Cl(5,5) Majorana mass after the existing
exterior-Fock to Witt-coordinate algebra equivalence. This records the actual
change of matrix coordinates instead of identifying the two presentations by
notation. -/
theorem massHamiltonian_eq_complexified_native_mass :
    massHamiltonian = coherentComplexifyClStage 5
      (InfoGeometry.Canonical.Cl55CARRepresentationCalibration.exteriorToWittStageEquiv
        (InfoGeometry.Canonical.PeirceTetraktysColimitCoercivity.cl55ToStage5
          nativeFiveModeMajorana)) := by
  rw [InfoGeometry.Canonical.Cl55AllModeMassCoercivity.nativeFiveModeMajorana_calibration]
  rfl

private theorem fiveModeMajorana_isHermitian : fiveModeMajorana.IsHermitian := by
  unfold fiveModeMajorana
  exact (isSelfAdjoint_sum Finset.univ
    (fun i _ => (modeMajorana_unit_horizon i).1)).isHermitian

/-- The complex UHF seed sees the actual self-adjoint finite CAR mass. -/
theorem massHamiltonian_isHermitian : massHamiltonian.IsHermitian := by
  exact coherentComplexify_isHermitian fiveModeMajorana_isHermitian

/-- Complexification preserves the noncommutative quadratic mass relation
`M² = 5·1` exactly on the KMS matrix carrier. -/
theorem massHamiltonian_square :
    massHamiltonian * massHamiltonian = (5 : ℂ) • (1 : MatrixStage 5) := by
  change coherentComplexifyClStage 5 fiveModeMajorana *
      coherentComplexifyClStage 5 fiveModeMajorana =
    (5 : ℂ) • (1 : CoherentComplexStage 5)
  calc
    coherentComplexifyClStage 5 fiveModeMajorana *
        coherentComplexifyClStage 5 fiveModeMajorana =
        coherentComplexifyClStage 5 (fiveModeMajorana * fiveModeMajorana) :=
          (map_mul (coherentComplexifyClStage 5) _ _).symm
    _ = coherentComplexifyClStage 5 ((5 : ℝ) • 1) :=
          congrArg (coherentComplexifyClStage 5) fiveModeMajorana_square
    _ = (5 : ℂ) • 1 := by
          rw [map_smul]
          ext i j
          simp

/-- The color and complementary finite KMS Hamiltonians are Hermitian. -/
theorem color_and_complement_massHamiltonians_isHermitian :
    colorMassHamiltonian.IsHermitian ∧
    complementaryMassHamiltonian.IsHermitian := by
  constructor
  · unfold colorMassHamiltonian threeColorModeMajorana
    exact coherentComplexify_isHermitian
      ((isSelfAdjoint_sum (Finset.univ : Finset (Fin 3))
        (fun i _ => (modeMajorana_unit_horizon (Fin.castAdd 2 i)).1)).isHermitian)
  · unfold complementaryMassHamiltonian twoComplementModeMajorana
    exact coherentComplexify_isHermitian
      ((isSelfAdjoint_sum (Finset.univ : Finset (Fin 2))
        (fun i _ => (modeMajorana_unit_horizon (Fin.natAdd 3 i)).1)).isHermitian)

/-- Complexification preserves the color and complementary quadratic mass
weights on the finite KMS matrix carrier. -/
theorem color_and_complement_massHamiltonians_square :
    colorMassHamiltonian * colorMassHamiltonian =
        (3 : ℂ) • (1 : MatrixStage 5) ∧
    complementaryMassHamiltonian * complementaryMassHamiltonian =
        (2 : ℂ) • (1 : MatrixStage 5) := by
  constructor
  · change coherentComplexifyClStage 5 threeColorModeMajorana *
      coherentComplexifyClStage 5 threeColorModeMajorana = (3 : ℂ) • 1
    calc
      coherentComplexifyClStage 5 threeColorModeMajorana *
          coherentComplexifyClStage 5 threeColorModeMajorana =
          coherentComplexifyClStage 5
            (threeColorModeMajorana * threeColorModeMajorana) :=
          (map_mul (coherentComplexifyClStage 5) _ _).symm
      _ = coherentComplexifyClStage 5 ((3 : ℝ) • 1) :=
          congrArg (coherentComplexifyClStage 5) threeColorModeMajorana_square
      _ = (3 : ℂ) • 1 := by
          rw [map_smul]
          ext i j
          simp
  · change coherentComplexifyClStage 5 twoComplementModeMajorana *
      coherentComplexifyClStage 5 twoComplementModeMajorana = (2 : ℂ) • 1
    calc
      coherentComplexifyClStage 5 twoComplementModeMajorana *
          coherentComplexifyClStage 5 twoComplementModeMajorana =
          coherentComplexifyClStage 5
            (twoComplementModeMajorana * twoComplementModeMajorana) :=
          (map_mul (coherentComplexifyClStage 5) _ _).symm
      _ = coherentComplexifyClStage 5 ((2 : ℝ) • 1) :=
          congrArg (coherentComplexifyClStage 5) twoComplementModeMajorana_square
      _ = (2 : ℂ) • 1 := by
          rw [map_smul]
          ext i j
          simp

/-- The two KMS matrix-sector Hamiltonians have zero mixed
anticommutator. -/
theorem color_complement_massHamiltonians_anticommute :
    colorMassHamiltonian * complementaryMassHamiltonian +
      complementaryMassHamiltonian * colorMassHamiltonian = 0 := by
  change coherentComplexifyClStage 5 threeColorModeMajorana *
      coherentComplexifyClStage 5 twoComplementModeMajorana +
    coherentComplexifyClStage 5 twoComplementModeMajorana *
      coherentComplexifyClStage 5 threeColorModeMajorana = 0
  have h := congrArg (coherentComplexifyClStage 5)
    threeColor_twoComplement_mass_anticommute
  simpa only [map_add, map_mul, map_zero] using h

/-- The normalized finite Gibbs functional for the full mass reads the
color, complementary, and total quadratic mass observables as `3`, `2`, and
`5`. Thus the finite KMS state retains the sector-resolved mass sum. -/
theorem massGibbs_sector_second_moments (β : ℝ) :
    gibbsFunctional massHamiltonian massHamiltonian_isHermitian β
        (colorMassHamiltonian * colorMassHamiltonian) = 3 ∧
    gibbsFunctional massHamiltonian massHamiltonian_isHermitian β
        (complementaryMassHamiltonian * complementaryMassHamiltonian) = 2 ∧
    gibbsFunctional massHamiltonian massHamiltonian_isHermitian β
        (massHamiltonian * massHamiltonian) = 5 := by
  constructor
  · rw [color_and_complement_massHamiltonians_square.1, map_smul,
      gibbsFunctional_one]
    norm_num
  constructor
  · rw [color_and_complement_massHamiltonians_square.2, map_smul,
      gibbsFunctional_one]
    norm_num
  · rw [massHamiltonian_square, map_smul, gibbsFunctional_one]
    norm_num

/-- The full finite KMS Hamiltonian is the sum of its color and complementary
operator sectors. -/
theorem massHamiltonian_eq_color_add_complement :
    massHamiltonian = colorMassHamiltonian + complementaryMassHamiltonian := by
  change coherentComplexifyClStage 5 fiveModeMajorana =
    coherentComplexifyClStage 5 threeColorModeMajorana +
      coherentComplexifyClStage 5 twoComplementModeMajorana
  simpa only [map_add] using
    congrArg (coherentComplexifyClStage 5)
      fiveModeMajorana_color_two_mode_decomposition

/-- The adjoint action of the full mass sends the color mass into the
complementary sector product. -/
theorem massHamiltonian_color_commutator :
    massHamiltonian * colorMassHamiltonian -
        colorMassHamiltonian * massHamiltonian =
      (2 : ℂ) • (complementaryMassHamiltonian * colorMassHamiltonian) := by
  rw [massHamiltonian_eq_color_add_complement]
  rcases color_complement_massHamiltonians_anticommute with hanti
  have hcross : colorMassHamiltonian * complementaryMassHamiltonian =
      -(complementaryMassHamiltonian * colorMassHamiltonian) :=
    eq_neg_of_add_eq_zero_left hanti
  calc
    (colorMassHamiltonian + complementaryMassHamiltonian) *
        colorMassHamiltonian -
        colorMassHamiltonian * (colorMassHamiltonian + complementaryMassHamiltonian) =
      complementaryMassHamiltonian * colorMassHamiltonian -
        colorMassHamiltonian * complementaryMassHamiltonian := by noncomm_ring
    _ = (2 : ℂ) •
        (complementaryMassHamiltonian * colorMassHamiltonian) := by
      rw [hcross]
      module

/-- The adjoint action of the full mass sends the complementary mass into
the color sector product. -/
theorem massHamiltonian_complement_commutator :
    massHamiltonian * complementaryMassHamiltonian -
        complementaryMassHamiltonian * massHamiltonian =
      (2 : ℂ) • (colorMassHamiltonian * complementaryMassHamiltonian) := by
  rw [massHamiltonian_eq_color_add_complement]
  rcases color_complement_massHamiltonians_anticommute with hanti
  have hcross : complementaryMassHamiltonian * colorMassHamiltonian =
      -(colorMassHamiltonian * complementaryMassHamiltonian) := by
    rw [show colorMassHamiltonian * complementaryMassHamiltonian =
        -(complementaryMassHamiltonian * colorMassHamiltonian) from
      eq_neg_of_add_eq_zero_left hanti]
    simp
  calc
    (colorMassHamiltonian + complementaryMassHamiltonian) *
        complementaryMassHamiltonian -
        complementaryMassHamiltonian * (colorMassHamiltonian + complementaryMassHamiltonian) =
      colorMassHamiltonian * complementaryMassHamiltonian -
        complementaryMassHamiltonian * colorMassHamiltonian := by noncomm_ring
    _ = (2 : ℂ) •
        (colorMassHamiltonian * complementaryMassHamiltonian) := by
      rw [hcross]
      module

/-- In the Gibbs state of the total mass, the ordered mixed color/complement
correlator vanishes by stationarity under the full mass commutator. -/
theorem massGibbs_ordered_mixed_sector_expectation_zero (β : ℝ) :
    gibbsFunctional massHamiltonian massHamiltonian_isHermitian β
      (complementaryMassHamiltonian * colorMassHamiltonian) = 0 := by
  have hstationary := gibbsFunctional_commutator_zero
    massHamiltonian massHamiltonian_isHermitian β colorMassHamiltonian
  rw [massHamiltonian_color_commutator] at hstationary
  have hdouble : (2 : ℂ) *
      gibbsFunctional massHamiltonian massHamiltonian_isHermitian β
        (complementaryMassHamiltonian * colorMassHamiltonian) = 0 := by
    simpa only [map_smul, smul_eq_mul] using hstationary
  rcases mul_eq_zero.mp hdouble with htwo | hmoment
  · norm_num at htwo
  · exact hmoment

/-- Andreev sector cancellation survives the finite matrix GNS construction:
the represented state vanishes on the algebraic-colimit image of the ordered
complementary/color mass product. The proof uses the existing colimit readback,
not an identification of the real CAR carrier with the complex matrix stage. -/
theorem massKMS_algebraic_colimit_mixed_sector_readout_zero (β : ℝ) (v : ℕ) :
    representedVacuumFunctional CStarMatrixStage cstarMatrixInductiveSystem
      (finiteSeedCompatibleStageStates massHamiltonian massHamiltonian_isHermitian β) v
      (algebraicColimitToRepresentedClosure CStarMatrixStage cstarMatrixInductiveSystem
        (finiteSeedCompatibleStageStates massHamiltonian massHamiltonian_isHermitian β)
        (algebraicStarDirectLimitOf CStarMatrixStage cstarMatrixInductiveSystem 5
          ((CStarMatrix.ofMatrixStarAlgEquiv : MatrixStage 5 ≃⋆ₐ[ℂ] CStarMatrixStage 5)
            (complementaryMassHamiltonian * colorMassHamiltonian)))) = 0 := by
  have hread := finiteSeedVacuum_algebraic_readback massHamiltonian
    massHamiltonian_isHermitian β v
    (algebraicStarDirectLimitOf CStarMatrixStage cstarMatrixInductiveSystem 5
      ((CStarMatrix.ofMatrixStarAlgEquiv : MatrixStage 5 ≃⋆ₐ[ℂ] CStarMatrixStage 5)
        (complementaryMassHamiltonian * colorMassHamiltonian)))
  have hcolim : cstarColimitToMatrixColimit
      (algebraicStarDirectLimitOf CStarMatrixStage cstarMatrixInductiveSystem 5
        ((CStarMatrix.ofMatrixStarAlgEquiv : MatrixStage 5 ≃⋆ₐ[ℂ] CStarMatrixStage 5)
          (complementaryMassHamiltonian * colorMassHamiltonian))) =
      stageInjection 5 (complementaryMassHamiltonian * colorMassHamiltonian) := by
    simpa only [StarAlgEquiv.symm_apply_apply] using
      (cstarColimitToMatrixColimit_stage 5
        ((CStarMatrix.ofMatrixStarAlgEquiv : MatrixStage 5 ≃⋆ₐ[ℂ] CStarMatrixStage 5)
          (complementaryMassHamiltonian * colorMassHamiltonian)))
  have hread' := hread.trans (congrArg
    (normalizedDeltaWeightedFunctional
      (stageUnitToColimit 5
        (gibbsDensityUnit massHamiltonian massHamiltonian_isHermitian β))) hcolim)
  have hstage := normalizedDeltaWeightedFunctional_stage_eq_gibbsFunctional
    massHamiltonian massHamiltonian_isHermitian β
    (complementaryMassHamiltonian * colorMassHamiltonian)
  exact hread'.trans (hstage.trans (massGibbs_ordered_mixed_sector_expectation_zero β))

/-- The represented algebraic-colimit KMS state reads the color, complementary,
and total mass-square observables as `3`, `2`, and `5`.  This transports the
finite CAR sector decomposition through the actual finite-seed GNS readback;
it does not infer these moments from spectral coordinates. -/
private theorem massKMS_color_square_readout (β : ℝ) (v : ℕ) :
    representedVacuumFunctional CStarMatrixStage cstarMatrixInductiveSystem
      (finiteSeedCompatibleStageStates massHamiltonian massHamiltonian_isHermitian β) v
      (algebraicColimitToRepresentedClosure CStarMatrixStage cstarMatrixInductiveSystem
        (finiteSeedCompatibleStageStates massHamiltonian massHamiltonian_isHermitian β)
        (algebraicStarDirectLimitOf CStarMatrixStage cstarMatrixInductiveSystem 5
          ((CStarMatrix.ofMatrixStarAlgEquiv : MatrixStage 5 ≃⋆ₐ[ℂ] CStarMatrixStage 5)
            (colorMassHamiltonian * colorMassHamiltonian)))) = 3 := by
  have hread := finiteSeedVacuum_algebraic_readback massHamiltonian
    massHamiltonian_isHermitian β v
    (algebraicStarDirectLimitOf CStarMatrixStage cstarMatrixInductiveSystem 5
      ((CStarMatrix.ofMatrixStarAlgEquiv : MatrixStage 5 ≃⋆ₐ[ℂ] CStarMatrixStage 5)
        (colorMassHamiltonian * colorMassHamiltonian)))
  have hcolim : cstarColimitToMatrixColimit
      (algebraicStarDirectLimitOf CStarMatrixStage cstarMatrixInductiveSystem 5
        ((CStarMatrix.ofMatrixStarAlgEquiv : MatrixStage 5 ≃⋆ₐ[ℂ] CStarMatrixStage 5)
          (colorMassHamiltonian * colorMassHamiltonian))) =
      stageInjection 5 (colorMassHamiltonian * colorMassHamiltonian) := by
    simpa only [StarAlgEquiv.symm_apply_apply] using
      (cstarColimitToMatrixColimit_stage 5
        ((CStarMatrix.ofMatrixStarAlgEquiv : MatrixStage 5 ≃⋆ₐ[ℂ] CStarMatrixStage 5)
          (colorMassHamiltonian * colorMassHamiltonian)))
  have hread' := hread.trans (congrArg
    (normalizedDeltaWeightedFunctional
      (stageUnitToColimit 5
        (gibbsDensityUnit massHamiltonian massHamiltonian_isHermitian β))) hcolim)
  have hstage := normalizedDeltaWeightedFunctional_stage_eq_gibbsFunctional
    massHamiltonian massHamiltonian_isHermitian β
    (colorMassHamiltonian * colorMassHamiltonian)
  exact (hread'.trans hstage).trans
    (massGibbs_sector_second_moments β).1

private theorem massKMS_complement_square_readout (β : ℝ) (v : ℕ) :
    representedVacuumFunctional CStarMatrixStage cstarMatrixInductiveSystem
      (finiteSeedCompatibleStageStates massHamiltonian massHamiltonian_isHermitian β) v
      (algebraicColimitToRepresentedClosure CStarMatrixStage cstarMatrixInductiveSystem
        (finiteSeedCompatibleStageStates massHamiltonian massHamiltonian_isHermitian β)
        (algebraicStarDirectLimitOf CStarMatrixStage cstarMatrixInductiveSystem 5
          ((CStarMatrix.ofMatrixStarAlgEquiv : MatrixStage 5 ≃⋆ₐ[ℂ] CStarMatrixStage 5)
            (complementaryMassHamiltonian * complementaryMassHamiltonian)))) = 2 := by
  have hread := finiteSeedVacuum_algebraic_readback massHamiltonian
    massHamiltonian_isHermitian β v
    (algebraicStarDirectLimitOf CStarMatrixStage cstarMatrixInductiveSystem 5
      ((CStarMatrix.ofMatrixStarAlgEquiv : MatrixStage 5 ≃⋆ₐ[ℂ] CStarMatrixStage 5)
        (complementaryMassHamiltonian * complementaryMassHamiltonian)))
  have hcolim : cstarColimitToMatrixColimit
      (algebraicStarDirectLimitOf CStarMatrixStage cstarMatrixInductiveSystem 5
        ((CStarMatrix.ofMatrixStarAlgEquiv : MatrixStage 5 ≃⋆ₐ[ℂ] CStarMatrixStage 5)
          (complementaryMassHamiltonian * complementaryMassHamiltonian))) =
      stageInjection 5 (complementaryMassHamiltonian * complementaryMassHamiltonian) := by
    simpa only [StarAlgEquiv.symm_apply_apply] using
      (cstarColimitToMatrixColimit_stage 5
        ((CStarMatrix.ofMatrixStarAlgEquiv : MatrixStage 5 ≃⋆ₐ[ℂ] CStarMatrixStage 5)
          (complementaryMassHamiltonian * complementaryMassHamiltonian)))
  have hread' := hread.trans (congrArg
    (normalizedDeltaWeightedFunctional
      (stageUnitToColimit 5
        (gibbsDensityUnit massHamiltonian massHamiltonian_isHermitian β))) hcolim)
  have hstage := normalizedDeltaWeightedFunctional_stage_eq_gibbsFunctional
    massHamiltonian massHamiltonian_isHermitian β
    (complementaryMassHamiltonian * complementaryMassHamiltonian)
  exact (hread'.trans hstage).trans
    (massGibbs_sector_second_moments β).2.1

private theorem massKMS_total_square_readout (β : ℝ) (v : ℕ) :
    representedVacuumFunctional CStarMatrixStage cstarMatrixInductiveSystem
      (finiteSeedCompatibleStageStates massHamiltonian massHamiltonian_isHermitian β) v
      (algebraicColimitToRepresentedClosure CStarMatrixStage cstarMatrixInductiveSystem
        (finiteSeedCompatibleStageStates massHamiltonian massHamiltonian_isHermitian β)
        (algebraicStarDirectLimitOf CStarMatrixStage cstarMatrixInductiveSystem 5
          ((CStarMatrix.ofMatrixStarAlgEquiv : MatrixStage 5 ≃⋆ₐ[ℂ] CStarMatrixStage 5)
            (massHamiltonian * massHamiltonian)))) = 5 := by
  have hread := finiteSeedVacuum_algebraic_readback massHamiltonian
    massHamiltonian_isHermitian β v
    (algebraicStarDirectLimitOf CStarMatrixStage cstarMatrixInductiveSystem 5
      ((CStarMatrix.ofMatrixStarAlgEquiv : MatrixStage 5 ≃⋆ₐ[ℂ] CStarMatrixStage 5)
        (massHamiltonian * massHamiltonian)))
  have hcolim : cstarColimitToMatrixColimit
      (algebraicStarDirectLimitOf CStarMatrixStage cstarMatrixInductiveSystem 5
        ((CStarMatrix.ofMatrixStarAlgEquiv : MatrixStage 5 ≃⋆ₐ[ℂ] CStarMatrixStage 5)
          (massHamiltonian * massHamiltonian))) =
      stageInjection 5 (massHamiltonian * massHamiltonian) := by
    simpa only [StarAlgEquiv.symm_apply_apply] using
      (cstarColimitToMatrixColimit_stage 5
        ((CStarMatrix.ofMatrixStarAlgEquiv : MatrixStage 5 ≃⋆ₐ[ℂ] CStarMatrixStage 5)
          (massHamiltonian * massHamiltonian)))
  have hread' := hread.trans (congrArg
    (normalizedDeltaWeightedFunctional
      (stageUnitToColimit 5
        (gibbsDensityUnit massHamiltonian massHamiltonian_isHermitian β))) hcolim)
  have hstage := normalizedDeltaWeightedFunctional_stage_eq_gibbsFunctional
    massHamiltonian massHamiltonian_isHermitian β
    (massHamiltonian * massHamiltonian)
  exact (hread'.trans hstage).trans
    (massGibbs_sector_second_moments β).2.2

theorem massKMS_algebraic_colimit_second_moments (β : ℝ) (v : ℕ) :
    representedVacuumFunctional CStarMatrixStage cstarMatrixInductiveSystem
      (finiteSeedCompatibleStageStates massHamiltonian massHamiltonian_isHermitian β) v
      (algebraicColimitToRepresentedClosure CStarMatrixStage cstarMatrixInductiveSystem
        (finiteSeedCompatibleStageStates massHamiltonian massHamiltonian_isHermitian β)
        (algebraicStarDirectLimitOf CStarMatrixStage cstarMatrixInductiveSystem 5
          ((CStarMatrix.ofMatrixStarAlgEquiv : MatrixStage 5 ≃⋆ₐ[ℂ] CStarMatrixStage 5)
            (colorMassHamiltonian * colorMassHamiltonian)))) = 3 ∧
    representedVacuumFunctional CStarMatrixStage cstarMatrixInductiveSystem
      (finiteSeedCompatibleStageStates massHamiltonian massHamiltonian_isHermitian β) v
      (algebraicColimitToRepresentedClosure CStarMatrixStage cstarMatrixInductiveSystem
        (finiteSeedCompatibleStageStates massHamiltonian massHamiltonian_isHermitian β)
        (algebraicStarDirectLimitOf CStarMatrixStage cstarMatrixInductiveSystem 5
          ((CStarMatrix.ofMatrixStarAlgEquiv : MatrixStage 5 ≃⋆ₐ[ℂ] CStarMatrixStage 5)
            (complementaryMassHamiltonian * complementaryMassHamiltonian)))) = 2 ∧
    representedVacuumFunctional CStarMatrixStage cstarMatrixInductiveSystem
      (finiteSeedCompatibleStageStates massHamiltonian massHamiltonian_isHermitian β) v
      (algebraicColimitToRepresentedClosure CStarMatrixStage cstarMatrixInductiveSystem
        (finiteSeedCompatibleStageStates massHamiltonian massHamiltonian_isHermitian β)
        (algebraicStarDirectLimitOf CStarMatrixStage cstarMatrixInductiveSystem 5
          ((CStarMatrix.ofMatrixStarAlgEquiv : MatrixStage 5 ≃⋆ₐ[ℂ] CStarMatrixStage 5)
            (massHamiltonian * massHamiltonian)))) = 5 := by
  exact ⟨massKMS_color_square_readout β v,
    massKMS_complement_square_readout β v,
    massKMS_total_square_readout β v⟩

/-- A finite-dimensional matrix spectrum inherits the quadratic polynomial
of its operator, without a diagonalization assumption. -/
theorem spectrum_square_of_scalar_square {T : MatrixStage 5} {r : ℂ}
    (hT : T * T = r • (1 : MatrixStage 5)) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ T) : μ ^ 2 = r := by
  rw [← Matrix.spectrum_toLin'] at hμ
  rw [← Module.End.hasEigenvalue_iff_mem_spectrum] at hμ
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hEigen : Matrix.toLin' T v = μ • v := hv.apply_eq_smul
  have hSquareEigen : Matrix.toLin' (T * T) v = (μ ^ 2 : ℂ) • v := by
    calc
      Matrix.toLin' (T * T) v =
          Matrix.toLin' T (Matrix.toLin' T v) := Matrix.toLin'_mul_apply _ _ _
      _ = Matrix.toLin' T (μ • v) := by rw [hEigen]
      _ = μ • Matrix.toLin' T v := map_smul _ _ _
      _ = μ • (μ • v) := by rw [hEigen]
      _ = (μ ^ 2 : ℂ) • v := by rw [smul_smul, pow_two]
  rw [hT] at hSquareEigen
  have hScalar : (μ ^ 2 : ℂ) • v = r • v := by
    simpa using hSquareEigen.symm
  obtain ⟨i, hi⟩ : ∃ i : Fin 32, v i ≠ 0 := by
    by_contra h
    have hz : ∀ i : Fin 32, v i = 0 := by simpa using h
    exact hv.2 (funext hz)
  have hcoord := congrArg (fun w : Fin 32 → ℂ => w i) hScalar
  have hmul : μ ^ 2 * v i = r * v i := by
    simpa only [Pi.smul_apply, smul_eq_mul] using hcoord
  exact (mul_right_cancel₀ hi) hmul

/-- The color-sector KMS spectrum is constrained by the exact polynomial
`μ² = 3`. -/
theorem colorMassHamiltonian_spectrum_square {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ colorMassHamiltonian) : μ ^ 2 = 3 := by
  exact spectrum_square_of_scalar_square
    color_and_complement_massHamiltonians_square.1 hμ

/-- The complementary-sector KMS spectrum is constrained by the exact
polynomial `μ² = 2`. -/
theorem complementaryMassHamiltonian_spectrum_square {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ complementaryMassHamiltonian) : μ ^ 2 = 2 := by
  exact spectrum_square_of_scalar_square
    color_and_complement_massHamiltonians_square.2 hμ

/-- Every spectral value of the finite mass Hamiltonian satisfies its exact
quadratic mass polynomial. This is the finite-dimensional spectral statement
seen by the represented KMS dynamics. -/
theorem massHamiltonian_spectrum_square {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ massHamiltonian) : μ ^ 2 = 5 := by
  exact spectrum_square_of_scalar_square massHamiltonian_square hμ

end InfoGeometry.Canonical.Cl55MassAnalyticKMS
