import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitOctonion1331ExteriorDiracSouriauBridge
import InfoGeometry.Canonical.SplitOctonionExteriorGradePeirceParityBridge
import InfoGeometry.Clifford.Cl55ZornCARComparison
import InfoGeometry.Clifford.SplitClifford55PureSpinorGrassmannianBridge

/-! The basis-compatible `1+3+3+1` degree projectors and their selected
`Cl(5,5)` vacuum pure-spinor readout.  The Grassmannian in this file is the
repository's genuine five-dimensional maximal-neutral one. -/

noncomputable section
namespace InfoGeometry.Canonical.SplitOctonion1331PureSpinorGradingBridge

open scoped BigOperators LinearAlgebra.Projectivization
open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge
open InfoGeometry.Canonical.SplitOctonion1331ExteriorDiracSouriauBridge
open InfoGeometry.Canonical.SplitOctonionExteriorGradePeirceParityBridge
open InfoGeometry.Clifford.SplitClifford55ZornCARComparison
open InfoGeometry.Clifford.SplitClifford55ExteriorSpinor
open InfoGeometry.Clifford.SplitClifford55ProjectivePureSpinor
open InfoGeometry.Clifford.SplitClifford55PureSpinorGrassmannianBridge

abbrev Exterior3 := SplitOctonionExterior3HodgeDiracBridge.Exterior3
abbrev Coord8 := InfoGeometry.Algebra.FiniteSpin.Vec8R

def degreeCoordinateProjector (k : ℕ) : Coord8 →ₗ[ℝ] Coord8 where
  toFun x i := if exteriorDegree1331 i = k then x i else 0
  map_add' x y := by
    ext i
    by_cases h : exteriorDegree1331 i = k <;> simp [h]
  map_smul' c x := by
    ext i
    by_cases h : exteriorDegree1331 i = k <;> simp [h]

def exteriorDegreeProjector1331 (k : ℕ) : Exterior3 →ₗ[ℝ] Exterior3 :=
  exterior3PeirceBasis.equivFun.symm.toLinearMap.comp
    ((degreeCoordinateProjector k).comp exterior3PeirceBasis.equivFun.toLinearMap)

theorem exteriorDegree1331_packet :
    exteriorDegree1331 0 = 0 ∧
      (∀ i : Fin 3, exteriorDegree1331 ⟨i.1 + 1, by omega⟩ = 1) ∧
      (∀ i : Fin 3, exteriorDegree1331 ⟨i.1 + 5, by omega⟩ = 2) ∧
      exteriorDegree1331 4 = 3 := by
  refine ⟨rfl, ?_, ?_, rfl⟩ <;> intro i <;> fin_cases i <;> rfl

theorem peirceVacuum_eq_exteriorVacuum :
    exterior3PeirceBasis 0 = (1 : Exterior3) := exterior3PeirceBasis_zero

theorem peirceDegreeOne_from_vacuum (i : Fin 3) :
    exteriorWedge3 (Pi.single i 1) (exterior3PeirceBasis 0) =
      exterior3PeirceBasis ⟨i.1 + 1, by omega⟩ := exteriorWedge3_basis_zero i

theorem firstThree_dual_channels_mem_vacuum_annihilator (i : Fin 3) :
    (0, dualBasisVector (firstThreeIndex i)) ∈ neutralAnnihilator (1 : Spinor) :=
  dual_channel_mem_vacuum_neutralAnnihilator i

theorem vacuum_1331_maximalNeutralGrassmannian_readout :
    projectivePureSpinorGrassmannianPoint
        ⟨Projectivization.mk ℝ (1 : Spinor) one_ne_zero,
          projective_vacuum_isPureSpinor⟩ =
      ⟨neutralAnnihilator (1 : Spinor),
        vacuum_neutralAnnihilator_isMaximalNeutralTotallyNull⟩ :=
  vacuum_projectivePureSpinorGrassmannianPoint

theorem peirce_exterior_pureSpinor_corridor (i : Fin 3) :
    exteriorDegree1331 0 = 0 ∧
    exteriorDegree1331 ⟨i.1 + 1, by omega⟩ = 1 ∧
    exteriorWedge3 (Pi.single i 1) (exterior3PeirceBasis 0) =
      exterior3PeirceBasis ⟨i.1 + 1, by omega⟩ ∧
    (0, dualBasisVector (firstThreeIndex i)) ∈ neutralAnnihilator (1 : Spinor) ∧
    projectivePureSpinorGrassmannianPoint
        ⟨Projectivization.mk ℝ (1 : Spinor) one_ne_zero,
          projective_vacuum_isPureSpinor⟩ =
      ⟨neutralAnnihilator (1 : Spinor),
        vacuum_neutralAnnihilator_isMaximalNeutralTotallyNull⟩ := by
  exact ⟨rfl, by fin_cases i <;> rfl, peirceDegreeOne_from_vacuum i,
    firstThree_dual_channels_mem_vacuum_annihilator i,
    vacuum_1331_maximalNeutralGrassmannian_readout⟩

end InfoGeometry.Canonical.SplitOctonion1331PureSpinorGradingBridge
