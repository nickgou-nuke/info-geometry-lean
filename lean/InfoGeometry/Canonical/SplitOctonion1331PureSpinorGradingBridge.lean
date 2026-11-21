/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
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

@[simp] theorem exterior3PeirceBasis_equivFun_basis (i : Fin 8) :
    exterior3PeirceBasis.equivFun (exterior3PeirceBasis i) = Pi.single i 1 := by
  ext j
  by_cases h : i = j
  · subst j
    simp [Module.Basis.equivFun_self]
  · have h' : j ≠ i := fun hji => h hji.symm
    simp [Module.Basis.equivFun_self, h, h']

/-- Exact basis action of the transported exterior-degree projector. -/
theorem exteriorDegreeProjector1331_basis (k : ℕ) (i : Fin 8) :
    exteriorDegreeProjector1331 k (exterior3PeirceBasis i) =
      if exteriorDegree1331 i = k then exterior3PeirceBasis i else 0 := by
  apply (exterior3PeirceBasis.equivFun.toEquiv.symm_apply_eq).2
  change degreeCoordinateProjector k (exterior3PeirceBasis.equivFun (exterior3PeirceBasis i)) =
    exterior3PeirceBasis.equivFun
      (if exteriorDegree1331 i = k then exterior3PeirceBasis i else 0)
  by_cases h : exteriorDegree1331 i = k
  · rw [if_pos h, exterior3PeirceBasis_equivFun_basis]
    ext j
    by_cases hji : j = i
    · subst j
      simp [degreeCoordinateProjector, h]
    · simp [degreeCoordinateProjector, hji]
  · rw [if_neg h]
    simp only [map_zero]
    ext j
    by_cases hjk : exteriorDegree1331 j = k
    · have hij : i ≠ j := by
        intro hij
        subst j
        exact h hjk
      simp [degreeCoordinateProjector, hjk, hij]
    · simp [degreeCoordinateProjector, hjk]

/-- The four degree projectors resolve the identity on the full 8-dimensional
three-mode exterior carrier. -/
theorem exteriorDegreeProjector1331_sum_eq_id :
    exteriorDegreeProjector1331 0 + exteriorDegreeProjector1331 1 +
        exteriorDegreeProjector1331 2 + exteriorDegreeProjector1331 3 =
      LinearMap.id := by
  apply exterior3PeirceBasis.ext
  intro i
  fin_cases i <;> simp [exteriorDegreeProjector1331_basis, exteriorDegree1331]

/-- Each transported degree projector is idempotent. -/
theorem exteriorDegreeProjector1331_idempotent (k : ℕ) :
    (exteriorDegreeProjector1331 k).comp (exteriorDegreeProjector1331 k) =
      exteriorDegreeProjector1331 k := by
  apply exterior3PeirceBasis.ext
  intro i
  by_cases h : exteriorDegree1331 i = k <;>
    simp [LinearMap.comp_apply, exteriorDegreeProjector1331_basis, h]

/-- Distinct exterior-degree projectors are orthogonal. -/
theorem exteriorDegreeProjector1331_orthogonal
    {k l : ℕ} (hkl : k ≠ l) :
    (exteriorDegreeProjector1331 k).comp (exteriorDegreeProjector1331 l) = 0 := by
  apply exterior3PeirceBasis.ext
  intro i
  by_cases hk : exteriorDegree1331 i = k
  · have hl : exteriorDegree1331 i ≠ l := by
      intro hil
      exact hkl (hk.symm.trans hil)
    simp [LinearMap.comp_apply, exteriorDegreeProjector1331_basis, hk, hl,
      if_neg (fun h => hkl h), LinearMap.map_zero]
  · by_cases hil : exteriorDegree1331 i = l
    · calc
        (exteriorDegreeProjector1331 k ∘ₗ exteriorDegreeProjector1331 l) (exterior3PeirceBasis i)
          = exteriorDegreeProjector1331 k (exteriorDegreeProjector1331 l (exterior3PeirceBasis i)) := rfl
        _ = exteriorDegreeProjector1331 k (exterior3PeirceBasis i) := by
          rw [exteriorDegreeProjector1331_basis]; simp [hil]
        _ = 0 := by
          rw [exteriorDegreeProjector1331_basis]; simp [hk]
    · simp [LinearMap.comp_apply, exteriorDegreeProjector1331_basis, hk, hil, LinearMap.map_zero]

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

/-- Combined compatibility statement between the degree-zero exterior vacuum,
its three degree-one creation directions, and the selected pure-spinor
annihilator channels. -/
theorem vacuum_degreeOne_annihilator_1331_packet (i : Fin 3) :
    exteriorDegree1331 0 = 0 ∧
    exteriorDegree1331 ⟨i.1 + 1, by omega⟩ = 1 ∧
    exteriorWedge3 (Pi.single i 1) (exterior3PeirceBasis 0) =
      exterior3PeirceBasis ⟨i.1 + 1, by omega⟩ ∧
    (0, dualBasisVector (firstThreeIndex i)) ∈
      neutralAnnihilator (1 : Spinor) := by
  refine ⟨rfl, ?_, peirceDegreeOne_from_vacuum i,
    firstThree_dual_channels_mem_vacuum_annihilator i⟩
  fin_cases i <;> rfl

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
