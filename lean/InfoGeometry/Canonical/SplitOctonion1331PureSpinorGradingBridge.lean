import Mathlib.Tactic
import InfoGeometry.Canonical.SplitOctonion1331ExteriorDiracSouriauBridge
import InfoGeometry.Canonical.SplitOctonionExteriorGradePeirceParityBridge
import InfoGeometry.Clifford.Cl55ZornCARComparison
import InfoGeometry.Clifford.SplitClifford55PureSpinorGrassmannianBridge

/-!
# 1+3+3+1 exterior grading and pure-spinor annihilator bridge

This owner packages the established linear `1+3+3+1` correspondence

`u+ | U_i | V_i | u-`

with the literal exterior degrees

`Λ^0 | Λ^1 | Λ^2 | Λ^3`

of `ExteriorAlgebra ℝ (Fin 3 → ℝ)`.  The correspondence is linear and
basis-compatible; no claim identifies the non-associative Zorn product with
exterior wedge multiplication.

The final section records the sound intersection with the repository's native
split-Clifford pure-spinor lane.  The latter is the existing `Cl(5,5)` exterior
spinor carrier, so the theorem identifies only the selected first-three vacuum
annihilator channels with the three-mode degree-one directions.  It does not
rename that `Cl(5,5)` maximal-neutral Grassmannian as `OGr(3,6)`.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitOctonion1331PureSpinorGradingBridge

open scoped BigOperators LinearAlgebra.Projectivization

open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge
open InfoGeometry.Canonical.SplitOctonion1331ExteriorDiracSouriauBridge
open InfoGeometry.Canonical.SplitOctonionExteriorGradePeirceParityBridge
open InfoGeometry.Lie.SplitOctonionCircularPeirceBasis
open InfoGeometry.Clifford.SplitClifford55ZornCARComparison
open InfoGeometry.Clifford.SplitClifford55ExteriorSpinor
open InfoGeometry.Clifford.SplitClifford55ProjectivePureSpinor
open InfoGeometry.Clifford.SplitClifford55PureSpinorGrassmannianBridge

abbrev Exterior3 :=
  InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge.Exterior3
abbrev Coord8 := Fin 8 → ℝ

/-- Coordinate projector onto one of the four exterior degrees in the
established circular Peirce ordering. -/
def degreeCoordinateProjector (k : ℕ) : Coord8 →ₗ[ℝ] Coord8 where
  toFun x i := if exteriorDegree1331 i = k then x i else 0
  map_add' x y := by
    ext i
    by_cases h : exteriorDegree1331 i = k <;> simp [h]
  map_smul' c x := by
    ext i
    by_cases h : exteriorDegree1331 i = k <;> simp [h]

/-- The genuine exterior-degree projector obtained by transporting the diagonal
coordinate projector through the native `exterior3PeirceBasis`. -/
def exteriorDegreeProjector1331 (k : ℕ) : Exterior3 →ₗ[ℝ] Exterior3 :=
  exterior3PeirceBasis.equivFun.symm.toLinearMap.comp
    ((degreeCoordinateProjector k).comp exterior3PeirceBasis.equivFun.toLinearMap)

@[simp] theorem exterior3PeirceBasis_equivFun_basis (i : Fin 8) :
    exterior3PeirceBasis.equivFun (exterior3PeirceBasis i) = Pi.single i 1 := by
  simp only [Module.Basis.equivFun_apply, Module.Basis.repr_self,
    Finsupp.single_eq_pi_single, Finsupp.equivFunOnFintype_single]

/-- Exact basis action of the transported exterior-degree projector. -/
theorem exteriorDegreeProjector1331_basis (k : ℕ) (i : Fin 8) :
    exteriorDegreeProjector1331 k (exterior3PeirceBasis i) =
      if exteriorDegree1331 i = k then exterior3PeirceBasis i else 0 := by
  apply exterior3PeirceBasis.equivFun.injective
  ext j
  by_cases hdeg : exteriorDegree1331 i = k
  · by_cases hji : j = i
    · subst j
      simp [exteriorDegreeProjector1331, degreeCoordinateProjector, hdeg]
    · simp [exteriorDegreeProjector1331, degreeCoordinateProjector, hdeg,
        hji, Pi.single_apply]
  · simp [exteriorDegreeProjector1331, degreeCoordinateProjector, hdeg]

/-- The four degree projectors resolve the identity on the full 8-dimensional
three-mode exterior carrier. -/
theorem exteriorDegreeProjector1331_sum_eq_id :
    exteriorDegreeProjector1331 0 + exteriorDegreeProjector1331 1 +
        exteriorDegreeProjector1331 2 + exteriorDegreeProjector1331 3 =
      LinearMap.id := by
  ext x
  apply exterior3PeirceBasis.equivFun.injective
  ext i
  fin_cases i <;>
    simp [exteriorDegreeProjector1331, degreeCoordinateProjector,
      exteriorDegree1331]

/-- Each transported degree projector is idempotent. -/
theorem exteriorDegreeProjector1331_idempotent (k : ℕ) :
    exteriorDegreeProjector1331 k.comp exteriorDegreeProjector1331 k =
      exteriorDegreeProjector1331 k := by
  ext x
  apply exterior3PeirceBasis.equivFun.injective
  ext i
  by_cases h : exteriorDegree1331 i = k <;>
    simp [exteriorDegreeProjector1331, degreeCoordinateProjector, h]

/-- Distinct exterior-degree projectors are orthogonal. -/
theorem exteriorDegreeProjector1331_orthogonal
    {k l : ℕ} (hkl : k ≠ l) :
    (exteriorDegreeProjector1331 k).comp (exteriorDegreeProjector1331 l) = 0 := by
  ext x
  apply exterior3PeirceBasis.equivFun.injective
  ext i
  by_cases hk : exteriorDegree1331 i = k
  · have hl : exteriorDegree1331 i ≠ l := by
      intro hil
      exact hkl (hk.symm.trans hil)
    simp [exteriorDegreeProjector1331, degreeCoordinateProjector, hk, hl]
  · simp [exteriorDegreeProjector1331, degreeCoordinateProjector, hk]

/-- The established Peirce order has the exact `1+3+3+1` degree pattern. -/
theorem exteriorDegree1331_packet :
    exteriorDegree1331 0 = 0 ∧
    (∀ i : Fin 3, exteriorDegree1331 ⟨i.1 + 1, by omega⟩ = 1) ∧
    (∀ i : Fin 3, exteriorDegree1331 ⟨i.1 + 5, by omega⟩ = 2) ∧
    exteriorDegree1331 4 = 3 := by
  refine ⟨rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i <;> rfl
  · intro i
    fin_cases i <;> rfl

/-- The degree-zero Peirce vector is literally the exterior vacuum. -/
theorem peirceVacuum_eq_exteriorVacuum :
    exterior3PeirceBasis 0 = (1 : Exterior3) :=
  exterior3PeirceBasis_zero

/-- Wedge creation from the degree-zero vacuum reaches exactly the three
established degree-one Peirce channels. -/
theorem peirceDegreeOne_from_vacuum (i : Fin 3) :
    exteriorWedge3
        (InfoGeometry.Canonical.SplitOctonionCARBdGRegularLift.modeVector i)
        (exterior3PeirceBasis 0) =
      exterior3PeirceBasis ⟨i.1 + 1, by omega⟩ := by
  simpa [InfoGeometry.Canonical.SplitOctonionCARBdGRegularLift.modeVector] using
    exteriorWedge3_basis_zero i

/-- The three selected dual Clifford channels annihilate the pure-spinor
vacuum.  These are the dual channels paired with the same first-three creation
directions used by the `1+3+3+1` exterior packet. -/
theorem firstThree_dual_channels_mem_vacuum_annihilator (i : Fin 3) :
    (0, dualBasisVector (firstThreeIndex i)) ∈
      neutralAnnihilator (1 : Spinor) :=
  dual_channel_mem_vacuum_neutralAnnihilator i

/-- Combined compatibility statement between the degree-zero exterior vacuum,
its three degree-one creation directions, and the selected pure-spinor
annihilator channels. -/
theorem vacuum_degreeOne_annihilator_1331_packet (i : Fin 3) :
    exteriorDegree1331 0 = 0 ∧
    exteriorDegree1331 ⟨i.1 + 1, by omega⟩ = 1 ∧
    exteriorWedge3
        (InfoGeometry.Canonical.SplitOctonionCARBdGRegularLift.modeVector i)
        (exterior3PeirceBasis 0) =
      exterior3PeirceBasis ⟨i.1 + 1, by omega⟩ ∧
    (0, dualBasisVector (firstThreeIndex i)) ∈
      neutralAnnihilator (1 : Spinor) := by
  refine ⟨rfl, ?_, peirceDegreeOne_from_vacuum i,
    firstThree_dual_channels_mem_vacuum_annihilator i⟩
  fin_cases i <;> rfl

/-- The same vacuum annihilator is the repository-owned maximal-neutral
Grassmannian readout of the projective pure-spinor vacuum. -/
theorem vacuum_1331_maximalNeutralGrassmannian_readout :
    projectivePureSpinorGrassmannianPoint
        ⟨Projectivization.mk ℝ (1 : Spinor) one_ne_zero,
          projective_vacuum_isPureSpinor⟩ =
      ⟨neutralAnnihilator (1 : Spinor),
        vacuum_neutralAnnihilator_isMaximalNeutralTotallyNull⟩ :=
  vacuum_projectivePureSpinorGrassmannianPoint

/-- Compact corridor theorem: the full exterior carrier resolves as
`1+3+3+1`; its vacuum creates the three degree-one channels; the matching
first-three dual Clifford channels lie in the vacuum annihilator; and that
annihilator is the native maximal-neutral Grassmannian point. -/
theorem peirce_exterior_pureSpinor_corridor (i : Fin 3) :
    (exteriorDegreeProjector1331 0 + exteriorDegreeProjector1331 1 +
        exteriorDegreeProjector1331 2 + exteriorDegreeProjector1331 3 =
      LinearMap.id) ∧
    exteriorWedge3
        (InfoGeometry.Canonical.SplitOctonionCARBdGRegularLift.modeVector i)
        (exterior3PeirceBasis 0) =
      exterior3PeirceBasis ⟨i.1 + 1, by omega⟩ ∧
    (0, dualBasisVector (firstThreeIndex i)) ∈
      neutralAnnihilator (1 : Spinor) ∧
    projectivePureSpinorGrassmannianPoint
        ⟨Projectivization.mk ℝ (1 : Spinor) one_ne_zero,
          projective_vacuum_isPureSpinor⟩ =
      ⟨neutralAnnihilator (1 : Spinor),
        vacuum_neutralAnnihilator_isMaximalNeutralTotallyNull⟩ := by
  exact ⟨exteriorDegreeProjector1331_sum_eq_id,
    peirceDegreeOne_from_vacuum i,
    firstThree_dual_channels_mem_vacuum_annihilator i,
    vacuum_1331_maximalNeutralGrassmannian_readout⟩

end InfoGeometry.Canonical.SplitOctonion1331PureSpinorGradingBridge
