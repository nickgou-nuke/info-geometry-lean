import Mathlib.RingTheory.GradedAlgebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitOctonion1331ExteriorDiracSouriauBridge
import InfoGeometry.Canonical.Exterior3NativeGradedLadderBridge
import InfoGeometry.Canonical.SplitOctonion1331PureSpinorGradingBridge
import InfoGeometry.Lie.SplitOctonionPeirceNativeProjectors
import InfoGeometry.Canonical.SplitOctonion1331GradedProjectorActionBridge

/-! Basis-level compatibility between the native exterior projector and the
established `1 + 3 + 3 + 1` Peirce basis. -/
namespace InfoGeometry.Canonical.SplitOctonionExteriorPeirceProjectorBridge

noncomputable section

open scoped DirectSum
open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge
open InfoGeometry.Canonical.SplitOctonion1331ExteriorDiracSouriauBridge
open InfoGeometry.Canonical.Exterior3NativeGradedLadderBridge
open InfoGeometry.Canonical.SplitOctonion1331PureSpinorGradingBridge
open InfoGeometry.Lie.SplitOctonionPeirceNativeProjectors
open InfoGeometry.Canonical.SplitOctonion1331GradedProjectorActionBridge

theorem nativeExteriorProjector_peirceBasis (i : Fin 8) :
    nativeExteriorProjector (peirceSubset i).card (exterior3PeirceBasis i) =
      exterior3PeirceBasis i := by
  rw [nativeExteriorProjector, GradedAlgebra.proj_apply]
  rw [exterior3PeirceBasis_ιMulti]
  apply DirectSum.decompose_of_mem_same
  apply ExteriorAlgebra.ιMulti_range
  exact ⟨vBasis3 ∘ (Set.powersetCard.ofFinEmbEquiv.symm
      ⟨peirceSubset i, by simp⟩), rfl⟩

theorem nativeExteriorProjector_coordinate_basis (i : Fin 8) :
    exterior3SplitOctonionCoordinateEquiv
        (nativeExteriorProjector (peirceSubset i).card
          (exterior3PeirceBasis i)) = Pi.single i 1 := by
  rw [nativeExteriorProjector_peirceBasis i]
  exact exterior3SplitOctonionCoordinateEquiv_basis i

noncomputable def transportedNativeExteriorProjector (k : ℕ) :
    Module.End ℝ (Fin 8 → ℝ) :=
  exterior3SplitOctonionCoordinateEquiv.toLinearMap.comp
    ((nativeExteriorProjector k).comp
      exterior3SplitOctonionCoordinateEquiv.symm.toLinearMap)

theorem nativeExteriorProjector_coordinate_basis_general (k : ℕ) (i : Fin 8) :
    exterior3SplitOctonionCoordinateEquiv
        (nativeExteriorProjector k (exterior3PeirceBasis i)) =
      if (peirceSubset i).card = k then Pi.single i 1 else 0 := by
  by_cases h : (peirceSubset i).card = k
  · subst k
    rw [nativeExteriorProjector_peirceBasis i]
    simp [exterior3SplitOctonionCoordinateEquiv_basis i]
  · rw [nativeExteriorProjector, GradedAlgebra.proj_apply]
    rw [DirectSum.decompose_of_mem_ne
      (ℳ := fun n : ℕ => ⋀[ℝ]^n (Fin 3 → ℝ))
      (exterior3PeirceBasis_mem_exteriorPower i) h]
    simp [h]

theorem nativeExteriorProjector_mem_degree (k : ℕ)
    (x : SplitOctonionExterior3HodgeDiracBridge.Exterior3) :
    nativeExteriorProjector k x ∈ ⋀[ℝ]^k
      SplitOctonionExterior3HodgeDiracBridge.V3 := by
  rw [nativeExteriorProjector, GradedAlgebra.proj_apply]
  exact (DirectSum.decompose
    (fun n : ℕ => ⋀[ℝ]^n SplitOctonionExterior3HodgeDiracBridge.V3) x k).property

theorem nativeExteriorProjector_range_le_degree (k : ℕ) :
    LinearMap.range (nativeExteriorProjector k) ≤
      ⋀[ℝ]^k SplitOctonionExterior3HodgeDiracBridge.V3 := by
  rintro _ ⟨x, rfl⟩
  exact nativeExteriorProjector_mem_degree k x

theorem nativeExteriorProjector_range_eq_degree (k : ℕ) :
    LinearMap.range (nativeExteriorProjector k) =
      ⋀[ℝ]^k SplitOctonionExterior3HodgeDiracBridge.V3 := by
  apply le_antisymm
  · exact nativeExteriorProjector_range_le_degree k
  · intro x hx
    refine ⟨x, ?_⟩
    rw [nativeExteriorProjector, GradedAlgebra.proj_apply]
    exact DirectSum.decompose_of_mem_same
      (fun n : ℕ => ⋀[ℝ]^n SplitOctonionExterior3HodgeDiracBridge.V3) hx

theorem exteriorContract3_maps_native_grade :
    InfoGeometry.OperatorAlgebra.MapsToGradeBetween
      (fun k : ℕ => nativeExteriorGrade (k + 1))
      nativeExteriorGrade
      (fun φ x => exteriorContract3 φ x)
      (fun _ k => k) := by
  intro φ k x hx
  change x ∈ LinearMap.range (nativeExteriorProjector (k + 1)) at hx
  change exteriorContract3 φ x ∈ LinearMap.range (nativeExteriorProjector k)
  have hxdeg : x ∈ ⋀[ℝ]^(k + 1)
      SplitOctonionExterior3HodgeDiracBridge.V3 := by
    rw [← nativeExteriorProjector_range_eq_degree (k + 1)]
    exact hx
  rw [nativeExteriorProjector_range_eq_degree k]
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hxdeg
  refine Submodule.span_induction (p := fun y _ =>
    exteriorContract3 φ y ∈ ⋀[ℝ]^k
      SplitOctonionExterior3HodgeDiracBridge.V3) ?_ ?_ ?_ ?_ hxdeg
  · intro y hy
    rcases hy with ⟨v, rfl⟩
    exact exteriorContract3_ιMulti_succ_mem φ k v
  · simp
  · intro y z hy hz hhy hhz
    simpa only [map_add] using
      (⋀[ℝ]^k SplitOctonionExterior3HodgeDiracBridge.V3).add_mem hhy hhz
  · intro r y hy hhy
    simpa only [map_smul] using
      (⋀[ℝ]^k SplitOctonionExterior3HodgeDiracBridge.V3).smul_mem r hhy

theorem exteriorNativeGrade_ladder_packet :
    InfoGeometry.OperatorAlgebra.MapsToGradeBetween
      (fun k : ℕ => nativeExteriorGrade k)
      (fun k : ℕ => nativeExteriorGrade (k + 1))
      (fun v x => exteriorWedge3 v x)
      (fun _ k => k) ∧
    InfoGeometry.OperatorAlgebra.MapsToGradeBetween
      (fun k : ℕ => nativeExteriorGrade (k + 1))
      (fun k : ℕ => nativeExteriorGrade k)
      (fun φ x => exteriorContract3 φ x)
      (fun _ k => k) := by
  constructor
  · exact exteriorWedge3_maps_native_grade
  · exact exteriorContract3_maps_native_grade

theorem exteriorPeirceLadderHodge_action_packet :
    InfoGeometry.OperatorAlgebra.MapsToGradeBetween
      (fun k : ℕ => nativeExteriorGrade k)
      (fun k : ℕ => nativeExteriorGrade (k + 1))
      (fun v x => exteriorWedge3 v x)
      (fun _ k => k) ∧
    InfoGeometry.OperatorAlgebra.MapsToGradeBetween
      (fun k : ℕ => nativeExteriorGrade (k + 1))
      nativeExteriorGrade
      (fun φ x => exteriorContract3 φ x)
      (fun _ k => k) ∧
    InfoGeometry.OperatorAlgebra.MapsToGrade
      peirce1331Grade
      (fun _ : Unit =>
        (InfoGeometry.Lie.PeirceExteriorHodgeTransport.peirceHodgeStar :
          PeirceCarrier → PeirceCarrier))
      (fun _ : Unit => peirce1331Complement) := by
  refine ⟨exteriorWedge3_maps_native_grade,
    exteriorContract3_maps_native_grade, ?_⟩
  exact peirceHodgeStar_maps_1331_grades

theorem transportedNativeExteriorProjector_apply_basis (k : ℕ) (i : Fin 8) :
    transportedNativeExteriorProjector k (Pi.single i 1) =
      if (peirceSubset i).card = k then Pi.single i 1 else 0 := by
  change exterior3SplitOctonionCoordinateEquiv
      (nativeExteriorProjector k
        (exterior3SplitOctonionCoordinateEquiv.symm (Pi.single i 1))) = _
  have hi : exterior3SplitOctonionCoordinateEquiv.symm (Pi.single i 1) =
      exterior3PeirceBasis i := by
    apply exterior3SplitOctonionCoordinateEquiv.injective
    simp
  rw [hi, nativeExteriorProjector_coordinate_basis_general]

theorem transportedNativeExteriorProjector_packet :
    transportedNativeExteriorProjector 0 = projectorPP ∧
    transportedNativeExteriorProjector 1 = projectorPM ∧
    transportedNativeExteriorProjector 2 = projectorMP ∧
    transportedNativeExteriorProjector 3 = projectorMM := by
  constructor
  · apply Module.Basis.ext (Pi.basisFun ℝ (Fin 8))
    intro i
    simp only [Pi.basisFun_apply]
    rw [transportedNativeExteriorProjector_apply_basis]
    fin_cases i <;>
      simp [projectorPP_apply] <;>
      ext j <;> fin_cases j <;> rfl
  constructor
  · apply Module.Basis.ext (Pi.basisFun ℝ (Fin 8))
    intro i
    simp only [Pi.basisFun_apply]
    rw [transportedNativeExteriorProjector_apply_basis]
    fin_cases i <;>
      simp [projectorPM_apply] <;>
      ext j <;> fin_cases j <;> rfl
  constructor
  · apply Module.Basis.ext (Pi.basisFun ℝ (Fin 8))
    intro i
    simp only [Pi.basisFun_apply]
    rw [transportedNativeExteriorProjector_apply_basis]
    fin_cases i <;>
      simp [projectorMP_apply] <;>
      ext j <;> fin_cases j <;> rfl
  · apply Module.Basis.ext (Pi.basisFun ℝ (Fin 8))
    intro i
    simp only [Pi.basisFun_apply]
    rw [transportedNativeExteriorProjector_apply_basis]
    fin_cases i <;>
      simp [projectorMM_apply] <;>
      ext j <;> fin_cases j <;> rfl

theorem transportedNativeExteriorProjector_fin4 (k : Fin 4) :
    transportedNativeExteriorProjector k.val = peirce1331Projector k := by
  fin_cases k
  · exact transportedNativeExteriorProjector_packet.1
  · exact transportedNativeExteriorProjector_packet.2.1
  · exact transportedNativeExteriorProjector_packet.2.2.1
  · exact transportedNativeExteriorProjector_packet.2.2.2

theorem exteriorPeirceUnifiedGrading_packet :
    InfoGeometry.OperatorAlgebra.MapsToGrade nativeExteriorGrade
      (fun v x => exteriorWedge3 v x)
      (fun _ k => k + 1) ∧
    peirceHodgeStarEquiv '' peirce1331Grade 0 = peirce1331Grade 3 ∧
    peirceHodgeStarEquiv '' peirce1331Grade 1 = peirce1331Grade 2 ∧
    peirceHodgeStarEquiv '' peirce1331Grade 2 = peirce1331Grade 1 ∧
    peirceHodgeStarEquiv '' peirce1331Grade 3 = peirce1331Grade 0 ∧
    (∀ φ ψ, exteriorGrade3 (exteriorContract3 φ ψ) =
      -(exteriorContract3 φ (exteriorGrade3 ψ))) ∧
    (∀ φ v, nativeExteriorProjector 0
        (exteriorContract3 φ (exteriorWedge3 v
          (1 : SplitOctonionExterior3HodgeDiracBridge.Exterior3))) =
      exteriorContract3 φ
        (nativeExteriorProjector 1 (exteriorWedge3 v
          (1 : SplitOctonionExterior3HodgeDiracBridge.Exterior3)))) := by
  refine ⟨exteriorWedge3_maps_native_grade, ?_⟩
  refine ⟨peirceHodgeStar_maps_1331_grades_image_eq 0,
    peirceHodgeStar_maps_1331_grades_image_eq 1,
    peirceHodgeStar_maps_1331_grades_image_eq 2,
    peirceHodgeStar_maps_1331_grades_image_eq 3, ?_⟩
  refine ⟨?_, ?_⟩
  · intro φ ψ
    exact exteriorGrade3_contract φ ψ
  · intro φ v
    exact exteriorContract3_wedge_vacuum_grade_shift φ v

end
end InfoGeometry.Canonical.SplitOctonionExteriorPeirceProjectorBridge
