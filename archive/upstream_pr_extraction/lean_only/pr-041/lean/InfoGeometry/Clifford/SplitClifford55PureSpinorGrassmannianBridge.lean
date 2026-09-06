import InfoGeometry.Clifford.SplitClifford55ProjectivePureSpinor
import InfoGeometry.Projective.ExteriorKleinTwoPlaneQuotient
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Projective pure-spinor to maximal-neutral Grassmannian bridge

This file packages the finite Grassmannian carrier owned by the split
`(5,5)` neutral space and records the canonical readout from a projective
pure-spinor line to its annihilator plane.  It proves only the forward
compatibility edge; no surjectivity or Plücker embedding is asserted here.
-/

noncomputable section

namespace InfoGeometry.Clifford.SplitClifford55PureSpinorGrassmannianBridge

open InfoGeometry.Clifford.SplitClifford55ExteriorSpinor
open InfoGeometry.Clifford.SplitClifford55ProjectivePureSpinor
open InfoGeometry.Projective.ExteriorKleinTwoPlaneQuotient
open scoped LinearAlgebra.Projectivization

/-- The finite maximal-neutral Grassmannian carrier for the split `(5,5)` space. -/
def MaximalNeutralGrassmannian : Type :=
  {W : Submodule ℝ NeutralSpace // IsMaximalNeutralTotallyNull W}

/-- The annihilator plane attached to a projective pure-spinor line. -/
def projectivePureSpinorGrassmannianPoint
    (p : {p : ℙ ℝ Spinor // p ∈ ProjectivePureSpinor}) :
    MaximalNeutralGrassmannian :=
  ⟨projectivePureSpinorAnnihilator p.1,
    projectivePureSpinorAnnihilator_isMaximalNeutralTotallyNull p.1 p.2⟩

@[simp] theorem projectivePureSpinorGrassmannianPoint_val
    (p : {p : ℙ ℝ Spinor // p ∈ ProjectivePureSpinor}) :
    (projectivePureSpinorGrassmannianPoint p).1 =
      projectivePureSpinorAnnihilator p.1 := by
  rfl

theorem projectivePureSpinorGrassmannianPoint_finrank
    (p : {p : ℙ ℝ Spinor // p ∈ ProjectivePureSpinor}) :
    Module.finrank ℝ (projectivePureSpinorGrassmannianPoint p).1 = 5 := by
  rw [projectivePureSpinorGrassmannianPoint_val]
  exact projectivePureSpinorAnnihilator_finrank p.1 p.2

theorem projectivePureSpinorGrassmannianPoint_totallyNull
    (p : {p : ℙ ℝ Spinor // p ∈ ProjectivePureSpinor}) :
    BudinichSpinorsNullVectors.IsTotallyNull neutralPairing
      (projectivePureSpinorGrassmannianPoint p).1 := by
  exact (projectivePureSpinorGrassmannianPoint p).2.1

theorem projectivePureSpinor_exists_nonzeroPluckerReadout
    (p : {p : ℙ ℝ Spinor // p ∈ ProjectivePureSpinor}) :
    ∃ b : Module.Basis (Fin 5) ℝ
        (projectivePureSpinorGrassmannianPoint p).1,
      exteriorPower.ιMulti ℝ 5
          (fun i => (b i : NeutralSpace)) ≠ 0 := by
  let P := projectivePureSpinorGrassmannianPoint p
  letI : FiniteDimensional ℝ NeutralSpace := inferInstance
  letI : FiniteDimensional ℝ P.1 := inferInstance
  letI : Module.Free ℝ P.1 := Module.Free.of_divisionRing ℝ P.1
  have hP : Module.finrank ℝ P.1 = 5 :=
    projectivePureSpinorGrassmannianPoint_finrank p
  let b : Module.Basis (Fin 5) ℝ P.1 :=
    (Module.finBasis ℝ P.1).reindex (finCongr hP)
  refine ⟨b, ?_⟩
  exact exterior_ιMulti_coe_basis_ne_zero b

theorem vacuum_projectivePureSpinorGrassmannianPoint
    : projectivePureSpinorGrassmannianPoint
        ⟨Projectivization.mk ℝ (1 : Spinor) one_ne_zero,
          projective_vacuum_isPureSpinor⟩ =
      ⟨neutralAnnihilator (1 : Spinor),
        vacuum_neutralAnnihilator_isMaximalNeutralTotallyNull⟩ := by
  rfl

end InfoGeometry.Clifford.SplitClifford55PureSpinorGrassmannianBridge
