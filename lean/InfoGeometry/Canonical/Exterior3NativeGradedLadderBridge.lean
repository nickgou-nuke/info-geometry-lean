import Mathlib.RingTheory.GradedAlgebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitOctonion1331PureSpinorGradingBridge
import InfoGeometry.OperatorAlgebra.GradeActionInterface

/-! Native graded creation/projector transport on the three-mode exterior
algebra.  This uses Mathlib's graded-algebra projection, not coordinate
case-splitting. -/
namespace InfoGeometry.Canonical.Exterior3NativeGradedLadderBridge

noncomputable section
open scoped DirectSum
open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge
open InfoGeometry.OperatorAlgebra

abbrev V3 := InfoGeometry.Algebra.FiniteSpin.Vec3R
abbrev Exterior3 := ExteriorAlgebra ℝ V3
abbrev Exterior3End := Module.End ℝ Exterior3

def nativeExteriorProjector (k : ℕ) : Exterior3End :=
  GradedAlgebra.proj (fun n : ℕ => ⋀[ℝ]^n V3) k

theorem exteriorGenerator_mem_degreeOne (v : V3) :
    ExteriorAlgebra.ι ℝ v ∈ (⋀[ℝ]^1 V3) := by
  simpa only [pow_one] using
    LinearMap.mem_range_self (ExteriorAlgebra.ι ℝ : V3 →ₗ[ℝ] Exterior3) v

theorem nativeExteriorProjector_wedge_shift (v : V3) (k : ℕ) :
    (nativeExteriorProjector (k + 1)).comp (exteriorWedge3 v) =
      (exteriorWedge3 v).comp (nativeExteriorProjector k) := by
  apply LinearMap.ext
  intro x
  change GradedAlgebra.proj (fun n : ℕ => ⋀[ℝ]^n V3) (k + 1)
      (ExteriorAlgebra.ι ℝ v * x) =
    ExteriorAlgebra.ι ℝ v *
      GradedAlgebra.proj (fun n : ℕ => ⋀[ℝ]^n V3) k x
  rw [GradedAlgebra.proj_apply, GradedAlgebra.proj_apply]
  rw [show k + 1 = 1 + k by omega]
  exact DirectSum.coe_decompose_mul_add_of_left_mem
    (fun n : ℕ => ⋀[ℝ]^n V3) (exteriorGenerator_mem_degreeOne v)

theorem nativeExteriorProjector_wedge_shift_apply
    (v : V3) (k : ℕ) (x : Exterior3) :
    nativeExteriorProjector (k + 1) (exteriorWedge3 v x) =
      exteriorWedge3 v (nativeExteriorProjector k x) := by
  exact congrArg (fun T : Exterior3End => T x)
    (nativeExteriorProjector_wedge_shift v k)

def nativeExteriorGrade (k : ℕ) : Set Exterior3 :=
  Set.range (nativeExteriorProjector k)

theorem exteriorWedge3_maps_native_grade :
    MapsToGrade nativeExteriorGrade
      (fun v x => exteriorWedge3 v x)
      (fun _ k => k + 1) := by
  intro v k x hx
  rcases hx with ⟨y, rfl⟩
  refine ⟨exteriorWedge3 v y, ?_⟩
  exact nativeExteriorProjector_wedge_shift_apply v k y

/-! The first contraction boundary is available directly from Mathlib's
contraction API.  This is the honest endpoint before a general contraction
grading theorem: it records the annihilation of the vacuum without assuming a
Hodge-factorisation of contraction. -/
theorem exteriorContract3_vacuum (φ : Module.Dual ℝ V3) :
    exteriorContract3 φ (1 : Exterior3) = 0 := by
  exact CliffordAlgebra.contractLeft_one
    (Q := (0 : QuadraticForm ℝ V3)) φ

theorem exteriorContract3_ιMulti_succ_mem
    (φ : Module.Dual ℝ V3) (n : ℕ) (v : Fin (n + 1) → V3) :
    exteriorContract3 φ (ExteriorAlgebra.ιMulti ℝ (n + 1) v) ∈
      ⋀[ℝ]^n V3 := by
  induction n with
  | zero =>
      change CliffordAlgebra.contractLeft
        (Q := (0 : QuadraticForm ℝ V3)) φ
          (ExteriorAlgebra.ιMulti ℝ (0 + 1) v) ∈ ⋀[ℝ]^0 V3
      rw [ExteriorAlgebra.ιMulti_succ_apply,
        ExteriorAlgebra.ιMulti_zero_apply,
        CliffordAlgebra.contractLeft_ι_mul]
      simpa [exteriorContract3_vacuum] using
        ((⋀[ℝ]^0 V3).smul_mem (φ (v 0)) (by
          exact SetLike.GradedOne.one_mem))
  | succ n ih =>
      change CliffordAlgebra.contractLeft
        (Q := (0 : QuadraticForm ℝ V3)) φ
          (ExteriorAlgebra.ιMulti ℝ (n + 1 + 1) v) ∈ ⋀[ℝ]^(n + 1) V3
      rw [ExteriorAlgebra.ιMulti_succ_apply,
        CliffordAlgebra.contractLeft_ι_mul]
      have htail : ExteriorAlgebra.ιMulti ℝ (n + 1) (Matrix.vecTail v) ∈
          ⋀[ℝ]^(n + 1) V3 := by
        apply ExteriorAlgebra.ιMulti_range
        exact ⟨Matrix.vecTail v, rfl⟩
      have hcontract : exteriorContract3 φ
          (ExteriorAlgebra.ιMulti ℝ (n + 1) (Matrix.vecTail v)) ∈
          ⋀[ℝ]^n V3 := ih (Matrix.vecTail v)
      have hhead : ExteriorAlgebra.ι ℝ (v 0) ∈ ⋀[ℝ]^1 V3 := by
        simpa only [pow_one] using
          (LinearMap.mem_range_self
            (ExteriorAlgebra.ι ℝ : V3 →ₗ[ℝ] Exterior3) (v 0))
      have hmul : ExteriorAlgebra.ι ℝ (v 0) *
          exteriorContract3 φ (ExteriorAlgebra.ιMulti ℝ (n + 1)
            (Matrix.vecTail v)) ∈ ⋀[ℝ]^(n + 1) V3 := by
        simpa [Nat.add_comm] using
          (SetLike.GradedMonoid.toGradedMul.mul_mem
            (i := 1) (j := n) hhead hcontract)
      exact (⋀[ℝ]^(n + 1) V3).sub_mem
        ((⋀[ℝ]^(n + 1) V3).smul_mem (φ (v 0)) htail) hmul

theorem exteriorContract3_wedge_vacuum_grade_shift
    (φ : Module.Dual ℝ V3) (v : V3) :
    nativeExteriorProjector 0
        (exteriorContract3 φ (exteriorWedge3 v (1 : Exterior3))) =
      exteriorContract3 φ
        (nativeExteriorProjector 1 (exteriorWedge3 v (1 : Exterior3))) := by
  have hzero : nativeExteriorProjector 0 (1 : Exterior3) = 1 := by
    rw [nativeExteriorProjector, GradedAlgebra.proj_apply]
    change ((DirectSum.decompose (fun n : ℕ => ⋀[ℝ]^n V3) (1 : Exterior3)) 0 : Exterior3) = 1
    rw [DirectSum.decompose_one]
    rfl
  have hproj :
      nativeExteriorProjector 1 (exteriorWedge3 v (1 : Exterior3)) =
        exteriorWedge3 v (1 : Exterior3) := by
    rw [nativeExteriorProjector_wedge_shift_apply v 0]
    rw [nativeExteriorProjector, GradedAlgebra.proj_apply,
      DirectSum.decompose_one]
    change (ExteriorAlgebra.ι ℝ v) * (1 : Exterior3) = _
    simp
  rw [hproj]
  rw [exteriorContract3_wedge3_apply, exteriorContract3_vacuum]
  simp only [map_zero, smul_zero, sub_zero]
  rw [map_smul, hzero]

end
end InfoGeometry.Canonical.Exterior3NativeGradedLadderBridge
