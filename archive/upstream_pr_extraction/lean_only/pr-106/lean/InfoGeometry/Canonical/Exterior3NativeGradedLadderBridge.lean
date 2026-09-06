import Mathlib.RingTheory.GradedAlgebra.Basic
import InfoGeometry.Canonical.SplitOctonion1331GradedProjectorActionBridge

/-!
# Native graded ladder identity on the three-mode exterior carrier

This owner uses Mathlib's native graded-algebra decomposition of
`ExteriorAlgebra ℝ (Fin 3 → ℝ)`. It proves the exact creation/projector
intertwiner

`P_(k+1) ∘ ε_v = ε_v ∘ P_k`

for every degree `k` and every one-form generator `v`.

This is the full graded-algebra statement behind the finite `1+3+3+1`
generator readouts in `SplitOctonion1331GradedProjectorActionBridge`.
-/

noncomputable section

namespace InfoGeometry.Canonical.Exterior3NativeGradedLadderBridge

open scoped DirectSum

open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge

abbrev V3 := Fin 3 → ℝ
abbrev Exterior3 := ExteriorAlgebra ℝ V3
abbrev Exterior3End := Module.End ℝ Exterior3

/-- Mathlib's native projection onto the `k`th exterior-power summand. -/
noncomputable def nativeExteriorProjector (k : ℕ) : Exterior3End :=
  GradedAlgebra.proj (fun n : ℕ => ⋀[ℝ]^n V3) k

/-- A canonical exterior generator is homogeneous of degree one. -/
theorem exteriorGenerator_mem_degreeOne (v : V3) :
    ExteriorAlgebra.ι ℝ v ∈ (⋀[ℝ]^1 V3) := by
  simpa only [pow_one] using
    LinearMap.mem_range_self (ExteriorAlgebra.ι ℝ : V3 →ₗ[ℝ] Exterior3) v

/-- Exact native graded-ladder identity:
`P_(k+1) ε_v = ε_v P_k`. -/
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
    (fun n : ℕ => ⋀[ℝ]^n V3)
    (exteriorGenerator_mem_degreeOne v)

/-- Pointwise form of the exact native graded-ladder identity. -/
theorem nativeExteriorProjector_wedge_shift_apply
    (v : V3) (k : ℕ) (x : Exterior3) :
    nativeExteriorProjector (k + 1) (exteriorWedge3 v x) =
      exteriorWedge3 v (nativeExteriorProjector k x) := by
  exact congrArg (fun T : Exterior3End => T x)
    (nativeExteriorProjector_wedge_shift v k)

/-- The top-degree instance of the same shift identity.  No separate vanishing
claim is made here; vanishing above degree three belongs to the exterior-power
subsingleton API. -/
theorem nativeExteriorProjector_wedge_shift_from_top
    (v : V3) (x : Exterior3) :
    nativeExteriorProjector 4 (exteriorWedge3 v x) =
      exteriorWedge3 v (nativeExteriorProjector 3 x) := by
  simpa using nativeExteriorProjector_wedge_shift_apply v 3 x

/-- Compact theorem packet combining native graded creation with the existing
CAR relation. -/
theorem native_exterior_creation_CAR_projector_packet
    (v : V3) (phi : Module.Dual ℝ V3) (k : ℕ) :
    (nativeExteriorProjector (k + 1)).comp (exteriorWedge3 v) =
        (exteriorWedge3 v).comp (nativeExteriorProjector k) ∧
    exteriorContract3 phi * exteriorWedge3 v +
        exteriorWedge3 v * exteriorContract3 phi =
      (phi v) • (1 : Exterior3End) := by
  exact ⟨nativeExteriorProjector_wedge_shift v k,
    exteriorContract3_wedge3_CAR phi v⟩

end InfoGeometry.Canonical.Exterior3NativeGradedLadderBridge
