import InfoGeometry.Twistor.NullProjective
import InfoGeometry.Geometry.PauliParavectorKernelBoundary
import InfoGeometry.Geometry.ParavectorZornBoundary

/-!
# Minkowski paravectors as projective-null boundary points

This owner bundles the existing Minkowski quadratic readout as a native
mathlib `QuadraticForm`.  A nonzero null paravector therefore defines a point
of the generic projective-null `TwistorSpace` used by the configuration and
braid-monodromy infrastructure.

The same representative already has two equivalent finite readouts:

* a Pauli operator with nontrivial kernel;
* an explicit Zorn representative with zero reduced norm.

No anyon state is identified with a four-vector here.  Anyonic/braid data live
on configurations and exchange paths of these projective-null boundary points.
-/

noncomputable section

namespace InfoGeometry.Twistor.MinkowskiProjectiveNullBoundary

open InfoGeometry.Twistor
open InfoGeometry.Geometry.PauliParavectorBridge
open InfoGeometry.Geometry.PauliParavectorKernelBoundary
open InfoGeometry.Geometry.ParavectorZornBoundary

/-- Symmetric bilinear form of signature `(1,3)` on the real paravector
carrier. -/
def minkowskiBilin : LinearMap.BilinForm ℝ Minkowski4 := by
  refine LinearMap.mk₂ ℝ
    (fun v w => v.t * w.t - v.x * w.x - v.y * w.y - v.z * w.z)
    ?_ ?_ ?_ ?_
  · intro v₁ v₂ w
    simp [Minkowski4.t, Minkowski4.x, Minkowski4.y, Minkowski4.z]
    ring
  · intro r v w
    simp [Minkowski4.t, Minkowski4.x, Minkowski4.y, Minkowski4.z]
    ring
  · intro v w₁ w₂
    simp [Minkowski4.t, Minkowski4.x, Minkowski4.y, Minkowski4.z]
    ring
  · intro r v w
    simp [Minkowski4.t, Minkowski4.x, Minkowski4.y, Minkowski4.z]
    ring

/-- Native quadratic form whose zero locus is the Minkowski light cone. -/
def minkowskiQuadraticForm : QuadraticForm ℝ Minkowski4 :=
  minkowskiBilin.toQuadraticMap

@[simp] theorem minkowskiQuadraticForm_apply (v : Minkowski4) :
    minkowskiQuadraticForm v = v.q := by
  simp [minkowskiQuadraticForm, minkowskiBilin, Minkowski4.q,
    Minkowski4.t, Minkowski4.x, Minkowski4.y, Minkowski4.z]

/-- Projectivized Minkowski light cone, using the repository's generic
projective-null twistor infrastructure. -/
abbrev MinkowskiNullBoundary : Type _ :=
  TwistorSpace minkowskiQuadraticForm

/-- A nonzero lightlike four-vector defines a projective-null boundary point. -/
def minkowskiNullBoundaryMk
    (v : Minkowski4) (hv : v ≠ 0) (hnull : v.IsNull) :
    MinkowskiNullBoundary :=
  twistorMk minkowskiQuadraticForm v hv (by
    simpa [Minkowski4.IsNull] using hnull)

@[simp] theorem minkowskiNullBoundaryMk_rep
    (v : Minkowski4) (hv : v ≠ 0) (hnull : v.IsNull) :
    (minkowskiNullBoundaryMk v hv hnull).1 =
      Projectivization.mk ℝ v hv :=
  rfl

/-- The projective-null predicate on a concrete representative is exactly the
usual Minkowski null equation. -/
theorem projectiveNull_mk_iff_minkowskiNull
    (v : Minkowski4) (hv : v ≠ 0) :
    IsNull minkowskiQuadraticForm (Projectivization.mk ℝ v hv) ↔ v.IsNull := by
  rw [isNull_mk_iff]
  simp [Minkowski4.IsNull]

/-- Boundary nullness, Pauli-kernel degeneracy, and Zorn zero norm are three
proved readouts of the same nonzero paravector representative. -/
theorem boundary_point_kernel_zorn_packet
    (v : Minkowski4) (hv : v ≠ 0) :
    IsNull minkowskiQuadraticForm (Projectivization.mk ℝ v hv) ↔
      LinearMap.ker (pauliOperator v) ≠ ⊥ ∧
        IsZornNull (zornBoundaryOfMinkowski4 v) := by
  rw [projectiveNull_mk_iff_minkowskiNull,
    isNull_iff_pauliKernel_ne_bot,
    ← isZornNull_boundary_iff_isNull]
  constructor <;> intro h
  · exact ⟨h, h⟩
  · exact h.1

end InfoGeometry.Twistor.MinkowskiProjectiveNullBoundary
