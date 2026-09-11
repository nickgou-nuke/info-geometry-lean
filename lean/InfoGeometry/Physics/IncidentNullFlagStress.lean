import Mathlib.LinearAlgebra.Dual.Defs
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.FierzKleinFoundation

/-!
# Explicit incident null-flag stress readouts

This file is deliberately predicate-based.  It defines no model records and
stores no proof obligations in bundled carriers.  Every theorem takes the
concrete vectors, covectors, and linear maps it uses as explicit arguments.
-/

noncomputable section

namespace InfoGeometry.Physics.IncidentNullFlagStress

open InfoGeometry.Canonical.FierzKleinFoundation

/-- Coordinate basis vector in the explicit `Vec4 = I4 → ℝ` model. -/
def vec4Basis (i : I4) : Vec4 :=
  fun j => if j = i then 1 else 0

/-- Coordinates of a dual vector against the explicit coordinate basis. -/
def dualVec4Coordinates (W : Module.Dual ℝ Vec4) : Vec4 :=
  fun i => W (vec4Basis i)

/-- Explicit quadratic readout associated to the repo's Minkowski pairing. -/
def minkowskiQuadraticVec4 (Z : Vec4) : ℝ :=
  minkowskiDot Z Z

/-- Explicit incident null-flag predicate. -/
def IsFierzKleinIncidentNullFlag (Z : Vec4) (W : Module.Dual ℝ Vec4) : Prop :=
  Z ≠ 0 ∧ minkowskiDot Z Z = 0 ∧ W Z = 0

/-- Explicit boundary Majorana predicate on concrete maps and a concrete source vector. -/
def IsBoundaryMajoranaFlag
    (Z : Vec4)
    (Pboundary Pzero J Dboundary : Vec4 →ₗ[ℝ] Vec4) : Prop :=
  Pboundary Z = Z ∧ Pzero Z = Z ∧ J Z = Z ∧ Dboundary Z = 0

/-- The explicit incident predicate exposes source nonzero-ness. -/
theorem incident_source_ne_zero
    {Z : Vec4} {W : Module.Dual ℝ Vec4}
    (h : IsFierzKleinIncidentNullFlag Z W) :
    Z ≠ 0 :=
  h.1

/-- The explicit incident predicate exposes source nullness. -/
theorem incident_source_null
    {Z : Vec4} {W : Module.Dual ℝ Vec4}
    (h : IsFierzKleinIncidentNullFlag Z W) :
    minkowskiDot Z Z = 0 :=
  h.2.1

/-- The explicit incident predicate exposes dual incidence. -/
theorem incident_dual_pairing_eq_zero
    {Z : Vec4} {W : Module.Dual ℝ Vec4}
    (h : IsFierzKleinIncidentNullFlag Z W) :
    W Z = 0 :=
  h.2.2

/-- Pluecker bivector of the explicit source vector and dual-coordinate vector. -/
def incidentPlucker (Z : Vec4) (W : Module.Dual ℝ Vec4) : Bivector4 :=
  wedgeVec4 Z (dualVec4Coordinates W)

/-- The explicit Pluecker bivector lies on the Klein quadric by the wedge theorem. -/
theorem incidentPlucker_on_klein (Z : Vec4) (W : Module.Dual ℝ Vec4) :
    IsOnKleinQuadric (incidentPlucker Z W) := by
  unfold incidentPlucker
  exact wedgeVec4_on_klein Z (dualVec4Coordinates W)

/-- The Klein area defect of the explicit Pluecker bivector vanishes. -/
theorem kleinAreaDefect_incidentPlucker_eq_zero
    (Z : Vec4) (W : Module.Dual ℝ Vec4) :
    kleinAreaDefect (incidentPlucker Z W) = 0 :=
  kleinAreaDefect_eq_zero_of_on_klein
    (incidentPlucker Z W) (incidentPlucker_on_klein Z W)

/-- Explicit Euclidean residual square on `Vec4`; used only as a nonnegative defect. -/
def vec4EuclideanSq (v : Vec4) : ℝ :=
  v I4.t ^ 2 + v I4.x ^ 2 + v I4.y ^ 2 + v I4.z ^ 2

/-- The explicit residual square is nonnegative. -/
theorem vec4EuclideanSq_nonneg (v : Vec4) :
    0 ≤ vec4EuclideanSq v := by
  unfold vec4EuclideanSq
  nlinarith [sq_nonneg (v I4.t), sq_nonneg (v I4.x),
    sq_nonneg (v I4.y), sq_nonneg (v I4.z)]

/-- Explicit residual-square boundary friction. -/
def boundaryMajoranaFriction
    (Z : Vec4)
    (Pboundary Pzero J Dboundary : Vec4 →ₗ[ℝ] Vec4) : ℝ :=
  vec4EuclideanSq (vsub (Pboundary Z) Z)
    + vec4EuclideanSq (vsub (Pzero Z) Z)
    + vec4EuclideanSq (vsub (J Z) Z)
    + vec4EuclideanSq (Dboundary Z)

/-- The explicit boundary friction is nonnegative. -/
theorem boundaryMajoranaFriction_nonneg
    (Z : Vec4)
    (Pboundary Pzero J Dboundary : Vec4 →ₗ[ℝ] Vec4) :
    0 ≤ boundaryMajoranaFriction Z Pboundary Pzero J Dboundary := by
  unfold boundaryMajoranaFriction
  nlinarith [vec4EuclideanSq_nonneg (vsub (Pboundary Z) Z),
    vec4EuclideanSq_nonneg (vsub (Pzero Z) Z),
    vec4EuclideanSq_nonneg (vsub (J Z) Z),
    vec4EuclideanSq_nonneg (Dboundary Z)]

/-- A boundary Majorana predicate gives zero explicit residual-square friction. -/
theorem boundaryMajoranaFriction_eq_zero_of_boundaryMajorana
    {Z : Vec4}
    {Pboundary Pzero J Dboundary : Vec4 →ₗ[ℝ] Vec4}
    (h : IsBoundaryMajoranaFlag Z Pboundary Pzero J Dboundary) :
    boundaryMajoranaFriction Z Pboundary Pzero J Dboundary = 0 := by
  rcases h with ⟨hP, h0, hJ, hD⟩
  unfold boundaryMajoranaFriction vec4EuclideanSq vsub
  rw [hP, h0, hJ, hD]
  simp

/-- Symmetry of the explicit Minkowski pairing. -/
theorem minkowskiDot_comm (X Y : Vec4) :
    minkowskiDot X Y = minkowskiDot Y X := by
  unfold minkowskiDot
  ring

/-- Explicit metric/stress readout attached to incident-boundary arguments. -/
def incidentStressTensor
    (_Z : Vec4)
    (_Pboundary _Pzero _J _Dboundary : Vec4 →ₗ[ℝ] Vec4) :
    Vec4 → Vec4 → ℝ :=
  minkowskiDot

/-- The explicit metric/stress readout is symmetric. -/
theorem incidentStressTensor_swap
    (Z : Vec4)
    (Pboundary Pzero J Dboundary : Vec4 →ₗ[ℝ] Vec4)
    (X Y : Vec4) :
    incidentStressTensor Z Pboundary Pzero J Dboundary X Y =
      incidentStressTensor Z Pboundary Pzero J Dboundary Y X :=
  minkowskiDot_comm X Y

end InfoGeometry.Physics.IncidentNullFlagStress
