import InfoGeometry.Lie.SplitOctonionEllFlowOperator
import InfoGeometry.Lie.SplitOctonionEllClosedFlow

/-!
# Quaternionic `(4+4)` coordinates and the canonical Zorn carrier

This owner formalizes the real linear change of coordinates

`((q₀,q),(r₀,r)) ↦ (q₀+r₀, q₀-r₀, q+r, r-q)`

between two quaternion-coordinate copies and the canonical Zorn carrier.  It
proves the inverse formulas, the exact difference-of-quaternion-norm identity,
and the two flow readouts from the same coordinate equivalence:

* the normalized `ell` commutator is exchange of the two imaginary
  quaternionic triples while killing their scalar coordinates;
* the closed diagonal Zorn flow is the circular-coordinate form of three
  simultaneous real hyperbolic rotations between those triples.

No second split-octonion multiplication is introduced.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates

open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Lie.SplitOctonionEllClosedFlow
open InfoGeometry.Lie.SplitOctonionEllFlowOperator

abbrev Vec3 := Fin 3 → ℝ
abbrev QuaternionCoordinates := ℝ × Vec3
abbrev CartesianCoordinates := QuaternionCoordinates × QuaternionCoordinates
abbrev CZ := CanonicalZorn

/-- Euclidean quaternion norm in scalar/vector coordinates. -/
def quaternionNorm (q : QuaternionCoordinates) : ℝ :=
  q.1 ^ 2 + dot q.2 q.2

/-- The circular/Witt coordinate transformation from `(4+4)` quaternion
coordinates to `(1+1+3+3)` Zorn coordinates. -/
def cartesianZornLinearEquiv : CartesianCoordinates ≃ₗ[ℝ] CZ where
  toFun qr :=
    { a := qr.1.1 + qr.2.1
      b := qr.1.1 - qr.2.1
      x := qr.1.2 + qr.2.2
      y := qr.2.2 - qr.1.2 }
  invFun Z :=
    (((Z.a + Z.b) / 2, (Z.x - Z.y) / 2),
      ((Z.a - Z.b) / 2, (Z.x + Z.y) / 2))
  left_inv qr := by
    rcases qr with ⟨⟨q0, q⟩, ⟨r0, r⟩⟩
    apply Prod.ext
    · apply Prod.ext
      · dsimp
        ring
      · funext i
        simp
        ring
    · apply Prod.ext
      · dsimp
        ring
      · funext i
        simp
        ring
  right_inv Z := by
    ext i <;> simp <;> ring
  map_add' X Y := by
    ext i <;> simp <;> ring
  map_smul' c X := by
    ext i <;> simp [Equiv.smul_def, coordEquiv, smul_eq_mul] <;> ring

@[simp] theorem cartesianZornLinearEquiv_apply
    (qr : CartesianCoordinates) :
    cartesianZornLinearEquiv qr =
      { a := qr.1.1 + qr.2.1
        b := qr.1.1 - qr.2.1
        x := qr.1.2 + qr.2.2
        y := qr.2.2 - qr.1.2 } := rfl

@[simp] theorem cartesianZornLinearEquiv_symm_apply (Z : CZ) :
    cartesianZornLinearEquiv.symm Z =
      (((Z.a + Z.b) / 2, (Z.x - Z.y) / 2),
        ((Z.a - Z.b) / 2, (Z.x + Z.y) / 2)) := rfl

/-- Exact transport of the native `(4,4)` determinant to the difference of
the two Euclidean quaternion norms. -/
theorem detZ_cartesianZornLinearEquiv (qr : CartesianCoordinates) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
        (cartesianZornLinearEquiv qr) =
      quaternionNorm qr.1 - quaternionNorm qr.2 := by
  rcases qr with ⟨⟨q0, q⟩, ⟨r0, r⟩⟩
  simp [InfoGeometry.Algebra.Zorn.ZornMatrix.detZ, quaternionNorm, dot,
    Fin.sum_univ_three]
  ring

/-- The normalized `ell` commutator in Cartesian coordinates: it kills the
two scalar directions and exchanges the two imaginary quaternion triples. -/
def cartesianEllGrading :
    CartesianCoordinates →ₗ[ℝ] CartesianCoordinates where
  toFun qr := ((0, qr.2.2), (0, qr.1.2))
  map_add' X Y := by
    apply Prod.ext <;> apply Prod.ext <;> simp
  map_smul' c X := by
    apply Prod.ext <;> apply Prod.ext <;> simp

@[simp] theorem cartesianEllGrading_apply (qr : CartesianCoordinates) :
    cartesianEllGrading qr = ((0, qr.2.2), (0, qr.1.2)) := rfl

/-- The circular/Zorn coordinate equivalence conjugates Cartesian exchange to
the native tripotent `ell` grading. -/
theorem cartesianZorn_intertwines_ellGrading
    (qr : CartesianCoordinates) :
    cartesianZornLinearEquiv (cartesianEllGrading qr) =
      diagEllGrading (cartesianZornLinearEquiv qr) := by
  rw [diagEllGrading_coord]
  ext i <;> simp [cartesianEllGrading] <;> ring

/-- Bundled operator form of the exact conjugacy: the circular coordinate
equivalence diagonalizes Cartesian exchange into the native ell grading. -/
theorem cartesianZorn_ellGrading_conjugacy :
    cartesianZornLinearEquiv.toLinearMap.comp cartesianEllGrading =
      diagEllGrading.comp cartesianZornLinearEquiv.toLinearMap := by
  apply LinearMap.ext
  intro qr
  exact cartesianZorn_intertwines_ellGrading qr

/-- Readback of the same conjugacy on arbitrary Zorn coordinates. -/
theorem cartesian_ellGrading_readback (Z : CZ) :
    cartesianEllGrading (cartesianZornLinearEquiv.symm Z) =
      cartesianZornLinearEquiv.symm (diagEllGrading Z) := by
  apply cartesianZornLinearEquiv.injective
  calc
    cartesianZornLinearEquiv
          (cartesianEllGrading (cartesianZornLinearEquiv.symm Z)) =
        diagEllGrading
          (cartesianZornLinearEquiv (cartesianZornLinearEquiv.symm Z)) :=
      cartesianZorn_intertwines_ellGrading _
    _ = diagEllGrading Z := by rw [cartesianZornLinearEquiv.apply_symm_apply]
    _ = cartesianZornLinearEquiv
          (cartesianZornLinearEquiv.symm (diagEllGrading Z)) := by
      rw [cartesianZornLinearEquiv.apply_symm_apply]

/-- Three simultaneous hyperbolic rotations of the quaternionic vector
coordinates, with both scalar coordinates fixed. -/
def cartesianHyperbolicFlow (t : ℝ) :
    CartesianCoordinates →ₗ[ℝ] CartesianCoordinates where
  toFun qr :=
    ((qr.1.1, Real.cosh t • qr.1.2 + Real.sinh t • qr.2.2),
      (qr.2.1, Real.sinh t • qr.1.2 + Real.cosh t • qr.2.2))
  map_add' X Y := by
    apply Prod.ext <;> apply Prod.ext
    · simp
    · funext i
      simp [smul_eq_mul]
      ring
    · simp
    · funext i
      simp [smul_eq_mul]
      ring
  map_smul' c X := by
    apply Prod.ext <;> apply Prod.ext
    · simp
    · funext i
      simp [smul_eq_mul]
      ring
    · simp
    · funext i
      simp [smul_eq_mul]
      ring

@[simp] theorem cartesianHyperbolicFlow_apply
    (t : ℝ) (qr : CartesianCoordinates) :
    cartesianHyperbolicFlow t qr =
      ((qr.1.1, Real.cosh t • qr.1.2 + Real.sinh t • qr.2.2),
        (qr.2.1, Real.sinh t • qr.1.2 + Real.cosh t • qr.2.2)) := rfl

/-- In circular/Zorn coordinates the Cartesian hyperbolic rotation is exactly
the opposite-weight closed `ell` flow. -/
theorem cartesianZorn_intertwines_closedFlow
    (t : ℝ) (qr : CartesianCoordinates) :
    cartesianZornLinearEquiv (cartesianHyperbolicFlow t qr) =
      ellFlowPhi t (cartesianZornLinearEquiv qr) := by
  rw [ellFlowPhi_coord]
  ext i
  · simp [cartesianHyperbolicFlow]
  · simp [cartesianHyperbolicFlow]
  · simp [cartesianHyperbolicFlow, smul_eq_mul]
    rw [← Real.cosh_add_sinh]
    ring
  · simp [cartesianHyperbolicFlow, smul_eq_mul]
    rw [← Real.cosh_sub_sinh]
    ring

/-- Bundled operator form of the closed-flow conjugacy. -/
theorem cartesianZorn_closedFlow_conjugacy (t : ℝ) :
    cartesianZornLinearEquiv.toLinearMap.comp (cartesianHyperbolicFlow t) =
      (ellFlowPhi t).comp cartesianZornLinearEquiv.toLinearMap := by
  apply LinearMap.ext
  intro qr
  exact cartesianZorn_intertwines_closedFlow t qr

/-- Readback of the closed flow on arbitrary Zorn coordinates. -/
theorem cartesian_closedFlow_readback (t : ℝ) (Z : CZ) :
    cartesianHyperbolicFlow t (cartesianZornLinearEquiv.symm Z) =
      cartesianZornLinearEquiv.symm (ellFlowPhi t Z) := by
  apply cartesianZornLinearEquiv.injective
  calc
    cartesianZornLinearEquiv
          (cartesianHyperbolicFlow t (cartesianZornLinearEquiv.symm Z)) =
        ellFlowPhi t
          (cartesianZornLinearEquiv (cartesianZornLinearEquiv.symm Z)) :=
      cartesianZorn_intertwines_closedFlow _ _
    _ = ellFlowPhi t Z := by rw [cartesianZornLinearEquiv.apply_symm_apply]
    _ = cartesianZornLinearEquiv
          (cartesianZornLinearEquiv.symm (ellFlowPhi t Z)) := by
      rw [cartesianZornLinearEquiv.apply_symm_apply]

/-- The Cartesian hyperbolic flow preserves the difference of quaternion
norms, inherited through the exact native Zorn determinant identity. -/
theorem cartesianHyperbolicFlow_preserves_normDifference
    (t : ℝ) (qr : CartesianCoordinates) :
    quaternionNorm (cartesianHyperbolicFlow t qr).1 -
        quaternionNorm (cartesianHyperbolicFlow t qr).2 =
      quaternionNorm qr.1 - quaternionNorm qr.2 := by
  rw [← detZ_cartesianZornLinearEquiv,
    cartesianZorn_intertwines_closedFlow,
    ellFlowPhi_preserves_det,
    detZ_cartesianZornLinearEquiv]

end InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates
