import InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Negative Clifford generators on the existing three-mode exterior carrier

Creation minus contraction squares to the negative Euclidean quadratic form.
The resulting map is lifted with Mathlib's actual Clifford universal property.
Unit vectors give invertible reflection operators, and their twisted action is
proved to be the plane reflection. This is the local algebra underlying Pin-minus,
not a construction of a Pin principal bundle or an antiunitary time reversal.
-/

noncomputable section

namespace InfoGeometry.Clifford.ExteriorNegativeCliffordReflection

open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge
open scoped BigOperators

/-- Euclidean pairing on the existing three-dimensional generating space. -/
def dotBilin : LinearMap.BilinForm ℝ V3 :=
  LinearMap.mk₂ ℝ (fun v w => ∑ i, v i * w i)
    (by intros; simp [add_mul, Finset.sum_add_distrib])
    (by intros; simp [mul_assoc, Finset.mul_sum])
    (by intros; simp [mul_add, Finset.sum_add_distrib])
    (by intros; simp [mul_left_comm, Finset.mul_sum])

@[simp] theorem dotBilin_apply (v w : V3) : dotBilin v w = ∑ i, v i * w i := rfl

theorem dotBilin_symm (v w : V3) : dotBilin v w = dotBilin w v := by
  simp [dotBilin_apply, mul_comm]

/-- The negative-definite quadratic form, as a native Mathlib quadratic form. -/
def negativeQuadratic : QuadraticForm ℝ V3 := -dotBilin.toQuadraticMap

@[simp] theorem negativeQuadratic_apply (v : V3) :
    negativeQuadratic v = -dotBilin v v := rfl

/-- Odd Clifford operator: creation minus annihilation, on the original exterior algebra. -/
def gamma : V3 →ₗ[ℝ] Exterior3End where
  toFun v := exteriorWedge3 v - exteriorContract3 (dotBilin v)
  map_add' v w := by
    apply LinearMap.ext
    intro ψ
    simp [exteriorWedge3, exteriorContract3, map_add, add_mul] <;> module
  map_smul' r v := by
    apply LinearMap.ext
    intro ψ
    simp [exteriorWedge3, exteriorContract3, map_smul, smul_mul_assoc,
      smul_sub]

@[simp] theorem gamma_apply (v : V3) :
    gamma v = exteriorWedge3 v - exteriorContract3 (dotBilin v) := rfl

/-- The negative square law is derived from the pre-existing exterior CAR. -/
theorem gamma_sq (v : V3) : gamma v * gamma v = (-dotBilin v v) • (1 : Exterior3End) := by
  calc
    _ = -(exteriorContract3 (dotBilin v) * exteriorWedge3 v +
        exteriorWedge3 v * exteriorContract3 (dotBilin v)) := by
      simp only [gamma_apply, sub_mul, mul_sub, exteriorWedge3_sq, exteriorContract3_sq]
      abel
    _ = _ := by rw [exteriorContract3_wedge3_CAR]; simp

/-- The complete associative negative Clifford algebra acts on the exterior carrier. -/
def negativeCliffordRep : CliffordAlgebra negativeQuadratic →ₐ[ℝ] Exterior3End :=
  CliffordAlgebra.lift negativeQuadratic ⟨gamma, by
    intro v
    rw [gamma_sq, negativeQuadratic_apply, Algebra.algebraMap_eq_smul_one]⟩

@[simp] theorem negativeCliffordRep_ι (v : V3) :
    negativeCliffordRep (CliffordAlgebra.ι negativeQuadratic v) = gamma v := by
  exact CliffordAlgebra.lift_ι_apply _ _ _

/-- Polarization of the square law gives all negative-sign Clifford relations. -/
theorem gamma_anticommutator (v w : V3) :
    gamma v * gamma w + gamma w * gamma v =
      (-2 * dotBilin v w) • (1 : Exterior3End) := by
  calc
    _ = gamma (v + w) * gamma (v + w) - gamma v * gamma v - gamma w * gamma w := by
      rw [map_add]
      noncomm_ring
    _ = _ := by
      rw [gamma_sq, gamma_sq, gamma_sq]
      simp only [map_add, LinearMap.add_apply]
      rw [dotBilin_symm w v]
      module

/-- Plane reflection in a unit normal, before passing to operators. -/
def planeReflection (n v : V3) : V3 := v - (2 * dotBilin n v) • n

/-- The sandwich is exactly the twisted Pin-minus reflection, not a rotation. -/
theorem gamma_reflection (n v : V3) (hn : dotBilin n n = 1) :
    gamma n * gamma v * gamma n = gamma (planeReflection n v) := by
  have hswap : gamma n * gamma v =
      (-2 * dotBilin n v) • (1 : Exterior3End) - gamma v * gamma n :=
    eq_sub_of_add_eq (gamma_anticommutator n v)
  rw [hswap, sub_mul, smul_mul_assoc, one_mul, mul_assoc, gamma_sq, hn]
  simp only [planeReflection, map_sub, map_smul]
  simp <;> module

/-- A unit normal gives an actual unit of the operator algebra, with inverse minus itself. -/
def reflectionUnit (n : V3) (hn : dotBilin n n = 1) : Exterior3Endˣ where
  val := gamma n
  inv := -gamma n
  val_inv := by rw [mul_neg, gamma_sq, hn]; simp
  inv_val := by rw [neg_mul, gamma_sq, hn]; simp

@[simp] theorem reflectionUnit_sq (n : V3) (hn : dotBilin n n = 1) :
    (reflectionUnit n hn : Exterior3End) * reflectionUnit n hn = -1 := by
  change gamma n * gamma n = -1
  rw [gamma_sq, hn]
  simp

/-- Exterior parity changes sign on every Clifford vector. -/
theorem gamma_odd (v : V3) (ψ : Exterior3) :
    exteriorGrade3 (gamma v ψ) = -(gamma v (exteriorGrade3 ψ)) := by
  change exteriorGrade3 (exteriorWedge3 v ψ - exteriorContract3 (dotBilin v) ψ) = _
  rw [map_sub, exteriorGrade3_wedge, exteriorGrade3_contract]
  simp [gamma, sub_eq_add_neg]
  abel

/-- Products of two vectors preserve parity, giving the even spin-operator layer. -/
theorem gamma_pair_even (v w : V3) (ψ : Exterior3) :
    exteriorGrade3 ((gamma v * gamma w) ψ) =
      (gamma v * gamma w) (exteriorGrade3 ψ) := by
  simp only [Module.End.mul_apply, gamma_odd, map_neg, neg_neg]

/-- Orthogonal unit normals produce a square-minus-one lifted half-turn. -/
theorem bivector_sq (v w : V3) (hv : dotBilin v v = 1)
    (hw : dotBilin w w = 1) (hvw : dotBilin v w = 0) :
    (gamma v * gamma w) * (gamma v * gamma w) = -1 := by
  have hanti : gamma w * gamma v = -(gamma v * gamma w) := by
    have h := gamma_anticommutator v w
    rw [hvw, mul_zero, zero_smul] at h
    exact eq_neg_of_add_eq_zero_right h
  calc
    _ = gamma v * (gamma w * gamma v) * gamma w := by noncomm_ring
    _ = -(gamma v * gamma v * (gamma w * gamma w)) := by rw [hanti]; noncomm_ring
    _ = -1 := by rw [gamma_sq, gamma_sq, hv, hw]; simp

end InfoGeometry.Clifford.ExteriorNegativeCliffordReflection
