import InfoGeometry.Topology.DiscreteDiracHodge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Pairing bridge for the finite discrete Dirac--Hodge carrier

The discrete owner represents the codifferential by transposed incidence
matrices.  This file records the corresponding Euclidean pairing identity,
using the reusable transpose/mulVec lemma from `EckmannDiscreteHodge`.
-/

namespace InfoGeometry.Topology.DiscreteDiracHodge

open InfoGeometry.Topology.EckmannDiscreteHodge

noncomputable section

variable {n0 n1 n2 : ℕ}

/-- The direct-sum Euclidean pairing on finite total forms. -/
def totalFormPairing (x y : TotalForm n0 n1 n2) : ℝ :=
  eckmannDot x.zero y.zero + eckmannDot x.one y.one + eckmannDot x.two y.two

/-- The matrix-transpose codifferential is the adjoint of the exterior
    derivative for the direct-sum Euclidean pairing. -/
theorem totalFormPairing_exteriorDerivative
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (x y : TotalForm n0 n1 n2) :
    totalFormPairing (exteriorDerivative d0 d1 x) y =
      totalFormPairing x (codifferential d0 d1 y) := by
  unfold totalFormPairing exteriorDerivative codifferential
  simp only [eckmannDot_zero_left, eckmannDot_zero_right, zero_add,
    add_zero]
  rw [eckmannDot_mulVec_transpose, eckmannDot_mulVec_transpose]

/-! The reverse adjoint readout is useful when expanding the discrete Hodge
    Laplacian.  It is derived from the same pairing, rather than introduced
    as a second independent convention. -/

theorem totalFormPairing_codifferential
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (x y : TotalForm n0 n1 n2) :
    totalFormPairing (codifferential d0 d1 x) y =
      totalFormPairing x (exteriorDerivative d0 d1 y) := by
  simpa only [totalFormPairing, eckmannDot_comm, add_comm, add_left_comm,
    add_assoc] using (totalFormPairing_exteriorDerivative d0 d1 y x).symm

theorem totalFormPairing_add_left
    (x y z : TotalForm n0 n1 n2) :
    totalFormPairing (x + y) z = totalFormPairing x z + totalFormPairing y z := by
  simp [totalFormPairing, eckmannDot, Finset.sum_add_distrib, add_mul,
    add_assoc, add_left_comm]

theorem totalFormPairing_add_right
    (x y z : TotalForm n0 n1 n2) :
    totalFormPairing x (y + z) = totalFormPairing x y + totalFormPairing x z := by
  simp [totalFormPairing, eckmannDot, Finset.sum_add_distrib, mul_add,
    add_assoc, add_left_comm]

/-! The discrete Hodge Laplacian is self-adjoint for the same pairing. -/

theorem totalFormPairing_hodgeLaplacian
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (x y : TotalForm n0 n1 n2) :
    totalFormPairing (hodgeLaplacian d0 d1 x) y =
      totalFormPairing x (hodgeLaplacian d0 d1 y) := by
  unfold hodgeLaplacian
  rw [totalFormPairing_add_left, totalFormPairing_add_right]
  rw [totalFormPairing_exteriorDerivative,
    totalFormPairing_codifferential,
    totalFormPairing_codifferential,
    totalFormPairing_exteriorDerivative]

theorem totalFormPairing_hodgeLaplacian_self_nonneg
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (x : TotalForm n0 n1 n2) :
    0 ≤ totalFormPairing (hodgeLaplacian d0 d1 x) x := by
  unfold hodgeLaplacian
  rw [totalFormPairing_add_left,
    totalFormPairing_exteriorDerivative]
  have hcod := totalFormPairing_codifferential d0 d1
    (exteriorDerivative d0 d1 x) x
  rw [hcod]
  unfold totalFormPairing
  exact add_nonneg
    (add_nonneg (add_nonneg (eckmannDot_self_nonneg _)
      (eckmannDot_self_nonneg _)) (eckmannDot_self_nonneg _))
    (add_nonneg (add_nonneg (eckmannDot_self_nonneg _)
      (eckmannDot_self_nonneg _)) (eckmannDot_self_nonneg _))

end

end InfoGeometry.Topology.DiscreteDiracHodge
