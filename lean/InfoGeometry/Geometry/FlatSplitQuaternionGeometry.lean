import InfoGeometry.Clifford.SplitAtomInvolutions
import Mathlib.LinearAlgebra.BilinearForm.Basic

/-!
# A four-dimensional neutral model and its alternating forms

The tangent model is the four-dimensional regular module M₂(ℝ), not the
real two-dimensional spinor module.  The metric is the polarization of det.
The forms g(I·,·), g(J·,·), g(K·,·) are alternating and nondegenerate.  None
is an Onsager positive metric.  This file is linear algebra; it does not
assert a Levi-Civita connection, a holonomy theorem, or a curvature theorem.
-/

noncomputable section

namespace InfoGeometry.Geometry.FlatSplitQuaternion

open InfoGeometry.Clifford.SplitAtom

private def metricValue (A B : Mat2) : ℝ :=
  (A 0 0 * B 1 1 + A 1 1 * B 0 0 - A 0 1 * B 1 0 - A 1 0 * B 0 1) / 2

/-- The native bilinear polarization of the determinant. -/
def metric : LinearMap.BilinForm ℝ Mat2 where
  toFun A :=
    { toFun := metricValue A
      map_add' B C := by
        simp [metricValue, Matrix.add_apply]; ring
      map_smul' r B := by
        simp [metricValue, Matrix.smul_apply]; ring }
  map_add' A B := by
    ext C
    simp [metricValue, Matrix.add_apply]; ring
  map_smul' r A := by
    ext B
    simp [metricValue, Matrix.smul_apply]; ring

@[simp] theorem metric_apply (A B : Mat2) :
    metric A B =
      (A 0 0 * B 1 1 + A 1 1 * B 0 0 - A 0 1 * B 1 0 - A 1 0 * B 0 1) / 2 := rfl

theorem metric_symm (A B : Mat2) : metric A B = metric B A := by
  simp only [metric_apply]; ring

theorem metric_self (A : Mat2) : metric A A = A.det := by
  simp [Matrix.det_fin_two]; ring

/-- In the split-quaternion coordinates, the metric is diag(1,1,-1,-1). -/
theorem metric_signature_formula (a b c d : ℝ) :
    metric (a • 1 + b • I + c • J + d • K)
      (a • 1 + b • I + c • J + d • K) = a ^ 2 + b ^ 2 - c ^ 2 - d ^ 2 := by
  simp [I, J, K, InfoGeometry.Clifford.Cl11Matrix.Eminus,
    InfoGeometry.Clifford.Cl11Matrix.Eplus, InfoGeometry.Clifford.Cl11Matrix.J1]
  ring

theorem metric_left_nondegenerate (A : Mat2)
    (h : ∀ B : Mat2, metric A B = 0) : A = 0 := by
  have h1 := h 1
  have hI := h I
  have hJ := h J
  have hK := h K
  simp [I, J, K, InfoGeometry.Clifford.Cl11Matrix.Eminus,
    InfoGeometry.Clifford.Cl11Matrix.Eplus,
    InfoGeometry.Clifford.Cl11Matrix.J1] at h1 hI hJ hK
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.zero_apply] <;> linarith

/-- Left multiplication is a native linear endomorphism. -/
def leftAction (u : Mat2) : Module.End ℝ Mat2 where
  toFun A := u * A
  map_add' A B := mul_add u A B
  map_smul' r A := mul_smul_comm r u A

@[simp] theorem leftAction_apply (u A : Mat2) : leftAction u A = u * A := rfl

theorem metric_left_scaling (u A B : Mat2) :
    metric (u * A) (u * B) = u.det * metric A B := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two]
  ring

theorem metric_I (A B : Mat2) : metric (I * A) (I * B) = metric A B := by
  rw [metric_left_scaling]
  norm_num [I, InfoGeometry.Clifford.Cl11Matrix.Eminus, Matrix.det_fin_two]

theorem metric_J (A B : Mat2) : metric (J * A) (J * B) = -metric A B := by
  rw [metric_left_scaling]
  norm_num [J, InfoGeometry.Clifford.Cl11Matrix.Eplus, Matrix.det_fin_two]

theorem metric_K (A B : Mat2) : metric (K * A) (K * B) = -metric A B := by
  rw [metric_left_scaling]
  norm_num [K, InfoGeometry.Clifford.Cl11Matrix.J1, Matrix.det_fin_two]

/-- Precomposition of the first slot by an actual linear endomorphism. -/
def omega (u : Mat2) : LinearMap.BilinForm ℝ Mat2 := metric.comp (leftAction u)

@[simp] theorem omega_apply (u A B : Mat2) : omega u A B = metric (u * A) B := rfl

theorem omega_I_alternating (A : Mat2) : omega I A A = 0 := by
  simp [I, InfoGeometry.Clifford.Cl11Matrix.Eminus,
    Matrix.mul_apply, Fin.sum_univ_two]; ring

theorem omega_J_alternating (A : Mat2) : omega J A A = 0 := by
  simp [J, InfoGeometry.Clifford.Cl11Matrix.Eplus,
    Matrix.mul_apply, Fin.sum_univ_two]; ring

theorem omega_K_alternating (A : Mat2) : omega K A A = 0 := by
  simp [K, InfoGeometry.Clifford.Cl11Matrix.J1,
    Matrix.mul_apply, Fin.sum_univ_two]; ring

theorem omega_nondegenerate_of_left_inverse (u v : Mat2) (hvu : v * u = 1)
    (A : Mat2) (h : ∀ B : Mat2, omega u A B = 0) : A = 0 := by
  have huA : u * A = 0 := metric_left_nondegenerate (u * A) h
  calc
    A = (v * u) * A := by rw [hvu]; simp
    _ = v * (u * A) := mul_assoc _ _ _
    _ = 0 := by rw [huA, mul_zero]

theorem omega_I_nondegenerate (A : Mat2)
    (h : ∀ B : Mat2, omega I A B = 0) : A = 0 :=
  omega_nondegenerate_of_left_inverse I (-I) (by simp) A h

theorem omega_J_nondegenerate (A : Mat2)
    (h : ∀ B : Mat2, omega J A B = 0) : A = 0 :=
  omega_nondegenerate_of_left_inverse J J J_sq A h

theorem omega_K_nondegenerate (A : Mat2)
    (h : ∀ B : Mat2, omega K A B = 0) : A = 0 :=
  omega_nondegenerate_of_left_inverse K K K_sq A h

/-- The K-form is not a symmetric dissipative tensor. -/
theorem omega_K_not_symmetric : ¬ ∀ A B : Mat2, omega K A B = omega K B A := by
  intro h
  have h1K := h 1 K
  norm_num [K, InfoGeometry.Clifford.Cl11Matrix.J1,
    Matrix.mul_apply, Fin.sum_univ_two] at h1K

/-- On the 2D spinor module no nonzero symmetric compatible metric exists. -/
theorem two_dimensional_metric_obstruction (G : Mat2)
    (hSymm : Gᵀ = G) (hI : Iᵀ * G * I = G) (hJ : Jᵀ * G * J = -G) :
    G = 0 := by
  have h00 := congrArg (fun A : Mat2 => A 0 0) hJ
  have h11 := congrArg (fun A : Mat2 => A 1 1) hJ
  have h01 := congrArg (fun A : Mat2 => A 0 1) hI
  have h10 := congrArg (fun A : Mat2 => A 0 1) hSymm
  simp [I, J, InfoGeometry.Clifford.Cl11Matrix.Eminus,
    InfoGeometry.Clifford.Cl11Matrix.Eplus,
    Matrix.mul_apply, Fin.sum_univ_two] at h00 h11 h01 h10
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.zero_apply] <;> linarith

end InfoGeometry.Geometry.FlatSplitQuaternion
