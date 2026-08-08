import InfoGeometry.Canonical.QuaternionCondensate
import InfoGeometry.Clifford.DiracPauliGamma
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Star.Basic

noncomputable section

namespace InfoGeometry.Canonical.CartanInvolution

open Complex
open InfoGeometry.Canonical.QuaternionCondensate
open InfoGeometry.Clifford.DiracPauliGamma

/-!
# Quaternion Cartan Decomposition Witness

This file records the finite matrix-side Cartan/involution property for the
quaternion condensate lane.

The intended reading is not a literal universal embedding theorem.  Instead,
the explicit `4x4` matrices property the compact / noncompact split induced by
the Cartan involution, and the associated finite projection layer is the
matrix-side shadow of the `OP^3 = OP` decomposition story.

The file only proves the quaternion basis relations and the finite matrix
projection property.  It does not prove a universal algebra equivalence
`ℍ ≃ Cl(0,2)` and does not prove a full `Cl(1,3; ℂ)` embedding theorem.
-/

/-- The Dirac Gamma Matrices in 4x4 representation -/
abbrev DiracMatrix := Matrix (Fin 4) (Fin 4) ℂ

/-- Cartan Involution θ(X) on the Clifford Algebra.
    We define the involution via the time-like reflection γ⁰ X γ⁰.
    For spatial bivectors, this acts as the identity, extracting the 
    maximal compact subalgebra 𝔨. -/
def cartan_involution (gamma0 : DiracMatrix) (X : DiracMatrix) : DiracMatrix :=
  gamma0 * X * gamma0

/-- Matrix identity element used as the image of quaternion `1`. -/
abbrev embedOne : DiracMatrix := 1

 /-- Projection onto the compact subalgebra 𝔨. -/
def compact_projection (gamma0 X : DiracMatrix) : DiracMatrix :=
  (2 : ℂ)⁻¹ • (X + cartan_involution gamma0 X)

/-- Image of quaternion `i` as the spatial bivector `gamma1 * gamma2`. -/
def embedI : DiracMatrix := gamma1 * gamma2

/-- Image of quaternion `j` as the spatial bivector `gamma2 * gamma3`. -/
def embedJ : DiracMatrix := gamma2 * gamma3

/-- Image of quaternion `k` as the spatial bivector `gamma3 * gamma1`. -/
def embedK : DiracMatrix := gamma3 * gamma1

/-- Linear component map from the finite `H4` carrier into `4x4` complex matrices. -/
def embedH4 (q : H4) : DiracMatrix :=
  (q.re : ℂ) • embedOne +
    (q.imI : ℂ) • embedI +
      (q.imJ : ℂ) • embedJ +
        (q.imK : ℂ) • embedK

@[simp] theorem cartan_involution_i : cartan_involution gamma0 embedI = embedI := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [cartan_involution, embedI, gamma0, gamma1, gamma2, Matrix.mul_apply, Fin.sum_univ_succ]

@[simp] theorem cartan_involution_j : cartan_involution gamma0 embedJ = embedJ := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [cartan_involution, embedJ, gamma0, gamma2, gamma3, Matrix.mul_apply, Fin.sum_univ_succ]

@[simp] theorem cartan_involution_k : cartan_involution gamma0 embedK = embedK := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [cartan_involution, embedK, gamma0, gamma1, gamma3, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The boost generators (e.g. gamma0 * gamma1) are in the non-compact subspace 𝔭. -/
@[simp] theorem cartan_involution_boost : cartan_involution gamma0 (gamma0 * gamma1) = -(gamma0 * gamma1) := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [cartan_involution, gamma0, gamma1, Matrix.mul_apply, Fin.sum_univ_succ]

@[simp] theorem embedI_sq : embedI * embedI = -embedOne := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [embedI, embedOne, gamma1, gamma2, Matrix.mul_apply, Fin.sum_univ_succ]

@[simp] theorem embedJ_sq : embedJ * embedJ = -embedOne := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [embedJ, embedOne, gamma2, gamma3, Matrix.mul_apply, Fin.sum_univ_succ]

@[simp] theorem embedK_sq : embedK * embedK = -embedOne := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [embedK, embedOne, gamma1, gamma3, Matrix.mul_apply, Fin.sum_univ_succ]

@[simp] theorem embedI_mul_embedJ : embedI * embedJ = embedK := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [embedI, embedJ, embedK, gamma1, gamma2, gamma3, Matrix.mul_apply, Fin.sum_univ_succ]

@[simp] theorem embedJ_mul_embedK : embedJ * embedK = embedI := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [embedI, embedJ, embedK, gamma1, gamma2, gamma3, Matrix.mul_apply, Fin.sum_univ_succ]

@[simp] theorem embedK_mul_embedI : embedK * embedI = embedJ := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [embedI, embedJ, embedK, gamma1, gamma2, gamma3, Matrix.mul_apply, Fin.sum_univ_succ]

@[simp] theorem embedJ_mul_embedI : embedJ * embedI = -embedK := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [embedI, embedJ, embedK, gamma1, gamma2, gamma3, Matrix.mul_apply, Fin.sum_univ_succ]

@[simp] theorem embedK_mul_embedJ : embedK * embedJ = -embedI := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [embedI, embedJ, embedK, gamma1, gamma2, gamma3, Matrix.mul_apply, Fin.sum_univ_succ]

@[simp] theorem embedI_mul_embedK : embedI * embedK = -embedJ := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [embedI, embedJ, embedK, gamma1, gamma2, gamma3, Matrix.mul_apply, Fin.sum_univ_succ]

@[simp] theorem embedI_mul_embedJ_mul_embedK :
    (embedI * embedJ) * embedK = -embedOne := by
  rw [embedI_mul_embedJ, embedK_sq]

@[simp] theorem embedH4_one : embedH4 H4.one = embedOne := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [embedH4, embedOne, H4.one, embedI, embedJ, embedK]

@[simp] theorem embedH4_i : embedH4 H4.i = embedI := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [embedH4, H4.i, embedI, embedOne, embedJ, embedK]

@[simp] theorem embedH4_j : embedH4 H4.j = embedJ := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [embedH4, H4.j, embedJ, embedOne, embedI, embedK]

@[simp] theorem embedH4_k : embedH4 H4.k = embedK := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [embedH4, H4.k, embedK, embedOne, embedI, embedJ]

end InfoGeometry.Canonical.CartanInvolution
