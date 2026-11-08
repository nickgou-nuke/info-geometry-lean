/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.CliffordWeyl.DiracMetricCovariance

/-! Operator action on Dirac ket–bras.
The right spinor action becomes right matrix multiplication by the metric
adjoint `ξ * Aᴴ * η`, where `η * ξ = 1`. This is distinct from octonion
right multiplication and from ordinary conjugate transpose. No identification
of those operations is assumed.
-/
namespace InfoGeometry.CliffordWeyl.SpinorBilinearSoldering
open Matrix
variable {R n : Type*} [CommRing R] [StarRing R] [Fintype n] [DecidableEq n]

theorem diracRow_operator_action (η ξ A : Matrix n n R)
    (hηξ : η * ξ = 1) (r : n → R) :
    diracRow η (A *ᵥ r) = diracRow η r ᵥ* (ξ * A.conjTranspose * η) := by
  simp only [diracRow, star_mulVec, vecMul_vecMul]
  have h : η * (ξ * A.conjTranspose * η) = A.conjTranspose * η := by
    rw [← mul_assoc, ← mul_assoc, hηξ, one_mul]
  rw [h]

omit [DecidableEq n] in
theorem solder_left_operator_action (η A : Matrix n n R) (l r : n → R) :
    solder η (A *ᵥ l) r = A * solder η l r := by
  exact (mul_vecMulVec A l (diracRow η r)).symm

theorem solder_right_operator_action (η ξ A : Matrix n n R)
    (hηξ : η * ξ = 1) (l r : n → R) :
    solder η l (A *ᵥ r) = solder η l r * (ξ * A.conjTranspose * η) := by
  unfold solder
  rw [diracRow_operator_action η ξ A hηξ]
  exact (vecMulVec_mul l (diracRow η r) (ξ * A.conjTranspose * η)).symm

/-- Acting on both spinor factors produces the metric-adjoint bimodule action. -/
theorem solder_bimodule_action (η ξ A B : Matrix n n R)
    (hηξ : η * ξ = 1) (l r : n → R) :
    solder η (A *ᵥ l) (B *ᵥ r) =
      A * solder η l r * (ξ * B.conjTranspose * η) := by
  rw [solder_right_operator_action η ξ B hηξ, solder_left_operator_action]

/-- Move an operator from the first spinor to the second using the metric adjoint. -/
theorem bilinear_metric_adjoint_action (η ξ A : Matrix n n R)
    (hηξ : η * ξ = 1) (l r : n → R) :
    bilinear η 1 (A *ᵥ l) r = bilinear η (ξ * A.conjTranspose * η) l r := by
  simp only [bilinear, one_mulVec, diracRow_operator_action η ξ A hηξ,
    dotProduct_mulVec]

/-- Specialization to the repository's algebraic Krein/Dirac adjoint. -/
theorem solder_right_dirac_action
    (K : InfoGeometry.Physics.KasparovKreinData (Matrix n n R))
    (A : Matrix n n R) (l r : n → R) :
    solder K.eta l (A *ᵥ r) = solder K.eta l r * K.diracAdjoint A := by
  exact solder_right_operator_action K.eta K.eta A K.2.1 l r

end InfoGeometry.CliffordWeyl.SpinorBilinearSoldering
