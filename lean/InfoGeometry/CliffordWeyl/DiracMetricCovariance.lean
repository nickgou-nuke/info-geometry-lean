/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.CliffordWeyl.DiracSolderAdjoint

/-! General matrix coordinate changes transport both Dirac ket–bras and the metric.
`S,T` are mutually inverse matrices. The transported metric is `Tᴴ η T`,
whose inverse is `S ξ Sᴴ` when ξ is the inverse of η. No isometry or
involutive transported metric is assumed. All identities concern full matrices.
-/
namespace InfoGeometry.CliffordWeyl.SpinorBilinearSoldering
open Matrix
variable {R n : Type*} [CommRing R] [StarRing R] [Fintype n] [DecidableEq n]

theorem diracRow_change_basis (S T η : Matrix n n R) (hTS : T * S = 1)
    (r : n → R) :
    diracRow (T.conjTranspose * η * T) (S *ᵥ r) = diracRow η r ᵥ* T := by
  have hd : S.conjTranspose * T.conjTranspose = 1 := by
    rw [← conjTranspose_mul, hTS, conjTranspose_one]
  simp only [diracRow, star_mulVec, vecMul_vecMul, mul_assoc]
  rw [← mul_assoc S.conjTranspose T.conjTranspose, hd, one_mul]

theorem solder_change_basis (S T η : Matrix n n R) (hTS : T * S = 1)
    (l r : n → R) :
    solder (T.conjTranspose * η * T) (S *ᵥ l) (S *ᵥ r) =
      S * solder η l r * T := by
  unfold solder
  rw [diracRow_change_basis S T η hTS, mul_vecMulVec, vecMulVec_mul]

omit [DecidableEq n] in
theorem transported_metric_hermitian (T η : Matrix n n R)
    (hη : η.conjTranspose = η) :
    (T.conjTranspose * η * T).conjTranspose = T.conjTranspose * η * T := by
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, hη, mul_assoc]

theorem transported_metric_inverse (S T η ξ : Matrix n n R)
    (hTS : T * S = 1) (hST : S * T = 1) (hηξ : η * ξ = 1) :
    (T.conjTranspose * η * T) * (S * ξ * S.conjTranspose) = 1 := by
  have hd : T.conjTranspose * S.conjTranspose = 1 := by
    rw [← conjTranspose_mul, hST, conjTranspose_one]
  calc
    _ = T.conjTranspose * η * (T * S) * ξ * S.conjTranspose := by noncomm_ring
    _ = 1 := by rw [hTS, mul_one, mul_assoc T.conjTranspose η ξ, hηξ, mul_one, hd]

theorem metric_adjoint_change_basis (S T η ξ A : Matrix n n R)
    (hTS : T * S = 1) :
    (S * ξ * S.conjTranspose) * (S * A * T).conjTranspose *
      (T.conjTranspose * η * T) = S * (ξ * A.conjTranspose * η) * T := by
  have hd : S.conjTranspose * T.conjTranspose = 1 := by
    rw [← conjTranspose_mul, hTS, conjTranspose_one]
  simp only [conjTranspose_mul]
  calc
    _ = S * ξ * (S.conjTranspose * T.conjTranspose) * A.conjTranspose *
        (S.conjTranspose * T.conjTranspose) * η * T := by noncomm_ring
    _ = S * (ξ * A.conjTranspose * η) * T := by rw [hd]; noncomm_ring


/-- The complementary inverse law for the transported metric. -/
theorem transported_metric_left_inverse (S T η ξ : Matrix n n R)
    (hTS : T * S = 1) (hST : S * T = 1) (hξη : ξ * η = 1) :
    (S * ξ * S.conjTranspose) * (T.conjTranspose * η * T) = 1 := by
  have hd : S.conjTranspose * T.conjTranspose = 1 := by
    rw [← conjTranspose_mul, hTS, conjTranspose_one]
  calc
    _ = S * ξ * (S.conjTranspose * T.conjTranspose) * η * T := by noncomm_ring
    _ = 1 := by rw [hd, mul_one, mul_assoc S ξ η, hξη, mul_one, hST]

/-- Dirac adjunction exchanges ket–bras for any Hermitian metric with a left inverse. -/
theorem solder_inverse_metric_adjoint (η ξ : Matrix n n R)
    (hη : η.conjTranspose = η) (hξη : ξ * η = 1) (l r : n → R) :
    ξ * (solder η l r).conjTranspose * η = solder η r l := by
  rw [solder_eq_vecMulVec_mul, conjTranspose_mul, conjTranspose_vecMulVec,
    hη, star_star, solder_eq_vecMulVec_mul]
  rw [← mul_assoc, hξη, one_mul]

end InfoGeometry.CliffordWeyl.SpinorBilinearSoldering
