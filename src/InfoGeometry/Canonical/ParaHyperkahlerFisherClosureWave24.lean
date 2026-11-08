/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.Sp4ParaHyperkahlerPresymplecticBridge

namespace InfoGeometry.Canonical.Sp4ParaHyperkahlerPresymplecticBridge

/-- The elliptic contraction is symmetric and therefore can serve as the
positive bilinear channel associated with the para-hypercomplex frame. -/
theorem omegaI4_symm (u v : R4) : omegaI4 u v = omegaI4 v u := by
  rw [omegaI4_eq_euclidean, omegaI4_eq_euclidean]
  ring

/-- The elliptic contraction is positive semidefinite on the real carrier. -/
theorem omegaI4_nonneg (u : R4) : 0 ≤ omegaI4 u u := by
  rw [omegaI4_eq_euclidean]
  nlinarith [sq_nonneg (u 0), sq_nonneg (u 1), sq_nonneg (u 2), sq_nonneg (u 3)]

/-- The elliptic contraction is nondegenerate on the real carrier. -/
theorem omegaI4_self_eq_zero_iff (u : R4) : omegaI4 u u = 0 ↔ u = 0 := by
  rw [omegaI4_eq_euclidean]
  constructor
  · intro h
    have h0 : u 0 = 0 := by nlinarith [sq_nonneg (u 1), sq_nonneg (u 2), sq_nonneg (u 3)]
    have h1 : u 1 = 0 := by nlinarith [sq_nonneg (u 0), sq_nonneg (u 2), sq_nonneg (u 3)]
    have h2 : u 2 = 0 := by nlinarith [sq_nonneg (u 0), sq_nonneg (u 1), sq_nonneg (u 3)]
    have h3 : u 3 = 0 := by nlinarith [sq_nonneg (u 0), sq_nonneg (u 1), sq_nonneg (u 2)]
    funext i
    fin_cases i <;> assumption
  · intro h
    rw [h]
    norm_num

/-- The para-complex generator preserves the positive elliptic metric. -/
theorem omegaI4_J4_isometry (u v : R4) :
    omegaI4 (J4_para.mulVec u) (J4_para.mulVec v) = omegaI4 u v := by
  rw [omegaI4_eq_euclidean, omegaI4_eq_euclidean]
  simp only [J4_mulVec_0, J4_mulVec_1, J4_mulVec_2, J4_mulVec_3]
  ring

/-- The second para-hypercomplex generator is an anti-isometry of the
neutral contraction. -/
theorem omegaJ4_J4_anti_isometry (u v : R4) :
    omegaJ4 (J4_para.mulVec u) (J4_para.mulVec v) = - omegaJ4 u v := by
  rw [omegaJ4_eq_neutral, omegaJ4_eq_neutral]
  simp only [J4_mulVec_0, J4_mulVec_1, J4_mulVec_2, J4_mulVec_3]
  ring

/-- The split generator also preserves the positive elliptic metric. -/
theorem omegaI4_K4_isometry (u v : R4) :
    omegaI4 (K4_para.mulVec u) (K4_para.mulVec v) = omegaI4 u v := by
  rw [omegaI4_eq_euclidean, omegaI4_eq_euclidean]
  simp only [K4_mulVec_0, K4_mulVec_1, K4_mulVec_2, K4_mulVec_3]
  ring

end InfoGeometry.Canonical.Sp4ParaHyperkahlerPresymplecticBridge
