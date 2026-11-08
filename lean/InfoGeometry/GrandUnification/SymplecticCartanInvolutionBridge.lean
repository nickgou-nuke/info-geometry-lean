/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.GrandUnification.ArchetypeDictionary
import InfoGeometry.Canonical.Sp4ParaHyperkahlerPresymplecticBridge

/-!
# Finite Symplectic Matrix Involution Projections

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * Instantiates `InfoGeometry.GrandUnification.ArchetypeDictionary.SplitInvolution` at the real
    $4 \times 4$ matrices `J4_para` and `K4_para` from
    `InfoGeometry.Canonical.Sp4ParaHyperkahlerPresymplecticBridge`.
- BUCKET 2 (Concrete Vector Carrier Projections):
  * Defines `J4_chiral_plus` and `J4_chiral_minus` on `Vec4R = Fin 4 → ℝ` via `Matrix.mulVec`.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `J4_projector_sum_eq_one`, `J4_projectors_orthogonal`, `K4_projector_sum_eq_one`,
    `K4_projectors_orthogonal`: projector completeness and orthogonality for `J4_para` and `K4_para`.
  * `J4_R4_chiral_decomposition`, `J4_R4_chiral_cross_zero`, `J4_R4_chiral_decomposition_unique`:
    existence, mutual annihilation, and uniqueness of the chiral vector decomposition on `Vec4R`.
-/
namespace InfoGeometry.GrandUnification.SymplecticCartanInvolutionBridge

open InfoGeometry.Canonical.Sp4ParaHyperkahlerPresymplecticBridge
open InfoGeometry.GrandUnification.ArchetypeDictionary
open InfoGeometry.Algebra.FiniteSpin

/-- The para-hyperkähler J_4 generator acts as a canonical Split Involution. -/
def J4_SplitInvolution : SplitInvolution ℝ Mat4R where
  epsilon := J4_para
  sq_eq_one := J4_sq

/-- The para-hyperkähler K_4 generator acts as a complementary Split Involution. -/
def K4_SplitInvolution : SplitInvolution ℝ Mat4R where
  epsilon := K4_para
  sq_eq_one := K4_sq

/-- The canonical J_4 split Peirce projectors sum to the identity matrix. -/
theorem J4_projector_sum_eq_one :
    J4_SplitInvolution.P_plus + J4_SplitInvolution.P_minus = 1 := by
  apply J4_SplitInvolution.P_plus_add_P_minus

/-- The J_4 projectors are orthogonal (mutually annihilating). -/
theorem J4_projectors_orthogonal :
    J4_SplitInvolution.P_plus * J4_SplitInvolution.P_minus = 0 := by
  apply J4_SplitInvolution.P_plus_mul_P_minus

/-- The canonical K_4 split Peirce projectors sum to the identity matrix. -/
theorem K4_projector_sum_eq_one :
    K4_SplitInvolution.P_plus + K4_SplitInvolution.P_minus = 1 := by
  apply K4_SplitInvolution.P_plus_add_P_minus

/-- The K_4 projectors are orthogonal (mutually annihilating). -/
theorem K4_projectors_orthogonal :
    K4_SplitInvolution.P_plus * K4_SplitInvolution.P_minus = 0 := by
  apply K4_SplitInvolution.P_plus_mul_P_minus

/-- The positive J₄ projection acting on the concrete vector carrier ℝ⁴. -/
noncomputable def J4_chiral_plus (x : Vec4R) : Vec4R := J4_SplitInvolution.P_plus.mulVec x

/-- The negative J₄ projection acting on the concrete vector carrier ℝ⁴. -/
noncomputable def J4_chiral_minus (x : Vec4R) : Vec4R := J4_SplitInvolution.P_minus.mulVec x

/-- Every vector is the sum of its two J₄ Peirce projections. -/
theorem J4_R4_chiral_decomposition (x : Vec4R) :
    x = J4_chiral_plus x + J4_chiral_minus x := by
  unfold J4_chiral_plus J4_chiral_minus
  rw [← Matrix.add_mulVec, J4_projector_sum_eq_one, Matrix.one_mulVec]

/-- The two J₄ vector projections annihilate one another in either order. -/
theorem J4_R4_chiral_cross_zero (x : Vec4R) :
    J4_chiral_plus (J4_chiral_minus x) = 0 ∧
      J4_chiral_minus (J4_chiral_plus x) = 0 := by
  constructor
  · unfold J4_chiral_plus J4_chiral_minus
    rw [Matrix.mulVec_mulVec, J4_SplitInvolution.P_plus_mul_P_minus, Matrix.zero_mulVec]
  · unfold J4_chiral_plus J4_chiral_minus
    rw [Matrix.mulVec_mulVec, J4_SplitInvolution.P_minus_mul_P_plus, Matrix.zero_mulVec]

/-- Uniqueness of the J₄ vector decomposition in the two projection ranges. -/
theorem J4_R4_chiral_decomposition_unique (x a b : Vec4R)
    (ha : J4_chiral_plus a = a)
    (hb : J4_chiral_minus b = b)
    (hsum : x = a + b) :
    a = J4_chiral_plus x ∧ b = J4_chiral_minus x := by
  have hplus_b : J4_chiral_plus b = 0 := by
    rw [← hb]
    exact (J4_R4_chiral_cross_zero b).1
  have hminus_a : J4_chiral_minus a = 0 := by
    rw [← ha]
    exact (J4_R4_chiral_cross_zero a).2
  constructor
  · calc
      a = J4_chiral_plus a := ha.symm
      _ = J4_chiral_plus a + J4_chiral_plus b := by rw [hplus_b, add_zero]
      _ = J4_chiral_plus (a + b) := by
        unfold J4_chiral_plus
        rw [Matrix.mulVec_add]
      _ = J4_chiral_plus x := by rw [← hsum]
  · calc
      b = J4_chiral_minus b := hb.symm
      _ = J4_chiral_minus a + J4_chiral_minus b := by rw [hminus_a, zero_add]
      _ = J4_chiral_minus (a + b) := by
        unfold J4_chiral_minus
        rw [Matrix.mulVec_add]
      _ = J4_chiral_minus x := by rw [← hsum]

end InfoGeometry.GrandUnification.SymplecticCartanInvolutionBridge
