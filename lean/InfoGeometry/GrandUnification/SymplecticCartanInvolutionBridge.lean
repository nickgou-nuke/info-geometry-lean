import InfoGeometry.GrandUnification.ArchetypeDictionary
import InfoGeometry.Canonical.Sp4ParaHyperkahlerPresymplecticBridge


/-!
# Finite Symplectic Matrix Involution Projections

This module instantiates the abstract algebraic involution projectors at the
real 4-by-4 matrices `J4_para` and `K4_para` from the finite matrix owner. It
applies the resulting matrices to the real four-dimensional vector carrier and proves decomposition,
cross-annihilation, and uniqueness identities. These are finite matrix and
vector statements; no symmetric space, bundle, or topology is constructed.
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

/-- The canonical J_4 split Peirce projectors sum exactly to the identity matrix. -/
theorem J4_projector_sum_eq_one :
    J4_SplitInvolution.P_plus + J4_SplitInvolution.P_minus = 1 :=
  J4_SplitInvolution.P_plus_add_P_minus

/-- The J_4 projectors are exactly orthogonal (mutually annihilating). -/
theorem J4_projectors_orthogonal :
    J4_SplitInvolution.P_plus * J4_SplitInvolution.P_minus = 0 :=
  J4_SplitInvolution.P_plus_mul_P_minus

/-- The canonical K_4 split Peirce projectors sum exactly to the identity matrix. -/
theorem K4_projector_sum_eq_one :
    K4_SplitInvolution.P_plus + K4_SplitInvolution.P_minus = 1 :=
  K4_SplitInvolution.P_plus_add_P_minus

/-- The K_4 projectors are exactly orthogonal (mutually annihilating). -/
theorem K4_projectors_orthogonal :
    K4_SplitInvolution.P_plus * K4_SplitInvolution.P_minus = 0 :=
  K4_SplitInvolution.P_plus_mul_P_minus

/-- The positive J₄ projection acting on the concrete vector carrier ℝ⁴. -/
noncomputable def J4_chiral_plus (x : Vec4R) : Vec4R := J4_SplitInvolution.P_plus.mulVec x

/-- The negative J₄ projection acting on the concrete vector carrier ℝ⁴. -/
noncomputable def J4_chiral_minus (x : Vec4R) : Vec4R := J4_SplitInvolution.P_minus.mulVec x

/-- Every vector is the sum of its two J₄ Peirce projections. -/
theorem J4_R4_chiral_decomposition (x : Vec4R) :
    x = J4_chiral_plus x + J4_chiral_minus x := by
  calc
    x = (1 : Mat4R).mulVec x := by simp
    _ = (J4_SplitInvolution.P_plus + J4_SplitInvolution.P_minus).mulVec x := by
      rw [← J4_projector_sum_eq_one]
    _ = J4_chiral_plus x + J4_chiral_minus x := by
      simp [J4_chiral_plus, J4_chiral_minus, Matrix.add_mulVec]

/-- The two J₄ vector projections annihilate one another in either order. -/
theorem J4_R4_chiral_cross_zero (x : Vec4R) :
    J4_chiral_plus (J4_chiral_minus x) = 0 ∧
      J4_chiral_minus (J4_chiral_plus x) = 0 := by
  constructor
  · change J4_SplitInvolution.P_plus.mulVec
      (J4_SplitInvolution.P_minus.mulVec x) = 0
    rw [Matrix.mulVec_mulVec]
    have h := congrArg (fun A : Mat4R => A.mulVec x)
      J4_SplitInvolution.P_plus_mul_P_minus
    simpa using h
  · change J4_SplitInvolution.P_minus.mulVec
      (J4_SplitInvolution.P_plus.mulVec x) = 0
    rw [Matrix.mulVec_mulVec]
    have h := congrArg (fun A : Mat4R => A.mulVec x)
      J4_SplitInvolution.P_minus_mul_P_plus
    simpa using h

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
        simp [J4_chiral_plus, Matrix.mulVec_add]
      _ = J4_chiral_plus x := by rw [← hsum]
  · calc
      b = J4_chiral_minus b := hb.symm
      _ = J4_chiral_minus a + J4_chiral_minus b := by rw [hminus_a, zero_add]
      _ = J4_chiral_minus (a + b) := by
        simp [J4_chiral_minus, Matrix.mulVec_add]
      _ = J4_chiral_minus x := by rw [← hsum]

end InfoGeometry.GrandUnification.SymplecticCartanInvolutionBridge
