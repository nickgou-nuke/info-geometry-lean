import Mathlib
import InfoGeometry.Algebra.KantorTripleFiveGrading
import InfoGeometry.Lie.G2DoubleStarRootDecomposition
import Omega.Zeta.CyclotomicSectorIdentity

noncomputable section

namespace InfoGeometry.Canonical.CyclotomicOperatorSpine

open Polynomial
open InfoGeometry.Algebra.KantorTripleFiveGrading
open InfoGeometry.Lie.G2DoubleStarRootDecomposition
open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
open Omega.Zeta.CyclotomicSectorIdentity

/-!
This file records the theorem-safe algebraic content of the proposed
"cyclotomic operator spectrum" picture.

The factorization identities below are identities of polynomials evaluated on
one associative endomorphism.  They do **not** assert that an arbitrary
operator has this minimal polynomial, nor do they identify the native G2 root
weights or Leech-lattice data with eigenvalues of one universal operator.
-/

section OperatorPolynomial

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

local notation "EndV" => Module.End ℂ V

/-- Evaluation of Phi_1 at an endomorphism. -/
def phi1Eval (T : EndV) : EndV := T - 1

/-- Evaluation of Phi_2 at an endomorphism. -/
def phi2Eval (T : EndV) : EndV := T + 1

/-- Evaluation of Phi_3 at an endomorphism. -/
def phi3Eval (T : EndV) : EndV := T ^ 2 + T + 1

/-- Evaluation of Phi_4 at an endomorphism. -/
def phi4Eval (T : EndV) : EndV := T ^ 2 + 1

/-- Evaluation of Phi_6 at an endomorphism. -/
def phi6Eval (T : EndV) : EndV := T ^ 2 - T + 1

/-- Evaluation of Phi_8 at an endomorphism. -/
def phi8Eval (T : EndV) : EndV := T ^ 4 + 1

/-- Evaluation of Phi_12 at an endomorphism. -/
def phi12Eval (T : EndV) : EndV := T ^ 4 - T ^ 2 + 1

/-- Evaluation of Phi_24 at an endomorphism. -/
def phi24Eval (T : EndV) : EndV := T ^ 8 - T ^ 4 + 1

/-- Product of the cyclotomic factors indexed by the divisors of 6. -/
def divisorProduct6 (T : EndV) : EndV :=
  phi1Eval T * phi2Eval T * phi3Eval T * phi6Eval T

/-- Product of the cyclotomic factors indexed by the divisors of 12. -/
def divisorProduct12 (T : EndV) : EndV :=
  phi1Eval T * phi2Eval T * phi3Eval T * phi4Eval T *
    phi6Eval T * phi12Eval T

/-- Product of the cyclotomic factors indexed by the divisors of 24. -/
def divisorProduct24 (T : EndV) : EndV :=
  phi1Eval T * phi2Eval T * phi3Eval T * phi4Eval T *
    phi6Eval T * phi8Eval T * phi12Eval T * phi24Eval T

/-- The proposed degree-25 annihilating expression `T * (T^24 - 1)`. -/
def masterP25 (T : EndV) : EndV := T * (T ^ 24 - 1)

/-- Exact factorization `prod_{d|6} Phi_d(T) = T^6 - 1`. -/
theorem divisorProduct6_eq (T : EndV) :
    divisorProduct6 T = T ^ 6 - 1 := by
  unfold divisorProduct6 phi1Eval phi2Eval phi3Eval phi6Eval
  noncomm_ring

/-- Exact factorization `prod_{d|12} Phi_d(T) = T^12 - 1`. -/
theorem divisorProduct12_eq (T : EndV) :
    divisorProduct12 T = T ^ 12 - 1 := by
  unfold divisorProduct12 phi1Eval phi2Eval phi3Eval phi4Eval phi6Eval phi12Eval
  noncomm_ring

/-- Exact factorization `prod_{d|24} Phi_d(T) = T^24 - 1`. -/
theorem divisorProduct24_eq (T : EndV) :
    divisorProduct24 T = T ^ 24 - 1 := by
  unfold divisorProduct24 phi1Eval phi2Eval phi3Eval phi4Eval phi6Eval
    phi8Eval phi12Eval phi24Eval
  noncomm_ring

/-- Exact factorization of the degree-25 expression. -/
theorem masterP25_factorization (T : EndV) :
    masterP25 T = T * divisorProduct24 T := by
  rw [masterP25, divisorProduct24_eq]

/-- An operator of order dividing 24 is annihilated by the degree-25 expression. -/
theorem masterP25_eq_zero_of_pow24_eq_one
    (T : EndV) (hT : T ^ 24 = 1) :
    masterP25 T = 0 := by
  simp [masterP25, hT]

/-- Tripotency gives the exact factor `T Phi_1(T) Phi_2(T) = 0`. -/
theorem tripotent_factor_zero
    (T : EndV) (hT : T ^ 3 = T) :
    T * phi1Eval T * phi2Eval T = 0 := by
  unfold phi1Eval phi2Eval
  calc
    T * (T - 1) * (T + 1) = T ^ 3 - T := by noncomm_ring
    _ = 0 := sub_eq_zero.mpr hT

/-- The relation `T^3 = -T` gives the `T Phi_4(T)` factor. -/
theorem complex_cubic_factor_zero
    (T : EndV) (hT : T ^ 3 = -T) :
    T * phi4Eval T = 0 := by
  unfold phi4Eval
  calc
    T * (T ^ 2 + 1) = T ^ 3 + T := by noncomm_ring
    _ = 0 := by rw [hT]; abel

/-- A fourth root of `-1` is exactly a zero of the Phi_8 evaluation. -/
theorem phi8_zero_of_pow4_eq_neg_one
    (T : EndV) (hT : T ^ 4 = -1) :
    phi8Eval T = 0 := by
  unfold phi8Eval
  rw [hT]
  simp

/-- Order dividing six implies order dividing twelve. -/
theorem pow12_eq_one_of_pow6_eq_one
    (T : EndV) (hT : T ^ 6 = 1) :
    T ^ 12 = 1 := by
  calc
    T ^ 12 = (T ^ 6) ^ 2 := by
      rw [show (12 : ℕ) = 6 * 2 by norm_num, pow_mul]
    _ = 1 := by rw [hT]; simp

/-- Order dividing twelve implies order dividing twenty-four. -/
theorem pow24_eq_one_of_pow12_eq_one
    (T : EndV) (hT : T ^ 12 = 1) :
    T ^ 24 = 1 := by
  calc
    T ^ 24 = (T ^ 12) ^ 2 := by
      rw [show (24 : ℕ) = 12 * 2 by norm_num, pow_mul]
    _ = 1 := by rw [hT]; simp

/-- Hence every order-six operator is annihilated by the 24-stage master expression. -/
theorem masterP25_eq_zero_of_pow6_eq_one
    (T : EndV) (hT : T ^ 6 = 1) :
    masterP25 T = 0 := by
  apply masterP25_eq_zero_of_pow24_eq_one
  exact pow24_eq_one_of_pow12_eq_one T (pow12_eq_one_of_pow6_eq_one T hT)

/-- Likewise for every order-twelve operator. -/
theorem masterP25_eq_zero_of_pow12_eq_one
    (T : EndV) (hT : T ^ 12 = 1) :
    masterP25 T = 0 :=
  masterP25_eq_zero_of_pow24_eq_one T (pow24_eq_one_of_pow12_eq_one T hT)

end OperatorPolynomial

section ComplexRoots

/-- The existing exact roots-of-unity owner specializes at conductor 24. -/
theorem root_of_unity_product_24 (x : ℂ) :
    ∏ k ∈ Finset.range 24, (1 - x * rootOfUnity 24 k) = 1 - x ^ 24 := by
  exact paper_finite_part_cyclic_lift_cyclotomic_sector 24 (by norm_num) x

end ComplexRoots

section KantorReadout

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- The repository's native Kantor owner already proves the displayed first identity. -/
theorem kantor_first_identity_readout
    (K : KantorTripleSystem R V) (u v x y : V) :
    K.endCommutator (K.D u v) (K.D x y) =
      K.D (K.D u v x) y - K.D x (K.D v u y) :=
  K.D_comm_D u v x y

end KantorReadout

section G2Readout

/-- The native double-star readout consists of exactly twelve nonzero root channels. -/
theorem g2_double_star_card : doubleStarIndices.card = 12 :=
  doubleStarIndices_card

/-- The two zero-weight channels are exactly indices 6 and 13. -/
theorem g2_zero_weight_iff (j : Fin 14) :
    rootWeight j = 0 ↔ j = 6 ∨ j = 13 :=
  rootWeight_eq_zero_iff j

/-- The native short-root channel has cardinality six. -/
theorem g2_short_root_card : shortRootIndices.card = 6 :=
  shortRootIndices_card

/-- The native long-root channel has cardinality six. -/
theorem g2_long_root_card : longRootIndices.card = 6 :=
  longRootIndices_card

end G2Readout

end InfoGeometry.Canonical.CyclotomicOperatorSpine
