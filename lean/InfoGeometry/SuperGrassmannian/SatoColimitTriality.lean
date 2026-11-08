import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Abel
import InfoGeometry.Canonical.ComplexMatrixStage
import InfoGeometry.Canonical.GenuineMatrixStageMorphism
import InfoGeometry.Canonical.MatrixStageInductiveLimit

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

/-!
# Conditional Split-Cell Identities and Matrix-Stage Trace Descent

This file contains three distinct algebraic developments. First, the
`SplitCliffordCell` record assumes split-generator relations in an arbitrary
ring; the CAR and grading lemmas are conditional consequences, with a concrete
noncommutative real-matrix inhabitant supplied by
`SplitCliffordCellMatrixWitness`. Second, `NormalizedCyclicFunctional` is a
normalized additive cyclic functional record, with no positivity or state axioms; its
compression identities are algebraic consequences of those fields. Third, the
`MatrixStageLimit` section proves product, involution, and trace compatibility
for the repository's concrete matrix-stage limit.

The scalar dimension-difference structures in this file encode equal-shift
arithmetic. They do not define Fredholm operators, a Sato Grassmannian, a
Fredholm index, or a colimit of Clifford cells. The concrete matrix-stage trace
results are separate from those scalar identities.
-/

namespace InfoGeometry.SuperGrassmannian.SatoColimitTriality

open InfoGeometry.Canonical.ComplexMatrixStage
open InfoGeometry.Canonical.GenuineMatrixStageMorphism
open InfoGeometry.Canonical.MatrixStageInductiveLimit

/-! ### 1. Noncommutative Split Clifford Cell & CAR Generator Algebra -/

/-- Elements satisfying split-generator relations in a ring with central half-unit. -/
structure SplitCliffordCell (R : Type*) [Ring R] where
  e : R
  f : R
  half : R
  e_sq : e ^ 2 = 1
  f_sq : f ^ 2 = -1
  anticomm : e * f + f * e = 0
  two_half : half + half = 1
  half_comm : ∀ x : R, half * x = x * half

namespace SplitCliffordCell

variable {R : Type*} [Ring R] (C : SplitCliffordCell R)

lemma e_mul_e : C.e * C.e = 1 := by
  have h := C.e_sq
  rwa [sq] at h

lemma f_mul_f : C.f * C.f = -1 := by
  have h := C.f_sq
  rwa [sq] at h

lemma fe_eq_neg_ef : C.f * C.e = - (C.e * C.f) := by
  calc
    C.f * C.e = (C.e * C.f + C.f * C.e) - C.e * C.f := by abel
    _ = 0 - C.e * C.f := by rw [C.anticomm]
    _ = - (C.e * C.f) := by abel

lemma two_mul_half : (2 : R) * C.half = 1 := by
  rw [two_mul, C.two_half]

lemma half_mul_two : C.half * (2 : R) = 1 := by
  rw [mul_two, C.two_half]

lemma half_sq_mul_four : (C.half * C.half) * (4 : R) = 1 := by
  have h4 : (4 : R) = (2 : R) * (2 : R) := by norm_num
  rw [h4, ← mul_assoc (C.half * C.half) 2 2, mul_assoc C.half C.half 2, half_mul_two, mul_one, half_mul_two]

lemma mul_half_mul_half (x y : R) :
    (C.half * x) * (C.half * y) = (C.half * C.half) * (x * y) := by
  calc
    (C.half * x) * (C.half * y) = C.half * (x * C.half) * y := by noncomm_ring
    _ = C.half * (C.half * x) * y := by rw [C.half_comm x]
    _ = (C.half * C.half) * (x * y) := by noncomm_ring

lemma mul_half_assoc (x y : R) : x * (C.half * y) = C.half * (x * y) := by
  calc
    x * (C.half * y) = (x * C.half) * y := by rw [← mul_assoc]
    _ = (C.half * x) * y := by rw [← C.half_comm x]
    _ = C.half * (x * y) := by rw [mul_assoc]

/-- Chiral grading operator $\Gamma = e f$. -/
def gamma : R := C.e * C.f

/-- Annihilation lightcone operator $a = \text{half} \cdot (e + f)$. -/
def a : R := C.half * (C.e + C.f)

/-- Creation lightcone operator $a^* = \text{half} \cdot (e - f)$. -/
def a_star : R := C.half * (C.e - C.f)

/-- Number operator $N = a^* a$. -/
def numberOp : R := C.a_star * C.a

/-- Vacuum projector $P_0 = a a^*$. -/
def vacProj : R := C.a * C.a_star

/-- Positive chiral projector $\Pi_+ = N$. -/
def projPlus : R := C.numberOp

/-- Negative chiral projector $\Pi_- = P_0$. -/
def projMinus : R := C.vacProj

/-- Chiral grading operator squares to identity: $\Gamma^2 = 1$. -/
theorem gamma_sq_one : C.gamma ^ 2 = 1 := by
  dsimp [gamma]
  rw [sq]
  calc
    (C.e * C.f) * (C.e * C.f) = C.e * (C.f * C.e) * C.f := by noncomm_ring
    _ = C.e * (- (C.e * C.f)) * C.f := by rw [fe_eq_neg_ef]
    _ = - (C.e * C.e) * (C.f * C.f) := by noncomm_ring
    _ = - (1 : R) * (-1) := by rw [e_mul_e, f_mul_f]
    _ = 1 := by norm_num

lemma gamma_mul_gamma : C.gamma * C.gamma = 1 := by
  have h := C.gamma_sq_one
  rwa [sq] at h

/-- Lightcone Pauli exclusion / nilpotency: $a^2 = 0$. -/
theorem a_sq_zero : C.a ^ 2 = 0 := by
  dsimp [a]
  rw [sq, C.mul_half_mul_half]
  have he2 : C.e * C.e = 1 := C.e_mul_e
  have hf2 : C.f * C.f = -1 := C.f_mul_f
  have hanti : C.e * C.f + C.f * C.e = 0 := C.anticomm
  have h_inner : (C.e + C.f) * (C.e + C.f) = 0 := by
    calc
      (C.e + C.f) * (C.e + C.f) = C.e * C.e + (C.e * C.f + C.f * C.e) + C.f * C.f := by noncomm_ring
      _ = 1 + 0 + (-1) := by rw [he2, hanti, hf2]
      _ = 0 := by abel
  rw [h_inner, mul_zero]

/-- Lightcone Pauli exclusion / nilpotency: $(a^*)^2 = 0$. -/
theorem a_star_sq_zero : C.a_star ^ 2 = 0 := by
  dsimp [a_star]
  rw [sq, C.mul_half_mul_half]
  have he2 : C.e * C.e = 1 := C.e_mul_e
  have hf2 : C.f * C.f = -1 := C.f_mul_f
  have hanti : C.e * C.f + C.f * C.e = 0 := C.anticomm
  have h_inner : (C.e - C.f) * (C.e - C.f) = 0 := by
    calc
      (C.e - C.f) * (C.e - C.f) = C.e * C.e - (C.e * C.f + C.f * C.e) + C.f * C.f := by noncomm_ring
      _ = 1 - 0 + (-1) := by rw [he2, hanti, hf2]
      _ = 0 := by abel
  rw [h_inner, mul_zero]

/-- Canonical Anticommutation Relation: $\{a, a^*\} = 1$. -/
theorem car_anticomm : C.a * C.a_star + C.a_star * C.a = 1 := by
  dsimp [a, a_star]
  rw [C.mul_half_mul_half, C.mul_half_mul_half, ← mul_add]
  have he2 : C.e * C.e = 1 := C.e_mul_e
  have hf2 : C.f * C.f = -1 := C.f_mul_f
  have h_sum : (C.e + C.f) * (C.e - C.f) + (C.e - C.f) * (C.e + C.f) = (4 : R) := by
    calc
      (C.e + C.f) * (C.e - C.f) + (C.e - C.f) * (C.e + C.f) =
          (C.e * C.e - C.f * C.f) + (C.e * C.e - C.f * C.f) := by noncomm_ring
      _ = (1 - (-1)) + (1 - (-1)) := by rw [he2, hf2]
      _ = (4 : R) := by norm_num
  rw [h_sum]
  exact C.half_sq_mul_four

/-- Number operator idempotence: $N^2 = N$. -/
theorem numberOp_sq : C.numberOp ^ 2 = C.numberOp := by
  dsimp [numberOp]
  have ha2 : C.a * C.a = 0 := by have h := C.a_sq_zero; rwa [sq] at h
  have ha_star2 : C.a_star * C.a_star = 0 := by have h := C.a_star_sq_zero; rwa [sq] at h
  have h_car : C.a * C.a_star = 1 - C.a_star * C.a := by
    calc
      C.a * C.a_star = (C.a * C.a_star + C.a_star * C.a) - C.a_star * C.a := by abel
      _ = 1 - C.a_star * C.a := by rw [C.car_anticomm]
  rw [sq]
  calc
    (C.a_star * C.a) * (C.a_star * C.a) =
        C.a_star * (C.a * C.a_star) * C.a := by noncomm_ring
    _ = C.a_star * (1 - C.a_star * C.a) * C.a := by rw [h_car]
    _ = C.a_star * C.a - (C.a_star * C.a_star) * (C.a * C.a) := by noncomm_ring
    _ = C.a_star * C.a - 0 * 0 := by rw [ha_star2, ha2]
    _ = C.a_star * C.a := by noncomm_ring

/-- Vacuum projector idempotence: $P_0^2 = P_0$. -/
theorem vacProj_sq : C.vacProj ^ 2 = C.vacProj := by
  dsimp [vacProj]
  have ha2 : C.a * C.a = 0 := by have h := C.a_sq_zero; rwa [sq] at h
  have ha_star2 : C.a_star * C.a_star = 0 := by have h := C.a_star_sq_zero; rwa [sq] at h
  have h_car : C.a_star * C.a = 1 - C.a * C.a_star := by
    calc
      C.a_star * C.a = (C.a * C.a_star + C.a_star * C.a) - C.a * C.a_star := by abel
      _ = 1 - C.a * C.a_star := by rw [C.car_anticomm]
  rw [sq]
  calc
    (C.a * C.a_star) * (C.a * C.a_star) =
        C.a * (C.a_star * C.a) * C.a_star := by noncomm_ring
    _ = C.a * (1 - C.a * C.a_star) * C.a_star := by rw [h_car]
    _ = C.a * C.a_star - (C.a * C.a) * (C.a_star * C.a_star) := by noncomm_ring
    _ = C.a * C.a_star - 0 * 0 := by rw [ha2, ha_star2]
    _ = C.a * C.a_star := by noncomm_ring

/-- Partition of identity: $N + P_0 = 1$. -/
theorem number_add_vac : C.numberOp + C.vacProj = 1 := by
  dsimp [numberOp, vacProj]
  have h := C.car_anticomm
  calc
    C.a_star * C.a + C.a * C.a_star = C.a * C.a_star + C.a_star * C.a := by abel
    _ = 1 := h

lemma N_mul_a : C.numberOp * C.a = 0 := by
  dsimp [numberOp]
  have ha2 : C.a * C.a = 0 := by have h := C.a_sq_zero; rwa [sq] at h
  rw [mul_assoc, ha2, mul_zero]

lemma a_mul_N : C.a * C.numberOp = C.a := by
  dsimp [numberOp]
  have h_car : C.a * C.a_star = 1 - C.numberOp := by
    dsimp [numberOp]
    calc
      C.a * C.a_star = (C.a * C.a_star + C.a_star * C.a) - C.a_star * C.a := by abel
      _ = 1 - C.a_star * C.a := by rw [C.car_anticomm]
  calc
    C.a * (C.a_star * C.a) = (C.a * C.a_star) * C.a := by rw [← mul_assoc]
    _ = (1 - C.numberOp) * C.a := by rw [h_car]
    _ = 1 * C.a - C.numberOp * C.a := by noncomm_ring
    _ = C.a - 0 := by rw [one_mul, C.N_mul_a]
    _ = C.a := by abel

/-- Annihilation ladder commutator: $[N, a] = -a$. -/
theorem ladder_lower : C.numberOp * C.a - C.a * C.numberOp = - C.a := by
  rw [C.N_mul_a, C.a_mul_N]
  abel

lemma a_star_mul_N : C.a_star * C.numberOp = 0 := by
  dsimp [numberOp]
  have ha_star2 : C.a_star * C.a_star = 0 := by have h := C.a_star_sq_zero; rwa [sq] at h
  calc
    C.a_star * (C.a_star * C.a) = (C.a_star * C.a_star) * C.a := by rw [← mul_assoc]
    _ = 0 * C.a := by rw [ha_star2]
    _ = 0 := by rw [zero_mul]

lemma N_mul_a_star : C.numberOp * C.a_star = C.a_star := by
  dsimp [numberOp]
  have h_car : C.a * C.a_star = 1 - C.numberOp := by
    dsimp [numberOp]
    calc
      C.a * C.a_star = (C.a * C.a_star + C.a_star * C.a) - C.a_star * C.a := by abel
      _ = 1 - C.a_star * C.a := by rw [C.car_anticomm]
  calc
    (C.a_star * C.a) * C.a_star = C.a_star * (C.a * C.a_star) := by rw [mul_assoc]
    _ = C.a_star * (1 - C.numberOp) := by rw [h_car]
    _ = C.a_star * 1 - C.a_star * C.numberOp := by noncomm_ring
    _ = C.a_star - 0 := by rw [mul_one, C.a_star_mul_N]
    _ = C.a_star := by abel

/-- Creation ladder commutator: $[N, a^*] = +a^*$. -/
theorem ladder_raise : C.numberOp * C.a_star - C.a_star * C.numberOp = C.a_star := by
  rw [C.N_mul_a_star, C.a_star_mul_N]
  abel

lemma gamma_mul_a : C.gamma * C.a = - C.a := by
  dsimp [gamma, a]
  rw [C.mul_half_assoc]
  have he2 : C.e * C.e = 1 := C.e_mul_e
  have hf2 : C.f * C.f = -1 := C.f_mul_f
  have hef : C.f * C.e = - (C.e * C.f) := C.fe_eq_neg_ef
  have h_inner : (C.e * C.f) * (C.e + C.f) = - (C.e + C.f) := by
    calc
      (C.e * C.f) * (C.e + C.f) = C.e * (C.f * C.e) + C.e * (C.f * C.f) := by noncomm_ring
      _ = C.e * (- (C.e * C.f)) + C.e * (-1) := by rw [hef, hf2]
      _ = - (C.e * C.e) * C.f - C.e := by noncomm_ring
      _ = - 1 * C.f - C.e := by rw [he2]
      _ = - (C.e + C.f) := by noncomm_ring
  rw [h_inner, mul_neg]

lemma gamma_mul_a_star : C.gamma * C.a_star = C.a_star := by
  dsimp [gamma, a_star]
  rw [C.mul_half_assoc]
  have he2 : C.e * C.e = 1 := C.e_mul_e
  have hf2 : C.f * C.f = -1 := C.f_mul_f
  have hef : C.f * C.e = - (C.e * C.f) := C.fe_eq_neg_ef
  have h_inner : (C.e * C.f) * (C.e - C.f) = C.e - C.f := by
    calc
      (C.e * C.f) * (C.e - C.f) = C.e * (C.f * C.e) - C.e * (C.f * C.f) := by noncomm_ring
      _ = C.e * (- (C.e * C.f)) - C.e * (-1) := by rw [hef, hf2]
      _ = - (C.e * C.e) * C.f + C.e := by noncomm_ring
      _ = - 1 * C.f + C.e := by rw [he2]
      _ = C.e - C.f := by noncomm_ring
  rw [h_inner]

/-! ### 2. Noncommutative Chiral Projector Decomposition -/

/-- Positive chiral projector $\Pi_+$ is idempotent: $\Pi_+^2 = \Pi_+$. -/
theorem projPlus_sq : C.projPlus ^ 2 = C.projPlus := C.numberOp_sq

/-- Negative chiral projector $\Pi_-$ is idempotent: $\Pi_-^2 = \Pi_-$. -/
theorem projMinus_sq : C.projMinus ^ 2 = C.projMinus := C.vacProj_sq

/-- Orthogonal chiral annihilation: $\Pi_+ \Pi_- = 0$. -/
theorem proj_orthogonal : C.projPlus * C.projMinus = 0 := by
  dsimp [projPlus, projMinus, numberOp, vacProj]
  have ha2 : C.a * C.a = 0 := by have h := C.a_sq_zero; rwa [sq] at h
  calc
    (C.a_star * C.a) * (C.a * C.a_star) = C.a_star * (C.a * C.a) * C.a_star := by noncomm_ring
    _ = C.a_star * 0 * C.a_star := by rw [ha2]
    _ = 0 := by noncomm_ring

/-- Partition of identity: $\Pi_+ + \Pi_- = 1$. -/
theorem proj_sum_one : C.projPlus + C.projMinus = 1 := C.number_add_vac

/-- Chiral grading reflection: $\Pi_+ - \Pi_- = \Gamma$. -/
theorem proj_sub_gamma : C.projPlus - C.projMinus = C.gamma := by
  dsimp [projPlus, projMinus, numberOp, vacProj, a, a_star, gamma]
  rw [C.mul_half_mul_half, C.mul_half_mul_half, ← mul_sub]
  have he2 : C.e * C.e = 1 := C.e_mul_e
  have hf2 : C.f * C.f = -1 := C.f_mul_f
  have hef : C.f * C.e = - (C.e * C.f) := C.fe_eq_neg_ef
  have h_diff : (C.e - C.f) * (C.e + C.f) - (C.e + C.f) * (C.e - C.f) = (4 : R) * (C.e * C.f) := by
    calc
      (C.e - C.f) * (C.e + C.f) - (C.e + C.f) * (C.e - C.f) =
          2 * (C.e * C.f) - 2 * (C.f * C.e) := by noncomm_ring
      _ = 2 * (C.e * C.f) - 2 * (- (C.e * C.f)) := by rw [hef]
      _ = 2 * (C.e * C.f) + 2 * (C.e * C.f) := by rw [mul_neg, sub_neg_eq_add]
      _ = (2 + 2 : R) * (C.e * C.f) := by rw [add_mul]
      _ = (4 : R) * (C.e * C.f) := by norm_num
  rw [h_diff, ← mul_assoc, C.half_sq_mul_four, one_mul]

/-- Chiral eigenspace action: $\Gamma \Pi_+ = \Pi_+$. -/
theorem gamma_mul_projPlus : C.gamma * C.projPlus = C.projPlus := by
  dsimp [projPlus, numberOp]
  rw [← mul_assoc, C.gamma_mul_a_star]

/-- Chiral eigenspace action: $\Gamma \Pi_- = -\Pi_-$. -/
theorem gamma_mul_projMinus : C.gamma * C.projMinus = - C.projMinus := by
  dsimp [projMinus, vacProj]
  rw [← mul_assoc, C.gamma_mul_a, neg_mul]

end SplitCliffordCell

/-! ### 3. Normalized Additive Cyclic Functionals -/

/-- A normalized additive functional with cyclicity; positivity is not assumed. -/
structure NormalizedCyclicFunctional (A : Type*) [Ring A] where
  tau : A → ℝ
  tau_add : ∀ x y, tau (x + y) = tau x + tau y
  tau_sub : ∀ x y, tau (x - y) = tau x - tau y
  tau_one : tau 1 = 1
  tau_comm : ∀ x y, tau (x * y) = tau (y * x)

namespace NormalizedCyclicFunctional

variable {A : Type*} [Ring A] (T : NormalizedCyclicFunctional A)

/-- The functional vanishes on commutators by additivity and cyclicity. -/
theorem tracial_commutator_zero (x y : A) :
    T.tau (x * y - y * x) = 0 := by
  rw [T.tau_sub, T.tau_comm x y, sub_self]

/-- Cyclic invariance for products of three elements. -/
theorem tracial_cyclic_three (x y z : A) :
    T.tau (x * y * z) = T.tau (y * z * x) := by
  calc
    T.tau (x * y * z) = T.tau (z * (x * y)) := by rw [T.tau_comm (x * y) z]
    _ = T.tau (z * x * y) := by rw [← mul_assoc]
    _ = T.tau (y * (z * x)) := by rw [T.tau_comm (z * x) y]
    _ = T.tau (y * z * x) := by rw [← mul_assoc]

end NormalizedCyclicFunctional

/-! ### 4. Cyclic-Functional Compression Identities -/

/-- The value of the normalized cyclic functional on the compression $P Γ P$. -/
def cyclicFunctionalCompression {A : Type*} [Ring A] (T : NormalizedCyclicFunctional A) (P Gamma : A) : ℝ :=
  T.tau (P * Gamma * P)

/-- Cyclicity reduces the compressed functional value when `P` is idempotent. -/
theorem cyclicFunctionalCompression_eq_tau_mul {A : Type*} [Ring A]
    (T : NormalizedCyclicFunctional A) (P Gamma : A) (hP : P ^ 2 = P) :
    cyclicFunctionalCompression T P Gamma = T.tau (P * Gamma) := by
  dsimp [cyclicFunctionalCompression]
  have h_comm := T.tau_comm (P * Gamma) P
  have hP2 : P * P = P := by rwa [sq] at hP
  calc
    T.tau (P * Gamma * P) = T.tau (P * (P * Gamma)) := h_comm
    _ = T.tau (P * P * Gamma) := by rw [← mul_assoc P P Gamma]
    _ = T.tau (P * Gamma) := by rw [hP2]

/-- The functional value at the identity vanishes when its argument has value zero. -/
theorem cyclicFunctional_compression_one_vanishes {A : Type*} [Ring A]
    (T : NormalizedCyclicFunctional A) (Gamma : A) (hG : T.tau Gamma = 0) :
    cyclicFunctionalCompression T 1 Gamma = 0 := by
  have h1 : (1 : A) ^ 2 = 1 := by rw [sq, one_mul]
  rw [cyclicFunctionalCompression_eq_tau_mul T 1 Gamma h1, one_mul, hG]

/-- Cyclic-functional compression is invariant under the stated algebraic unitary conjugation. -/
theorem cyclicFunctional_compression_unitary_invariant {A : Type*} [Ring A]
    (T : NormalizedCyclicFunctional A) (P Gamma U U_star : A)
    (hP : P ^ 2 = P)
    (hU_left : U_star * U = 1)
    (hU_right : U * U_star = 1)
    (hU_comm : U * Gamma = Gamma * U) :
    cyclicFunctionalCompression T (U * P * U_star) Gamma = cyclicFunctionalCompression T P Gamma := by
  have hP2 : P * P = P := by rwa [sq] at hP
  have hUPU_sq : (U * P * U_star) ^ 2 = U * P * U_star := by
    rw [sq]
    calc
      (U * P * U_star) * (U * P * U_star) =
          U * P * (U_star * U) * P * U_star := by noncomm_ring
      _ = U * P * 1 * P * U_star := by rw [hU_left]
      _ = U * (P * P) * U_star := by noncomm_ring
      _ = U * P * U_star := by rw [hP2]
  rw [cyclicFunctionalCompression_eq_tau_mul T (U * P * U_star) Gamma hUPU_sq]
  rw [cyclicFunctionalCompression_eq_tau_mul T P Gamma hP]
  calc
    T.tau (U * P * U_star * Gamma) = T.tau (U * P * (U_star * Gamma)) := by noncomm_ring
    _ = T.tau ((U_star * Gamma) * (U * P)) := by rw [T.tau_comm]
    _ = T.tau (U_star * (Gamma * U) * P) := by noncomm_ring
    _ = T.tau (U_star * (U * Gamma) * P) := by rw [hU_comm]
    _ = T.tau ((U_star * U) * (Gamma * P)) := by noncomm_ring
    _ = T.tau (1 * (Gamma * P)) := by rw [hU_left]
    _ = T.tau (Gamma * P) := by rw [one_mul]
    _ = T.tau (P * Gamma) := by rw [T.tau_comm]

/-! ### 5. Inductive Colimit Matrix Stages & Canonical State Descent -/

/-- Canonical stage inclusion preserves operator multiplication. -/
theorem canonicalStageHom_operator_mul (n : ℕ) (X Y : Stage n) :
    canonicalStageHom n (X * Y) = canonicalStageHom n X * canonicalStageHom n Y := by
  exact (canonicalStageHom n).map_mul X Y

/-- Canonical stage inclusion preserves operator star-involution. -/
theorem canonicalStageHom_operator_star (n : ℕ) (X : Stage n) :
    canonicalStageHom n (star X) = star (canonicalStageHom n X) := by
  exact (canonicalStageHom n).map_star' X

/-- Canonical direct limit trace satisfies tracial commutator vanishing for all limit operators. -/
theorem limitTrace_operator_commutator (X Y : MatrixStageLimit) :
    limitTrace (X * Y - Y * X) = 0 := by
  have h_comm := limitTrace_mul_comm X Y
  have h_sub : limitTrace (X * Y - Y * X) = limitTrace (X * Y) - limitTrace (Y * X) := by
    change limitNormalizedTrace (X * Y - Y * X) = limitNormalizedTrace (X * Y) - limitNormalizedTrace (Y * X)
    exact map_sub limitNormalizedTrace (X * Y) (Y * X)
  rw [h_sub, h_comm, sub_self]

/-- Descended trace compatibility on all finite stage operators. -/
theorem stage_operator_trace_compat (n : ℕ) (X : Stage n) :
    limitTrace (canonicalStageHom n X) = normalizedTrace n X := by
  have h := inductiveLimitTrace_comp_stage n
  have h_app := LinearMap.congr_fun h X
  exact h_app

/-- The chiral trace readout on the actual algebraic matrix-stage colimit.

This is an algebraic trace functional on `MatrixStageLimit`; it is not a
Fredholm index or a construction of a Sato Grassmannian. -/
def limitChiralTraceReadout (P Gamma : MatrixStageLimit) : ℂ :=
  limitTrace (P * Gamma * P)

/-- The colimit chiral readout agrees with the normalized finite-stage trace
when both operators come from the same matrix stage. -/
theorem limitChiralTraceReadout_stage (n : ℕ) (P Gamma : Stage n) :
    limitChiralTraceReadout (canonicalStageHom n P) (canonicalStageHom n Gamma) =
      normalizedTrace n (P * Gamma * P) := by
  unfold limitChiralTraceReadout
  rw [← canonicalStageHom_operator_mul n P Gamma,
    ← canonicalStageHom_operator_mul n (P * Gamma) P]
  exact stage_operator_trace_compat n (P * Gamma * P)

/-- Idempotency reduces the colimit chiral trace readout to a two-factor
pairing by cyclicity of the actual descended trace. -/
theorem limitChiralTraceReadout_eq_mul_of_idempotent
    (P Gamma : MatrixStageLimit) (hP : P * P = P) :
    limitChiralTraceReadout P Gamma = limitTrace (P * Gamma) := by
  unfold limitChiralTraceReadout
  calc
    limitTrace (P * Gamma * P) = limitTrace (P * (P * Gamma)) := by
      rw [limitTrace_mul_comm (P * Gamma) P]
    _ = limitTrace (P * P * Gamma) := by rw [← mul_assoc]
    _ = limitTrace (P * Gamma) := by rw [hP]

/-- The actual complex matrix-stage colimit trace readout is invariant under
star-unitary conjugation by an operator commuting with the grading element.

This theorem concerns the algebraic direct-limit trace already defined by
`MatrixStageInductiveLimit`; it does not assert Fredholm-index invariance. -/
theorem limitChiralTraceReadout_starUnitary_invariant
    (P Gamma U : MatrixStageLimit)
    (hP : P * P = P)
    (hU_left : star U * U = 1)
    (hU_right : U * star U = 1)
    (hU_comm : U * Gamma = Gamma * U) :
    limitChiralTraceReadout (U * P * star U) Gamma =
      limitChiralTraceReadout P Gamma := by
  have h_conj_idem :
      (U * P * star U) * (U * P * star U) = U * P * star U := by
    calc
      (U * P * star U) * (U * P * star U) = U * P * (star U * U) * P * star U := by
        noncomm_ring
      _ = U * P * 1 * P * star U := by rw [hU_left]
      _ = U * P * P * star U := by noncomm_ring
      _ = U * (P * P) * star U := by noncomm_ring
      _ = U * P * star U := by rw [hP]
  have h_conj_gamma : star U * Gamma * U = Gamma := by
    calc
      star U * Gamma * U = star U * (Gamma * U) := by rw [mul_assoc]
      _ = star U * (U * Gamma) := by rw [← hU_comm]
      _ = (star U * U) * Gamma := by rw [← mul_assoc]
      _ = Gamma := by rw [hU_left, one_mul]
  calc
    limitChiralTraceReadout (U * P * star U) Gamma =
        limitTrace ((U * P * star U) * Gamma) :=
      limitChiralTraceReadout_eq_mul_of_idempotent (U * P * star U) Gamma h_conj_idem
    _ = limitTrace (U * (P * star U * Gamma)) := by congr 1 <;> noncomm_ring
    _ = limitTrace ((P * star U * Gamma) * U) := limitTrace_mul_comm U (P * star U * Gamma)
    _ = limitTrace (P * (star U * Gamma * U)) := by congr 1 <;> noncomm_ring
    _ = limitTrace (P * Gamma) := by rw [h_conj_gamma]
    _ = limitChiralTraceReadout P Gamma :=
      (limitChiralTraceReadout_eq_mul_of_idempotent P Gamma hP).symm

end InfoGeometry.SuperGrassmannian.SatoColimitTriality
