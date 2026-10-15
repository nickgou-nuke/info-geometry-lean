import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Abel

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Majorana CAR Algebra, Nilpotent Lightcone Modes, and Chiral Superalgebra

Module: `InfoGeometry.SuperGrassmannian.MajoranaCARSuperalgebra`

This module formalizes the foundational first pillar of the Split Metric
$\mathcal{C}\ell(1, 1)^n$ Tower:
1. **The Split Clifford Cell $\mathcal{C}\ell(1, 1)$**:
   - Generators $e, f$ in a ring $R$ equipped with central element $1/2$.
   - Hyperbolic/spacelike generator: $e^2 = 1$.
   - Elliptic/timelike generator: $f^2 = -1$.
   - Anti-commutation: $e f + f e = 0$.
2. **Majorana CAR Ladder Operators (Nilpotent Lightcone Modes)**:
   - Annihilation mode: $a = \frac{1}{2}(e + f)$.
   - Creation mode: $a^* = \frac{1}{2}(e - f)$.
   - Nilpotency: $a^2 = 0$ and $(a^*)^2 = 0$ (Pauli exclusion on the lightcone).
   - Canonical Anticommutation Relation (CAR): $\{a, a^*\} = a a^* + a^* a = 1$.
3. **Chiral Grading Operator $\Gamma = e f$**:
   - Involution / reflection: $\Gamma^2 = 1$.
   - Fermion odd parity: $\Gamma a + a \Gamma = 0$ and $\Gamma a^* + a^* \Gamma = 0$.
   - Spectral eigenspaces: $\Gamma a = -a$, $a \Gamma = a$, $\Gamma a^* = a^*$, $a^* \Gamma = -a^*$.
4. **Number and Vacuum Projectors**:
   - Number operator: $N = a^* a = \frac{1}{2}(1 + \Gamma)$.
   - Vacuum projection: $1 - N = a a^* = \frac{1}{2}(1 - \Gamma)$.
   - Projector idempotence: $N^2 = N$ and $(1 - N)^2 = 1 - N$.
   - Orthogonal annihilation: $N (1 - N) = 0$ and $(1 - N) N = 0$.
   - Parity reflection formula: $\Gamma = 2N - 1$, and $1 - 2N = f e = -\Gamma$.
5. **Quantum Ladder Dynamics & Vacuum Annihilation**:
   - $[N, a] = -a$ (annihilation operator reduces particle number).
   - $[N, a^*] = +a^*$ (creation operator increases particle number).
   - $a (1 - N) = 0$ (annihilation destroys the vacuum state).
   - $(1 - N) a^* = 0$ (creation maps into the orthogonal occupied sector).
   - $[N, \Gamma] = 0$ (number operator is parity-even).
6. **Master Verification Certificate**:
   - Structure `MajoranaCARSuperalgebraCertificate : Prop`.
   - Theorem `compile_majorana_car_superalgebra` with 0 sorry, 0 admit, 0 custom axioms.
-/

namespace InfoGeometry.SuperGrassmannian.MajoranaCAR

/-! ### 1. Split Clifford Cell Structure Cl(1,1) -/

/-- A split Clifford cell $\mathcal{C}\ell(1, 1)$ in a ring `R` equipped with central scalar `half`. -/
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

/-- Spacelike generator $e$ squares to $+1$. -/
theorem e_sq_one : C.e ^ 2 = 1 := C.e_sq

/-- Timelike generator $f$ squares to $-1$. -/
theorem f_sq_neg_one : C.f ^ 2 = -1 := C.f_sq

/-- Spacelike and timelike generators anticommute: $\{e, f\} = 0$. -/
theorem ef_anticomm_zero : C.e * C.f + C.f * C.e = 0 := C.anticomm

/-- Spacelike generator multiplication: $e \cdot e = 1$. -/
lemma e_mul_e : C.e * C.e = 1 := by
  have h := C.e_sq
  rwa [sq] at h

/-- Timelike generator multiplication: $f \cdot f = -1$. -/
lemma f_mul_f : C.f * C.f = -1 := by
  have h := C.f_sq
  rwa [sq] at h

/-- Anticommutation flip: $f e = - (e f)$. -/
lemma fe_eq_neg_ef : C.f * C.e = - (C.e * C.f) := by
  calc
    C.f * C.e = (C.e * C.f + C.f * C.e) - C.e * C.f := by abel
    _ = 0 - C.e * C.f := by rw [C.anticomm]
    _ = - (C.e * C.f) := by abel

/-- Anticommutation flip: $e f = - (f e)$. -/
lemma ef_eq_neg_fe : C.e * C.f = - (C.f * C.e) := by
  rw [fe_eq_neg_ef, neg_neg]

/-- Left scalar multiplication: $2 \cdot \text{half} = 1$. -/
lemma two_mul_half : (2 : R) * C.half = 1 := by
  rw [two_mul, C.two_half]

/-- Right scalar multiplication: $\text{half} \cdot 2 = 1$. -/
lemma half_mul_two : C.half * (2 : R) = 1 := by
  rw [mul_two, C.two_half]

/-- Product of halves normalized by 4: $(\text{half} \cdot \text{half}) \cdot 4 = 1$. -/
lemma half_sq_mul_four : (C.half * C.half) * (4 : R) = 1 := by
  have h4 : (4 : R) = (2 : R) * (2 : R) := by norm_num
  rw [h4, ← mul_assoc (C.half * C.half) 2 2, mul_assoc C.half C.half 2, half_mul_two, mul_one, half_mul_two]

/-- Central commutation of half-scalar factors across a product. -/
lemma mul_half_mul_half (x y : R) :
    (C.half * x) * (C.half * y) = (C.half * C.half) * (x * y) := by
  calc
    (C.half * x) * (C.half * y) = C.half * (x * C.half) * y := by noncomm_ring
    _ = C.half * (C.half * x) * y := by rw [C.half_comm x]
    _ = (C.half * C.half) * (x * y) := by noncomm_ring

/-- Central pull-through of half-scalar on the left. -/
lemma mul_half_assoc (x y : R) : x * (C.half * y) = C.half * (x * y) := by
  calc
    x * (C.half * y) = (x * C.half) * y := by rw [← mul_assoc]
    _ = (C.half * x) * y := by rw [← C.half_comm x]
    _ = C.half * (x * y) := by rw [mul_assoc]

/-! ### 2. Majorana CAR Ladder Operators & Nilpotent Lightcone Modes -/

/-- Annihilation ladder operator: $a = \frac{1}{2}(e + f)$. -/
def a : R := C.half * (C.e + C.f)

/-- Creation ladder operator: $a^* = \frac{1}{2}(e - f)$. -/
def a_star : R := C.half * (C.e - C.f)

/-- Chiral grading operator: $\Gamma = e f$. -/
def Gamma : R := C.e * C.f

/-- Number operator: $N = a^* a$. -/
def N : R := a_star C * a C

/-- Annihilation operator multiplication self-annihilates: $a \cdot a = 0$. -/
theorem a_mul_a : a C * a C = 0 := by
  dsimp [a]
  rw [mul_half_mul_half]
  have h_inner : (C.e + C.f) * (C.e + C.f) = 0 := by
    calc
      (C.e + C.f) * (C.e + C.f) = C.e * C.e + (C.e * C.f + C.f * C.e) + C.f * C.f := by noncomm_ring
      _ = 1 + 0 + -1 := by rw [e_mul_e, C.anticomm, f_mul_f]
      _ = 0 := by abel
  rw [h_inner, mul_zero]

/-- **Theorem**: Annihilation mode is nilpotent: $a^2 = 0$. -/
theorem a_sq_zero : (a C) ^ 2 = 0 := by
  rw [sq, a_mul_a]

/-- Creation operator multiplication self-annihilates: $a^* \cdot a^* = 0$. -/
theorem a_star_mul_a_star : a_star C * a_star C = 0 := by
  dsimp [a_star]
  rw [mul_half_mul_half]
  have h_inner : (C.e - C.f) * (C.e - C.f) = 0 := by
    calc
      (C.e - C.f) * (C.e - C.f) = C.e * C.e - (C.e * C.f + C.f * C.e) + C.f * C.f := by noncomm_ring
      _ = 1 - 0 + -1 := by rw [e_mul_e, C.anticomm, f_mul_f]
      _ = 0 := by abel
  rw [h_inner, mul_zero]

/-- **Theorem**: Creation mode is nilpotent: $(a^*)^2 = 0$. -/
theorem a_star_sq_zero : (a_star C) ^ 2 = 0 := by
  rw [sq, a_star_mul_a_star]

/-- **Theorem**: Canonical Anticommutation Relation (CAR): $\{a, a^*\} = 1$. -/
theorem car_anticommutator : a C * a_star C + a_star C * a C = 1 := by
  dsimp [a, a_star]
  rw [mul_half_mul_half, mul_half_mul_half, ← mul_add]
  have h_sum : (C.e + C.f) * (C.e - C.f) + (C.e - C.f) * (C.e + C.f) = (4 : R) := by
    calc
      (C.e + C.f) * (C.e - C.f) + (C.e - C.f) * (C.e + C.f) =
          (C.e * C.e - C.f * C.f) + (C.e * C.e - C.f * C.f) := by noncomm_ring
      _ = (1 - -1) + (1 - -1) := by rw [e_mul_e, f_mul_f]
      _ = (4 : R) := by norm_num
  rw [h_sum]
  exact half_sq_mul_four C

/-- Reverse CAR decomposition: $a \cdot a^* = 1 - N$. -/
theorem a_mul_a_star_eq : a C * a_star C = 1 - N C := by
  dsimp [N]
  calc
    a C * a_star C = (a C * a_star C + a_star C * a C) - a_star C * a C := by abel
    _ = 1 - a_star C * a C := by rw [car_anticommutator]

/-! ### 3. Chiral Grading Operator & Odd Parity -/

/-- Chiral grading operator squares to identity: $\Gamma \cdot \Gamma = 1$. -/
theorem Gamma_mul_Gamma : Gamma C * Gamma C = 1 := by
  dsimp [Gamma]
  calc
    (C.e * C.f) * (C.e * C.f) = C.e * (C.f * C.e) * C.f := by noncomm_ring
    _ = C.e * (- (C.e * C.f)) * C.f := by rw [fe_eq_neg_ef]
    _ = - (C.e * C.e) * (C.f * C.f) := by noncomm_ring
    _ = - (1 : R) * (-1) := by rw [e_mul_e, f_mul_f]
    _ = 1 := by norm_num

/-- **Theorem**: Chiral grading operator is an involution: $\Gamma^2 = 1$. -/
theorem Gamma_sq : (Gamma C) ^ 2 = 1 := by
  rw [sq, Gamma_mul_Gamma]

/-- Left action of chiral grading on annihilation mode: $\Gamma \cdot a = -a$. -/
theorem Gamma_mul_a : Gamma C * a C = - a C := by
  dsimp [Gamma, a]
  rw [mul_half_assoc]
  have h_inner : (C.e * C.f) * (C.e + C.f) = - (C.e + C.f) := by
    calc
      (C.e * C.f) * (C.e + C.f) = C.e * (C.f * C.e) + C.e * (C.f * C.f) := by noncomm_ring
      _ = C.e * (- (C.e * C.f)) + C.e * (-1) := by rw [fe_eq_neg_ef, f_mul_f]
      _ = - (C.e * C.e) * C.f - C.e := by noncomm_ring
      _ = - 1 * C.f - C.e := by rw [e_mul_e]
      _ = - (C.e + C.f) := by noncomm_ring
  rw [h_inner, mul_neg]

/-- Right action of chiral grading on annihilation mode: $a \cdot \Gamma = a$. -/
theorem a_mul_Gamma : a C * Gamma C = a C := by
  dsimp [Gamma, a]
  rw [mul_assoc]
  have h_inner : (C.e + C.f) * (C.e * C.f) = C.e + C.f := by
    calc
      (C.e + C.f) * (C.e * C.f) = (C.e * C.e) * C.f + C.f * (C.e * C.f) := by noncomm_ring
      _ = (1 : R) * C.f + (C.f * C.e) * C.f := by rw [e_mul_e, mul_assoc]
      _ = C.f + (- (C.e * C.f)) * C.f := by rw [fe_eq_neg_ef, one_mul]
      _ = C.f - C.e * (C.f * C.f) := by noncomm_ring
      _ = C.f - C.e * (-1) := by rw [f_mul_f]
      _ = C.e + C.f := by noncomm_ring
  rw [h_inner]

/-- **Theorem**: Chiral grading anticommutes with annihilation mode: $\{\Gamma, a\} = 0$. -/
theorem Gamma_anticomm_a : Gamma C * a C + a C * Gamma C = 0 := by
  rw [Gamma_mul_a, a_mul_Gamma]
  abel

/-- Left action of chiral grading on creation mode: $\Gamma \cdot a^* = a^*$. -/
theorem Gamma_mul_a_star : Gamma C * a_star C = a_star C := by
  dsimp [Gamma, a_star]
  rw [mul_half_assoc]
  have h_inner : (C.e * C.f) * (C.e - C.f) = C.e - C.f := by
    calc
      (C.e * C.f) * (C.e - C.f) = C.e * (C.f * C.e) - C.e * (C.f * C.f) := by noncomm_ring
      _ = C.e * (- (C.e * C.f)) - C.e * (-1) := by rw [fe_eq_neg_ef, f_mul_f]
      _ = - (C.e * C.e) * C.f + C.e := by noncomm_ring
      _ = - 1 * C.f + C.e := by rw [e_mul_e]
      _ = C.e - C.f := by noncomm_ring
  rw [h_inner]

/-- Right action of chiral grading on creation mode: $a^* \cdot \Gamma = -a^*$. -/
theorem a_star_mul_Gamma : a_star C * Gamma C = - a_star C := by
  dsimp [Gamma, a_star]
  rw [mul_assoc]
  have h_inner : (C.e - C.f) * (C.e * C.f) = - (C.e - C.f) := by
    calc
      (C.e - C.f) * (C.e * C.f) = (C.e * C.e) * C.f - C.f * (C.e * C.f) := by noncomm_ring
      _ = (1 : R) * C.f - (C.f * C.e) * C.f := by rw [e_mul_e, mul_assoc]
      _ = C.f - (- (C.e * C.f)) * C.f := by rw [fe_eq_neg_ef, one_mul]
      _ = C.f + C.e * (C.f * C.f) := by noncomm_ring
      _ = C.f + C.e * (-1) := by rw [f_mul_f]
      _ = - (C.e - C.f) := by noncomm_ring
  rw [h_inner, mul_neg]

/-- **Theorem**: Chiral grading anticommutes with creation mode: $\{\Gamma, a^*\} = 0$. -/
theorem Gamma_anticomm_a_star : Gamma C * a_star C + a_star C * Gamma C = 0 := by
  rw [Gamma_mul_a_star, a_star_mul_Gamma]
  abel

/-! ### 4. Number and Vacuum Projectors & Orthogonal Annihilation -/

/-- Number operator multiplication is idempotent: $N \cdot N = N$. -/
theorem N_mul_N : N C * N C = N C := by
  dsimp [N]
  have h_car : a C * a_star C = 1 - a_star C * a C := by
    calc
      a C * a_star C = (a C * a_star C + a_star C * a C) - a_star C * a C := by abel
      _ = 1 - a_star C * a C := by rw [car_anticommutator]
  calc
    (a_star C * a C) * (a_star C * a C) =
        a_star C * (a C * a_star C) * a C := by noncomm_ring
    _ = a_star C * (1 - a_star C * a C) * a C := by rw [h_car]
    _ = a_star C * a C - (a_star C * a_star C) * (a C * a C) := by noncomm_ring
    _ = a_star C * a C - 0 * 0 := by rw [a_star_mul_a_star, a_mul_a]
    _ = a_star C * a C := by noncomm_ring

/-- **Theorem**: Number operator is an idempotent projector: $N^2 = N$. -/
theorem N_sq : (N C) ^ 2 = N C := by
  rw [sq, N_mul_N]

/-- **Theorem**: Vacuum projector is an idempotent projector: $(1 - N)^2 = 1 - N$. -/
theorem vac_proj_sq : (1 - N C) ^ 2 = 1 - N C := by
  rw [sq]
  calc
    (1 - N C) * (1 - N C) = 1 - (N C + N C) + N C * N C := by noncomm_ring
    _ = 1 - (N C + N C) + N C := by rw [N_mul_N]
    _ = 1 - N C := by abel

/-- **Theorem**: Orthogonal annihilation: $N \cdot (1 - N) = 0$. -/
theorem ortho_annihilation : N C * (1 - N C) = 0 := by
  calc
    N C * (1 - N C) = N C - N C * N C := by noncomm_ring
    _ = N C - N C := by rw [N_mul_N]
    _ = 0 := by abel

/-- Orthogonal annihilation from the left: $(1 - N) \cdot N = 0$. -/
theorem ortho_annihilation_left : (1 - N C) * N C = 0 := by
  calc
    (1 - N C) * N C = N C - N C * N C := by noncomm_ring
    _ = N C - N C := by rw [N_mul_N]
    _ = 0 := by abel

/-- Number operator formula in terms of chiral grading: $N = \frac{1}{2}(1 + \Gamma)$. -/
lemma N_eq_half_one_add_Gamma : N C = C.half * (1 + Gamma C) := by
  dsimp [N, a_star, a, Gamma]
  rw [mul_half_mul_half]
  have h_inner : (C.e - C.f) * (C.e + C.f) = (2 : R) * (1 + C.e * C.f) := by
    calc
      (C.e - C.f) * (C.e + C.f) = C.e * C.e + C.e * C.f - C.f * C.e - C.f * C.f := by noncomm_ring
      _ = 1 + C.e * C.f - (- (C.e * C.f)) - (-1) := by rw [e_mul_e, fe_eq_neg_ef, f_mul_f]
      _ = 2 + 2 * (C.e * C.f) := by
        have : (1 : R) + C.e * C.f - (- (C.e * C.f)) - (-1) =
            (1 - -1 : R) + (C.e * C.f + C.e * C.f) := by abel
        rw [this]
        norm_num
        rw [← two_mul]
      _ = (2 : R) * 1 + (2 : R) * (C.e * C.f) := by rw [mul_one]
      _ = (2 : R) * (1 + C.e * C.f) := by rw [mul_add]
  rw [h_inner, ← mul_assoc, mul_assoc C.half C.half 2, half_mul_two, mul_one]

/-- Doubled number operator equals $1 + \Gamma$: $2 N = 1 + \Gamma$. -/
theorem two_mul_N : (2 : R) * N C = 1 + Gamma C := by
  rw [N_eq_half_one_add_Gamma, ← mul_assoc, two_mul_half, one_mul]

/-- **Theorem**: Parity formula for chiral grading: $\Gamma = 2N - 1$. -/
theorem Gamma_eq_two_N_sub_one : Gamma C = (2 : R) * N C - 1 := by
  rw [two_mul_N]
  abel

/-- **Theorem**: Parity reflection formula in terms of $f e$: $1 - 2N = f e = -\Gamma$. -/
theorem parity_reflection_fe : 1 - (2 : R) * N C = C.f * C.e := by
  rw [two_mul_N]
  have h1 : 1 - (1 + Gamma C) = - Gamma C := by abel
  rw [h1]
  dsimp [Gamma]
  exact (fe_eq_neg_ef C).symm

/-- **Theorem**: Parity reflection formula in terms of the vacuum projector: $1 - 2(a a^*) = \Gamma$. -/
theorem vac_parity_reflection : 1 - (2 : R) * (a C * a_star C) = Gamma C := by
  rw [a_mul_a_star_eq, mul_sub, mul_one, two_mul_N]
  calc
    1 - ((2 : R) - (1 + Gamma C)) = 1 - 2 + (1 + Gamma C) := by abel
    _ = (1 - 2 + 1 : R) + Gamma C := by abel
    _ = 0 + Gamma C := by
      have : (1 - 2 + 1 : R) = 0 := by norm_num
      rw [this]
    _ = Gamma C := by rw [zero_add]

/-! ### 5. Quantum Ladder Dynamics & Vacuum Annihilation -/

/-- Number operator left action on annihilation: $N \cdot a = 0$. -/
theorem N_mul_a : N C * a C = 0 := by
  dsimp [N]
  rw [mul_assoc, a_mul_a, mul_zero]

/-- Annihilation right action on number operator: $a \cdot N = a$. -/
theorem a_mul_N : a C * N C = a C := by
  dsimp [N]
  calc
    a C * (a_star C * a C) = (a C * a_star C) * a C := by rw [← mul_assoc]
    _ = (1 - N C) * a C := by rw [a_mul_a_star_eq]
    _ = 1 * a C - N C * a C := by noncomm_ring
    _ = a C - 0 := by rw [one_mul, N_mul_a]
    _ = a C := by abel

/-- **Theorem**: Ladder commutator lowering relation: $[N, a] = -a$. -/
theorem ladder_bracket_N_a : N C * a C - a C * N C = - a C := by
  rw [N_mul_a, a_mul_N]
  abel

/-- Creation operator left action on number operator: $a^* \cdot N = 0$. -/
theorem a_star_mul_N : a_star C * N C = 0 := by
  dsimp [N]
  calc
    a_star C * (a_star C * a C) = (a_star C * a_star C) * a C := by rw [← mul_assoc]
    _ = 0 * a C := by rw [a_star_mul_a_star]
    _ = 0 := by rw [zero_mul]

/-- Number operator right action on creation: $N \cdot a^* = a^*$. -/
theorem N_mul_a_star : N C * a_star C = a_star C := by
  dsimp [N]
  calc
    (a_star C * a C) * a_star C = a_star C * (a C * a_star C) := by rw [mul_assoc]
    _ = a_star C * (1 - N C) := by rw [a_mul_a_star_eq]
    _ = a_star C * 1 - a_star C * N C := by noncomm_ring
    _ = a_star C - 0 := by rw [mul_one, a_star_mul_N]
    _ = a_star C := by abel

/-- **Theorem**: Ladder commutator raising relation: $[N, a^*] = +a^*$. -/
theorem ladder_bracket_N_a_star : N C * a_star C - a_star C * N C = a_star C := by
  rw [N_mul_a_star, a_star_mul_N]
  abel

/-- **Theorem**: Vacuum annihilation: $a \cdot (1 - N) = 0$. -/
theorem a_mul_vac_proj : a C * (1 - N C) = 0 := by
  calc
    a C * (1 - N C) = a C * 1 - a C * N C := by noncomm_ring
    _ = a C - a C := by rw [mul_one, a_mul_N]
    _ = 0 := by abel

/-- **Theorem**: Vacuum creation isolation: $(1 - N) \cdot a^* = 0$. -/
theorem vac_proj_mul_a_star : (1 - N C) * a_star C = 0 := by
  calc
    (1 - N C) * a_star C = 1 * a_star C - N C * a_star C := by noncomm_ring
    _ = a_star C - a_star C := by rw [one_mul, N_mul_a_star]
    _ = 0 := by abel

/-- Number operator right action on chiral grading: $N \cdot \Gamma = N$. -/
theorem N_mul_Gamma : N C * Gamma C = N C := by
  dsimp [N]
  calc
    (a_star C * a C) * Gamma C = a_star C * (a C * Gamma C) := by rw [mul_assoc]
    _ = a_star C * a C := by rw [a_mul_Gamma]

/-- Chiral grading left action on number operator: $\Gamma \cdot N = N$. -/
theorem Gamma_mul_N : Gamma C * N C = N C := by
  dsimp [N]
  calc
    Gamma C * (a_star C * a C) = (Gamma C * a_star C) * a C := by rw [← mul_assoc]
    _ = a_star C * a C := by rw [Gamma_mul_a_star]

/-- **Theorem**: Number operator is even (commutes with chiral grading): $[N, \Gamma] = 0$. -/
theorem bracket_N_Gamma : N C * Gamma C - Gamma C * N C = 0 := by
  rw [N_mul_Gamma, Gamma_mul_N]
  abel

end SplitCliffordCell

/-! ### 6. Master Verification Certificate -/

open SplitCliffordCell

/--
Master verification certificate for the first pillar of the Split Metric $\mathcal{C}\ell(1, 1)^n$ Tower:
"Majorana CAR Algebra, Nilpotent Lightcone Modes, and Chiral Superalgebra"
-/
structure MajoranaCARSuperalgebraCertificate : Prop where
  -- 1. Split Clifford cell
  e_sq : ∀ {R : Type*} [Ring R] (C : SplitCliffordCell R), (C.e) ^ 2 = 1
  f_sq : ∀ {R : Type*} [Ring R] (C : SplitCliffordCell R), (C.f) ^ 2 = -1
  ef_anticomm : ∀ {R : Type*} [Ring R] (C : SplitCliffordCell R), C.e * C.f + C.f * C.e = 0
  -- 2. Majorana CAR ladder operators
  a_nilpotent : ∀ {R : Type*} [Ring R] (C : SplitCliffordCell R), (a C) ^ 2 = 0
  a_star_nilpotent : ∀ {R : Type*} [Ring R] (C : SplitCliffordCell R), (a_star C) ^ 2 = 0
  car_anticommutator : ∀ {R : Type*} [Ring R] (C : SplitCliffordCell R), a C * a_star C + a_star C * a C = 1
  -- 3. Chiral grading operator
  gamma_involution : ∀ {R : Type*} [Ring R] (C : SplitCliffordCell R), (Gamma C) ^ 2 = 1
  gamma_odd_a : ∀ {R : Type*} [Ring R] (C : SplitCliffordCell R), Gamma C * a C + a C * Gamma C = 0
  gamma_odd_a_star : ∀ {R : Type*} [Ring R] (C : SplitCliffordCell R), Gamma C * a_star C + a_star C * Gamma C = 0
  -- 4. Number and vacuum projectors
  n_idempotent : ∀ {R : Type*} [Ring R] (C : SplitCliffordCell R), (N C) ^ 2 = N C
  vac_idempotent : ∀ {R : Type*} [Ring R] (C : SplitCliffordCell R), (1 - N C) ^ 2 = 1 - N C
  ortho_annihilation : ∀ {R : Type*} [Ring R] (C : SplitCliffordCell R), N C * (1 - N C) = 0
  gamma_parity_formula : ∀ {R : Type*} [Ring R] (C : SplitCliffordCell R), Gamma C = (2 : R) * N C - 1
  chiral_parity_reflection : ∀ {R : Type*} [Ring R] (C : SplitCliffordCell R), 1 - (2 : R) * N C = C.f * C.e
  vac_parity_reflection : ∀ {R : Type*} [Ring R] (C : SplitCliffordCell R), 1 - (2 : R) * (a C * a_star C) = Gamma C
  -- 5. Ladder dynamics and vacuum annihilation
  ladder_comm_annihilate : ∀ {R : Type*} [Ring R] (C : SplitCliffordCell R), N C * a C - a C * N C = - a C
  ladder_comm_create : ∀ {R : Type*} [Ring R] (C : SplitCliffordCell R), N C * a_star C - a_star C * N C = a_star C
  vacuum_annihilate : ∀ {R : Type*} [Ring R] (C : SplitCliffordCell R), a C * (1 - N C) = 0

/--
Instantiation of the master certificate with zero open assumptions (0 sorry, 0 admit, 0 custom axioms).
-/
theorem compile_majorana_car_superalgebra : MajoranaCARSuperalgebraCertificate where
  e_sq := fun C => C.e_sq_one
  f_sq := fun C => C.f_sq_neg_one
  ef_anticomm := fun C => C.ef_anticomm_zero
  a_nilpotent := fun C => C.a_sq_zero
  a_star_nilpotent := fun C => C.a_star_sq_zero
  car_anticommutator := fun C => C.car_anticommutator
  gamma_involution := fun C => C.Gamma_sq
  gamma_odd_a := fun C => C.Gamma_anticomm_a
  gamma_odd_a_star := fun C => C.Gamma_anticomm_a_star
  n_idempotent := fun C => C.N_sq
  vac_idempotent := fun C => C.vac_proj_sq
  ortho_annihilation := fun C => C.ortho_annihilation
  gamma_parity_formula := fun C => C.Gamma_eq_two_N_sub_one
  chiral_parity_reflection := fun C => C.parity_reflection_fe
  vac_parity_reflection := fun C => C.vac_parity_reflection
  ladder_comm_annihilate := fun C => C.ladder_bracket_N_a
  ladder_comm_create := fun C => C.ladder_bracket_N_a_star
  vacuum_annihilate := fun C => C.a_mul_vac_proj

end InfoGeometry.SuperGrassmannian.MajoranaCAR
