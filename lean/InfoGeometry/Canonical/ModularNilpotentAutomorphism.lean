import InfoGeometry.Canonical.SplitCliffordSourceWickBase
import Mathlib.Tactic

/-!
# InfoGeometry.Canonical.ModularNilpotentAutomorphism

Finite nilpotent modular automorphism seed.

This file proves the concrete algebraic expansion

  `(1 + tN) A (1 - tN)
     = A + t • (N*A - A*N) - (t*t) • (N*A*N)`

inside `M₂(ℝ)` for the square-zero parabolic atom `N`.

It also proves the local zero free-energy readout

  `(Δ - 1) - log(Δ) = 0`

where, in the nilpotent sector, `Δ = 1 + N` and `log(Δ)` is represented by
the truncated logarithm `N`.

No Tomita--Takesaki theorem.
No Type III predual theorem.
No KMS analytic continuation.
No Virasoro central-charge theorem.
-/

namespace InfoGeometry.Canonical.ModularNilpotentAutomorphism

open Matrix
open InfoGeometry.Canonical.SplitCliffordSourceWickBase

/-- Local modular perturbation `Δ = 1 + N`. -/
def Delta : M2R :=
  (1 : M2R) + N

/--
Nilpotent logarithmic modular coordinate.

For `N² = 0`, the formal logarithm of `1 + N` truncates to `N`.
-/
def logModular : M2R :=
  N

/-- Regularized modular flux coordinate `Δ - 1`. -/
def entropyFlux : M2R :=
  Delta - (1 : M2R)

/-- Local information free-energy operator `(Δ - 1) - log(Δ)`. -/
def informationFreeEnergy : M2R :=
  entropyFlux - logModular

/-- The parabolic atom is square-zero. -/
@[simp]
theorem N_sq_zero :
    N * N = (0 : M2R) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [N, Matrix.mul_apply, Fin.sum_univ_two]

/-- The regularized modular flux is exactly the nilpotent generator. -/
@[simp]
theorem entropyFlux_eq_N :
    entropyFlux = N := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [entropyFlux, Delta, N]

/--
Local information free energy vanishes exactly:

`(Δ - 1) - log(Δ) = N - N = 0`.
-/
@[simp]
theorem informationFreeEnergy_eq_zero :
    informationFreeEnergy = (0 : M2R) := by
  unfold informationFreeEnergy logModular
  rw [entropyFlux_eq_N]
  simp

/-- Nilpotent modular flow `E(t)=1+tN`. -/
def nilpotentFlow (t : ℝ) : M2R :=
  (1 : M2R) + t • N

/-- The nilpotent flow starts at the identity. -/
@[simp]
theorem nilpotentFlow_zero :
    nilpotentFlow 0 = (1 : M2R) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [nilpotentFlow, N]

/-- At time `1`, the nilpotent flow is `Δ`. -/
@[simp]
theorem nilpotentFlow_one :
    nilpotentFlow 1 = Delta := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [nilpotentFlow, Delta, N]

/--
Nilpotent flow group law:

`(1+sN)(1+tN)=1+(s+t)N`.
-/
theorem nilpotentFlow_mul (s t : ℝ) :
    nilpotentFlow s * nilpotentFlow t = nilpotentFlow (s + t) := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [nilpotentFlow, N, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [nilpotentFlow, N, Matrix.mul_apply, Fin.sum_univ_two]
    simpa [add_comm]
  · simp [nilpotentFlow, N, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [nilpotentFlow, N, Matrix.mul_apply, Fin.sum_univ_two]

/--
Finite-power law for the nilpotent flow:
`(E(t))^n = E(n t)`.
-/
theorem nilpotentFlow_pow (t : ℝ) (n : ℕ) :
    (nilpotentFlow t) ^ n = nilpotentFlow ((n : ℝ) * t) := by
  induction n with
  | zero =>
      simp [nilpotentFlow]
  | succ n ih =>
      calc
        (nilpotentFlow t) ^ (n + 1)
            = (nilpotentFlow t) ^ n * nilpotentFlow t := by simp [pow_succ]
        _ = nilpotentFlow ((n : ℝ) * t) * nilpotentFlow t := by simpa [ih]
        _ = nilpotentFlow (((n : ℝ) * t) + t) := by
              simpa [add_comm] using nilpotentFlow_mul ((n : ℝ) * t) t
        _ = nilpotentFlow (((n + 1 : ℕ) : ℝ) * t) := by
              simp [Nat.cast_add, add_mul, one_mul, add_comm, add_left_comm, add_assoc]

/-- The inverse of `E(t)` is `E(-t)`. -/
@[simp]
theorem nilpotentFlow_mul_neg (t : ℝ) :
    nilpotentFlow t * nilpotentFlow (-t) = (1 : M2R) := by
  rw [nilpotentFlow_mul]
  simp

/-- The opposite inverse identity. -/
@[simp]
theorem nilpotentFlow_neg_mul (t : ℝ) :
    nilpotentFlow (-t) * nilpotentFlow t = (1 : M2R) := by
  rw [nilpotentFlow_mul]
  simp

/--
Finite nilpotent modular automorphism:

`σₜ(A)=E(t) A E(-t)`.
-/
def modularAutomorphism (t : ℝ) (A : M2R) : M2R :=
  nilpotentFlow t * A * nilpotentFlow (-t)

/--
Exact polynomial expansion of the nilpotent modular automorphism.

This is the concrete finite replacement for any BCH/exponential-series claim
in the square-zero sector.
-/
theorem modularAutomorphism_exact_expansion
    (t : ℝ) (A : M2R) :
    modularAutomorphism t A =
      A + t • (N * A - A * N) - (t * t) • (N * A * N) := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [modularAutomorphism, nilpotentFlow, N, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  · simp [modularAutomorphism, nilpotentFlow, N, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    ring
  · simp [modularAutomorphism, nilpotentFlow, N, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  · simp [modularAutomorphism, nilpotentFlow, N, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    simpa [mul_comm, add_comm, add_left_comm, add_assoc]

/-- At time zero, the modular automorphism is the identity on operators. -/
@[simp]
theorem modularAutomorphism_zero
    (A : M2R) :
    modularAutomorphism 0 A = A := by
  unfold modularAutomorphism
  simp

/--
If an operator commutes with the nilpotent generator `N`,
the finite nilpotent modular automorphism fixes it for all times.
-/
theorem modularAutomorphism_eq_self_of_commute_N
    (t : ℝ) (A : M2R)
    (hcomm : N * A = A * N) :
    modularAutomorphism t A = A := by
  rw [modularAutomorphism_exact_expansion]
  rw [hcomm]
  have hANN : A * N * N = 0 := by
    calc
      A * N * N = A * (N * N) := by simp [mul_assoc]
      _ = 0 := by simp [N_sq_zero]
  simp [hANN]

/--
Difference from identity at finite time.
-/
theorem modularAutomorphism_sub_self
    (t : ℝ) (A : M2R) :
    modularAutomorphism t A - A =
      t • (N * A - A * N) - (t * t) • (N * A * N) := by
  rw [modularAutomorphism_exact_expansion]
  abel

/--
Odd part in time isolates the commutator term:
the quadratic nilpotent correction cancels between `t` and `-t`.
-/
theorem modularAutomorphism_sub_neg
    (t : ℝ) (A : M2R) :
    modularAutomorphism t A - modularAutomorphism (-t) A =
      (2 * t) • (N * A - A * N) := by
  rw [modularAutomorphism_exact_expansion, modularAutomorphism_exact_expansion]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, N, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · simp [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, N, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · simp [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, N, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · simp [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, N, Matrix.mul_apply, Fin.sum_univ_two]
    ring

/--
Characterization of fixed operators for the nilpotent modular flow:
an operator is fixed at all times iff it commutes with `N`.
-/
theorem modularAutomorphism_fixed_all_iff_commute_N
    (A : M2R) :
    (∀ t : ℝ, modularAutomorphism t A = A) ↔ N * A = A * N := by
  constructor
  · intro hfix
    have hsub : modularAutomorphism 1 A - modularAutomorphism (-1) A = 0 := by
      rw [hfix 1, hfix (-1)]
      simp
    have hodd := modularAutomorphism_sub_neg 1 A
    rw [hsub] at hodd
    have hzero : (2 : ℝ) • (N * A - A * N) = 0 := by simpa using hodd.symm
    have hcomm_sub : N * A - A * N = 0 := by
      exact smul_eq_zero.mp hzero |>.resolve_left two_ne_zero
    exact sub_eq_zero.mp hcomm_sub
  · intro hcomm t
    exact modularAutomorphism_eq_self_of_commute_N t A hcomm

/--
Commutator readout from symmetric-time modular data:
the `t=±1` difference recovers the commutator exactly.
-/
theorem commutator_eq_half_time_symmetric_difference
    (A : M2R) :
    N * A - A * N =
      ((1 / 2 : ℝ)) • (modularAutomorphism 1 A - modularAutomorphism (-1) A) := by
  have hodd := modularAutomorphism_sub_neg 1 A
  have hsmul :
      ((1 / 2 : ℝ)) • (modularAutomorphism 1 A - modularAutomorphism (-1) A) =
        ((1 / 2 : ℝ)) • ((2 : ℝ) • (N * A - A * N)) := by
    simpa [hodd]
  calc
    N * A - A * N
        = (1 : ℝ) • (N * A - A * N) := by simp
    _ = ((1 / 2 : ℝ) * (2 : ℝ)) • (N * A - A * N) := by norm_num
    _ = ((1 / 2 : ℝ)) • ((2 : ℝ) • (N * A - A * N)) := by
          rw [smul_smul]
    _ = ((1 / 2 : ℝ)) • (modularAutomorphism 1 A - modularAutomorphism (-1) A) := by
          simpa [hsmul] using hsmul.symm

/--
Even-time readout isolates the quadratic nilpotent correction term.
-/
theorem quadratic_term_eq_even_time_readout
    (t : ℝ) (A : M2R) :
    (t * t) • (N * A * N) =
      (1 / 2 : ℝ) •
        ((2 : ℝ) • A - modularAutomorphism t A - modularAutomorphism (-t) A) := by
  let C : M2R := N * A - A * N
  let Q : M2R := (t * t) • (N * A * N)
  have ht : modularAutomorphism t A = A + t • C - Q := by
    simp [C, Q, modularAutomorphism_exact_expansion]
  have hneg : modularAutomorphism (-t) A = A + (-t) • C - Q := by
    simp [C, Q, modularAutomorphism_exact_expansion]
  have hcore :
      ((2 : ℝ) • A - (A + t • C - Q) - (A + (-t) • C - Q)) = (2 : ℝ) • Q := by
    ext i j
    simp [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply]
    ring
  calc
    Q = (1 / 2 : ℝ) • ((2 : ℝ) • Q) := by
      rw [smul_smul]
      norm_num
    _ = (1 / 2 : ℝ) • ((2 : ℝ) • A - (A + t • C - Q) - (A + (-t) • C - Q)) := by
      rw [hcore]
    _ = (1 / 2 : ℝ) •
        ((2 : ℝ) • A - modularAutomorphism t A - modularAutomorphism (-t) A) := by
      simp [ht, hneg]
    _ = (1 / 2 : ℝ) •
        ((2 : ℝ) • A - modularAutomorphism t A - modularAutomorphism (-t) A) := rfl

/--
The nilpotent modular automorphisms compose additively in the time parameter.

This is the finite group-action readout:
`σ_s(σ_t(A)) = σ_{s+t}(A)`.
-/
theorem modularAutomorphism_comp
    (s t : ℝ) (A : M2R) :
    modularAutomorphism s (modularAutomorphism t A) =
      modularAutomorphism (s + t) A := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [modularAutomorphism, nilpotentFlow, N, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · simp [modularAutomorphism, nilpotentFlow, N, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · simp [modularAutomorphism, nilpotentFlow, N, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [modularAutomorphism, nilpotentFlow, N, Matrix.mul_apply, Fin.sum_univ_two]
    ring

/--
Finite iterate law for the nilpotent modular automorphism in recursion form:
repeating `A ↦ σ_t(A)` `n` times equals `σ_(n t)(A)`.
-/
theorem modularAutomorphism_rec_nat
    (t : ℝ) (n : ℕ) (A : M2R) :
    Nat.rec A (fun _ B => modularAutomorphism t B) n =
      modularAutomorphism ((n : ℝ) * t) A := by
  induction n with
  | zero =>
      simp [modularAutomorphism_zero]
  | succ n ih =>
      simp [ih]
      rw [modularAutomorphism_comp t ((n : ℝ) * t) A]
      have hcast : t + ((n : ℝ) * t) = (((n + 1 : ℕ) : ℝ) * t) := by
        calc
          t + ((n : ℝ) * t) = ((n : ℝ) + 1) * t := by ring
          _ = (((n + 1 : ℕ) : ℝ) * t) := by simp [Nat.cast_add, add_comm]
      rw [hcast]
      have hcast2 : (((n + 1 : ℕ) : ℝ) * t) = ((n : ℝ) + 1) * t := by
        simp [Nat.cast_add, add_comm]
      simpa [hcast2]

/--
Closed-form finite iterate of the nilpotent modular automorphism:
`n` recursive applications equal conjugation by `nilpotentFlow t` to the `n`th power.
-/
theorem modularAutomorphism_rec_nat_closed_form
    (t : ℝ) (n : ℕ) (A : M2R) :
    Nat.rec A (fun _ B => modularAutomorphism t B) n =
      (nilpotentFlow t) ^ n * A * (nilpotentFlow (-t)) ^ n := by
  calc
    Nat.rec A (fun _ B => modularAutomorphism t B) n
        = modularAutomorphism ((n : ℝ) * t) A := by
            exact modularAutomorphism_rec_nat t n A
    _ = nilpotentFlow ((n : ℝ) * t) * A * nilpotentFlow (-( (n : ℝ) * t)) := by
          rfl
    _ = (nilpotentFlow t) ^ n * A * nilpotentFlow (-( (n : ℝ) * t)) := by
          rw [nilpotentFlow_pow t n]
    _ = (nilpotentFlow t) ^ n * A * (nilpotentFlow (-t)) ^ n := by
          rw [nilpotentFlow_pow (-t) n]
          congr 1
          ring

/--
The inverse automorphism is obtained by negating time.
-/
@[simp]
theorem modularAutomorphism_neg_comp
    (t : ℝ) (A : M2R) :
    modularAutomorphism (-t) (modularAutomorphism t A) = A := by
  rw [modularAutomorphism_comp]
  simp

/--
The opposite inverse identity.
-/
@[simp]
theorem modularAutomorphism_comp_neg
    (t : ℝ) (A : M2R) :
    modularAutomorphism t (modularAutomorphism (-t) A) = A := by
  rw [modularAutomorphism_comp]
  simp


/--
The modular perturbation fixes the local vacuum vector.
-/
@[simp]
theorem Delta_vacuum :
    Delta * vac = vac := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [Delta, N, vac, Matrix.mul_apply, Fin.sum_univ_two]

/--
The flux annihilates the local vacuum vector.
-/
@[simp]
theorem entropyFlux_vacuum :
    entropyFlux * vac = 0 := by
  rw [entropyFlux_eq_N]
  simpa [a] using vacuum_annihilation

/--
The nilpotent modular flow fixes the local vacuum for every time.
-/
theorem nilpotentFlow_vacuum (t : ℝ) :
    nilpotentFlow t * vac = vac := by
  unfold nilpotentFlow
  have hNv : N * vac = 0 := by simpa [a] using vacuum_annihilation
  calc
    ((1 : M2R) + t • N) * vac
        = (1 : M2R) * vac + (t • N) * vac := by
            simpa using Matrix.add_mul (1 : M2R) (t • N) vac
    _ = vac + t • (N * vac) := by simp
    _ = vac := by simp [hNv]

end InfoGeometry.Canonical.ModularNilpotentAutomorphism
