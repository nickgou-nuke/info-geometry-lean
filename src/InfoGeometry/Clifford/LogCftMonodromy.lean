import InfoGeometry.Algebra.HypercomplexTriad
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.SupermatrixKoszul
import InfoGeometry.Clifford.OpSignatureBridge
import InfoGeometry.Quantum.Monodromy
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

noncomputable section

/-!
# LogCftMonodromy

Concrete `2 × 2` logarithmic-CFT monodromy matrices.

The file models the rank-two Jordan cell for a logarithmic pair and the
associated parabolic monodromy.  It is deliberately matrix-level: the semantic
bridge to Clifford / signature machinery is through the already-owned
`OpSignatureBridge` and `InfoGeometry.Algebra.SupermatrixKoszul` lanes.
-/

namespace InfoGeometry.Clifford.LogCftMonodromy

open Matrix
open InfoGeometry.Algebra.HypercomplexTriad
open InfoGeometry.Algebra.SupermatrixKoszul
open OpSignatureBridge

/-- The carrier for a rank-two logarithmic pair. -/
abbrev LogCftModule (K : Type*) := Fin 2 → K

/-- Upper-triangular equal-diagonal `2 × 2` block. -/
def upperJordan {K : Type*} [Zero K] (a b : K) : Matrix (Fin 2) (Fin 2) K :=
  !![a, b; 0, a]

/-- The nilpotent Jordan shear `N`, with `N² = 0`. -/
def jordanNilpotent {K : Type*} [Zero K] [One K] : Matrix (Fin 2) (Fin 2) K :=
  !![0, 1; 0, 0]

/-- Complex-named alias for the nilpotent dual-number unit. -/
abbrev epsilon : Matrix (Fin 2) (Fin 2) ℂ :=
  jordanNilpotent

/--
Hadjiivanov-style rank-two Virasoro `L₀` cell:
`[[h, 1], [0, h]]`.
-/
def virasoroL0Cell {K : Type*} [Zero K] [One K] (h : K) :
    Matrix (Fin 2) (Fin 2) K :=
  upperJordan h 1

/-- The Jordan cell splits into a scalar diagonal and a nilpotent shear. -/
theorem l0_cell_decomposition {K : Type*} [CommRing K] (h : K) :
    virasoroL0Cell h =
      h • (1 : Matrix (Fin 2) (Fin 2) K) + jordanNilpotent := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [virasoroL0Cell, upperJordan, jordanNilpotent]

/-- The logarithmic shear is the parabolic `Op² = 0` block. -/
theorem jordanNilpotent_eq_parabolic_block :
    (jordanNilpotent : Mat2) = toSupermatrixBlock OpSignature.parabolic := by
  rfl

/-- The same nilpotent shear is the parabolic unit of the hypercomplex triad. -/
theorem jordanNilpotent_eq_hypercomplex_N :
    (jordanNilpotent : Mat2) = N := by
  rfl

/-- Over `ℝ`, the Virasoro Jordan cell is a scalar plus the parabolic triad unit. -/
theorem real_l0_cell_hypercomplex_parabolic (h : ℝ) :
    virasoroL0Cell h = h • (1 : Mat2) + N := by
  simpa [jordanNilpotent_eq_hypercomplex_N] using
    (l0_cell_decomposition (K := ℝ) h)

/-- The nilpotent Jordan shear squares to zero. -/
theorem jordanNilpotent_sq {K : Type*} [CommSemiring K] :
    (jordanNilpotent : Matrix (Fin 2) (Fin 2) K) * jordanNilpotent = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jordanNilpotent, Matrix.mul_apply]

/-- The complex dual-number unit squares to zero. -/
theorem epsilon_sq :
    epsilon * epsilon = 0 := by
  exact jordanNilpotent_sq (K := ℂ)

/-- Every power `N^k` with `2 ≤ k` vanishes. -/
theorem jordanNilpotent_pow_zero {K : Type*} [CommSemiring K]
    (k : ℕ) (hk : 2 ≤ k) :
    (jordanNilpotent : Matrix (Fin 2) (Fin 2) K) ^ k = 0 := by
  induction k, hk using Nat.le_induction with
  | base =>
      simpa [pow_succ] using (jordanNilpotent_sq (K := K))
  | succ k hk ih =>
      rw [pow_succ, ih, zero_mul]

/-- Every power `epsilon^k` with `2 ≤ k` vanishes. -/
theorem epsilon_pow_zero (k : ℕ) (hk : 2 ≤ k) :
    epsilon ^ k = 0 := by
  exact jordanNilpotent_pow_zero (K := ℂ) k hk

/-- Multiplication law for equal-diagonal upper-Jordan blocks. -/
theorem upperJordan_mul {K : Type*} [CommSemiring K] (a b c d : K) :
    upperJordan a b * upperJordan c d =
      upperJordan (a * c) (a * d + b * c) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperJordan, Matrix.mul_apply]

/--
Power law for an equal-diagonal Jordan block.

The off-diagonal coefficient grows linearly in the winding/power index; the
`n = 0` case is harmless because the coefficient is multiplied by `(0 : K)`.
-/
theorem upperJordan_pow {K : Type*} [CommSemiring K] (a b : K) :
    ∀ n : ℕ,
      upperJordan a b ^ n =
        upperJordan (a ^ n) ((n : K) * b * a ^ (n - 1)) := by
  intro n
  induction n with
  | zero =>
      ext i j
      fin_cases i <;> fin_cases j <;> simp [upperJordan]
  | succ n ih =>
      rw [pow_succ, ih, upperJordan_mul]
      congr 1
      · ring
      · by_cases hn : n = 0
        · subst n
          simp
        · have hpow : a ^ (n - 1) * a = a ^ n := by
            rw [← pow_succ]
            have hnpos : 0 < n := Nat.pos_of_ne_zero hn
            have hsub : n - 1 + 1 = n := by omega
            rw [hsub]
          have hsub_succ : n + 1 - 1 = n := by omega
          rw [hsub_succ]
          rw [mul_assoc ((n : K) * b) (a ^ (n - 1)) a, hpow]
          rw [Nat.cast_succ]
          ring

/-- Inductive power law for the Virasoro `L₀` Jordan cell. -/
theorem virasoroL0Cell_pow {K : Type*} [CommSemiring K] (h : K) (n : ℕ) :
    virasoroL0Cell h ^ n =
      upperJordan (h ^ n) ((n : K) * h ^ (n - 1)) := by
  simpa [virasoroL0Cell, one_mul] using upperJordan_pow (a := h) (b := (1 : K)) n

/-- Complex `L₀` written in the explicit dual-number / parabolic form. -/
theorem virasoroL0Cell_triad_form (h : ℂ) :
    virasoroL0Cell h =
      h • (1 : Matrix (Fin 2) (Fin 2) ℂ) + jordanNilpotent := by
  exact l0_cell_decomposition (K := ℂ) h

/-- Binomial-facing decomposition name for the Virasoro Jordan cell. -/
theorem virasoroL0Cell_decomp (h : ℂ) :
    virasoroL0Cell h =
      h • (1 : Matrix (Fin 2) (Fin 2) ℂ) + epsilon := by
  exact virasoroL0Cell_triad_form h

/--
Algebraic power form of the Virasoro cell: scalar power on the diagonal, and a
single nilpotent contribution with coefficient `n * h^(n-1)`.
-/
theorem virasoroL0Cell_pow_algebraic (h : ℂ) (n : ℕ) :
    virasoroL0Cell h ^ n =
      h ^ n • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        ((n : ℂ) * h ^ (n - 1)) • jordanNilpotent := by
  rw [virasoroL0Cell_pow]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [upperJordan, jordanNilpotent]

/--
Binomial-facing form of the Virasoro power law.  The nilpotent expansion
truncates after the linear term because `epsilon^2 = 0`.
-/
theorem virasoroL0Cell_pow_binomial (h : ℂ) (n : ℕ) :
    virasoroL0Cell h ^ n =
      h ^ n • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        ((n : ℂ) * h ^ (n - 1)) • epsilon := by
  exact virasoroL0Cell_pow_algebraic h n

/-- Coordinate readout of the Virasoro power law. -/
theorem virasoroL0Cell_pow_original (h : ℂ) (n : ℕ) :
    virasoroL0Cell h ^ n =
      !![h ^ n, (n : ℂ) * h ^ (n - 1); 0, h ^ n] := by
  rw [virasoroL0Cell_pow]
  rfl

/-- The logarithmic phase for one positive monodromy wrap. -/
def lcftPhase (h : ℂ) : ℂ :=
  Complex.exp (-(2 : ℂ) * Complex.I * (Real.pi : ℂ) * h)

/-- The universal logarithmic shear coefficient before multiplying by the phase. -/
def logShearBase : ℂ :=
  -(2 : ℂ) * Complex.I * (Real.pi : ℂ)

/-- The actual one-wrap shear coefficient. -/
def logShear (h : ℂ) : ℂ :=
  logShearBase * lcftPhase h

/--
Hadjiivanov logarithmic monodromy for one wrap around a singularity:
`phase` on the diagonal and logarithmic shear in the upper-right entry.
-/
def hadjiivanovMonodromy (h : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  upperJordan (lcftPhase h) (logShear h)

/-- The nilpotent part of the one-wrap monodromy. -/
def monodromyNilpotentPart (h : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, logShear h; 0, 0]

/-- The monodromy splits into a scalar phase and a nilpotent logarithmic shear. -/
theorem monodromy_decomposition (h : ℂ) :
    hadjiivanovMonodromy h =
      lcftPhase h • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        monodromyNilpotentPart h := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadjiivanovMonodromy, upperJordan, monodromyNilpotentPart]

/--
One wrap is a scalar phase multiplying a unipotent parabolic shear.
This is the LCFT form `phase • (1 - 2πi N)`.
-/
theorem hadjiivanovMonodromy_phase_nilpotent (h : ℂ) :
    hadjiivanovMonodromy h =
      lcftPhase h •
        ((1 : Matrix (Fin 2) (Fin 2) ℂ) + logShearBase • jordanNilpotent) := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [hadjiivanovMonodromy, upperJordan, jordanNilpotent, logShear]
  all_goals ring

/--
Named triad-form wrapper for the one-wrap logarithmic monodromy:
`M(h) = phase • (1 - 2πi N)`.
-/
theorem hadjiivanovMonodromy_triad_form (h : ℂ) :
    hadjiivanovMonodromy h =
      lcftPhase h •
        ((1 : Matrix (Fin 2) (Fin 2) ℂ) + logShearBase • jordanNilpotent) := by
  exact hadjiivanovMonodromy_phase_nilpotent h

/-- Binomial-facing decomposition name for the one-wrap monodromy. -/
theorem hadjiivanovMonodromy_decomp (h : ℂ) :
    hadjiivanovMonodromy h =
      lcftPhase h •
        ((1 : Matrix (Fin 2) (Fin 2) ℂ) + logShearBase • epsilon) := by
  exact hadjiivanovMonodromy_triad_form h

/-- The logarithmic anomaly is nilpotent. -/
theorem monodromy_nilpotency (h : ℂ) :
    monodromyNilpotentPart h * monodromyNilpotentPart h = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [monodromyNilpotentPart, Matrix.mul_apply]

/-- The determinant is the repeated phase root squared. -/
theorem monodromy_is_parabolic (h : ℂ) :
    (hadjiivanovMonodromy h).det = lcftPhase h ^ 2 := by
  simp [hadjiivanovMonodromy, upperJordan, Matrix.det_fin_two]
  ring

/--
Inductive compounding law: after `n` wraps, the diagonal phase is raised to
`n`, while the logarithmic shear coefficient grows linearly in `n`.
-/
theorem hadjiivanovMonodromy_pow_upper (h : ℂ) (n : ℕ) :
    hadjiivanovMonodromy h ^ n =
      upperJordan (lcftPhase h ^ n)
        ((n : ℂ) * logShear h * lcftPhase h ^ (n - 1)) := by
  simpa [hadjiivanovMonodromy] using
    upperJordan_pow (a := lcftPhase h) (b := logShear h) n

/--
Equivalent readout of the monodromy power: the upper-right coefficient is
`n` times the base logarithmic shear, multiplied by the accumulated phase.
-/
theorem hadjiivanovMonodromy_pow (h : ℂ) (n : ℕ) :
    hadjiivanovMonodromy h ^ n =
      upperJordan (lcftPhase h ^ n)
        ((n : ℂ) * logShearBase * lcftPhase h ^ n) := by
  rw [hadjiivanovMonodromy_pow_upper]
  congr 1
  by_cases hn : n = 0
  · subst n
    simp
  · have hpow : lcftPhase h * lcftPhase h ^ (n - 1) = lcftPhase h ^ n := by
      rw [mul_comm, ← pow_succ]
      have hsub : n - 1 + 1 = n := by omega
      rw [hsub]
    simp [logShear]
    calc
      (n : ℂ) * (logShearBase * lcftPhase h) * lcftPhase h ^ (n - 1)
          = (n : ℂ) * logShearBase *
              (lcftPhase h * lcftPhase h ^ (n - 1)) := by ring
      _ = (n : ℂ) * logShearBase * lcftPhase h ^ n := by rw [hpow]

/--
Winding-number form of the compounded monodromy.  The nilpotent coefficient is
exactly `n` times the one-wrap logarithmic shear, while the phase accumulates as
`phase^n`.
-/
theorem hadjiivanovMonodromy_pow_winding (h : ℂ) (n : ℕ) :
    hadjiivanovMonodromy h ^ n =
      lcftPhase h ^ n •
        ((1 : Matrix (Fin 2) (Fin 2) ℂ) +
          ((n : ℂ) * logShearBase) • jordanNilpotent) := by
  rw [hadjiivanovMonodromy_pow]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [upperJordan, jordanNilpotent]
  all_goals ring

/-- Diagonal `00` readout of the `n`-fold logarithmic monodromy. -/
theorem hadjiivanovMonodromy_pow_00 (h : ℂ) (n : ℕ) :
    (hadjiivanovMonodromy h ^ n) 0 0 = lcftPhase h ^ n := by
  rw [hadjiivanovMonodromy_pow_winding]
  simp [jordanNilpotent]

/-- Upper-right logarithmic-shear readout after `n` windings. -/
theorem hadjiivanovMonodromy_pow_01 (h : ℂ) (n : ℕ) :
    (hadjiivanovMonodromy h ^ n) 0 1 =
        lcftPhase h ^ n * ((n : ℂ) * logShearBase) := by
  rw [hadjiivanovMonodromy_pow_winding]
  simp [jordanNilpotent]

/-- The lower-left entry remains zero after every winding. -/
theorem hadjiivanovMonodromy_pow_10 (h : ℂ) (n : ℕ) :
    (hadjiivanovMonodromy h ^ n) 1 0 = 0 := by
  rw [hadjiivanovMonodromy_pow_winding]
  simp [jordanNilpotent]

/-- Diagonal `11` readout of the `n`-fold logarithmic monodromy. -/
theorem hadjiivanovMonodromy_pow_11 (h : ℂ) (n : ℕ) :
    (hadjiivanovMonodromy h ^ n) 1 1 = lcftPhase h ^ n := by
  rw [hadjiivanovMonodromy_pow_winding]
  simp [jordanNilpotent]

/--
Genuine Hadjiivanov monodromy coefficient theorem.

After `n` windings, the logarithmic monodromy remains in the same rank-two
Jordan class: the diagonal phase is `phase^n`, the lower-left entry stays zero,
and the only nontrivial nilpotent datum is the upper-right coefficient
`phase^n * n * (-2πi)`.
-/
theorem hadjiivanovMonodromy_genuine_coefficient_readout (h : ℂ) (n : ℕ) :
    hadjiivanovMonodromy h ^ n =
        lcftPhase h ^ n •
          ((1 : Matrix (Fin 2) (Fin 2) ℂ) +
            ((n : ℂ) * logShearBase) • jordanNilpotent)
      ∧ (hadjiivanovMonodromy h ^ n) 0 0 = lcftPhase h ^ n
      ∧ (hadjiivanovMonodromy h ^ n) 0 1 =
          lcftPhase h ^ n * ((n : ℂ) * logShearBase)
      ∧ (hadjiivanovMonodromy h ^ n) 1 0 = 0
      ∧ (hadjiivanovMonodromy h ^ n) 1 1 = lcftPhase h ^ n := by
  exact ⟨hadjiivanovMonodromy_pow_winding h n,
         hadjiivanovMonodromy_pow_00 h n,
         hadjiivanovMonodromy_pow_01 h n,
         hadjiivanovMonodromy_pow_10 h n,
         hadjiivanovMonodromy_pow_11 h n⟩

/--
Named algebraic form of the compounded monodromy.  This is the same theorem as
`hadjiivanovMonodromy_pow_winding`, exposed under the dual-number interface
name for downstream imports.
-/
theorem hadjiivanovMonodromy_pow_algebraic (h : ℂ) (n : ℕ) :
    hadjiivanovMonodromy h ^ n =
      lcftPhase h ^ n •
        ((1 : Matrix (Fin 2) (Fin 2) ℂ) +
          ((n : ℂ) * logShearBase) • jordanNilpotent) := by
  exact hadjiivanovMonodromy_pow_winding h n

/--
Binomial-facing power law for a unipotent nilpotent perturbation:
`(1 + c epsilon)^n = 1 + n c epsilon`.
-/
theorem one_plus_c_epsilon_pow (c : ℂ) (n : ℕ) :
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) + c • epsilon) ^ n =
      1 + ((n : ℂ) * c) • epsilon := by
  have hshape :
      (1 : Matrix (Fin 2) (Fin 2) ℂ) + c • epsilon =
        upperJordan 1 c := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [upperJordan, jordanNilpotent]
  rw [hshape, upperJordan_pow]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperJordan, jordanNilpotent]

/--
Equivalent subtraction form:
`(1 - c epsilon)^n = 1 - n c epsilon`.
-/
theorem one_minus_c_epsilon_pow (c : ℂ) (n : ℕ) :
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) - c • epsilon) ^ n =
      1 - ((n : ℂ) * c) • epsilon := by
  simpa [sub_eq_add_neg, neg_smul, mul_neg] using
    (one_plus_c_epsilon_pow (-c) n)

/-- Binomial-facing name for the compounded monodromy law. -/
theorem hadjiivanovMonodromy_pow_binomial (h : ℂ) (n : ℕ) :
    hadjiivanovMonodromy h ^ n =
      lcftPhase h ^ n •
        ((1 : Matrix (Fin 2) (Fin 2) ℂ) +
          ((n : ℂ) * logShearBase) • epsilon) := by
  exact hadjiivanovMonodromy_pow_algebraic h n

/-- Coordinate readout of the compounded monodromy law. -/
theorem hadjiivanovMonodromy_pow_original (h : ℂ) (n : ℕ) :
    hadjiivanovMonodromy h ^ n =
      upperJordan (lcftPhase h ^ n)
        ((n : ℂ) * logShearBase * lcftPhase h ^ n) := by
  exact hadjiivanovMonodromy_pow h n

/-! ## Dual/lower-triangular scattering convention -/

/--
Lower-triangular equal-diagonal `2 × 2` block.

This is the dual-basis / transposed convention for the same parabolic
logarithmic monodromy carried by `upperJordan`.
-/
def lowerJordan {K : Type*} [Zero K] (a b : K) : Matrix (Fin 2) (Fin 2) K :=
  !![a, 0; b, a]

/-- The lower-triangular nilpotent shear, dual to `jordanNilpotent`. -/
def lowerJordanNilpotent {K : Type*} [Zero K] [One K] : Matrix (Fin 2) (Fin 2) K :=
  !![0, 0; 1, 0]

/-- Lower-Jordan blocks are transposes of upper-Jordan blocks. -/
theorem lowerJordan_eq_transpose {K : Type*} [Zero K] (a b : K) :
    lowerJordan a b = (upperJordan a b)ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerJordan, upperJordan, Matrix.transpose_apply]

/-- The lower nilpotent shear is the transpose of the upper nilpotent shear. -/
theorem lowerJordanNilpotent_eq_transpose {K : Type*} [Zero K] [One K] :
    (lowerJordanNilpotent : Matrix (Fin 2) (Fin 2) K) = jordanNilpotentᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerJordanNilpotent, jordanNilpotent, Matrix.transpose_apply]

/-- The lower-triangular logarithmic shear also squares to zero. -/
theorem lowerJordanNilpotent_sq {K : Type*} [CommSemiring K] :
    (lowerJordanNilpotent : Matrix (Fin 2) (Fin 2) K) *
      lowerJordanNilpotent = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerJordanNilpotent, Matrix.mul_apply]

/--
Dual/lower-triangular Hadjiivanov monodromy.  This is the same analytic
monodromy in the transposed scattering convention.
-/
def lowerHadjiivanovMonodromy (h : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  lowerJordan (lcftPhase h) (logShear h)

/-- The lower monodromy is exactly the transpose of the upper monodromy. -/
theorem lowerHadjiivanovMonodromy_eq_transpose (h : ℂ) :
    lowerHadjiivanovMonodromy h = (hadjiivanovMonodromy h)ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerHadjiivanovMonodromy, hadjiivanovMonodromy, lowerJordan,
      upperJordan, Matrix.transpose_apply]

/--
Lower-triangular winding law.  In the dual/scattering convention, repeated
wraps accumulate the same linear nilpotent coefficient in the lower-left entry.
-/
theorem lowerHadjiivanovMonodromy_pow_winding (h : ℂ) (n : ℕ) :
    lowerHadjiivanovMonodromy h ^ n =
      lcftPhase h ^ n •
        ((1 : Matrix (Fin 2) (Fin 2) ℂ) +
          ((n : ℂ) * logShearBase) • lowerJordanNilpotent) := by
  induction n with
  | zero =>
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [lowerHadjiivanovMonodromy, lowerJordanNilpotent]
  | succ n ih =>
      rw [pow_succ, ih]
      ext i j
      fin_cases i <;> fin_cases j
      all_goals
        simp [lowerHadjiivanovMonodromy, lowerJordan, lowerJordanNilpotent,
          logShear, Matrix.mul_apply]
      all_goals ring_nf

/-- Coordinate readout of the lower-triangular compounded monodromy law. -/
theorem lowerHadjiivanovMonodromy_pow_original (h : ℂ) (n : ℕ) :
    lowerHadjiivanovMonodromy h ^ n =
      lowerJordan (lcftPhase h ^ n)
        ((n : ℂ) * logShearBase * lcftPhase h ^ n) := by
  rw [lowerHadjiivanovMonodromy_pow_winding]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [lowerJordan, lowerJordanNilpotent]
  all_goals ring_nf

end InfoGeometry.Clifford.LogCftMonodromy
