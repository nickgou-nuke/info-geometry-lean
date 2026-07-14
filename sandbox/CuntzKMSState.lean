import Mathlib
import InfoGeometry.Algebra.CuntzMatrixUnits
import InfoGeometry.Algebra.CuntzPrimonHamiltonian
import InfoGeometry.Algebra.CuntzThermalState
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import InfoGeometry.Canonical.CantorBoundaryCuntzShift

open InfoGeometry.Algebra.CuntzTensorQuotient
open InfoGeometry.Algebra.CuntzPrimonHamiltonian
open InfoGeometry.Algebra

noncomputable section

namespace VirasoroProject.Extensions.CuntzKMSState

/-! ## Primon Boltzmann weights -/

/-- The Boltzmann factor for the i-th primon at inverse temperature β:
    exp(-β · log(p_i)) = p_i^{-β}.
    This is the eigenvalue of exp(-βH) on the projector P_i. -/
def boltzmannFactor (p : ℕ) (β : ℂ) : ℂ :=
  (p : ℂ) ^ (-β)

/-- The truncated primon partition function:
    Z_n(β) = Σ_{i=0}^{n-1} p_i^{-β}. -/
def primonPartition (n : ℕ) (primes : Fin n → ℕ) (β : ℂ) : ℂ :=
  ∑ i : Fin n, boltzmannFactor (primes i) β

/-- The normalized KMS weight for mode i:
    w_i = p_i^{-β} / Z_n(β).
    Requires Z_n(β) ≠ 0 (true for all β with Re(β) > 0, since each p_i^{-β} is
    a positive real when β is real). -/
def kmsWeight (n : ℕ) (primes : Fin n → ℕ) (β : ℂ) (i : Fin n) : ℂ :=
  boltzmannFactor (primes i) β / primonPartition n primes β

/-! ## Diagonal KMS state -/

/-- A diagonal KMS state: ℂ-linear functional on the diagonal subalgebra
    determined by a weight vector w_i with Σ_i w_i = 1. -/
structure DiagonalKMSState (n : ℕ) where
  /-- The weight assigned to each projector P_i. -/
  weights : Fin n → ℂ
  /-- Normalization: Σ_i w_i = 1. -/
  weights_sum_one : ∑ i : Fin n, weights i = 1

namespace DiagonalKMSState

variable {n : ℕ}

/-- Evaluate the diagonal KMS state on a diagonal element Σ_i c_i P_i,
    given by the coefficient vector c : Fin n → ℂ. -/
def eval (φ : DiagonalKMSState n) (c : Fin n → ℂ) : ℂ :=
  ∑ i : Fin n, c i * φ.weights i

/-- φ(1) = φ(Σ_i P_i) = Σ_i w_i = 1. -/
theorem eval_one (φ : DiagonalKMSState n) : φ.eval (λ _ => 1) = 1 := by
  dsimp [eval]
  simpa using φ.weights_sum_one

/-- φ is ℂ-linear. -/
theorem eval_add (φ : DiagonalKMSState n) (c d : Fin n → ℂ) :
    φ.eval (λ i => c i + d i) = φ.eval c + φ.eval d := by
  dsimp [eval]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (λ i _ => ?_)
  ring

/-- φ commutes with scalar multiplication. -/
theorem eval_smul (φ : DiagonalKMSState n) (a : ℂ) (c : Fin n → ℂ) :
    φ.eval (λ i => a * c i) = a * φ.eval c := by
  dsimp [eval]
  simp [Finset.mul_sum, mul_assoc]

/-- φ applied to the i-th projector P_i: φ(P_i) = w_i. -/
theorem eval_projector (φ : DiagonalKMSState n) (i : Fin n) :
    φ.eval (λ j => if j = i then 1 else 0) = φ.weights i := by
  dsimp [eval]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- The canonical KMS diagonal state at inverse temperature β:
    w_i = p_i^{-β} / Z_n(β).
    Requires the explicit finite nonzero denominator hypothesis `Z_n(β) ≠ 0`. -/
def canonical (primes : Fin n → ℕ) (β : ℂ) (hZ : primonPartition n primes β ≠ 0) :
    DiagonalKMSState n where
  weights := λ i => kmsWeight n primes β i
  weights_sum_one := by
    dsimp [kmsWeight]
    rw [← Finset.sum_div]
    exact div_self hZ

/-- The Hamiltonian H = Σ_i ε_i P_i evaluated under the KMS state:
    φ_β(H) = Σ_i ε_i · w_i. -/
theorem eval_hamiltonian_diagonal (φ : DiagonalKMSState n) (ε : Fin n → ℂ) :
    φ.eval ε = ∑ i : Fin n, ε i * φ.weights i := rfl

end DiagonalKMSState

/-! ## From truncated thermal state to partition function -/

/-- The truncated thermal state evaluated on the primon Hamiltonian.
    For ε_i = log(p_i): exp_N(-βH) = Σ_i (Σ_{k=0}^N (-β·log p_i)^k/k!) · P_i.
    This is the finite-N spectral action. -/
theorem primon_truncated_thermal_state (n : ℕ) (primes : Fin n → ℕ) (β : ℂ) (N : ℕ) :
    Polynomial.aeval (hamiltonian n (λ i => (Real.log (primes i : ℝ) : ℂ)))
      (CuntzThermalState.truncExpNegBeta β N) =
    ∑ i : Fin n,
      (∑ k ∈ Finset.range (N+1),
        ((-β * (Real.log (primes i : ℝ) : ℂ)) ^ k / (Nat.factorial k : ℂ))) • P n i := by
  simpa using
    CuntzThermalState.truncExp_neg_beta_explicit n
      (λ i => (Real.log (primes i : ℝ) : ℂ)) β N

/-- The sum of the mode coefficients in the truncated thermal state.
    Analytic convergence of the directed finite-prime cutoffs is not asserted here. -/
def truncatedPartitionSum (n : ℕ) (primes : Fin n → ℕ) (β : ℂ) (N : ℕ) : ℂ :=
  ∑ i : Fin n,
    (∑ k ∈ Finset.range (N+1),
      ((-β * (Real.log (primes i : ℝ) : ℂ)) ^ k / (Nat.factorial k : ℂ)))

/-! ## Topological KMS State on the Cuntz Boundary (Recovered Fragment) -/

/-- The modular automorphism group scaling factor for `O_2`.
σ_t(S) = e^{i t \ln 2} S -/
def modular_automorphism_phase (t : ℝ) : ℂ :=
  Complex.exp ⟨0, t * Real.log 2⟩

/-- The topological KMS trace of a single Cuntz projector `S_j S_j^*`.
Derived from the KMS condition `τ(A σ_{iβ}(B)) = τ(B A)`. -/
def kms_trace_projector (β : ℝ) : ℝ :=
  (2 : ℝ) ^ (-β)

lemma log_eq_zero_of_kms_cond {β : ℝ} (h : 2 * (2 : ℝ) ^ (-β) = 1) :
    Real.log 2 + -β * Real.log 2 = 0 := by
  have h_log : Real.log (2 * (2 : ℝ) ^ (-β)) = Real.log 1 := congrArg Real.log h
  rw [Real.log_one] at h_log
  have h_pos : (0 : ℝ) < 2 := by norm_num
  have h_pow_pos : (0 : ℝ) < (2 : ℝ) ^ (-β) := Real.rpow_pos_of_pos h_pos _
  rw [Real.log_mul (by norm_num) (ne_of_gt h_pow_pos)] at h_log
  rw [Real.log_rpow h_pos] at h_log
  exact h_log

lemma factor_log_eq_zero {β : ℝ} (h_eq : Real.log 2 + -β * Real.log 2 = 0) :
    (1 - β) * Real.log 2 = 0 := by
  calc
    (1 - β) * Real.log 2 = 1 * Real.log 2 - β * Real.log 2 := by ring
    _ = Real.log 2 + -β * Real.log 2 := by ring
    _ = 0 := h_eq

/-- **Theorem: Unique KMS Temperature for O_2**
The Cuntz boundary identity `P_left + P_right = 1` requires that the sum
of the traces equals 1. This forces the unique KMS inverse temperature
to be strictly `β = 1`. -/
theorem unique_kms_temperature {β : ℝ} (h : 2 * kms_trace_projector β = 1) :
    β = 1 := by
  unfold kms_trace_projector at h
  have h_eq := log_eq_zero_of_kms_cond h
  have h_eq2 := factor_log_eq_zero h_eq
  have h_log2_ne_zero : Real.log 2 ≠ 0 := by
    apply ne_of_gt
    exact Real.log_pos (by norm_num)
  cases mul_eq_zero.mp h_eq2 with
  | inl h_left => linarith
  | inr h_right => contradiction

end VirasoroProject.Extensions.CuntzKMSState

end noncomputable section
