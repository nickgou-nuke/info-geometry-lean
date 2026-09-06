import Mathlib.Tactic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import InfoGeometry.Arithmetic.PrimitiveSetsAbove

/-!
# InfoGeometry.Arithmetic.PrimonGasSupertrace

\[
E(n):=\log n,
\qquad
w_\beta(n):=e^{-\beta E(n)},
\qquad
w_\beta(0):=0.
\]

\[
Z_B(A,\beta)=\sum_{n\in A} w_\beta(n),
\quad
Z_{\mathrm{sf}}(A,\beta)=\sum_{n\in A\cap\mathrm{SqFree}} w_\beta(n),
\quad
\mathrm{Str}(A,\beta)=\sum_{n\in A}\mu(n)w_\beta(n).
\]
-/

noncomputable section

namespace InfoGeometry.Arithmetic.PrimonGasSupertrace

open scoped BigOperators

/-- `E(n):=\log n`. -/
def primonEnergy (n : ℕ) : ℝ :=
  Real.log (n : ℝ)

/-- `w_\beta(n)`. -/
def primonBoltzmannWeight (β : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else Real.exp (-β * primonEnergy n)

lemma primonBoltzmannWeight_nonneg (β : ℝ) (n : ℕ) :
    0 ≤ primonBoltzmannWeight β n := by
  unfold primonBoltzmannWeight
  split_ifs
  · norm_num
  · exact Real.exp_nonneg _

lemma primonBoltzmannWeight_pos_of_ne_zero {β : ℝ} {n : ℕ} (hn : n ≠ 0) :
    0 < primonBoltzmannWeight β n := by
  unfold primonBoltzmannWeight
  simp [hn, Real.exp_pos]

/-- `Z_B(A,\beta)`. -/
def finiteBosonicPartition
    (A : Finset ℕ)
    (β : ℝ) : ℝ :=
  ∑ n ∈ A, primonBoltzmannWeight β n

lemma finiteBosonicPartition_nonneg (A : Finset ℕ) (β : ℝ) :
    0 ≤ finiteBosonicPartition A β := by
  unfold finiteBosonicPartition
  exact Finset.sum_nonneg (fun n _hn => primonBoltzmannWeight_nonneg β n)

lemma finiteBosonicPartition_pos_of_mem_ne_zero
    {A : Finset ℕ} {β : ℝ} {n : ℕ} (hnA : n ∈ A) (hn : n ≠ 0) :
    0 < finiteBosonicPartition A β := by
  unfold finiteBosonicPartition
  exact Finset.sum_pos'
    (fun m _hm => primonBoltzmannWeight_nonneg β m)
    ⟨n, hnA, primonBoltzmannWeight_pos_of_ne_zero (β := β) hn⟩

/-- `\mathrm{SqFree}`. -/
def IsSquarefreeState (n : ℕ) : Prop :=
  Squarefree n

/-- `\mathrm{SqFree}` filter predicate. -/
noncomputable instance decidablePredIsSquarefreeState :
    DecidablePred IsSquarefreeState :=
  Classical.decPred IsSquarefreeState

/-- `Z_{\mathrm{sf}}(A,\beta)`. -/
def finiteSquarefreePartition
    (A : Finset ℕ)
    (β : ℝ) : ℝ :=
  by
    classical
    exact ∑ n ∈ A.filter IsSquarefreeState, primonBoltzmannWeight β n

lemma finiteSquarefreePartition_nonneg (A : Finset ℕ) (β : ℝ) :
    0 ≤ finiteSquarefreePartition A β := by
  classical
  unfold finiteSquarefreePartition
  exact Finset.sum_nonneg (fun n _hn => primonBoltzmannWeight_nonneg β n)

/-- Supplied coefficient `\mu : \mathbb N\to\mathbb R`. -/
structure MobiusCoefficient where
  coeff : ℕ → ℝ

  /-- `\neg\mathrm{SqFree}(n) \to \mu(n)=0`. -/
  coeff_eq_zero_of_not_squarefree :
    ∀ n : ℕ, ¬ IsSquarefreeState n → coeff n = 0

  /-- `\mathrm{SqFree}(n) \to \mu(n)^2=1`. -/
  coeff_sq_eq_one_of_squarefree :
    ∀ n : ℕ, IsSquarefreeState n → coeff n ^ 2 = 1

/-! ## Native Mathlib Mobius coefficient

The general `MobiusCoefficient` interface remains available for model-specific
coefficients.  The canonical arithmetic coefficient below is not an evidence
packet: it is Mathlib's `ArithmeticFunction.moebius`, coerced to `ℝ`.
-/

def mathlibMobiusCoefficient (n : ℕ) : ℝ :=
  (ArithmeticFunction.moebius n : ℤ)

theorem mathlibMobiusCoefficient_eq_zero_of_not_squarefree
    {n : ℕ} (h : ¬ IsSquarefreeState n) :
    mathlibMobiusCoefficient n = 0 := by
  unfold mathlibMobiusCoefficient
  rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]
  norm_num

theorem mathlibMobiusCoefficient_sq_eq_one_of_squarefree
    {n : ℕ} (h : IsSquarefreeState n) :
    mathlibMobiusCoefficient n ^ 2 = 1 := by
  unfold mathlibMobiusCoefficient
  exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree h

def canonicalMobiusCoefficient : MobiusCoefficient where
  coeff := mathlibMobiusCoefficient
  coeff_eq_zero_of_not_squarefree :=
    fun n h => mathlibMobiusCoefficient_eq_zero_of_not_squarefree h
  coeff_sq_eq_one_of_squarefree :=
    fun n h => mathlibMobiusCoefficient_sq_eq_one_of_squarefree h

namespace MobiusCoefficient

variable (μ : MobiusCoefficient)

/-- `\mathrm{Str}(A,\beta)`. -/
def finiteSupertrace
    (A : Finset ℕ)
    (β : ℝ) : ℝ :=
  ∑ n ∈ A, μ.coeff n * primonBoltzmannWeight β n

/-- `\mathrm{Str}(A,\beta)=\sum_{A\cap\mathrm{SqFree}} \mu(n)w_\beta(n)`. -/
theorem finiteSupertrace_eq_squarefree_filter
    (A : Finset ℕ)
    (β : ℝ) :
    μ.finiteSupertrace A β =
      ∑ n ∈ A.filter IsSquarefreeState,
        μ.coeff n * primonBoltzmannWeight β n := by
  classical
  unfold finiteSupertrace
  have hkill :
      ∑ x ∈ A.filter (fun a => ¬ IsSquarefreeState a),
          μ.coeff x * primonBoltzmannWeight β x = 0 := by
    refine Finset.sum_eq_zero ?_
    intro n hn
    have hnot : ¬ IsSquarefreeState n :=
      (Finset.mem_filter.mp hn).2
    rw [μ.coeff_eq_zero_of_not_squarefree n hnot]
    simp
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not
      (s := A)
      (p := IsSquarefreeState)
      (f := fun n => μ.coeff n * primonBoltzmannWeight β n)
  calc
    (∑ n ∈ A, μ.coeff n * primonBoltzmannWeight β n)
        =
      (∑ n ∈ A.filter IsSquarefreeState,
        μ.coeff n * primonBoltzmannWeight β n)
        +
      (∑ n ∈ A.filter (fun a => ¬ IsSquarefreeState a),
        μ.coeff n * primonBoltzmannWeight β n) := by
        simpa using hsplit.symm
    _ =
      (∑ n ∈ A.filter IsSquarefreeState,
        μ.coeff n * primonBoltzmannWeight β n) + 0 := by
        rw [hkill]
    _ =
      ∑ n ∈ A.filter IsSquarefreeState,
        μ.coeff n * primonBoltzmannWeight β n := by
        simp

end MobiusCoefficient

/-- `Z_B`. -/
def bosonicPartition (support : Finset ℕ) (beta : ℝ) : ℝ :=
  finiteBosonicPartition support beta

/-- `Z_{\mathrm{sf}}`. -/
def squarefreePartition (support : Finset ℕ) (beta : ℝ) : ℝ :=
  finiteSquarefreePartition support beta

lemma bosonicPartition_nonneg (support : Finset ℕ) (beta : ℝ) :
    0 ≤ bosonicPartition support beta := by
  exact finiteBosonicPartition_nonneg support beta

lemma squarefreePartition_nonneg (support : Finset ℕ) (beta : ℝ) :
    0 ≤ squarefreePartition support beta := by
  exact finiteSquarefreePartition_nonneg support beta

/-- `\mathrm{Str}`. -/
def supertrace (mobius : MobiusCoefficient) (support : Finset ℕ) (beta : ℝ) : ℝ :=
  mobius.finiteSupertrace support beta

/-- `\mathrm{Str}(A,\beta)=\sum_{A\cap\mathrm{SqFree}} \mu(n)w_\beta(n)`. -/
theorem supertrace_eq_squarefree_filter (mobius : MobiusCoefficient) (support : Finset ℕ) (beta : ℝ) :
    supertrace mobius support beta =
      ∑ n ∈ support.filter IsSquarefreeState,
        mobius.coeff n * primonBoltzmannWeight beta n := by
  classical
  exact mobius.finiteSupertrace_eq_squarefree_filter support beta

end InfoGeometry.Arithmetic.PrimonGasSupertrace
