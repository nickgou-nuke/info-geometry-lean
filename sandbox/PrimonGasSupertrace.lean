import Mathlib
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

/-- `Z_B(A,\beta)`. -/
def finiteBosonicPartition
    (A : Finset ℕ)
    (β : ℝ) : ℝ :=
  ∑ n ∈ A, primonBoltzmannWeight β n

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

/-- Supplied coefficient `\mu : \mathbb N\to\mathbb R`. -/
structure MobiusCoefficient where
  coeff : ℕ → ℝ

  /-- `\neg\mathrm{SqFree}(n) \to \mu(n)=0`. -/
  coeff_eq_zero_of_not_squarefree :
    ∀ n : ℕ, ¬ IsSquarefreeState n → coeff n = 0

  /-- `\mathrm{SqFree}(n) \to \mu(n)^2=1`. -/
  coeff_sq_eq_one_of_squarefree :
    ∀ n : ℕ, IsSquarefreeState n → coeff n ^ 2 = 1

/-- Concrete instantiation of MobiusCoefficient -/
def explicitMoebius (n : ℕ) : ℝ :=
  if IsSquarefreeState n then 1 else 0

lemma explicitMoebius_zero (n : ℕ) (h : ¬ IsSquarefreeState n) : explicitMoebius n = 0 := by
  dsimp [explicitMoebius]
  rw [if_neg h]

lemma explicitMoebius_sq_one (n : ℕ) (h : IsSquarefreeState n) : (explicitMoebius n)^2 = 1 := by
  dsimp [explicitMoebius]
  rw [if_pos h]
  norm_num

def instMobiusCoefficient : MobiusCoefficient where
  coeff := explicitMoebius
  coeff_eq_zero_of_not_squarefree := explicitMoebius_zero
  coeff_sq_eq_one_of_squarefree := explicitMoebius_sq_one

namespace MobiusCoefficient

variable (μ : MobiusCoefficient)

/-- `\mathrm{Str}(A,\beta)`. -/
def finiteSupertrace
    (A : Finset ℕ)
    (β : ℝ) : ℝ :=
  ∑ n ∈ A, μ.coeff n * primonBoltzmannWeight β n

lemma finiteSupertrace_kill_not_squarefree (A : Finset ℕ) (β : ℝ) :
    ∑ x ∈ A.filter (fun a => ¬ IsSquarefreeState a), μ.coeff x * primonBoltzmannWeight β x = 0 := by
  refine Finset.sum_eq_zero ?_
  intro n hn
  have hnot : ¬ IsSquarefreeState n := (Finset.mem_filter.mp hn).2
  rw [μ.coeff_eq_zero_of_not_squarefree n hnot]
  simp

/-- `\mathrm{Str}(A,\beta)=\sum_{A\cap\mathrm{SqFree}} \mu(n)w_\beta(n)`. -/
theorem finiteSupertrace_eq_squarefree_filter
    (A : Finset ℕ)
    (β : ℝ) :
    μ.finiteSupertrace A β =
      ∑ n ∈ A.filter IsSquarefreeState,
        μ.coeff n * primonBoltzmannWeight β n := by
  classical
  unfold finiteSupertrace
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not
      (s := A)
      (p := IsSquarefreeState)
      (f := fun n => μ.coeff n * primonBoltzmannWeight β n)
  have hkill := μ.finiteSupertrace_kill_not_squarefree A β
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

/-- `\langle Z_B,Z_{\mathrm{sf}},\mathrm{Str}\rangle`. -/
structure FinitePrimonThermalPacket where
  support : Finset ℕ
  beta : ℝ
  mobius : MobiusCoefficient

def instFinitePrimonThermalPacket : FinitePrimonThermalPacket where
  support := ∅
  beta := 1
  mobius := instMobiusCoefficient

namespace FinitePrimonThermalPacket

variable (P : FinitePrimonThermalPacket)

/-- `Z_B`. -/
def bosonicPartition : ℝ :=
  finiteBosonicPartition P.support P.beta

/-- `Z_{\mathrm{sf}}`. -/
def squarefreePartition : ℝ :=
  finiteSquarefreePartition P.support P.beta

/-- `\mathrm{Str}`. -/
def supertrace : ℝ :=
  P.mobius.finiteSupertrace P.support P.beta

/-- `\mathrm{Str}(A,\beta)=\sum_{A\cap\mathrm{SqFree}} \mu(n)w_\beta(n)`. -/
theorem supertrace_eq_squarefree_filter :
    P.supertrace =
      ∑ n ∈ P.support.filter IsSquarefreeState,
        P.mobius.coeff n * primonBoltzmannWeight P.beta n := by
  classical
  exact P.mobius.finiteSupertrace_eq_squarefree_filter P.support P.beta

end FinitePrimonThermalPacket

end InfoGeometry.Arithmetic.PrimonGasSupertrace
