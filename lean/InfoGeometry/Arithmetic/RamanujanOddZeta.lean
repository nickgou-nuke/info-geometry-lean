import Mathlib.Tactic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Data.PNat.Basic
import Mathlib.NumberTheory.Bernoulli

/-!
# InfoGeometry.Arithmetic.RamanujanOddZeta

Type-safe Lean surface for Ramanujan's transformation formula for odd zeta
values.

This file deliberately does not prove the analytic Ramanujan identity from
Eisenstein/Lambert-series theory.  It fixes the real-valued statement so that:

* the Lambert series is indexed by positive naturals `ℕ+`, avoiding the
  singular origin;
* the reflected `(-β)^{-n}` weight is represented as
  `(-1)^n * β^{-n}`, avoiding real powers of a negative base;
* the analytic identity is exposed as a proof-carrying socket, so downstream
  code can use the exact formula without adding placeholders or fake assumptions.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.RamanujanOddZeta

open Complex

/-- The positive odd integer `2n+1` used in Ramanujan's odd-zeta formula. -/
def oddZetaIndex (n : ℕ) : ℕ :=
  2 * n + 1

/-- The real readout of `ζ(2n+1)`. -/
def oddZetaValue (n : ℕ) : ℝ :=
  (riemannZeta ((oddZetaIndex n : ℕ) : ℂ)).re

/--
One positive-index Lambert term
`k^{-(2n+1)} / (exp(2αk)-1)`.
-/
def lambertTerm (n : ℕ) (α : ℝ) (k : ℕ+) : ℝ :=
  ((k : ℝ) ^ (-(oddZetaIndex n : ℝ))) /
    (Real.exp (2 * α * (k : ℝ)) - 1)

/-- Ramanujan Lambert series over positive integers only. -/
def lambertSeries (n : ℕ) (α : ℝ) : ℝ :=
  ∑' k : ℕ+, lambertTerm n α k

/-- The half-zeta plus Lambert block appearing on each thermal side. -/
def ramanujanThermalBlock (n : ℕ) (α : ℝ) : ℝ :=
  (1 / 2 : ℝ) * oddZetaValue n + lambertSeries n α

/-- The positive-side modular weight `α^{-n}`. -/
def modularWeight (n : ℕ) (α : ℝ) : ℝ :=
  α ^ (-(n : ℝ))

lemma modularWeight_pos {n : ℕ} {α : ℝ} (hα : 0 < α) :
    0 < modularWeight n α := by
  unfold modularWeight
  exact Real.rpow_pos_of_pos hα _

lemma modularWeight_ne_zero {n : ℕ} {α : ℝ} (hα : 0 < α) :
    modularWeight n α ≠ 0 :=
  (modularWeight_pos (n := n) hα).ne'

/--
The reflected modular weight, written without a real power of a negative base:
`(-β)^{-n}` is represented as `(-1)^n * β^{-n}`.
-/
def reflectedModularWeight (n : ℕ) (β : ℝ) : ℝ :=
  (-1 : ℝ) ^ n * β ^ (-(n : ℝ))

/-- Bernoulli/factorial coefficient `B_m / m!` as a real number. -/
def bernoulliFactor (m : ℕ) : ℝ :=
  (bernoulli m : ℝ) / ((Nat.factorial m : ℕ) : ℝ)

/-- One finite Bernoulli anomaly summand in Ramanujan's formula. -/
def bernoulliAnomalyTerm (n : ℕ) (α β : ℝ) (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k *
    bernoulliFactor (2 * k) *
    bernoulliFactor (2 * n + 2 - 2 * k) *
    α ^ ((n + 1 - k : ℕ) : ℝ) *
    β ^ (k : ℝ)

/-- The finite Bernoulli anomaly polynomial. -/
def bernoulliAnomaly (n : ℕ) (α β : ℝ) : ℝ :=
  (2 : ℝ) ^ (2 * n) *
    (Finset.range (n + 2)).sum (fun k => bernoulliAnomalyTerm n α β k)

/-- Left-hand side of Ramanujan's odd-zeta transformation. -/
def ramanujanOddZetaLHS (n : ℕ) (α : ℝ) : ℝ :=
  modularWeight n α * ramanujanThermalBlock n α

/-- Right-hand side of Ramanujan's odd-zeta transformation. -/
def ramanujanOddZetaRHS (n : ℕ) (α β : ℝ) : ℝ :=
  reflectedModularWeight n β * ramanujanThermalBlock n β -
    bernoulliAnomaly n α β

/-- Proposition form of Ramanujan's odd-zeta transformation. -/
def RamanujanOddZetaFormula (n : ℕ) (α β : ℝ) : Prop :=
  ramanujanOddZetaLHS n α = ramanujanOddZetaRHS n α β

/-! ## Type-safety lemmas for the two friction points -/

/-- Positive-natural indexing keeps the Lambert base strictly positive. -/
theorem pnat_real_coe_pos (k : ℕ+) :
    0 < (k : ℝ) := by
  exact_mod_cast k.pos

/-- The Lambert term is explicitly indexed away from the singular origin. -/
theorem lambertTerm_positive_base (n : ℕ) (α : ℝ) (k : ℕ+) :
    0 < (k : ℝ) ∧
      lambertTerm n α k =
        ((k : ℝ) ^ (-(oddZetaIndex n : ℝ))) /
          (Real.exp (2 * α * (k : ℝ)) - 1) := by
  exact ⟨pnat_real_coe_pos k, rfl⟩

lemma lambertTerm_pos {n : ℕ} {α : ℝ} (hα : 0 < α) (k : ℕ+) :
    0 < lambertTerm n α k := by
  unfold lambertTerm
  have hk : 0 < (k : ℝ) := pnat_real_coe_pos k
  have hbase : 0 < (k : ℝ) ^ (-(oddZetaIndex n : ℝ)) := Real.rpow_pos_of_pos hk _
  have hexp_arg : 0 < 2 * α * (k : ℝ) := by nlinarith
  have hden : 0 < Real.exp (2 * α * (k : ℝ)) - 1 := by
    exact sub_pos.mpr ((Real.one_lt_exp_iff).mpr hexp_arg)
  exact div_pos hbase hden

/-- The reflected side uses the sign-factored beta weight by definition. -/
theorem reflectedModularWeight_eq_sign_factored (n : ℕ) (β : ℝ) :
    reflectedModularWeight n β = (-1 : ℝ) ^ n * β ^ (-(n : ℝ)) := rfl

/-- The finite Bernoulli anomaly index never exceeds `n+1`. -/
theorem anomaly_index_le_of_mem_range {n k : ℕ}
    (hk : k ∈ Finset.range (n + 2)) :
    k ≤ n + 1 := by
  exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)

/-- Expanded form of the left side. -/
theorem ramanujanOddZetaLHS_eq (n : ℕ) (α : ℝ) :
    ramanujanOddZetaLHS n α =
      α ^ (-(n : ℝ)) *
        ((1 / 2 : ℝ) * oddZetaValue n + ∑' k : ℕ+, lambertTerm n α k) := by
  rfl

/-- Expanded form of the right side with the corrected sign-factored beta weight. -/
theorem ramanujanOddZetaRHS_eq (n : ℕ) (α β : ℝ) :
    ramanujanOddZetaRHS n α β =
      ((-1 : ℝ) ^ n * β ^ (-(n : ℝ))) *
          ((1 / 2 : ℝ) * oddZetaValue n + ∑' k : ℕ+, lambertTerm n β k) -
        (2 : ℝ) ^ (2 * n) *
          (Finset.range (n + 2)).sum (fun k => bernoulliAnomalyTerm n α β k) := by
  rfl

/-! ## Proof-carrying analytic socket -/

/--
Analytic owner socket for Ramanujan's odd-zeta transformation.

Instantiating this structure requires the actual analytic theorem.  This file
only supplies the correctly typed target and theorem-safe consequences.
-/
def RamanujanOddZetaAnalyticSocket : Prop :=
  ∀ (n : ℕ) (α β : ℝ),
    0 < n →
    0 < α →
    0 < β →
    α * β = Real.pi ^ 2 →
    RamanujanOddZetaFormula n α β

/-- The socket yields the proposition-form Ramanujan identity. -/
theorem ramanujan_odd_zeta
    (R : RamanujanOddZetaAnalyticSocket)
    (n : ℕ) (hn : 0 < n) (α β : ℝ)
    (hα : 0 < α) (hβ : 0 < β)
    (hαβ : α * β = Real.pi ^ 2) :
    RamanujanOddZetaFormula n α β :=
  R n α β hn hα hβ hαβ

/--
Expanded theorem form: the analytic socket gives the exact corrected formula
with positive-natural Lambert sums and sign-factored beta weight.
-/
theorem ramanujan_odd_zeta_expanded
    (R : RamanujanOddZetaAnalyticSocket)
    (n : ℕ) (hn : 0 < n) (α β : ℝ)
    (hα : 0 < α) (hβ : 0 < β)
    (hαβ : α * β = Real.pi ^ 2) :
    α ^ (-(n : ℝ)) *
        ((1 / 2 : ℝ) * oddZetaValue n + ∑' k : ℕ+, lambertTerm n α k) =
      ((-1 : ℝ) ^ n * β ^ (-(n : ℝ))) *
          ((1 / 2 : ℝ) * oddZetaValue n + ∑' k : ℕ+, lambertTerm n β k) -
        (2 : ℝ) ^ (2 * n) *
          (Finset.range (n + 2)).sum (fun k => bernoulliAnomalyTerm n α β k) := by
  exact R n α β hn hα hβ hαβ

end InfoGeometry.Arithmetic.RamanujanOddZeta
