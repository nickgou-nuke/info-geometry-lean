import InfoGeometry.Canonical.MassieuOptimalTransport
import InfoGeometry.Foundations.NewtonKantorovichCertificate
import Mathlib.Data.Finset.Range

/-!
# InfoGeometry.Canonical.MassieuNewtonKantorovichBridge

Bridge theorem linking:
* algebraic natural-gradient closure (`Δa = a`) from the Massieu lane
* scalar NK majorant update (`t ↦ t + Δ`) from the NK lane.
-/

namespace MassieuNewtonKantorovichBridge

open MassieuOptimalTransport
open InfoGeometry.Foundations.NewtonKantorovichBase
open NewtonKantorovichRoots
open NewtonKantorovichSequence

/--
Composed bridge:
if `Δa` satisfies the Massieu flow equation and is used as NK correction,
then the NK update is exactly `t + a`.
-/
theorem majorantStep_eq_t_add_massieu_coordinate
    (L η t : ℝ)
    (s : MassieuGradientState ℝ)
    (Δa : ℝ)
    (h_flow : s.H * Δa = -s.dPhi)
    (h_deriv : P_deriv L t ≠ 0)
    (hΔ : Δa = nkCorrection L η t) :
    majorantStep L η t = t + s.a := by
  have hcoord : Δa = s.a := natural_gradient_is_coordinate s Δa h_flow
  calc
    majorantStep L η t = t + Δa :=
      majorantStep_eq_t_add_of_correction L η t Δa h_deriv hΔ
    _ = t + s.a := by rw [hcoord]

/--
Step-indexed corollary along the NK majorant sequence:
if the correction at step `n` is realized by a Massieu flow coordinate `a`,
then the next iterate is `t_n + a`.
-/
theorem majorantSeq_succ_eq_add_massieu_coordinate
    (L η : ℝ) (n : Nat)
    (s : MassieuGradientState ℝ)
    (Δa : ℝ)
    (h_flow : s.H * Δa = -s.dPhi)
    (h_deriv : P_deriv L (majorantSeq L η n) ≠ 0)
    (hΔ : Δa = nkCorrection L η (majorantSeq L η n)) :
    majorantSeq L η (n + 1) = majorantSeq L η n + s.a := by
  calc
    majorantSeq L η (n + 1)
        = majorantStep L η (majorantSeq L η n) := by
            simp [majorantSeq_succ]
    _ = majorantSeq L η n + s.a := by
      exact majorantStep_eq_t_add_massieu_coordinate
        L η (majorantSeq L η n) s Δa h_flow h_deriv hΔ

/--
Generic telescoping identity for the majorant sequence:
if each step increment is `corr k`, then the value at `n` is the initial value
plus the finite sum of increments over `range n`.
-/
theorem majorantSeq_eq_initial_add_sum_corrections
    (L η : ℝ) (corr : Nat → ℝ)
    (hstep : ∀ k, majorantSeq L η (k + 1) = majorantSeq L η k + corr k) :
    ∀ n, majorantSeq L η n = majorantSeq L η 0 + Finset.sum (Finset.range n) corr := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        majorantSeq L η (n + 1)
            = majorantSeq L η n + corr n := hstep n
        _ = (majorantSeq L η 0 + Finset.sum (Finset.range n) corr) + corr n := by rw [ih]
        _ = majorantSeq L η 0 + (Finset.sum (Finset.range n) corr + corr n) := by ring
        _ = majorantSeq L η 0 + Finset.sum (Finset.range (n + 1)) corr := by
              rw [Finset.sum_range_succ]

/--
Massieu-specialized finite telescoping formula.

If each NK correction at step `k` is realized by a Massieu-flow coordinate
`(s k).a`, then `majorantSeq n` is `majorantSeq 0` plus the finite sum of
those coordinates.
-/
theorem majorantSeq_eq_initial_add_sum_massieu_coordinates
    (L η : ℝ)
    (s : Nat → MassieuGradientState ℝ)
    (Δ : Nat → ℝ)
    (h_flow : ∀ k, (s k).H * (Δ k) = -(s k).dPhi)
    (h_deriv : ∀ k, P_deriv L (majorantSeq L η k) ≠ 0)
    (hΔ : ∀ k, Δ k = nkCorrection L η (majorantSeq L η k)) :
    ∀ n, majorantSeq L η n = majorantSeq L η 0 + Finset.sum (Finset.range n) (fun k => (s k).a) := by
  refine majorantSeq_eq_initial_add_sum_corrections L η (fun k => (s k).a) ?_ 
  intro k
  exact majorantSeq_succ_eq_add_massieu_coordinate
    L η k (s k) (Δ k) (h_flow k) (h_deriv k) (hΔ k)

/--
Shifted telescoping identity:
if `t_{k+1} = t_k + corr_k`, then for every anchor `n`,
`t_{n+m} = t_n + Σ_{j < m} corr_{n+j}`.
-/
theorem majorantSeq_eq_anchor_add_sum_corrections
    (L η : ℝ) (corr : Nat → ℝ)
    (hstep : ∀ k, majorantSeq L η (k + 1) = majorantSeq L η k + corr k) :
    ∀ n m, majorantSeq L η (n + m) =
      majorantSeq L η n + Finset.sum (Finset.range m) (fun j => corr (n + j)) := by
  intro n m
  induction m with
  | zero =>
      simp
  | succ m ih =>
      calc
        majorantSeq L η (n + (m + 1))
            = majorantSeq L η ((n + m) + 1) := by simp [Nat.add_assoc]
        _ = majorantSeq L η (n + m) + corr (n + m) := hstep (n + m)
        _ = (majorantSeq L η n + Finset.sum (Finset.range m) (fun j => corr (n + j))) + corr (n + m) := by
              rw [ih]
        _ = majorantSeq L η n + (Finset.sum (Finset.range m) (fun j => corr (n + j)) + corr (n + m)) := by ring
        _ = majorantSeq L η n + Finset.sum (Finset.range (m + 1)) (fun j => corr (n + j)) := by
              rw [Finset.sum_range_succ]

/--
Massieu-specialized shifted telescoping identity:
`t_{n+m}` is `t_n` plus the finite tail sum of Massieu coordinates.
-/
theorem majorantSeq_eq_anchor_add_sum_massieu_coordinates
    (L η : ℝ)
    (s : Nat → MassieuGradientState ℝ)
    (Δ : Nat → ℝ)
    (h_flow : ∀ k, (s k).H * (Δ k) = -(s k).dPhi)
    (h_deriv : ∀ k, P_deriv L (majorantSeq L η k) ≠ 0)
    (hΔ : ∀ k, Δ k = nkCorrection L η (majorantSeq L η k)) :
    ∀ n m, majorantSeq L η (n + m) =
      majorantSeq L η n + Finset.sum (Finset.range m) (fun j => (s (n + j)).a) := by
  refine majorantSeq_eq_anchor_add_sum_corrections L η (fun k => (s k).a) ?_
  intro k
  exact majorantSeq_succ_eq_add_massieu_coordinate
    L η k (s k) (Δ k) (h_flow k) (h_deriv k) (hΔ k)

/--
Asymptotic transfer lemma (epsilon-tail form):
if finite tails of the Massieu-coordinate sums are eventually `ε`-small,
then the corresponding shifted NK sequence increments are eventually `ε`-small.
-/
theorem majorantSeq_tail_norm_lt_of_massieu_tail_norm_lt
    (L η : ℝ)
    (s : Nat → MassieuGradientState ℝ)
    (Δ : Nat → ℝ)
    (h_flow : ∀ k, (s k).H * (Δ k) = -(s k).dPhi)
    (h_deriv : ∀ k, P_deriv L (majorantSeq L η k) ≠ 0)
    (hΔ : ∀ k, Δ k = nkCorrection L η (majorantSeq L η k))
    (ε : ℝ)
    (_hε : 0 < ε)
    (htail : ∃ N : Nat, ∀ n m : Nat, N ≤ n →
      |Finset.sum (Finset.range m) (fun j => (s (n + j)).a)| < ε) :
    ∃ N : Nat, ∀ n m : Nat, N ≤ n →
      |majorantSeq L η (n + m) - majorantSeq L η n| < ε := by
  rcases htail with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n m hn
  have htel :=
    majorantSeq_eq_anchor_add_sum_massieu_coordinates
      L η s Δ h_flow h_deriv hΔ n m
  have hsum : |Finset.sum (Finset.range m) (fun j => (s (n + j)).a)| < ε :=
    hN n m hn
  have hdiff :
      majorantSeq L η (n + m) - majorantSeq L η n =
        Finset.sum (Finset.range m) (fun j => (s (n + j)).a) := by
    linarith [htel]
  simpa [hdiff] using hsum

/--
Standard two-index form (ordered indices):
if Massieu tail sums are eventually `ε`-small, then for all large
`n ≤ m`, one has `|t_m - t_n| < ε`.
-/
theorem majorantSeq_ordered_diff_norm_lt_of_massieu_tail_norm_lt
    (L η : ℝ)
    (s : Nat → MassieuGradientState ℝ)
    (Δ : Nat → ℝ)
    (h_flow : ∀ k, (s k).H * (Δ k) = -(s k).dPhi)
    (h_deriv : ∀ k, P_deriv L (majorantSeq L η k) ≠ 0)
    (hΔ : ∀ k, Δ k = nkCorrection L η (majorantSeq L η k))
    (ε : ℝ)
    (_hε : 0 < ε)
    (htail : ∃ N : Nat, ∀ n m : Nat, N ≤ n →
      |Finset.sum (Finset.range m) (fun j => (s (n + j)).a)| < ε) :
    ∃ N : Nat, ∀ n m : Nat, N ≤ n → n ≤ m →
      |majorantSeq L η m - majorantSeq L η n| < ε := by
  rcases majorantSeq_tail_norm_lt_of_massieu_tail_norm_lt
      L η s Δ h_flow h_deriv hΔ ε (by positivity) htail with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n m hn hnm
  let k := m - n
  have hm : m = n + k := by
    dsimp [k]
    exact (Nat.add_sub_of_le hnm).symm
  have hshift : |majorantSeq L η (n + k) - majorantSeq L η n| < ε := hN n k hn
  rw [hm]
  exact hshift

/--
Strict NK scalar envelope on the bridge surface:
there exists a least upper bound `ℓ` of the shifted majorant sequence and
it lies in the explicit interval `[η, tMinus]`.
-/
theorem shifted_majorant_exists_lub_in_Icc
    (L η : ℝ)
    (hL : 0 < L)
    (hη : 0 ≤ η)
    (hcond : L * η < 1 / 2) :
    ∃ ℓ : ℝ,
      IsLUB (Set.range (fun n : ℕ => majorantSeq L η (n + 1))) ℓ ∧
      η ≤ ℓ ∧ ℓ ≤ tMinus L η := by
  exact
    majorantSeq_shifted_exists_lub_in_Icc_of_kantorovich_strict
      L η hL hη hcond

/--
Strict NK convergence packaging on the bridge surface:
the shifted sequence `u n = majorantSeq L η (n+1)` converges to its least upper
bound `ℓ`, and `ℓ` lies in `[η, tMinus]`.
-/
theorem shifted_majorant_tendsto_lub_in_Icc
    (L η : ℝ)
    (hL : 0 < L)
    (hη : 0 ≤ η)
    (hcond : L * η < 1 / 2) :
    ∃ ℓ : ℝ,
      IsLUB (Set.range (fun n : ℕ => majorantSeq L η (n + 1))) ℓ ∧
      Filter.Tendsto (fun n : ℕ => majorantSeq L η (n + 1)) Filter.atTop (nhds ℓ) ∧
      η ≤ ℓ ∧ ℓ ≤ tMinus L η := by
  rcases shifted_majorant_exists_lub_in_Icc L η hL hη hcond with
    ⟨ℓ, hℓ, hηℓ, hℓtm⟩
  have hpack :=
    majorantSeq_mem_and_monotone_of_kantorovich_strict L η hL hη hcond
  rcases hpack with ⟨_hmem, hmonoStep⟩
  let u : ℕ → ℝ := fun n => majorantSeq L η (n + 1)
  have hu_mono : Monotone u := by
    exact monotone_nat_of_le_succ (fun n => by simpa [u] using hmonoStep n)
  have hu_tendsto : Filter.Tendsto u Filter.atTop (nhds ℓ) :=
    tendsto_atTop_isLUB hu_mono (by simpa [u] using hℓ)
  refine ⟨ℓ, hℓ, ?_, hηℓ, hℓtm⟩
  simpa [u] using hu_tendsto

/--
Cauchy-sequence corollary in `ℝ`:
eventual Massieu-tail smallness implies the NK majorant sequence is Cauchy.
-/
theorem majorantSeq_cauchy_of_massieu_tail
    (L η : ℝ)
    (s : Nat → MassieuGradientState ℝ)
    (Δ : Nat → ℝ)
    (h_flow : ∀ k, (s k).H * (Δ k) = -(s k).dPhi)
    (h_deriv : ∀ k, P_deriv L (majorantSeq L η k) ≠ 0)
    (hΔ : ∀ k, Δ k = nkCorrection L η (majorantSeq L η k))
    (htail : ∀ ε : ℝ, 0 < ε →
      ∃ N : Nat, ∀ n m : Nat, N ≤ n →
        |Finset.sum (Finset.range m) (fun j => (s (n + j)).a)| < ε) :
    CauchySeq (fun n : Nat => majorantSeq L η n) := by
  rw [Metric.cauchySeq_iff']
  intro ε hε
  rcases majorantSeq_ordered_diff_norm_lt_of_massieu_tail_norm_lt
      L η s Δ h_flow h_deriv hΔ ε hε (htail ε hε) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro m hm
  have h := hN N m (le_rfl : N ≤ N) hm
  simpa [Real.dist_eq, abs_sub_comm] using h

/--
Limit-existence corollary in `ℝ`:
eventual Massieu-tail smallness implies convergence of the NK majorant sequence.
-/
theorem majorantSeq_tendsto_of_massieu_tail
    (L η : ℝ)
    (s : Nat → MassieuGradientState ℝ)
    (Δ : Nat → ℝ)
    (h_flow : ∀ k, (s k).H * (Δ k) = -(s k).dPhi)
    (h_deriv : ∀ k, P_deriv L (majorantSeq L η k) ≠ 0)
    (hΔ : ∀ k, Δ k = nkCorrection L η (majorantSeq L η k))
    (htail : ∀ ε : ℝ, 0 < ε →
      ∃ N : Nat, ∀ n m : Nat, N ≤ n →
        |Finset.sum (Finset.range m) (fun j => (s (n + j)).a)| < ε) :
    ∃ ℓ : ℝ, Filter.Tendsto (fun n : Nat => majorantSeq L η n) Filter.atTop (nhds ℓ) := by
  have hcauchy : CauchySeq (fun n : Nat => majorantSeq L η n) :=
    majorantSeq_cauchy_of_massieu_tail L η s Δ h_flow h_deriv hΔ htail
  exact cauchySeq_tendsto_of_complete hcauchy

end MassieuNewtonKantorovichBridge
