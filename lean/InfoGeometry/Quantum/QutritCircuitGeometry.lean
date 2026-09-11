import InfoGeometry.Quantum.QutritGates
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

/-!
# Finite foundations for qutrit circuit geometry

This module formalizes the closed finite claims underlying Li--Yu--Fei,
*Geometry of Quantum Computation with Qutrits*, Scientific Reports 3, 2594
(2013), DOI `10.1038/srep02594`.

It reuses `QutritGates` for the eight normalized traceless Hermitian Gell--Mann
matrices.  The new content is:

* local Gell--Mann strings and their body support;
* the exact count `choose n k * 8^k` of `k`-body generator labels;
* the paper's `32 n^2 - 24 n` one/two-body count;
* the easy/hard coefficient-energy split and squared penalty cost from Eq. (3);
* the noncommutative power estimate used as Proposition 1;
* additive gatewise operator-norm error control for finite circuit products.

The source's operator norm and its Euclidean coefficient norm are kept distinct.
This file does not assert the paper's Lie-bracket generation lemma, Chow/geodesic
claims, time-dependent Schrödinger estimates, Trotter error constants, or final
asymptotic synthesis theorem.  Those require genuine Lie, differential-geometric,
and evolution-operator owners not supplied by the finite statements below.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Quantum.QutritCircuitGeometry

open InfoGeometry.Quantum.Qutrit
open scoped Matrix.Norms.L2Operator

/-- A local direction is either the identity or one of the eight Gell--Mann directions. -/
abbrev LocalGellMannDirection : Type := Option (Fin 8)

/-- A formal Gell--Mann tensor-string label on `n` qutrit sites. -/
abbrev GellMannString (n : ℕ) : Type := Fin n → LocalGellMannDirection

/-- Read a local direction in the existing normalized matrix owner. -/
def localDirectionMatrix : LocalGellMannDirection → QutritMatrix
  | none => 1
  | some a => gellMann a

/-- Sites on which a string carries a nonidentity Gell--Mann direction. -/
def bodySupport {n : ℕ} (s : GellMannString n) : Finset (Fin n) :=
  Finset.univ.filter fun i => (s i).isSome

/-- The body order of a formal Gell--Mann string. -/
def bodyOrder {n : ℕ} (s : GellMannString n) : ℕ :=
  (bodySupport s).card

/-- There are nine local labels: identity and eight Gell--Mann directions. -/
@[simp] theorem localGellMannDirection_card : Fintype.card LocalGellMannDirection = 9 := by
  simp [LocalGellMannDirection]

/-- There are `9^n` formal local-direction strings on `n` sites. -/
theorem gellMannString_card (n : ℕ) : Fintype.card (GellMannString n) = 9 ^ n := by
  simp [GellMannString, LocalGellMannDirection]

/-- A support of size `k`, together with one of eight generators at each support site. -/
abbrev ExactBodyLabel (n k : ℕ) : Type :=
  Σ S : {S : Finset (Fin n) // S.card = k}, ↥(S.1) → Fin 8

/-- Turn an exact-body parameter into its identity/Gell--Mann string. -/
def ExactBodyLabel.toString {n k : ℕ} (L : ExactBodyLabel n k) : GellMannString n :=
  fun i => if hi : i ∈ L.1.1 then some (L.2 ⟨i, hi⟩) else none

/-- The constructed string has exactly the selected support. -/
@[simp] theorem ExactBodyLabel.bodySupport_toString {n k : ℕ} (L : ExactBodyLabel n k) :
    bodySupport L.toString = L.1.1 := by
  ext i
  simp [bodySupport, ExactBodyLabel.toString]

/-- The constructed string has body order `k`. -/
@[simp] theorem ExactBodyLabel.bodyOrder_toString {n k : ℕ} (L : ExactBodyLabel n k) :
    bodyOrder L.toString = k := by
  rw [bodyOrder, ExactBodyLabel.bodySupport_toString]
  exact L.1.2

/-- Exact count of `k`-body Gell--Mann labels: `choose n k * 8^k`. -/
theorem exactBodyLabel_card (n k : ℕ) :
    Fintype.card (ExactBodyLabel n k) = Nat.choose n k * 8 ^ k := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
  simp_rw [show ∀ S : {S : Finset (Fin n) // S.card = k}, S.1.card = k from
    fun S => S.property]
  simp [Fintype.card_finset_len]

/-- Dimension/count of the formal `k`-body generator-label sector. -/
def qutritBodyDimension (n k : ℕ) : ℕ := Nat.choose n k * 8 ^ k

/-- There are `8n` one-body directions. -/
@[simp] theorem qutritOneBodyDimension (n : ℕ) : qutritBodyDimension n 1 = 8 * n := by
  simp [qutritBodyDimension, mul_comm]

/-- There are `64 * choose n 2` two-body directions. -/
@[simp] theorem qutritTwoBodyDimension (n : ℕ) :
    qutritBodyDimension n 2 = 64 * Nat.choose n 2 := by
  simp [qutritBodyDimension, mul_comm]

/-- Total number of one- and two-body Gell--Mann directions. -/
def qutritVisibleDimension (n : ℕ) : ℕ :=
  qutritBodyDimension n 1 + qutritBodyDimension n 2

/-- The source's exact count `L = 32n² - 24n`. -/
theorem qutritVisibleDimension_eq (n : ℕ) :
    qutritVisibleDimension n = 32 * n ^ 2 - 24 * n := by
  have hle : 24 * n ≤ 32 * n ^ 2 := by
    cases n with
    | zero => simp
    | succ n => nlinarith [Nat.zero_le n]
  apply Nat.cast_injective (R := ℚ)
  rw [Nat.cast_sub hle]
  simp [qutritVisibleDimension, qutritBodyDimension, Nat.cast_choose_two]
  ring

/-- Squared coefficient energy in the zero-, one-, and two-body sectors. -/
def easyEnergy {n : ℕ} (h : GellMannString n → ℝ) : ℝ :=
  ∑ s with bodyOrder s ≤ 2, (h s) ^ 2

/-- Squared coefficient energy in the three- and higher-body sectors. -/
def hardEnergy {n : ℕ} (h : GellMannString n → ℝ) : ℝ :=
  ∑ s with 2 < bodyOrder s, (h s) ^ 2

/-- Total squared Euclidean coefficient energy. -/
def totalEnergy {n : ℕ} (h : GellMannString n → ℝ) : ℝ :=
  ∑ s, (h s) ^ 2

/-- Coefficients supported on the zero-, one-, and two-body sectors. -/
def easyProjection {n : ℕ} (h : GellMannString n → ℝ) : GellMannString n → ℝ :=
  fun s => if bodyOrder s ≤ 2 then h s else 0

/-- Coefficients supported on the three- and higher-body sectors. -/
def hardProjection {n : ℕ} (h : GellMannString n → ℝ) : GellMannString n → ℝ :=
  fun s => if 2 < bodyOrder s then h s else 0

/-- Squared penalty cost from Eq. (3): `easy + p² * hard`. -/
def penaltyCostSq {n : ℕ} (p : ℝ) (h : GellMannString n → ℝ) : ℝ :=
  easyEnergy h + p ^ 2 * hardEnergy h

/-- Easy-sector energy is nonnegative. -/
theorem easyEnergy_nonneg {n : ℕ} (h : GellMannString n → ℝ) : 0 ≤ easyEnergy h := by
  apply Finset.sum_nonneg
  intro s _
  positivity

/-- Hard-sector energy is nonnegative. -/
theorem hardEnergy_nonneg {n : ℕ} (h : GellMannString n → ℝ) : 0 ≤ hardEnergy h := by
  apply Finset.sum_nonneg
  intro s _
  positivity

/-- The body-order split partitions the full coefficient energy. -/
theorem totalEnergy_eq_easy_add_hard {n : ℕ} (h : GellMannString n → ℝ) :
    totalEnergy h = easyEnergy h + hardEnergy h := by
  rw [easyEnergy, hardEnergy, totalEnergy]
  symm
  simpa only [not_le] using
    Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (GellMannString n))
      (fun s => bodyOrder s ≤ 2) (fun s => (h s) ^ 2)

/-- The easy and hard coefficient projections recover the original coefficients. -/
theorem easyProjection_add_hardProjection {n : ℕ} (h : GellMannString n → ℝ) :
    easyProjection h + hardProjection h = h := by
  funext s
  by_cases hs : bodyOrder s ≤ 2
  · simp [easyProjection, hardProjection, hs, not_lt_of_ge hs]
  · have hs' : 2 < bodyOrder s := Nat.lt_of_not_ge hs
    simp [easyProjection, hardProjection, hs, hs']

/-- The total energy of the easy projection is exactly the easy-sector energy. -/
theorem totalEnergy_easyProjection {n : ℕ} (h : GellMannString n → ℝ) :
    totalEnergy (easyProjection h) = easyEnergy h := by
  rw [totalEnergy, easyEnergy, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : bodyOrder s ≤ 2 <;> simp [easyProjection, hs]

/-- The total energy of the hard projection is exactly the hard-sector energy. -/
theorem totalEnergy_hardProjection {n : ℕ} (h : GellMannString n → ℝ) :
    totalEnergy (hardProjection h) = hardEnergy h := by
  rw [totalEnergy, hardEnergy, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : 2 < bodyOrder s <;> simp [hardProjection, hs]

/-- The penalty cost dominates the easy-sector energy. -/
theorem easyEnergy_le_penaltyCostSq {n : ℕ} (p : ℝ) (h : GellMannString n → ℝ) :
    easyEnergy h ≤ penaltyCostSq p h := by
  simp only [penaltyCostSq, le_add_iff_nonneg_right]
  exact mul_nonneg (sq_nonneg p) (hardEnergy_nonneg h)

/-- The penalty cost dominates the penalized hard-sector energy. -/
theorem penalizedHardEnergy_le_penaltyCostSq {n : ℕ}
    (p : ℝ) (h : GellMannString n → ℝ) :
    p ^ 2 * hardEnergy h ≤ penaltyCostSq p h := by
  simp only [penaltyCostSq]
  exact le_add_of_nonneg_left (easyEnergy_nonneg h)

/-- Positive penalty suppresses hard-sector energy by the inverse squared penalty. -/
theorem hardEnergy_le_penaltyCostSq_div_sq {n : ℕ} {p : ℝ} (hp : 0 < p)
    (h : GellMannString n → ℝ) :
    hardEnergy h ≤ penaltyCostSq p h / p ^ 2 := by
  rw [le_div_iff₀ (sq_pos_of_pos hp)]
  simpa [mul_comm] using penalizedHardEnergy_le_penaltyCostSq p h

/-- Any upper bound on penalty cost gives the corresponding hard-sector energy bound. -/
theorem hardEnergy_le_budget_div_sq {n : ℕ} {p budget : ℝ} (hp : 0 < p)
    (h : GellMannString n → ℝ) (hcost : penaltyCostSq p h ≤ budget) :
    hardEnergy h ≤ budget / p ^ 2 := by
  exact (hardEnergy_le_penaltyCostSq_div_sq hp h).trans
    ((div_le_div_iff_of_pos_right (sq_pos_of_pos hp)).2 hcost)

/-- For `p ≥ 1`, the penalty cost dominates the unweighted total energy. -/
theorem totalEnergy_le_penaltyCostSq {n : ℕ} {p : ℝ} (hp : 1 ≤ p)
    (h : GellMannString n → ℝ) :
    totalEnergy h ≤ penaltyCostSq p h := by
  rw [totalEnergy_eq_easy_add_hard]
  have hhard := hardEnergy_nonneg h
  have hp2 : 1 ≤ p ^ 2 := by nlinarith
  have hscaled := mul_le_mul_of_nonneg_right hp2 hhard
  simp only [one_mul] at hscaled
  simpa [penaltyCostSq] using add_le_add_left hscaled (easyEnergy h)

/--
Noncommutative power estimate used in Proposition 1.

The statement only needs both elements to lie in the closed unit ball; unitary
operators satisfy those hypotheses for their operator norm.
-/
theorem norm_pow_sub_pow_le {A : Type*} [NormedRing A] [NormOneClass A]
    (x y : A) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (N : ℕ) :
    ‖x ^ N - y ^ N‖ ≤ N * ‖x - y‖ := by
  induction N with
  | zero => simp
  | succ N ih =>
      calc
        ‖x ^ (N + 1) - y ^ (N + 1)‖ =
            ‖x ^ N * (x - y) + (x ^ N - y ^ N) * y‖ := by
              congr 1
              noncomm_ring
        _ ≤ ‖x ^ N * (x - y)‖ + ‖(x ^ N - y ^ N) * y‖ := norm_add_le _ _
        _ ≤ ‖x ^ N‖ * ‖x - y‖ + ‖x ^ N - y ^ N‖ * ‖y‖ := by
              gcongr <;> exact norm_mul_le _ _
        _ ≤ 1 * ‖x - y‖ + (N * ‖x - y‖) * 1 := by
              apply add_le_add
              · apply mul_le_mul_of_nonneg_right
                  (show ‖x ^ N‖ ≤ 1 by
                    exact (norm_pow_le x N).trans (pow_le_one₀ (norm_nonneg x) hx))
                exact norm_nonneg _
              · exact mul_le_mul ih hy
                  (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
        _ = ((N + 1 : ℕ) : ℝ) * ‖x - y‖ := by
              push_cast
              ring

/-- A qutrit-register unitary has native `L²` operator norm one. -/
theorem qutritRegisterGate_norm {n : ℕ} (U : QutritRegisterGate n) :
    ‖(U : Matrix (QutritRegisterIndex n) (QutritRegisterIndex n) ℂ)‖ = 1 := by
  have hunit :
      star (U : Matrix (QutritRegisterIndex n) (QutritRegisterIndex n) ℂ) * U = 1 :=
    U.property.1
  change Matrix.conjTranspose
    (U : Matrix (QutritRegisterIndex n) (QutritRegisterIndex n) ℂ) * U = 1 at hunit
  have hnorm := congrArg norm hunit
  rw [Matrix.l2_opNorm_conjTranspose_mul_self, norm_one] at hnorm
  nlinarith [norm_nonneg
    (U : Matrix (QutritRegisterIndex n) (QutritRegisterIndex n) ℂ)]

/-- Proposition 1 specialized to native qutrit-register gates and their operator norm. -/
theorem qutritRegisterGate_pow_sub_pow_le {n : ℕ}
    (A B : QutritRegisterGate n) (N : ℕ) :
    ‖(A : Matrix (QutritRegisterIndex n) (QutritRegisterIndex n) ℂ) ^ N -
        (B : Matrix (QutritRegisterIndex n) (QutritRegisterIndex n) ℂ) ^ N‖ ≤
      N * ‖(A : Matrix (QutritRegisterIndex n) (QutritRegisterIndex n) ℂ) -
        (B : Matrix (QutritRegisterIndex n) (QutritRegisterIndex n) ℂ)‖ := by
  apply norm_pow_sub_pow_le
  · exact (qutritRegisterGate_norm A).le
  · exact (qutritRegisterGate_norm B).le

/-- A product of contractions is a contraction. -/
theorem norm_list_prod_le_one {A : Type*} [NormedRing A] [NormOneClass A]
    (xs : List A) (hxs : ∀ x ∈ xs, ‖x‖ ≤ 1) : ‖xs.prod‖ ≤ 1 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      calc
        ‖(x :: xs).prod‖ = ‖x * xs.prod‖ := by rfl
        _ ≤ ‖x‖ * ‖xs.prod‖ := norm_mul_le _ _
        _ ≤ 1 * 1 := by
          apply mul_le_mul
          · exact hxs x (by simp)
          · exact ih (fun y hy => hxs y (by simp [hy]))
          · exact norm_nonneg _
          · exact zero_le_one
        _ = 1 := one_mul 1

/-- The error of two equal-length products of contractions is bounded by the sum of
factorwise errors. -/
theorem norm_list_prod_sub_prod_le {A : Type*} [NormedRing A] [NormOneClass A]
    (xs ys : List A) (hlen : xs.length = ys.length)
    (hxs : ∀ x ∈ xs, ‖x‖ ≤ 1) (hys : ∀ y ∈ ys, ‖y‖ ≤ 1) :
    ‖xs.prod - ys.prod‖ ≤ (xs.zipWith (fun x y => ‖x - y‖) ys).sum := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => simp
      | cons y ys => simp at hlen
  | cons x xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          have htail : xs.length = ys.length := by simpa using hlen
          calc
            ‖(x :: xs).prod - (y :: ys).prod‖ =
                ‖x * (xs.prod - ys.prod) + (x - y) * ys.prod‖ := by
                  congr 1
                  noncomm_ring
            _ ≤ ‖x * (xs.prod - ys.prod)‖ + ‖(x - y) * ys.prod‖ := norm_add_le _ _
            _ ≤ ‖x‖ * ‖xs.prod - ys.prod‖ + ‖x - y‖ * ‖ys.prod‖ := by
                  exact add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
            _ ≤ 1 * (xs.zipWith (fun a b => ‖a - b‖) ys).sum + ‖x - y‖ * 1 := by
                  gcongr
                  · exact hxs x (by simp)
                  · exact ih ys htail
                      (fun a ha => hxs a (by simp [ha]))
                      (fun b hb => hys b (by simp [hb]))
                  · exact norm_list_prod_le_one ys (fun b hb => hys b (by simp [hb]))
            _ = ((x :: xs).zipWith (fun a b => ‖a - b‖) (y :: ys)).sum := by
                  simp [add_comm]

/-- Matrices acting on an `n`-qutrit register. -/
abbrev QutritRegisterMatrix (n : ℕ) : Type :=
  Matrix (QutritRegisterIndex n) (QutritRegisterIndex n) ℂ

/-- Matrix underlying a bundled register gate. -/
def qutritRegisterGateMatrix {n : ℕ} (U : QutritRegisterGate n) :
    QutritRegisterMatrix n := U

/-- Matrix product represented by a finite qutrit-register circuit. -/
def qutritCircuitMatrix {n : ℕ} (C : List (QutritRegisterGate n)) :
    QutritRegisterMatrix n :=
  (C.map qutritRegisterGateMatrix).prod

/-- Sum of gatewise operator-norm errors between two circuits. -/
def qutritCircuitGatewiseError {n : ℕ}
    (C D : List (QutritRegisterGate n)) : ℝ :=
  ((C.map qutritRegisterGateMatrix).zipWith
    (fun U V => ‖U - V‖)
    (D.map qutritRegisterGateMatrix)).sum

/-- Gatewise approximation errors add under composition of equal-length qutrit circuits. -/
theorem qutritCircuitMatrix_sub_norm_le_gatewiseError {n : ℕ}
    (C D : List (QutritRegisterGate n)) (hlen : C.length = D.length) :
    ‖qutritCircuitMatrix C - qutritCircuitMatrix D‖ ≤ qutritCircuitGatewiseError C D := by
  have hC : ∀ U ∈ C.map qutritRegisterGateMatrix, ‖U‖ ≤ 1 := by
    intro U hU
    rcases List.mem_map.mp hU with ⟨G, -, rfl⟩
    exact (qutritRegisterGate_norm G).le
  have hD : ∀ U ∈ D.map qutritRegisterGateMatrix, ‖U‖ ≤ 1 := by
    intro U hU
    rcases List.mem_map.mp hU with ⟨G, -, rfl⟩
    exact (qutritRegisterGate_norm G).le
  exact norm_list_prod_sub_prod_le _ _ (by simpa using hlen) hC hD

/-- A uniform gatewise error bound gives a circuit error budget linear in circuit length. -/
theorem qutritCircuitMatrix_sub_norm_le_length_mul {n : ℕ}
    (C D : List (QutritRegisterGate n)) (ε : ℝ)
    (hgate : List.Forall₂
      (fun U V => ‖qutritRegisterGateMatrix U - qutritRegisterGateMatrix V‖ ≤ ε) C D) :
    ‖qutritCircuitMatrix C - qutritCircuitMatrix D‖ ≤ C.length * ε := by
  apply (qutritCircuitMatrix_sub_norm_le_gatewiseError C D hgate.length_eq).trans
  induction hgate with
  | nil => simp [qutritCircuitGatewiseError]
  | @cons U V C D hUV _ ih =>
      change ‖qutritRegisterGateMatrix U - qutritRegisterGateMatrix V‖ +
          qutritCircuitGatewiseError C D ≤ ↑(List.length (U :: C)) * ε
      calc
        _ ≤ ε + C.length * ε := add_le_add hUV ih
        _ = ↑(List.length (U :: C)) * ε := by
          simp
          ring

end InfoGeometry.Quantum.QutritCircuitGeometry
