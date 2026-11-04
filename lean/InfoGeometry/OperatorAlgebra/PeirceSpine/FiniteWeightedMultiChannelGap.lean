/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.WeightedMultiChannelJordanAnomalyPoset
import InfoGeometry.Core.JordanAssociatorRing
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
Finite-channel extension of the weighted chiral block square identity.  The
channel assumptions are local: each weight commutes with its own nilpotent
pair, while distinct channels satisfy pairwise operator orthogonality.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

open InfoGeometry.OperatorAlgebra.PeirceSpine.WeightedMultiChannelJordanAnomalyPoset
open scoped BigOperators

variable {B ι : Type*} [Ring B] [DecidableEq ι]

/-- The square of a finite sum of pairwise mutually annihilating blocks is the
sum of their squares. -/
theorem sum_sq_of_pairwise_mul_zero (s : Finset ι) (f : ι → B)
    (hcross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f i * f j = 0) :
    (∑ i ∈ s, f i) * (∑ i ∈ s, f i) = ∑ i ∈ s, f i * f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, mul_add, add_mul, add_mul]
      have hleft : f a * (∑ i ∈ s, f i) = 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_eq_zero
        intro b hb
        exact hcross a (Finset.mem_insert_self a s) b
          (Finset.mem_insert_of_mem hb) (by
            intro h
            subst b
            exact (ha hb).elim)
      have hright : (∑ i ∈ s, f i) * f a = 0 := by
        rw [Finset.sum_mul]
        apply Finset.sum_eq_zero
        intro b hb
        exact hcross b (Finset.mem_insert_of_mem hb) a
          (Finset.mem_insert_self a s) (by
            intro h
            subst b
            exact (ha hb).elim)
      have hcross_s : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f i * f j = 0 := by
        intro i hi j hj hij
        exact hcross i (Finset.mem_insert_of_mem hi) j
          (Finset.mem_insert_of_mem hj) hij
      rw [hleft, hright, add_zero, zero_add, ih hcross_s]

/-- A finite product of two sums has only its diagonal terms when every
off-diagonal product vanishes. -/
theorem sum_mul_sum_of_pairwise_cross_zero (s : Finset ι) (f g : ι → B)
    (hcross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f i * g j = 0) :
    (∑ i ∈ s, f i) * (∑ i ∈ s, g i) = ∑ i ∈ s, f i * g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha,
        mul_add, add_mul, add_mul]
      have hleft : f a * (∑ i ∈ s, g i) = 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_eq_zero
        intro b hb
        exact hcross a (Finset.mem_insert_self a s) b
          (Finset.mem_insert_of_mem hb) (by
            intro h
            subst b
            exact (ha hb).elim)
      have hright : (∑ i ∈ s, f i) * g a = 0 := by
        rw [Finset.sum_mul]
        apply Finset.sum_eq_zero
        intro b hb
        exact hcross b (Finset.mem_insert_of_mem hb) a
          (Finset.mem_insert_self a s) (by
            intro h
            subst b
            exact (ha hb).elim)
      have hcross_s : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f i * g j = 0 := by
        intro i hi j hj hij
        exact hcross i (Finset.mem_insert_of_mem hi) j
          (Finset.mem_insert_of_mem hj) hij
      rw [hleft, hright, add_zero, zero_add, ih hcross_s]

variable [StarRing B]

/-- A self-adjoint weight commuting with its channel generator also commutes
with that generator's adjoint. This removes the redundant second local
commutation hypothesis from weighted channel interfaces. -/
theorem self_adjoint_weight_comm_star (c N : B)
    (hc_star : star c = c) (hc : c * N = N * c) :
    c * star N = star N * c := by
  calc c * star N
      = star c * star N := by rw [hc_star]
    _ = star (N * c) := by rw [← star_mul]
    _ = star (c * N) := by rw [hc]
    _ = star N * star c := by rw [star_mul]
    _ = star N * c := by rw [hc_star]

/-- For any finite pairwise orthogonal family of regular nilpotent channels,
the weighted chiral block square is the sum of the channel gaps weighted by
the squares of their own weights. No weight is required to commute with another
channel. -/
theorem weighted_finite_block_sq_eq_gap_sum
    (s : Finset ι) (c N : ι → B)
    (h_nil : ∀ i ∈ s, N i * N i = 0)
    (h_reg : ∀ i ∈ s, N i * star (N i) * N i = N i)
    (h_comm : ∀ i ∈ s, c i * N i = N i * c i)
    (h_comm_star : ∀ i ∈ s, c i * star (N i) = star (N i) * c i)
    (h_cross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      N i * N j = 0 ∧ N j * N i = 0 ∧
      N i * star (N j) = 0 ∧ star (N i) * N j = 0) :
    (∑ i ∈ s, c i * Phi (N i)) * (∑ i ∈ s, c i * Phi (N i)) =
      ∑ i ∈ s, (c i * c i) * Gap (N i) := by
  classical
  let f : ι → B := fun i => c i * Phi (N i)
  have hcross_f : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f i * f j = 0 := by
    intro i hi j hj hij
    rcases h_cross i hi j hj hij with ⟨hijN, hjiN, hiStarJ, hStarI_J⟩
    have hPhi : Phi (N i) * Phi (N j) = 0 :=
      Phi_mul_Phi_orthog (N i) (N j) hijN hjiN hiStarJ hStarI_J
    exact weighted_cross_zero (c i) (Phi (N i)) (c j) (Phi (N j))
      hPhi (comm_weight_Phi (c j) (N j) (h_comm j hj) (h_comm_star j hj))
  rw [sum_sq_of_pairwise_mul_zero s f hcross_f]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp [f]
  rw [weight_mul_weight (c i) (Phi (N i)) (Phi (N i))
      (comm_weight_Phi (c i) (N i) (h_comm i hi) (h_comm_star i hi)),
    Phi_sq_eq_Gap (N i) (h_nil i hi) (h_reg i hi)]

/-- Self-adjoint-weight form of `weighted_finite_block_sq_eq_gap_sum`.
Each weight commutes only with its own channel generator; self-adjointness
supplies commutation with that channel's adjoint. No cross-channel weight
commutation is assumed. -/
theorem weighted_finite_block_sq_eq_gap_sum_of_self_adjoint_weights
    (s : Finset ι) (c N : ι → B)
    (h_nil : ∀ i ∈ s, N i * N i = 0)
    (h_reg : ∀ i ∈ s, N i * star (N i) * N i = N i)
    (h_selfadjoint : ∀ i ∈ s, star (c i) = c i)
    (h_comm : ∀ i ∈ s, c i * N i = N i * c i)
    (h_cross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      N i * N j = 0 ∧ N j * N i = 0 ∧
      N i * star (N j) = 0 ∧ star (N i) * N j = 0) :
    (∑ i ∈ s, c i * Phi (N i)) * (∑ i ∈ s, c i * Phi (N i)) =
      ∑ i ∈ s, (c i * c i) * Gap (N i) := by
  apply weighted_finite_block_sq_eq_gap_sum s c N h_nil h_reg h_comm
  · intro i hi
    exact self_adjoint_weight_comm_star (c i) (N i)
      (h_selfadjoint i hi) (h_comm i hi)
  · exact h_cross

/-- If each channel weight is a sixth-cyclotomic root, the finite weighted
chiral block square has the linearly reduced coefficient `cᵢ - 1` on each
channel gap. This is the finite-family form of the single-channel `Φ₆`
specialization; weights still commute only with their own channels. -/
theorem cyclotomic_weighted_finite_block_sq_eq_gap_sum
    (s : Finset ι) (c N : ι → B)
    (h_cyc : ∀ i ∈ s, Phi6 (c i) = 0)
    (h_nil : ∀ i ∈ s, N i * N i = 0)
    (h_reg : ∀ i ∈ s, N i * star (N i) * N i = N i)
    (h_comm : ∀ i ∈ s, c i * N i = N i * c i)
    (h_comm_star : ∀ i ∈ s, c i * star (N i) = star (N i) * c i)
    (h_cross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      N i * N j = 0 ∧ N j * N i = 0 ∧
      N i * star (N j) = 0 ∧ star (N i) * N j = 0) :
    (∑ i ∈ s, c i * Phi (N i)) * (∑ i ∈ s, c i * Phi (N i)) =
      ∑ i ∈ s, (c i - 1) * Gap (N i) := by
  rw [weighted_finite_block_sq_eq_gap_sum s c N h_nil h_reg h_comm
    h_comm_star h_cross]
  apply Finset.sum_congr rfl
  intro i hi
  have hsq : c i * c i = c i - 1 := by
    calc c i * c i = Phi6 (c i) + (c i - 1) := by
          dsimp [Phi6]
          noncomm_ring
      _ = c i - 1 := by rw [h_cyc i hi, zero_add]
  rw [hsq]

omit [DecidableEq ι] in
/-- A family of self-adjoint weights that commute with their own channel
generators automatically commutes with the adjoint generators. -/
theorem self_adjoint_weights_commute_with_channel_adjoints
    (s : Finset ι) (c N : ι → B)
    (h_selfadjoint : ∀ i ∈ s, star (c i) = c i)
    (h_comm : ∀ i ∈ s, c i * N i = N i * c i) :
    ∀ i ∈ s, c i * star (N i) = star (N i) * c i := by
  intro i hi
  exact self_adjoint_weight_comm_star (c i) (N i)
    (h_selfadjoint i hi) (h_comm i hi)

/-- A channel's own gap fixes its weighted chiral block. -/
theorem gap_mul_weighted_phi_self (c N : B)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N)
    (hc : c * N = N * c) (hcs : c * star N = star N * c) :
    Gap N * (c * Phi N) = c * Phi N := by
  have hcPhi := comm_weight_Phi c N hc hcs
  calc Gap N * (c * Phi N)
    _ = Gap N * (Phi N * c) := by rw [hcPhi]
    _ = (Gap N * Phi N) * c := by rw [← mul_assoc]
    _ = Phi N * c := by rw [Gap_mul_Phi N h_nil h_reg]
    _ = c * Phi N := by rw [← hcPhi]

/-- The weighted gap sum acts on each selected channel with that channel's
quadratic weight. Cross-channel terms vanish using only local weight
commutation and pairwise channel orthogonality. -/
theorem weighted_finite_gap_mul_channel
    (s : Finset ι) (c N : ι → B) (k : ι) (hk : k ∈ s)
    (h_nil : ∀ i ∈ s, N i * N i = 0)
    (h_reg : ∀ i ∈ s, N i * star (N i) * N i = N i)
    (h_comm : ∀ i ∈ s, c i * N i = N i * c i)
    (h_comm_star : ∀ i ∈ s, c i * star (N i) = star (N i) * c i)
    (h_cross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      N i * N j = 0 ∧ N j * N i = 0 ∧
      N i * star (N j) = 0 ∧ star (N i) * N j = 0) :
    (∑ i ∈ s, (c i * c i) * Gap (N i)) * (c k * Phi (N k)) =
      (c k * c k) * (c k * Phi (N k)) := by
  classical
  have hterm (i : ι) (hi : i ∈ s) :
      ((c i * c i) * Gap (N i)) * (c k * Phi (N k)) =
        if i = k then (c k * c k) * (c k * Phi (N k)) else 0 := by
    by_cases hik : i = k
    · subst i
      simp
      calc ((c k * c k) * Gap (N k)) * (c k * Phi (N k))
          = (c k * c k) * (Gap (N k) * (c k * Phi (N k))) := by
            simp only [mul_assoc]
        _ = (c k * c k) * (c k * Phi (N k)) := by
          rw [gap_mul_weighted_phi_self (c k) (N k)
            (h_nil k hk) (h_reg k hk) (h_comm k hk) (h_comm_star k hk)]
    · simp [hik]
      rcases h_cross i hi k hk hik with ⟨hikN, hkiN, hiStarK, hStarI_K⟩
      have hgap : Gap (N i) * (c k * Phi (N k)) = 0 := by
        have hcPhi := comm_weight_Phi (c k) (N k) (h_comm k hk) (h_comm_star k hk)
        calc Gap (N i) * (c k * Phi (N k))
          _ = Gap (N i) * (Phi (N k) * c k) := by rw [hcPhi]
          _ = (Gap (N i) * Phi (N k)) * c k := by
            simp only [mul_assoc]
          _ = 0 := by
            rw [Gap_mul_Phi_orthog (N i) (N k) (h_nil i hi)
              hikN hkiN hiStarK hStarI_K, zero_mul]
      calc ((c i * c i) * Gap (N i)) * (c k * Phi (N k))
          = (c i * c i) * (Gap (N i) * (c k * Phi (N k))) := by
            simp only [mul_assoc]
        _ = (c i * c i) * 0 := by rw [hgap]
        _ = 0 := by rw [mul_zero]
  rw [Finset.sum_mul]
  rw [Finset.sum_eq_single k]
  · rw [hterm k hk]
    simp
  · intro i hi hik
    rw [hterm i hi]
    simp [hik]
  · intro hnot
    exact (hnot hk).elim

/-- Self-adjoint-weight interface for the channel filter: the only weight
commutation assumptions are `c i * N i = N i * c i` within each channel. -/
theorem weighted_finite_gap_mul_channel_of_self_adjoint_weights
    (s : Finset ι) (c N : ι → B) (k : ι) (hk : k ∈ s)
    (h_nil : ∀ i ∈ s, N i * N i = 0)
    (h_reg : ∀ i ∈ s, N i * star (N i) * N i = N i)
    (h_selfadjoint : ∀ i ∈ s, star (c i) = c i)
    (h_comm : ∀ i ∈ s, c i * N i = N i * c i)
    (h_cross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      N i * N j = 0 ∧ N j * N i = 0 ∧
      N i * star (N j) = 0 ∧ star (N i) * N j = 0) :
    (∑ i ∈ s, (c i * c i) * Gap (N i)) * (c k * Phi (N k)) =
      (c k * c k) * (c k * Phi (N k)) := by
  exact weighted_finite_gap_mul_channel s c N k hk h_nil h_reg h_comm
    (self_adjoint_weights_commute_with_channel_adjoints s c N
      h_selfadjoint h_comm) h_cross

/-- The weighted finite block obeys the channelwise secular equation: its
square minus the selected channel's squared weight annihilates that channel's
weighted chiral block. -/
theorem weighted_finite_block_secular_channel
    (s : Finset ι) (c N : ι → B) (k : ι) (hk : k ∈ s)
    (h_nil : ∀ i ∈ s, N i * N i = 0)
    (h_reg : ∀ i ∈ s, N i * star (N i) * N i = N i)
    (h_comm : ∀ i ∈ s, c i * N i = N i * c i)
    (h_comm_star : ∀ i ∈ s, c i * star (N i) = star (N i) * c i)
    (h_cross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      N i * N j = 0 ∧ N j * N i = 0 ∧
      N i * star (N j) = 0 ∧ star (N i) * N j = 0) :
    ((∑ i ∈ s, c i * Phi (N i)) * (∑ i ∈ s, c i * Phi (N i)) - c k * c k) *
      (c k * Phi (N k)) = 0 := by
  rw [weighted_finite_block_sq_eq_gap_sum s c N h_nil h_reg h_comm h_comm_star h_cross,
    sub_mul,
    weighted_finite_gap_mul_channel s c N k hk h_nil h_reg h_comm h_comm_star h_cross,
    sub_self]

/-- Self-adjoint-weight form of the channelwise secular equation, requiring
only channel-local commutation between each weight and its nilpotent. -/
theorem weighted_finite_block_secular_channel_of_self_adjoint_weights
    (s : Finset ι) (c N : ι → B) (k : ι) (hk : k ∈ s)
    (h_nil : ∀ i ∈ s, N i * N i = 0)
    (h_reg : ∀ i ∈ s, N i * star (N i) * N i = N i)
    (h_selfadjoint : ∀ i ∈ s, star (c i) = c i)
    (h_comm : ∀ i ∈ s, c i * N i = N i * c i)
    (h_cross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      N i * N j = 0 ∧ N j * N i = 0 ∧
      N i * star (N j) = 0 ∧ star (N i) * N j = 0) :
    ((∑ i ∈ s, c i * Phi (N i)) * (∑ i ∈ s, c i * Phi (N i)) - c k * c k) *
      (c k * Phi (N k)) = 0 := by
  exact weighted_finite_block_secular_channel s c N k hk h_nil h_reg h_comm
    (self_adjoint_weights_commute_with_channel_adjoints s c N
      h_selfadjoint h_comm) h_cross

omit [StarRing B] in
/-- Negating the left input of an anticommutator negates the result. -/
theorem anticomm_neg_left (x y : B) :
    anticomm (-x) y = -anticomm x y := by
  dsimp [anticomm]
  calc
    (-x) * y + y * (-x) = -(x * y) + -(y * x) := by rw [neg_mul, mul_neg]
    _ = -(x * y + y * x) := by rw [neg_add_rev, add_comm]

omit [StarRing B] in
/-- Negating the right input of an anticommutator negates the result. -/
theorem anticomm_neg_right (x y : B) :
    anticomm x (-y) = -anticomm x y := by
  dsimp [anticomm]
  calc
    x * (-y) + (-y) * x = -(x * y) + -(y * x) := by rw [mul_neg, neg_mul]
    _ = -(x * y + y * x) := by rw [neg_add_rev, add_comm]

omit [StarRing B] in
/-- A general product criterion for the Grade-3 Jordan associator. -/
theorem jordanAssoc_eq_quad_of_block_products (A J G S H : B)
    (hAA : A * A = G)
    (hJA : J * A = S)
    (hAJ : A * J = -S)
    (hGJ : G * J = H)
    (hJG : J * G = H) :
    JordanAssoc A A J = quad H := by
  have hAanti : anticomm A A = G + G := by
    dsimp [anticomm]
    rw [hAA]
  have hAJanti : anticomm A J = 0 := by
    dsimp [anticomm]
    rw [hAJ, hJA, neg_add_cancel]
  dsimp [JordanAssoc]
  rw [hAanti, hAJanti, anticomm_zero_right, sub_zero]
  dsimp [anticomm, quad]
  rw [add_mul, mul_add, hGJ, hJG]

omit [StarRing B] in
/-- All four repeated-slot placements of the chiral Jordan associator follow
from the block, rotor, and gap product identities. -/
theorem jordanAssoc_four_chiral_placements (A J G S H K : B)
    (hAA : A * A = G) (hJJ : J * J = -G)
    (hJA : J * A = S) (hAJ : A * J = -S)
    (hGJ : G * J = H) (hJG : J * G = H)
    (hGA : G * A = K) (hAG : A * G = K) :
    JordanAssoc A A J = quad H ∧
    JordanAssoc J A A = -quad H ∧
    JordanAssoc J J A = -quad K ∧
    JordanAssoc A J J = quad K := by
  have hAAanti : anticomm A A = G + G := by
    dsimp [anticomm]
    rw [hAA]
  have hAJanti : anticomm A J = 0 := by
    dsimp [anticomm]
    rw [hAJ, hJA, neg_add_cancel]
  have hJAanti : anticomm J A = 0 := by
    dsimp [anticomm]
    rw [hJA, hAJ]
    simp
  have hJJanti : anticomm J J = -(G + G) := by
    dsimp [anticomm]
    rw [hJJ, ← neg_add_rev]
  have hJGG : anticomm J (G + G) = quad H := by
    dsimp [anticomm, quad]
    calc J * (G + G) + (G + G) * J
        = (J * G + J * G) + (G * J + G * J) := by rw [mul_add, add_mul]
      _ = (H + H) + (H + H) := by rw [hJG, hGJ]
  have hGGJ : anticomm (G + G) J = quad H := by
    dsimp [anticomm, quad]
    calc (G + G) * J + J * (G + G)
        = (G * J + G * J) + (J * G + J * G) := by rw [add_mul, mul_add]
      _ = (H + H) + (H + H) := by rw [hGJ, hJG]
  have hGGA : anticomm (G + G) A = quad K := by
    dsimp [anticomm, quad]
    calc (G + G) * A + A * (G + G)
        = (G * A + G * A) + (A * G + A * G) := by rw [add_mul, mul_add]
      _ = (K + K) + (K + K) := by rw [hGA, hAG]
  have hAGG : anticomm A (G + G) = quad K := by
    dsimp [anticomm, quad]
    calc A * (G + G) + (G + G) * A
        = (A * G + A * G) + (G * A + G * A) := by rw [mul_add, add_mul]
      _ = (K + K) + (K + K) := by rw [hAG, hGA]
  have hNegGGA : anticomm (-(G + G)) A = -quad K := by
    calc anticomm (-(G + G)) A
        = -anticomm (G + G) A := anticomm_neg_left (G + G) A
      _ = -quad K := by rw [hGGA]
  have hAGNegGG : anticomm A (-(G + G)) = -quad K := by
    calc anticomm A (-(G + G))
        = -anticomm A (G + G) := anticomm_neg_right A (G + G)
      _ = -quad K := by rw [hAGG]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact jordanAssoc_eq_quad_of_block_products A J G S H
      hAA hJA hAJ hGJ hJG
  · dsimp [JordanAssoc]
    rw [hJAanti, anticomm_zero_left, hAAanti, hJGG, zero_sub]
  · change anticomm (anticomm J J) A - anticomm J (anticomm J A) = -quad K
    rw [hJJanti, hJAanti, anticomm_zero_right, hNegGGA, sub_zero]
  · change anticomm (anticomm A J) J - anticomm A (anticomm J J) = quad K
    rw [hAJanti, anticomm_zero_left, hJJanti, hAGNegGG, zero_sub, neg_neg]

/-- Finite weighted block, rotor, anomaly, gap, and cubic rotor sums. -/
def weightedFinitePhi (s : Finset ι) (c N : ι → B) : B :=
  ∑ i ∈ s, c i * Phi (N i)

def weightedFiniteJ (s : Finset ι) (c N : ι → B) : B :=
  ∑ i ∈ s, c i * J (N i)

def weightedFiniteSigma (s : Finset ι) (c N : ι → B) : B :=
  ∑ i ∈ s, (c i * c i) * Sigma (N i)

def weightedFiniteGap (s : Finset ι) (c N : ι → B) : B :=
  ∑ i ∈ s, (c i * c i) * Gap (N i)

/-- If each quadratic weight is an idempotent commuting with every selected
channel gap, and the unweighted channel gaps are pairwise orthogonal, then the
finite weighted gap is itself an idempotent. Channel-local weight commutation
alone proves the weighted block-square identity, but does not imply these
cross-support hypotheses. -/
theorem weightedFiniteGap_idem_of_orthogonal_supports
    (s : Finset ι) (c N : ι → B)
    (h_gap_idem : ∀ i ∈ s, Gap (N i) * Gap (N i) = Gap (N i))
    (h_weight_sq_idem : ∀ i ∈ s,
      (c i * c i) * (c i * c i) = c i * c i)
    (h_weight_comm_gap : ∀ i ∈ s, ∀ j ∈ s,
      (c j * c j) * Gap (N i) = Gap (N i) * (c j * c j))
    (h_gap_orthog : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Gap (N i) * Gap (N j) = 0) :
    weightedFiniteGap s c N * weightedFiniteGap s c N =
      weightedFiniteGap s c N := by
  classical
  let f : ι → B := fun i => (c i * c i) * Gap (N i)
  have hterm : ∀ i ∈ s, f i * f i = f i := by
    intro i hi
    dsimp [f]
    calc ((c i * c i) * Gap (N i)) * ((c i * c i) * Gap (N i))
        = (c i * c i) * ((Gap (N i) * (c i * c i)) * Gap (N i)) := by
          simp only [mul_assoc]
      _ = (c i * c i) * (((c i * c i) * Gap (N i)) * Gap (N i)) := by
          rw [h_weight_comm_gap i hi i hi]
      _ = ((c i * c i) * (c i * c i)) *
          (Gap (N i) * Gap (N i)) := by
          simp only [mul_assoc]
      _ = (c i * c i) * Gap (N i) := by
          rw [h_weight_sq_idem i hi, h_gap_idem i hi]
  have hcross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f i * f j = 0 := by
    intro i hi j hj hij
    dsimp [f]
    calc ((c i * c i) * Gap (N i)) * ((c j * c j) * Gap (N j))
        = (c i * c i) *
          ((Gap (N i) * (c j * c j)) * Gap (N j)) := by
          simp only [mul_assoc]
      _ = (c i * c i) *
          (((c j * c j) * Gap (N i)) * Gap (N j)) := by
          rw [h_weight_comm_gap i hi j hj]
      _ = ((c i * c i) * (c j * c j)) *
          (Gap (N i) * Gap (N j)) := by
          simp only [mul_assoc]
      _ = 0 := by rw [h_gap_orthog i hi j hj hij, mul_zero]
  change (∑ i ∈ s, f i) * (∑ i ∈ s, f i) = ∑ i ∈ s, f i
  rw [sum_sq_of_pairwise_mul_zero s f hcross]
  apply Finset.sum_congr rfl
  intro i hi
  exact hterm i hi

def weightedFiniteJ3 (s : Finset ι) (c N : ι → B) : B :=
  ∑ i ∈ s, cube (c i) * J (N i)

def weightedFinitePhi3 (s : Finset ι) (c N : ι → B) : B :=
  ∑ i ∈ s, cube (c i) * Phi (N i)

/-- The finite weighted rotor-block product is the quadratic weighted anomaly. -/
theorem weighted_finite_J_mul_Phi_eq_sigma
    (s : Finset ι) (c N : ι → B)
    (h_nil : ∀ i ∈ s, N i * N i = 0)
    (h_comm : ∀ i ∈ s, c i * N i = N i * c i)
    (h_comm_star : ∀ i ∈ s, c i * star (N i) = star (N i) * c i)
    (h_cross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      N i * N j = 0 ∧ N j * N i = 0 ∧
      N i * star (N j) = 0 ∧ star (N i) * N j = 0) :
    weightedFiniteJ s c N * weightedFinitePhi s c N =
      weightedFiniteSigma s c N := by
  classical
  have hcross_jp : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      (c i * J (N i)) * (c j * Phi (N j)) = 0 := by
    intro i hi j hj hij
    rcases h_cross i hi j hj hij with ⟨hijN, hjiN, hiStarJ, hStarI_J⟩
    exact weighted_cross_zero (c i) (J (N i)) (c j) (Phi (N j))
      (J_mul_Phi_orthog (N i) (N j) hijN hjiN hiStarJ hStarI_J)
      (comm_weight_Phi (c j) (N j) (h_comm j hj) (h_comm_star j hj))
  rw [weightedFiniteJ, weightedFinitePhi,
    sum_mul_sum_of_pairwise_cross_zero s
      (fun i => c i * J (N i)) (fun i => c i * Phi (N i)) hcross_jp]
  unfold weightedFiniteSigma
  apply Finset.sum_congr rfl
  intro i hi
  rw [weight_mul_weight (c i) (J (N i)) (Phi (N i))
      (comm_weight_J (c i) (N i) (h_comm i hi) (h_comm_star i hi)),
    J_mul_Phi (N i) (h_nil i hi)]

/-- Reversing the finite weighted block and rotor gives the negative anomaly. -/
theorem weighted_finite_Phi_mul_J_eq_neg_sigma
    (s : Finset ι) (c N : ι → B)
    (h_nil : ∀ i ∈ s, N i * N i = 0)
    (h_comm : ∀ i ∈ s, c i * N i = N i * c i)
    (h_comm_star : ∀ i ∈ s, c i * star (N i) = star (N i) * c i)
    (h_cross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      N i * N j = 0 ∧ N j * N i = 0 ∧
      N i * star (N j) = 0 ∧ star (N i) * N j = 0) :
    weightedFinitePhi s c N * weightedFiniteJ s c N =
      -weightedFiniteSigma s c N := by
  classical
  have hcross_pj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      (c i * Phi (N i)) * (c j * J (N j)) = 0 := by
    intro i hi j hj hij
    rcases h_cross i hi j hj hij with ⟨hijN, hjiN, hiStarJ, hStarI_J⟩
    exact weighted_cross_zero (c i) (Phi (N i)) (c j) (J (N j))
      (Phi_mul_J_orthog (N i) (N j) hijN hjiN hiStarJ hStarI_J)
      (comm_weight_J (c j) (N j) (h_comm j hj) (h_comm_star j hj))
  rw [weightedFinitePhi, weightedFiniteJ,
    sum_mul_sum_of_pairwise_cross_zero s
      (fun i => c i * Phi (N i)) (fun i => c i * J (N i)) hcross_pj]
  unfold weightedFiniteSigma
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [weight_mul_weight (c i) (Phi (N i)) (J (N i))
      (comm_weight_Phi (c i) (N i) (h_comm i hi) (h_comm_star i hi)),
    Phi_mul_J (N i) (h_nil i hi), mul_neg]

/-- Multiplication of the finite weighted gap by the finite weighted rotor
produces the cubic weighted rotor. -/
theorem weighted_finite_gap_mul_J_eq_J3
    (s : Finset ι) (c N : ι → B)
    (h_nil : ∀ i ∈ s, N i * N i = 0)
    (h_reg : ∀ i ∈ s, N i * star (N i) * N i = N i)
    (h_comm : ∀ i ∈ s, c i * N i = N i * c i)
    (h_comm_star : ∀ i ∈ s, c i * star (N i) = star (N i) * c i)
    (h_cross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      N i * N j = 0 ∧ N j * N i = 0 ∧
      N i * star (N j) = 0 ∧ star (N i) * N j = 0) :
    weightedFiniteGap s c N * weightedFiniteJ s c N =
      weightedFiniteJ3 s c N := by
  classical
  have hcross_gj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ((c i * c i) * Gap (N i)) * (c j * J (N j)) = 0 := by
    intro i hi j hj hij
    rcases h_cross i hi j hj hij with ⟨hijN, hjiN, hiStarJ, hStarI_J⟩
    exact weighted_cross_zero (c i * c i) (Gap (N i)) (c j) (J (N j))
      (Gap_mul_J_orthog (N i) (N j) (h_nil i hi)
        hijN hjiN hiStarJ hStarI_J)
      (comm_weight_J (c j) (N j) (h_comm j hj) (h_comm_star j hj))
  rw [weightedFiniteGap, weightedFiniteJ,
    sum_mul_sum_of_pairwise_cross_zero s
      (fun i => (c i * c i) * Gap (N i)) (fun i => c i * J (N i)) hcross_gj,
    weightedFiniteJ3]
  apply Finset.sum_congr rfl
  intro i hi
  rw [sq_weight_mul_right (c i) (Gap (N i)) (J (N i))
      (comm_weight_Gap (c i) (N i) (h_comm i hi) (h_comm_star i hi)),
    Gap_mul_J (N i) (h_nil i hi) (h_reg i hi)]

/-- Multiplication in the reverse order also produces the cubic weighted
rotor. -/
theorem weighted_finite_J_mul_gap_eq_J3
    (s : Finset ι) (c N : ι → B)
    (h_nil : ∀ i ∈ s, N i * N i = 0)
    (h_reg : ∀ i ∈ s, N i * star (N i) * N i = N i)
    (h_comm : ∀ i ∈ s, c i * N i = N i * c i)
    (h_comm_star : ∀ i ∈ s, c i * star (N i) = star (N i) * c i)
    (h_cross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      N i * N j = 0 ∧ N j * N i = 0 ∧
      N i * star (N j) = 0 ∧ star (N i) * N j = 0) :
    weightedFiniteJ s c N * weightedFiniteGap s c N =
      weightedFiniteJ3 s c N := by
  classical
  have hcross_jg : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      (c i * J (N i)) * ((c j * c j) * Gap (N j)) = 0 := by
    intro i hi j hj hij
    rcases h_cross i hi j hj hij with ⟨hijN, hjiN, hiStarJ, hStarI_J⟩
    have hcGap : (c j * c j) * Gap (N j) =
        Gap (N j) * (c j * c j) :=
      (comm_sq_of_comm (c j) (Gap (N j))
        (comm_weight_Gap (c j) (N j) (h_comm j hj) (h_comm_star j hj)))
    exact weighted_cross_zero (c i) (J (N i)) (c j * c j) (Gap (N j))
      (J_mul_Gap_orthog (N i) (N j) (h_nil j hj)
        hijN hjiN hiStarJ hStarI_J) hcGap
  rw [weightedFiniteJ, weightedFiniteGap,
    sum_mul_sum_of_pairwise_cross_zero s
      (fun i => c i * J (N i)) (fun i => (c i * c i) * Gap (N i)) hcross_jg,
    weightedFiniteJ3]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_sq_weight_right (c i) (J (N i)) (Gap (N i))
      (comm_weight_J (c i) (N i) (h_comm i hi) (h_comm_star i hi)),
    J_mul_Gap (N i) (h_nil i hi) (h_reg i hi)]

/-- The square of the finite weighted rotor is the negative weighted gap. -/
theorem weighted_finite_J_sq_eq_neg_gap
    (s : Finset ι) (c N : ι → B)
    (h_nil : ∀ i ∈ s, N i * N i = 0)
    (h_reg : ∀ i ∈ s, N i * star (N i) * N i = N i)
    (h_comm : ∀ i ∈ s, c i * N i = N i * c i)
    (h_comm_star : ∀ i ∈ s, c i * star (N i) = star (N i) * c i)
    (h_cross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      N i * N j = 0 ∧ N j * N i = 0 ∧
      N i * star (N j) = 0 ∧ star (N i) * N j = 0) :
    weightedFiniteJ s c N * weightedFiniteJ s c N =
      -weightedFiniteGap s c N := by
  classical
  have hcross_jj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      (c i * J (N i)) * (c j * J (N j)) = 0 := by
    intro i hi j hj hij
    rcases h_cross i hi j hj hij with ⟨hijN, hjiN, hiStarJ, hStarI_J⟩
    exact weighted_cross_zero (c i) (J (N i)) (c j) (J (N j))
      (J_mul_J_orthog (N i) (N j) hijN hjiN hiStarJ hStarI_J)
      (comm_weight_J (c j) (N j) (h_comm j hj) (h_comm_star j hj))
  rw [weightedFiniteJ,
    sum_sq_of_pairwise_mul_zero s (fun i => c i * J (N i)) hcross_jj,
    weightedFiniteGap]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [weight_mul_weight (c i) (J (N i)) (J (N i))
      (comm_weight_J (c i) (N i) (h_comm i hi) (h_comm_star i hi)),
    J_sq_eq_neg_Gap (N i) (h_nil i hi) (h_reg i hi), mul_neg]

/-- Self-adjoint-weight interface for the finite weighted rotor/block
product. Only each weight's commutation with its own nilpotent is assumed. -/
theorem weighted_finite_J_mul_Phi_eq_sigma_of_self_adjoint_weights
    (s : Finset ι) (c N : ι → B)
    (h_nil : ∀ i ∈ s, N i * N i = 0)
    (h_selfadjoint : ∀ i ∈ s, star (c i) = c i)
    (h_comm : ∀ i ∈ s, c i * N i = N i * c i)
    (h_cross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      N i * N j = 0 ∧ N j * N i = 0 ∧
      N i * star (N j) = 0 ∧ star (N i) * N j = 0) :
    weightedFiniteJ s c N * weightedFinitePhi s c N =
      weightedFiniteSigma s c N := by
  exact weighted_finite_J_mul_Phi_eq_sigma s c N h_nil h_comm
    (self_adjoint_weights_commute_with_channel_adjoints s c N
      h_selfadjoint h_comm) h_cross

/-- Self-adjoint-weight interface for the reversed weighted block/rotor
product, with only channel-local weight commutation. -/
theorem weighted_finite_Phi_mul_J_eq_neg_sigma_of_self_adjoint_weights
    (s : Finset ι) (c N : ι → B)
    (h_nil : ∀ i ∈ s, N i * N i = 0)
    (h_selfadjoint : ∀ i ∈ s, star (c i) = c i)
    (h_comm : ∀ i ∈ s, c i * N i = N i * c i)
    (h_cross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      N i * N j = 0 ∧ N j * N i = 0 ∧
      N i * star (N j) = 0 ∧ star (N i) * N j = 0) :
    weightedFinitePhi s c N * weightedFiniteJ s c N =
      -weightedFiniteSigma s c N := by
  exact weighted_finite_Phi_mul_J_eq_neg_sigma s c N h_nil h_comm
    (self_adjoint_weights_commute_with_channel_adjoints s c N
      h_selfadjoint h_comm) h_cross

/-- Self-adjoint-weight interface for the negative weighted rotor square;
weight commutation is required only within each channel. -/
theorem weighted_finite_J_sq_eq_neg_gap_of_self_adjoint_weights
    (s : Finset ι) (c N : ι → B)
    (h_nil : ∀ i ∈ s, N i * N i = 0)
    (h_reg : ∀ i ∈ s, N i * star (N i) * N i = N i)
    (h_selfadjoint : ∀ i ∈ s, star (c i) = c i)
    (h_comm : ∀ i ∈ s, c i * N i = N i * c i)
    (h_cross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      N i * N j = 0 ∧ N j * N i = 0 ∧
      N i * star (N j) = 0 ∧ star (N i) * N j = 0) :
    weightedFiniteJ s c N * weightedFiniteJ s c N =
      -weightedFiniteGap s c N := by
  exact weighted_finite_J_sq_eq_neg_gap s c N h_nil h_reg h_comm
    (self_adjoint_weights_commute_with_channel_adjoints s c N
      h_selfadjoint h_comm) h_cross

/-- The finite weighted gap sends the finite weighted block to its cubic block. -/
theorem weighted_finite_gap_mul_Phi_eq_Phi3
    (s : Finset ι) (c N : ι → B)
    (h_nil : ∀ i ∈ s, N i * N i = 0)
    (h_reg : ∀ i ∈ s, N i * star (N i) * N i = N i)
    (h_comm : ∀ i ∈ s, c i * N i = N i * c i)
    (h_comm_star : ∀ i ∈ s, c i * star (N i) = star (N i) * c i)
    (h_cross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      N i * N j = 0 ∧ N j * N i = 0 ∧
      N i * star (N j) = 0 ∧ star (N i) * N j = 0) :
    weightedFiniteGap s c N * weightedFinitePhi s c N =
      weightedFinitePhi3 s c N := by
  classical
  have hcross_gp : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ((c i * c i) * Gap (N i)) * (c j * Phi (N j)) = 0 := by
    intro i hi j hj hij
    rcases h_cross i hi j hj hij with ⟨hijN, hjiN, hiStarJ, hStarI_J⟩
    exact weighted_cross_zero (c i * c i) (Gap (N i)) (c j) (Phi (N j))
      (Gap_mul_Phi_orthog (N i) (N j) (h_nil i hi)
        hijN hjiN hiStarJ hStarI_J)
      (comm_weight_Phi (c j) (N j) (h_comm j hj) (h_comm_star j hj))
  rw [weightedFiniteGap, weightedFinitePhi,
    sum_mul_sum_of_pairwise_cross_zero s
      (fun i => (c i * c i) * Gap (N i)) (fun i => c i * Phi (N i)) hcross_gp,
    weightedFinitePhi3]
  apply Finset.sum_congr rfl
  intro i hi
  rw [sq_weight_mul_right (c i) (Gap (N i)) (Phi (N i))
      (comm_weight_Gap (c i) (N i) (h_comm i hi) (h_comm_star i hi)),
    Gap_mul_Phi (N i) (h_nil i hi) (h_reg i hi)]

/-- Multiplication in the reverse order also gives the cubic weighted block. -/
theorem weighted_finite_Phi_mul_gap_eq_Phi3
    (s : Finset ι) (c N : ι → B)
    (h_nil : ∀ i ∈ s, N i * N i = 0)
    (h_reg : ∀ i ∈ s, N i * star (N i) * N i = N i)
    (h_comm : ∀ i ∈ s, c i * N i = N i * c i)
    (h_comm_star : ∀ i ∈ s, c i * star (N i) = star (N i) * c i)
    (h_cross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      N i * N j = 0 ∧ N j * N i = 0 ∧
      N i * star (N j) = 0 ∧ star (N i) * N j = 0) :
    weightedFinitePhi s c N * weightedFiniteGap s c N =
      weightedFinitePhi3 s c N := by
  classical
  have hcross_pg : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      (c i * Phi (N i)) * ((c j * c j) * Gap (N j)) = 0 := by
    intro i hi j hj hij
    rcases h_cross i hi j hj hij with ⟨hijN, hjiN, hiStarJ, hStarI_J⟩
    have hcGap : (c j * c j) * Gap (N j) =
        Gap (N j) * (c j * c j) :=
      comm_sq_of_comm (c j) (Gap (N j))
        (comm_weight_Gap (c j) (N j) (h_comm j hj) (h_comm_star j hj))
    exact weighted_cross_zero (c i) (Phi (N i)) (c j * c j) (Gap (N j))
      (Phi_mul_Gap_orthog (N i) (N j) (h_nil j hj)
        hijN hjiN hiStarJ hStarI_J) hcGap
  rw [weightedFinitePhi, weightedFiniteGap,
    sum_mul_sum_of_pairwise_cross_zero s
      (fun i => c i * Phi (N i)) (fun i => (c i * c i) * Gap (N i)) hcross_pg,
    weightedFinitePhi3]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_sq_weight_right (c i) (Phi (N i)) (Gap (N i))
      (comm_weight_Phi (c i) (N i) (h_comm i hi) (h_comm_star i hi)),
    Phi_mul_Gap (N i) (h_nil i hi) (h_reg i hi)]

/-- The finite weighted multi-channel Jordan associator scales cubically with
the channel weights. -/
theorem weighted_finite_JordanAssoc_Phi_Phi_J
    (s : Finset ι) (c N : ι → B)
    (h_nil : ∀ i ∈ s, N i * N i = 0)
    (h_reg : ∀ i ∈ s, N i * star (N i) * N i = N i)
    (h_comm : ∀ i ∈ s, c i * N i = N i * c i)
    (h_comm_star : ∀ i ∈ s, c i * star (N i) = star (N i) * c i)
    (h_cross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      N i * N j = 0 ∧ N j * N i = 0 ∧
      N i * star (N j) = 0 ∧ star (N i) * N j = 0) :
    JordanAssoc (weightedFinitePhi s c N) (weightedFinitePhi s c N)
        (weightedFiniteJ s c N) = quad (weightedFiniteJ3 s c N) := by
  exact jordanAssoc_eq_quad_of_block_products
    (weightedFinitePhi s c N) (weightedFiniteJ s c N)
    (weightedFiniteGap s c N) (weightedFiniteSigma s c N)
    (weightedFiniteJ3 s c N)
    (weighted_finite_block_sq_eq_gap_sum s c N h_nil h_reg h_comm h_comm_star h_cross)
    (weighted_finite_J_mul_Phi_eq_sigma s c N h_nil h_comm h_comm_star h_cross)
    (weighted_finite_Phi_mul_J_eq_neg_sigma s c N h_nil h_comm h_comm_star h_cross)
    (weighted_finite_gap_mul_J_eq_J3 s c N h_nil h_reg h_comm h_comm_star h_cross)
    (weighted_finite_J_mul_gap_eq_J3 s c N h_nil h_reg h_comm h_comm_star h_cross)

/-- The finite weighted cubic rotor is also the double-commutator curvature
of the weighted block and rotor. This connects the finite channel expansion
to the repository's associative Jordan-associator identity. -/
theorem weighted_finite_curvature_double_commutator
    (s : Finset ι) (c N : ι → B)
    (h_nil : ∀ i ∈ s, N i * N i = 0)
    (h_reg : ∀ i ∈ s, N i * star (N i) * N i = N i)
    (h_comm : ∀ i ∈ s, c i * N i = N i * c i)
    (h_comm_star : ∀ i ∈ s, c i * star (N i) = star (N i) * c i)
    (h_cross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      N i * N j = 0 ∧ N j * N i = 0 ∧
      N i * star (N j) = 0 ∧ star (N i) * N j = 0) :
    WeightedMultiChannelJordanAnomalyPoset.comm
        (WeightedMultiChannelJordanAnomalyPoset.comm
          (weightedFiniteJ s c N) (weightedFinitePhi s c N))
        (weightedFinitePhi s c N) = quad (weightedFiniteJ3 s c N) := by
  have hcomm (A J : B) :
      WeightedMultiChannelJordanAnomalyPoset.comm
          (WeightedMultiChannelJordanAnomalyPoset.comm J A) A =
        WeightedMultiChannelJordanAnomalyPoset.comm A
          (WeightedMultiChannelJordanAnomalyPoset.comm A J) := by
    dsimp [WeightedMultiChannelJordanAnomalyPoset.comm]
    noncomm_ring
  calc
    WeightedMultiChannelJordanAnomalyPoset.comm
        (WeightedMultiChannelJordanAnomalyPoset.comm
          (weightedFiniteJ s c N) (weightedFinitePhi s c N))
        (weightedFinitePhi s c N)
      = WeightedMultiChannelJordanAnomalyPoset.comm
          (weightedFinitePhi s c N)
          (WeightedMultiChannelJordanAnomalyPoset.comm
            (weightedFinitePhi s c N) (weightedFiniteJ s c N)) :=
            hcomm _ _
    _ = JordanAssoc (weightedFinitePhi s c N) (weightedFinitePhi s c N)
          (weightedFiniteJ s c N) := by
            symm
            exact InfoGeometry.Core.JordanAssociator.symm_associator_eq_double_commutator
              (weightedFinitePhi s c N) (weightedFinitePhi s c N)
              (weightedFiniteJ s c N)
    _ = quad (weightedFiniteJ3 s c N) :=
          weighted_finite_JordanAssoc_Phi_Phi_J s c N
            h_nil h_reg h_comm h_comm_star h_cross

/-- The finite weighted channel family satisfies the complete quartet of
Grade-3 chiral Jordan associator identities. -/
theorem weighted_finite_JordanAssoc_chiral_quartet
    (s : Finset ι) (c N : ι → B)
    (h_nil : ∀ i ∈ s, N i * N i = 0)
    (h_reg : ∀ i ∈ s, N i * star (N i) * N i = N i)
    (h_comm : ∀ i ∈ s, c i * N i = N i * c i)
    (h_comm_star : ∀ i ∈ s, c i * star (N i) = star (N i) * c i)
    (h_cross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      N i * N j = 0 ∧ N j * N i = 0 ∧
      N i * star (N j) = 0 ∧ star (N i) * N j = 0) :
    JordanAssoc (weightedFinitePhi s c N) (weightedFinitePhi s c N)
        (weightedFiniteJ s c N) = quad (weightedFiniteJ3 s c N) ∧
    JordanAssoc (weightedFiniteJ s c N) (weightedFinitePhi s c N)
        (weightedFinitePhi s c N) = -quad (weightedFiniteJ3 s c N) ∧
    JordanAssoc (weightedFiniteJ s c N) (weightedFiniteJ s c N)
        (weightedFinitePhi s c N) = -quad (weightedFinitePhi3 s c N) ∧
    JordanAssoc (weightedFinitePhi s c N) (weightedFiniteJ s c N)
        (weightedFiniteJ s c N) = quad (weightedFinitePhi3 s c N) := by
  exact jordanAssoc_four_chiral_placements
    (weightedFinitePhi s c N) (weightedFiniteJ s c N)
    (weightedFiniteGap s c N) (weightedFiniteSigma s c N) (weightedFiniteJ3 s c N)
    (weightedFinitePhi3 s c N)
    (weighted_finite_block_sq_eq_gap_sum s c N h_nil h_reg h_comm h_comm_star h_cross)
    (weighted_finite_J_sq_eq_neg_gap s c N h_nil h_reg h_comm h_comm_star h_cross)
    (weighted_finite_J_mul_Phi_eq_sigma s c N h_nil h_comm h_comm_star h_cross)
    (weighted_finite_Phi_mul_J_eq_neg_sigma s c N h_nil h_comm h_comm_star h_cross)
    (weighted_finite_gap_mul_J_eq_J3 s c N h_nil h_reg h_comm h_comm_star h_cross)
    (weighted_finite_J_mul_gap_eq_J3 s c N h_nil h_reg h_comm h_comm_star h_cross)
    (weighted_finite_gap_mul_Phi_eq_Phi3 s c N h_nil h_reg h_comm h_comm_star h_cross)
    (weighted_finite_Phi_mul_gap_eq_Phi3 s c N h_nil h_reg h_comm h_comm_star h_cross)

/-- Self-adjoint-weight interface for the complete finite chiral Jordan
associator quartet. Each weight commutes only with its own channel generator;
self-adjointness supplies commutation with the adjoint generator. -/
theorem weighted_finite_JordanAssoc_chiral_quartet_of_self_adjoint_weights
    (s : Finset ι) (c N : ι → B)
    (h_nil : ∀ i ∈ s, N i * N i = 0)
    (h_reg : ∀ i ∈ s, N i * star (N i) * N i = N i)
    (h_selfadjoint : ∀ i ∈ s, star (c i) = c i)
    (h_comm : ∀ i ∈ s, c i * N i = N i * c i)
    (h_cross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      N i * N j = 0 ∧ N j * N i = 0 ∧
      N i * star (N j) = 0 ∧ star (N i) * N j = 0) :
    JordanAssoc (weightedFinitePhi s c N) (weightedFinitePhi s c N)
        (weightedFiniteJ s c N) = quad (weightedFiniteJ3 s c N) ∧
    JordanAssoc (weightedFiniteJ s c N) (weightedFinitePhi s c N)
        (weightedFinitePhi s c N) = -quad (weightedFiniteJ3 s c N) ∧
    JordanAssoc (weightedFiniteJ s c N) (weightedFiniteJ s c N)
        (weightedFinitePhi s c N) = -quad (weightedFinitePhi3 s c N) ∧
    JordanAssoc (weightedFinitePhi s c N) (weightedFiniteJ s c N)
        (weightedFiniteJ s c N) = quad (weightedFinitePhi3 s c N) := by
  exact weighted_finite_JordanAssoc_chiral_quartet s c N h_nil h_reg h_comm
    (self_adjoint_weights_commute_with_channel_adjoints s c N
      h_selfadjoint h_comm) h_cross

/-- If every finite-channel weight is a sixth-cyclotomic root, its cube is
`-1` and the weighted cubic Jordan anomaly synchronizes to the unweighted
channel sum. -/
theorem cyclotomic_weighted_finite_JordanAssoc_singlet
    (s : Finset ι) (c N : ι → B)
    (h_cyc : ∀ i ∈ s, Phi6 (c i) = 0)
    (h_nil : ∀ i ∈ s, N i * N i = 0)
    (h_reg : ∀ i ∈ s, N i * star (N i) * N i = N i)
    (h_comm : ∀ i ∈ s, c i * N i = N i * c i)
    (h_comm_star : ∀ i ∈ s, c i * star (N i) = star (N i) * c i)
    (h_cross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      N i * N j = 0 ∧ N j * N i = 0 ∧
      N i * star (N j) = 0 ∧ star (N i) * N j = 0) :
    JordanAssoc (weightedFinitePhi s c N) (weightedFinitePhi s c N)
        (weightedFiniteJ s c N) = -quad (∑ i ∈ s, J (N i)) := by
  rw [weighted_finite_JordanAssoc_Phi_Phi_J s c N
    h_nil h_reg h_comm h_comm_star h_cross]
  have hJ3 : weightedFiniteJ3 s c N = -(∑ i ∈ s, J (N i)) := by
    unfold weightedFiniteJ3
    calc ∑ i ∈ s, cube (c i) * J (N i)
        = ∑ i ∈ s, -(J (N i)) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [cube_eq_neg_one_of_Phi6 (c i) (h_cyc i hi), neg_mul, one_mul]
      _ = -(∑ i ∈ s, J (N i)) := by rw [← Finset.sum_neg_distrib]
  rw [hJ3, quad_neg]

end InfoGeometry.OperatorAlgebra.PeirceSpine
