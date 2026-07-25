import Mathlib.Tactic
import InfoGeometry.Canonical.BosonizationConstructiveCurrent
import InfoGeometry.Canonical.SplitCliffordWickCAR

/-!
# InfoGeometry.Canonical.SplitCliffordCurrentCommutator

Finite split-current commutator expansion and noncentral telescoping
in the native owner surface.

This file adds no wrapper structures.  It restates two concrete finite
commutator lemmas using the existing `RawCARModeCompletion`/matrix-unit API.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitCliffordCurrentCommutator

open scoped BigOperators
open InfoGeometry.Canonical.BosonizationConstructiveCurrent
open InfoGeometry.Canonical.SplitCliffordWickCAR

namespace RawCARModeCompletion

variable {A : Type*} [Ring A]
variable (C : RawCARModeCompletion A)

/--
Finite-window represented current commutator expansion from the Wick matrix-unit
theorem.
-/
theorem current_cutoff_commutator_expansion
    (N M : Nat) (m n : Int) :
    comm
        (∑ k ∈ integerWindow N, C.matrixUnit k (k + m))
        (∑ l ∈ integerWindow M, C.matrixUnit l (l + n))
      =
      ∑ k ∈ integerWindow N,
        ∑ l ∈ integerWindow M,
          ((if k + m = l then C.matrixUnit k (l + n) else 0)
            -
            (if k = l + n then C.matrixUnit l (k + m) else 0)
            +
            (if k + m = l ∧ k = l + n then
              (occ k - occ (k + m)) • C.central
            else
              0)) :=
  representedCutoffCurrent_commutator_expand_from_rawCAR C N M m n

/--
The noncentral finite-cutoff double-sum term is exactly its reindexed
telescoping boundary expression.
-/
theorem current_noncentral_telescope
    (N : Nat) (m n : Int) :
    C.cutoffBulkBoundaryTerm N m n =
      C.cutoffReindexedBulkBoundaryTerm N m n :=
  RawCARModeCompletion.cutoffBulkBoundaryTerm_eq_reindexedBulkBoundaryTerm C N m n

/--
Finite cutoff-current commutator equals boundary plus the Heisenberg central
term once the cutoff window contains the full crossing strip.
-/
theorem current_cutoff_commutator_eq_boundary_add_heisenberg_of_natAbs_le
    (N : Nat) (m n : Int) (hN : m.natAbs ≤ N) :
    comm (C.cutoffCurrent N m) (C.cutoffCurrent N n) =
      C.cutoffBoundaryTerm N m n +
        (if m + n = 0 then m • C.central else 0) :=
  RawCARModeCompletion.cutoffCurrent_commutator_eq_boundary_add_heisenberg_of_natAbs_le
    C N m n hN

/--
Downstream-ready finite-cutoff current commutator interface:

`[J_m^(N), J_n^(N)] = boundary + (if m+n=0 then m•K else 0)`.

Here `K` is the raw CAR central carrier `C.central`, and the cutoff is assumed
large enough to contain the full crossing strip for mode `m` (`|m| ≤ N`).
-/
theorem finite_cutoff_commutator_interface
    (N : Nat) (m n : Int) (hN : m.natAbs ≤ N) :
    comm (C.cutoffCurrent N m) (C.cutoffCurrent N n) =
      C.cutoffBoundaryTerm N m n +
        (if m + n = 0 then m • C.central else 0) :=
  current_cutoff_commutator_eq_boundary_add_heisenberg_of_natAbs_le C N m n hN

/--
If `m + n ≠ 0`, the finite cutoff-current commutator is purely the cutoff
boundary term.
-/
theorem current_cutoff_commutator_eq_boundary_of_noncentral
    (N : Nat) (m n : Int) (hmn : m + n ≠ 0) :
    comm (C.cutoffCurrent N m) (C.cutoffCurrent N n) =
      C.cutoffBoundaryTerm N m n := by
  rw [RawCARModeCompletion.cutoffCurrent_commutator_eq_boundary_add_windowCrossing C N m n]
  unfold RawCARModeCompletion.cutoffWindowCrossingTerm
  simp [hmn]

/--
If all shifted labels have matched cutoff membership, the noncentral cutoff
boundary vanishes.
-/
theorem current_cutoff_boundary_eq_zero_of_matched_window
    (N : Nat) (m n : Int)
    (hmatch :
      ∀ a : Int, a ∈ cutoffWindow N →
        ((a + m ∈ cutoffWindow N) ↔ (a + n ∈ cutoffWindow N)))
    (hmn : m + n ≠ 0) :
    C.cutoffBoundaryTerm N m n = 0 := by
  have hbulk0 : C.cutoffBulkBoundaryTerm N m n = 0 := by
    rw [RawCARModeCompletion.cutoffBulkBoundaryTerm_eq_reindexedBulkBoundaryTerm C N m n]
    unfold RawCARModeCompletion.cutoffReindexedBulkBoundaryTerm
    apply Finset.sum_eq_zero
    intro a ha
    exact RawCARModeCompletion.cutoffBulkBoundaryDiagonalTerm_eq_zero_of_same_shift_membership
      C N m n a (hmatch a ha)
  have hActual0 : C.cutoffActualCentralTerm N m n = 0 := by
    unfold RawCARModeCompletion.cutoffActualCentralTerm
    apply Finset.sum_eq_zero
    intro a ha
    apply Finset.sum_eq_zero
    intro b hb
    have hcontra : ¬ (a + m = b ∧ a = b + n) := by
      intro hab
      rcases hab with ⟨h1, h2⟩
      have hm0 : m + n = 0 := by
        omega
      exact hmn hm0
    simp [hcontra]
  have hCross0 : C.cutoffWindowCrossingTerm N m n = 0 := by
    unfold RawCARModeCompletion.cutoffWindowCrossingTerm
    simp [hmn]
  unfold RawCARModeCompletion.cutoffBoundaryTerm
  simp [hbulk0, hActual0, hCross0]

/--
Matched cutoff membership implies vanishing of the noncentral bulk boundary
term, independent of whether `m + n` is zero.
-/
theorem current_cutoff_bulk_boundary_eq_zero_of_matched_window
    (N : Nat) (m n : Int)
    (hmatch :
      ∀ a : Int, a ∈ cutoffWindow N →
        ((a + m ∈ cutoffWindow N) ↔ (a + n ∈ cutoffWindow N))) :
    C.cutoffBulkBoundaryTerm N m n = 0 := by
  rw [RawCARModeCompletion.cutoffBulkBoundaryTerm_eq_reindexedBulkBoundaryTerm C N m n]
  unfold RawCARModeCompletion.cutoffReindexedBulkBoundaryTerm
  apply Finset.sum_eq_zero
  intro a ha
  exact RawCARModeCompletion.cutoffBulkBoundaryDiagonalTerm_eq_zero_of_same_shift_membership
    C N m n a (hmatch a ha)

/--
Interior noncentral cancellation at finite cutoff: if `m + n ≠ 0` and the two
window shifts have matched membership across the cutoff window, then the finite
cutoff-current commutator vanishes.
-/
theorem current_cutoff_commutator_eq_zero_of_noncentral_matched_window
    (N : Nat) (m n : Int)
    (hmatch :
      ∀ a : Int, a ∈ cutoffWindow N →
        ((a + m ∈ cutoffWindow N) ↔ (a + n ∈ cutoffWindow N)))
    (hmn : m + n ≠ 0) :
    comm (C.cutoffCurrent N m) (C.cutoffCurrent N n) = 0 := by
  rw [current_cutoff_commutator_eq_boundary_of_noncentral C N m n hmn]
  exact current_cutoff_boundary_eq_zero_of_matched_window C N m n hmatch hmn

/--
Central branch at finite cutoff: if `|m| ≤ N` and the cutoff boundary term
vanishes at `(m, -m)`, then the commutator is exactly the Heisenberg central
term `m • central`.
-/
theorem current_cutoff_commutator_eq_heisenberg_of_central_boundary_zero
    (N : Nat) (m : Int) (hN : m.natAbs ≤ N)
    (hbdry : C.cutoffBoundaryTerm N m (-m) = 0) :
    comm (C.cutoffCurrent N m) (C.cutoffCurrent N (-m)) = m • C.central := by
  rw [current_cutoff_commutator_eq_boundary_add_heisenberg_of_natAbs_le C N m (-m) hN]
  simp [hbdry]

/--
Central branch closure with explicit decomposition: if the noncentral bulk
boundary and the finite central edge correction both vanish at `(m,-m)`, then
the finite cutoff commutator is exactly `m • central`.
-/
theorem current_cutoff_commutator_eq_heisenberg_of_central_bulk_and_edge_zero
    (N : Nat) (m : Int) (hN : m.natAbs ≤ N)
    (hbulk : C.cutoffBulkBoundaryTerm N m (-m) = 0)
    (hedge :
      C.cutoffActualCentralTerm N m (-m) - C.cutoffWindowCrossingTerm N m (-m) = 0) :
    comm (C.cutoffCurrent N m) (C.cutoffCurrent N (-m)) = m • C.central := by
  apply current_cutoff_commutator_eq_heisenberg_of_central_boundary_zero C N m hN
  unfold RawCARModeCompletion.cutoffBoundaryTerm
  simp [hbulk, hedge]

/--
Central closure from explicit matched-window plus edge-correction hypotheses.

This is the direct represented-current closure shape at finite cutoff:
if `(m,-m)` has no noncentral bulk boundary (proved from matched membership),
and the finite central edge correction vanishes, then
`[J_m^(N), J_{-m}^(N)] = m • central`.
-/
theorem current_cutoff_commutator_eq_heisenberg_of_central_matched_window_and_edge_zero
    (N : Nat) (m : Int) (hN : m.natAbs ≤ N)
    (hmatch :
      ∀ a : Int, a ∈ cutoffWindow N →
        ((a + m ∈ cutoffWindow N) ↔ (a - m ∈ cutoffWindow N)))
    (hedge :
      C.cutoffActualCentralTerm N m (-m) - C.cutoffWindowCrossingTerm N m (-m) = 0) :
    comm (C.cutoffCurrent N m) (C.cutoffCurrent N (-m)) = m • C.central := by
  apply current_cutoff_commutator_eq_heisenberg_of_central_bulk_and_edge_zero C N m hN
  · simpa [sub_eq_add_neg] using
      current_cutoff_bulk_boundary_eq_zero_of_matched_window C N m (-m) hmatch
  · exact hedge

/--
If every shifted label `a + m` stays inside the same cutoff window for
`a ∈ W_N`, then the finite central edge correction at `(m,-m)` vanishes.
-/
theorem current_central_edge_correction_eq_zero_of_full_shift_membership
    (N : Nat) (m : Int)
    (hfull : ∀ a : Int, a ∈ cutoffWindow N → a + m ∈ cutoffWindow N) :
    C.cutoffActualCentralTerm N m (-m) - C.cutoffWindowCrossingTerm N m (-m) = 0 := by
  have hActual :
      C.cutoffActualCentralTerm N m (-m) =
        ∑ a ∈ cutoffWindow N, (occ a - occ (a + m)) • C.central := by
    unfold RawCARModeCompletion.cutoffActualCentralTerm
    refine Finset.sum_congr rfl ?_
    intro a ha
    have hm : a + m ∈ cutoffWindow N := hfull a ha
    rw [Finset.sum_eq_single (a + m)]
    · have hEq : a = (a + m) + (-m) := by ring
      have hpos :
          (if a + m = a + m ∧ a = (a + m) + (-m)
            then (occ a - occ (a + m)) • C.central
            else 0) =
          (occ a - occ (a + m)) • C.central := by
        exact if_pos ⟨rfl, hEq⟩
      exact hpos
    · intro b hb hbne
      have hneq : ¬ (a + m = b ∧ a = b + (-m)) := by
        intro h
        exact hbne h.1.symm
      simp [hneq]
    · intro hnot
      exact (hnot hm).elim
  have hCross :
      C.cutoffWindowCrossingTerm N m (-m) =
        ∑ a ∈ cutoffWindow N, (occ a - occ (a + m)) • C.central := by
    unfold RawCARModeCompletion.cutoffWindowCrossingTerm
    simp
  rw [hActual, hCross]
  simp

/--
Weaker central edge-correction criterion.

If every missing-shift boundary index has balanced occupation
`occ a = occ (a + m)`, then the central edge correction at `(m,-m)` vanishes.
-/
theorem current_central_edge_correction_eq_zero_of_edge_occ_balance
    (N : Nat) (m : Int)
    (hedgeOcc :
      ∀ a : Int, a ∈ cutoffWindow N → a + m ∉ cutoffWindow N → occ a = occ (a + m)) :
    C.cutoffActualCentralTerm N m (-m) - C.cutoffWindowCrossingTerm N m (-m) = 0 := by
  have hActual :
      C.cutoffActualCentralTerm N m (-m) =
        ∑ a ∈ cutoffWindow N,
          (if a + m ∈ cutoffWindow N then (occ a - occ (a + m)) • C.central else 0) := by
    unfold RawCARModeCompletion.cutoffActualCentralTerm
    refine Finset.sum_congr rfl ?_
    intro a ha
    by_cases hm : a + m ∈ cutoffWindow N
    · rw [Finset.sum_eq_single (a + m)]
      · have hEq : a = (a + m) + (-m) := by ring
        have hconj : (a + m = a + m ∧ a = (a + m) + (-m)) := ⟨rfl, hEq⟩
        have hpos :
            (if a + m = a + m ∧ a = (a + m) + (-m)
              then (occ a - occ (a + m)) • C.central
              else 0) =
            (occ a - occ (a + m)) • C.central := if_pos hconj
        rw [if_pos hm]
        exact hpos
      · intro b hb hbne
        have hneq : ¬ (a + m = b ∧ a = b + (-m)) := by
          intro h
          exact hbne h.1.symm
        simp [hneq]
      · intro hnot
        exact (hnot hm).elim
    · have hzero :
        ∀ b : Int, b ∈ cutoffWindow N →
          (if a + m = b ∧ a = b + (-m) then (occ a - occ (a + m)) • C.central else 0) = 0 := by
        intro b hb
        have hneq : ¬ (a + m = b ∧ a = b + (-m)) := by
          intro h
          exact hm (h.1 ▸ hb)
        simp [hneq]
      have hsum0 :
          ∑ b ∈ cutoffWindow N,
            (if a + m = b ∧ a = b + (-m) then (occ a - occ (a + m)) • C.central else 0) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro b hb
        exact hzero b hb
      simpa [hm] using hsum0
  have hCross :
      C.cutoffWindowCrossingTerm N m (-m) =
        ∑ a ∈ cutoffWindow N, (occ a - occ (a + m)) • C.central := by
    unfold RawCARModeCompletion.cutoffWindowCrossingTerm
    simp
  rw [hActual, hCross]
  have hterm :
      ∀ a : Int, a ∈ cutoffWindow N →
        (if a + m ∈ cutoffWindow N then (occ a - occ (a + m)) • C.central else 0)
          - (occ a - occ (a + m)) • C.central = 0 := by
    intro a ha
    by_cases hm : a + m ∈ cutoffWindow N
    · simp [hm]
    · have hocc : occ a = occ (a + m) := hedgeOcc a ha hm
      simp [hm, hocc]
  calc
    (∑ a ∈ cutoffWindow N,
      (if a + m ∈ cutoffWindow N then (occ a - occ (a + m)) • C.central else 0))
      - ∑ a ∈ cutoffWindow N, (occ a - occ (a + m)) • C.central
        =
      ∑ a ∈ cutoffWindow N,
        ((if a + m ∈ cutoffWindow N then (occ a - occ (a + m)) • C.central else 0)
          - (occ a - occ (a + m)) • C.central) := by
          rw [Finset.sum_sub_distrib]
    _ = 0 := by
      refine Finset.sum_eq_zero ?_
      intro a ha
      exact hterm a ha

/--
The "full `+m` shift inclusion on `W_N`" hypothesis is rigid: it forces
`m = 0`.
-/
theorem full_shift_membership_forces_zero_mode
    (N : Nat) (m : Int)
    (hfull : ∀ a : Int, a ∈ cutoffWindow N → a + m ∈ cutoffWindow N) :
    m = 0 := by
  have hTopMem : (N : Int) ∈ cutoffWindow N := by
    simp [cutoffWindow]
  have hBotMem : (-(N : Int)) ∈ cutoffWindow N := by
    simp [cutoffWindow]
  have hTop := hfull (N : Int) hTopMem
  have hBot := hfull (-(N : Int)) hBotMem
  have hTopLe : (N : Int) + m ≤ (N : Int) := (Finset.mem_Icc.mp hTop).2
  have hBotLe : (-(N : Int)) ≤ (-(N : Int)) + m := (Finset.mem_Icc.mp hBot).1
  have hmle : m ≤ 0 := by linarith
  have hmge : 0 ≤ m := by linarith
  exact le_antisymm hmle hmge

/--
Concrete central closure with explicit sufficient conditions only:

* `|m| ≤ N`;
* matched cutoff-membership for shifts `+m` and `-m` (kills bulk boundary);
* full `+m` shift inclusion on `W_N` (kills central edge correction).
-/
theorem current_cutoff_commutator_eq_heisenberg_of_central_matched_and_full_shift
    (N : Nat) (m : Int) (hN : m.natAbs ≤ N)
    (hmatch :
      ∀ a : Int, a ∈ cutoffWindow N →
        ((a + m ∈ cutoffWindow N) ↔ (a - m ∈ cutoffWindow N)))
    (hfull : ∀ a : Int, a ∈ cutoffWindow N → a + m ∈ cutoffWindow N) :
    comm (C.cutoffCurrent N m) (C.cutoffCurrent N (-m)) = m • C.central := by
  apply current_cutoff_commutator_eq_heisenberg_of_central_matched_window_and_edge_zero
    C N m hN hmatch
  exact current_central_edge_correction_eq_zero_of_full_shift_membership C N m hfull

/--
Central branch closure from matched-window + edge-occupation balance.

This removes the strong full-shift hypothesis and uses only:

* `|m| ≤ N`;
* matched cutoff membership for shifts `+m` and `-m` (bulk boundary vanishes);
* occupation balance on missing-shift boundary indices (edge correction vanishes).
-/
theorem current_cutoff_commutator_eq_heisenberg_of_central_matched_and_edge_occ_balance
    (N : Nat) (m : Int) (hN : m.natAbs ≤ N)
    (hmatch :
      ∀ a : Int, a ∈ cutoffWindow N →
        ((a + m ∈ cutoffWindow N) ↔ (a - m ∈ cutoffWindow N)))
    (hedgeOcc :
      ∀ a : Int, a ∈ cutoffWindow N → a + m ∉ cutoffWindow N → occ a = occ (a + m)) :
    comm (C.cutoffCurrent N m) (C.cutoffCurrent N (-m)) = m • C.central := by
  apply current_cutoff_commutator_eq_heisenberg_of_central_matched_window_and_edge_zero
    C N m hN hmatch
  exact current_central_edge_correction_eq_zero_of_edge_occ_balance C N m hedgeOcc

/--
For the concrete integer polarization `occ` and symmetric cutoff window, the
edge-occupation balance hypothesis follows from `|m| ≤ N`.
-/
theorem edge_occ_balance_of_natAbs_le
    (N : Nat) (m : Int) (hN : m.natAbs ≤ N) :
    ∀ a : Int, a ∈ cutoffWindow N → a + m ∉ cutoffWindow N → occ a = occ (a + m) := by
  intro a ha hnot
  have haL : -(N : Int) ≤ a := (Finset.mem_Icc.mp ha).1
  have haU : a ≤ (N : Int) := (Finset.mem_Icc.mp ha).2
  have hmAbs : |m| ≤ (N : Int) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hN
  have hmL : -(N : Int) ≤ m := (abs_le.mp hmAbs).1
  have hmU : m ≤ (N : Int) := (abs_le.mp hmAbs).2
  have hOutside :
      a + m < -(N : Int) ∨ (N : Int) < a + m := by
    by_contra hIn
    have hGe : -(N : Int) ≤ a + m := by
      exact not_lt.mp (fun hlt => hIn (Or.inl hlt))
    have hLe : a + m ≤ (N : Int) := by
      exact not_lt.mp (fun hgt => hIn (Or.inr hgt))
    exact hnot (Finset.mem_Icc.mpr ⟨hGe, hLe⟩)
  rcases hOutside with hLow | hHigh
  · -- lower-edge escape; both occupied
    have hAmNeg : a + m < 0 := lt_of_lt_of_le hLow (neg_nonpos.mpr (Int.natCast_nonneg N))
    have hANeg : a < 0 := by
      by_contra hA0
      have ha0 : 0 ≤ a := le_of_not_gt hA0
      have ham0 : 0 ≤ a + m := by linarith
      exact (not_lt_of_ge ham0) hAmNeg
    simp [occ, hANeg, hAmNeg]
  · -- upper-edge escape; both unoccupied
    have hANonneg : 0 ≤ a := by
      have : (N : Int) - m ≤ a := by linarith
      have hNm : 0 ≤ (N : Int) - m := by linarith [hmU]
      exact le_trans hNm this
    have hAmNonneg : 0 ≤ a + m := by linarith
    have hANotNeg : ¬ a < 0 := not_lt.mpr hANonneg
    have hAmNotNeg : ¬ (a + m) < 0 := not_lt.mpr hAmNonneg
    simp [occ, hANotNeg, hAmNotNeg]

/--
Central branch closure from `|m| ≤ N` plus matched-window membership only.

The edge occupation balance is discharged automatically by the concrete
`occ`/window arithmetic.
-/
theorem current_cutoff_commutator_eq_heisenberg_of_central_matched_window_natAbs
    (N : Nat) (m : Int) (hN : m.natAbs ≤ N)
    (hmatch :
      ∀ a : Int, a ∈ cutoffWindow N →
        ((a + m ∈ cutoffWindow N) ↔ (a - m ∈ cutoffWindow N))) :
    comm (C.cutoffCurrent N m) (C.cutoffCurrent N (-m)) = m • C.central := by
  apply current_cutoff_commutator_eq_heisenberg_of_central_matched_and_edge_occ_balance
    C N m hN hmatch
  exact edge_occ_balance_of_natAbs_le N m hN

/--
Pointwise matched-window criterion.

If a label `a` in `W_N` satisfies `|a| + |m| ≤ N`, then both shifted labels
`a + m` and `a - m` lie in `W_N`, hence membership matches.
-/
theorem matched_window_at_of_natAbs_sum_le
    (N : Nat) (m a : Int)
    (_ha : a ∈ cutoffWindow N)
    (hmargin : a.natAbs + m.natAbs ≤ N) :
    ((a + m ∈ cutoffWindow N) ↔ (a - m ∈ cutoffWindow N)) := by
  have hPlusAbs : (a + m).natAbs ≤ N := by
    exact le_trans (Int.natAbs_add_le a m) hmargin
  have hMinusAbs : (a - m).natAbs ≤ N := by
    calc
      (a - m).natAbs = (a + (-m)).natAbs := by rw [sub_eq_add_neg]
      _ ≤ a.natAbs + (-m).natAbs := Int.natAbs_add_le a (-m)
      _ = a.natAbs + m.natAbs := by simp [Int.natAbs_neg]
      _ ≤ N := hmargin
  have hPlus : a + m ∈ cutoffWindow N :=
    mem_cutoffWindow_of_natAbs_le (a + m) N hPlusAbs
  have hMinus : a - m ∈ cutoffWindow N :=
    mem_cutoffWindow_of_natAbs_le (a - m) N hMinusAbs
  exact ⟨fun _ => hMinus, fun _ => hPlus⟩

/--
Uniform matched-window criterion in the exact shape required by the central
cutoff commutator closure theorem.
-/
theorem matched_window_of_uniform_natAbs_margin
    (N : Nat) (m : Int)
    (hmargin : ∀ a : Int, a ∈ cutoffWindow N → a.natAbs + m.natAbs ≤ N) :
    (∀ a : Int, a ∈ cutoffWindow N →
      ((a + m ∈ cutoffWindow N) ↔ (a - m ∈ cutoffWindow N))) := by
  intro a ha
  exact matched_window_at_of_natAbs_sum_le N m a ha (hmargin a ha)

/--
Central commutator closure from a single uniform cutoff-margin hypothesis.

If every `a ∈ W_N` satisfies `|a| + |m| ≤ N`, then the matched-window condition
holds automatically; together with `|m| ≤ N`, this yields the finite central
Heisenberg commutator.
-/
theorem current_cutoff_commutator_eq_heisenberg_of_central_uniform_margin
    (N : Nat) (m : Int)
    (hN : m.natAbs ≤ N)
    (hmargin : ∀ a : Int, a ∈ cutoffWindow N → a.natAbs + m.natAbs ≤ N) :
    comm (C.cutoffCurrent N m) (C.cutoffCurrent N (-m)) = m • C.central := by
  apply current_cutoff_commutator_eq_heisenberg_of_central_matched_window_natAbs C N m hN
  exact matched_window_of_uniform_natAbs_margin N m hmargin

/--
Concrete zero-mode finite commutator:

`[J_0^(N), J_0^(N)] = 0`.
-/
theorem current_cutoff_commutator_zero_mode
    (N : Nat) :
    comm (C.cutoffCurrent N 0) (C.cutoffCurrent N 0) = 0 := by
  have hN : (0 : Int).natAbs ≤ N := by simp
  have hmatch :
      ∀ a : Int, a ∈ cutoffWindow N →
        ((a + (0 : Int) ∈ cutoffWindow N) ↔ (a - (0 : Int) ∈ cutoffWindow N)) := by
    intro a ha
    simp
  have hfull :
      ∀ a : Int, a ∈ cutoffWindow N → a + (0 : Int) ∈ cutoffWindow N := by
    intro a ha
    simpa using ha
  have hcomm :
      comm (C.cutoffCurrent N 0) (C.cutoffCurrent N (-0)) = (0 : Int) • C.central :=
    current_cutoff_commutator_eq_heisenberg_of_central_matched_and_full_shift
      C N 0 hN hmatch hfull
  simpa using hcomm

end RawCARModeCompletion

end InfoGeometry.Canonical.SplitCliffordCurrentCommutator
