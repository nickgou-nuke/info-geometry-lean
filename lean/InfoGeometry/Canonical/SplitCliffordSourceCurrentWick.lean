import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic.NoncommRing
import InfoGeometry.Canonical.BosonizationConstructiveCurrent
import InfoGeometry.Canonical.CurrentSugawaraBridge
import InfoGeometry.Canonical.SplitCliffordFiniteCAR
import InfoGeometry.Canonical.SplitCliffordFiniteCurrentObstruction
import InfoGeometry.Canonical.SplitCliffordJordanWignerTwoModeCurrent
import InfoGeometry.Canonical.SplitCliffordSourceCurrent
import InfoGeometry.External.Virasoro.AffineKacMoody

/-!
# InfoGeometry.Canonical.SplitCliffordSourceCurrentWick

Wick/Schwinger commutator interface for split source currents.

This file records the endomorphism-valued commutator theorem required by the
Heisenberg bridge. Carrier-valued source currents must first be transported to
endomorphisms of the source vector space; only then does the commutator make
sense.

No closure is postulated here. The equation below remains a theorem debt for a
concrete transported current family.
-/

namespace SplitCliffordSourceCurrentWick

/--
Endomorphism-valued Wick/Schwinger commutator law.

This is the exact commutator equation required by the Heisenberg bridge.
Carrier-valued currents `V → Carrier` are intentionally not accepted here,
because their associative commutator is not defined without transport back to
`End(V)`.
-/
def SplitSourceEndWickLaw
    {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    (Jlift : Int → V →ₗ[𝕜] V) : Prop :=
  ∀ m n : Int,
    (Jlift m).commutator (Jlift n) =
      if m + n = 0 then (m : 𝕜) • (1 : V →ₗ[𝕜] V) else 0

/-- Backward-compatible name for the endomorphism-valued Wick law. -/
abbrev SplitSourceWickLaw := @SplitSourceEndWickLaw

/--
Off-diagonal Wick readout: if `m + n ≠ 0`, the commutator vanishes.
-/
theorem commutator_eq_zero_of_add_ne_zero
    {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    {Jlift : Int → V →ₗ[𝕜] V}
    (hWick : SplitSourceEndWickLaw Jlift)
    {m n : Int} (hmn : m + n ≠ 0) :
    (Jlift m).commutator (Jlift n) = 0 := by
  simpa [SplitSourceEndWickLaw, hmn] using hWick m n

/--
Diagonal Wick readout: if `m + n = 0`, the commutator is the central term.
-/
theorem commutator_eq_central_of_add_eq_zero
    {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    {Jlift : Int → V →ₗ[𝕜] V}
    (hWick : SplitSourceEndWickLaw Jlift)
    {m n : Int} (hmn : m + n = 0) :
    (Jlift m).commutator (Jlift n) = (m : 𝕜) • (1 : V →ₗ[𝕜] V) := by
  simpa [SplitSourceEndWickLaw, hmn] using hWick m n

/--
Honest raw-CAR corollary: the completed normal-ordered current bracket has the
Heisenberg central coefficient.
-/
theorem completed_current_commutator_from_rawCAR
    {A : Type*} [Ring A]
    (C : _root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.RawCARModeCompletion A)
    (m n : Int) :
    _root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.CCRBracketCompleted
        C
        (_root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.normalOrderedCurrent C m)
        (_root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.normalOrderedCurrent C n)
      =
      if m + n = 0 then
        m • _root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.completedCentral C
      else
        0 :=
  _root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.bosonization_constructive_heisenberg_current C m n

/--
Constructive cutoff-to-completed commutator limit exchange for
`normalOrderedCurrent`.

This is the explicit source-side infinite closure statement with no witness
packet: the completed current commutator is exactly the Heisenberg central term.
-/
theorem normalOrderedCurrent_commutator_limit_exchange
    {A : Type*} [Ring A]
    (C : _root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.RawCARModeCompletion A)
    (m n : Int) :
    _root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.CCRBracketCompleted
      C
      (_root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.normalOrderedCurrent C m)
      (_root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.normalOrderedCurrent C n)
      =
      if m + n = 0 then
        m • _root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.completedCentral C
      else
        0 := by
  simpa using completed_current_commutator_from_rawCAR C m n

/--
Honest represented current commutator from the existing charged Fock
representation owner surface.
-/
theorem represented_current_commutator_chargedFock
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    ∃ J :
        Int →
          VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
            VirasoroProject.ChargedFockSpace 𝕜 α,
      (∀ v, ∀ᶠ n : Int in Filter.atTop, J n v = 0) ∧
      (∀ m n : Int,
        (J m).commutator (J n) =
          if m + n = 0 then
            (m : 𝕜) •
              (1 :
                VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
                  VirasoroProject.ChargedFockSpace 𝕜 α)
          else
            0) := by
  let H :=
    _root_.InfoGeometry.Canonical.CurrentSugawaraBridge.chargedFockSpaceCurrentHeisenbergRep 𝕜 α
  exact ⟨H.J, H.trunc, H.comm⟩

/--
Constructive charged-Fock current closure with no existential witness packet.

This is the direct source-side theorem on the explicit current family.
-/
theorem representedChargedFockJ_constructive
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (∀ v, ∀ᶠ n : Int in Filter.atTop,
      (_root_.InfoGeometry.Canonical.CurrentSugawaraBridge.chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J n v = 0) ∧
      SplitSourceEndWickLaw
        ((_root_.InfoGeometry.Canonical.CurrentSugawaraBridge.chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J) := by
  let H :=
    _root_.InfoGeometry.Canonical.CurrentSugawaraBridge.chargedFockSpaceCurrentHeisenbergRep 𝕜 α
  exact ⟨H.trunc, H.comm⟩

/--
Concrete represented charged-Fock current family readout.

This removes an existential layer for downstream source-side packaging.
-/
noncomputable def representedChargedFockJ
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    Int →
      VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
        VirasoroProject.ChargedFockSpace 𝕜 α :=
  (_root_.InfoGeometry.Canonical.CurrentSugawaraBridge.chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J

/--
Concrete truncation theorem for `representedChargedFockJ`.
-/
theorem representedChargedFockJ_trunc
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    ∀ v, ∀ᶠ n : Int in Filter.atTop, representedChargedFockJ 𝕜 α n v = 0 :=
  (_root_.InfoGeometry.Canonical.CurrentSugawaraBridge.chargedFockSpaceCurrentHeisenbergRep 𝕜 α).trunc

/--
Concrete Wick/Heisenberg commutator theorem for `representedChargedFockJ`.
-/
theorem representedChargedFockJ_wick
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    SplitSourceEndWickLaw (representedChargedFockJ 𝕜 α) :=
  (_root_.InfoGeometry.Canonical.CurrentSugawaraBridge.chargedFockSpaceCurrentHeisenbergRep 𝕜 α).comm

/--
Full Heisenberg commutator law for the explicit represented charged-Fock
current family.

This is a direct theorem on `representedChargedFockJ` (no existential packet).
-/
theorem representedChargedFockJ_heisenberg_comm_full
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) (m n : Int) :
    (representedChargedFockJ 𝕜 α m).commutator
      (representedChargedFockJ 𝕜 α n)
      =
    (if m + n = 0 then (m : 𝕜) else 0) •
      (1 :
        VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
          VirasoroProject.ChargedFockSpace 𝕜 α) := by
  simpa [SplitSourceEndWickLaw] using representedChargedFockJ_wick (𝕜 := 𝕜) α m n

/--
Concrete central mode evaluation:
`[J₁, J_{-1}] = 1 • id`.
-/
theorem representedChargedFockJ_commutator_one_negOne
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (representedChargedFockJ 𝕜 α 1).commutator
        (representedChargedFockJ 𝕜 α (-1))
      =
    (1 : 𝕜) •
      (1 :
        VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
          VirasoroProject.ChargedFockSpace 𝕜 α) := by
  have h :=
    representedChargedFockJ_wick (𝕜 := 𝕜) α (m := 1) (n := -1)
  simpa using h

/--
Concrete off-diagonal mode evaluation:
`[J₁, J₀] = 0`.
-/
theorem representedChargedFockJ_commutator_one_zero
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (representedChargedFockJ 𝕜 α 1).commutator
        (representedChargedFockJ 𝕜 α 0)
      =
    (0 :
      VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
        VirasoroProject.ChargedFockSpace 𝕜 α) := by
  have h :=
    representedChargedFockJ_wick (𝕜 := 𝕜) α (m := 1) (n := 0)
  simpa using h

/--
Concrete central mode evaluation at the opposite orientation:
`[J_{-1}, J_1] = (-1) • id`.
-/
theorem representedChargedFockJ_commutator_negOne_one
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (representedChargedFockJ 𝕜 α (-1)).commutator
        (representedChargedFockJ 𝕜 α 1)
      =
    ((-1 : Int) : 𝕜) •
      (1 :
        VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
          VirasoroProject.ChargedFockSpace 𝕜 α) := by
  have h :=
    representedChargedFockJ_wick (𝕜 := 𝕜) α (m := -1) (n := 1)
  simpa using h

/--
Concrete central mode evaluation:
`[J₂, J_{-2}] = 2 • id`.
-/
theorem representedChargedFockJ_commutator_two_negTwo
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (representedChargedFockJ 𝕜 α 2).commutator
        (representedChargedFockJ 𝕜 α (-2))
      =
    (2 : 𝕜) •
      (1 :
        VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
          VirasoroProject.ChargedFockSpace 𝕜 α) := by
  have h :=
    representedChargedFockJ_wick (𝕜 := 𝕜) α (m := 2) (n := -2)
  simpa using h

/--
Concrete antisymmetry at the first central mode pair:
`[J₁, J_{-1}] = -[J_{-1}, J₁]`.
-/
theorem representedChargedFockJ_commutator_one_negOne_antisymm
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (representedChargedFockJ 𝕜 α 1).commutator
        (representedChargedFockJ 𝕜 α (-1))
      =
    -((representedChargedFockJ 𝕜 α (-1)).commutator
        (representedChargedFockJ 𝕜 α 1)) := by
  rw [representedChargedFockJ_commutator_one_negOne (𝕜 := 𝕜) α]
  rw [representedChargedFockJ_commutator_negOne_one (𝕜 := 𝕜) α]
  simp

/--
Concrete double-commutator vanishing at the first central mode:
`[J₁,[J₁,J_{-1}]] = 0`.
-/
theorem representedChargedFockJ_double_commutator_one_one_negOne
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (representedChargedFockJ 𝕜 α 1).commutator
      ((representedChargedFockJ 𝕜 α 1).commutator
        (representedChargedFockJ 𝕜 α (-1)))
      =
    (0 :
      VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
        VirasoroProject.ChargedFockSpace 𝕜 α) := by
  rw [representedChargedFockJ_commutator_one_negOne (𝕜 := 𝕜) α]
  simp [LinearMap.commutator]

/--
Concrete double-commutator vanishing at the opposite orientation:
`[J_{-1},[J_1,J_{-1}]] = 0`.
-/
theorem representedChargedFockJ_double_commutator_negOne_one_negOne
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (representedChargedFockJ 𝕜 α (-1)).commutator
      ((representedChargedFockJ 𝕜 α 1).commutator
        (representedChargedFockJ 𝕜 α (-1)))
      =
    (0 :
      VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
        VirasoroProject.ChargedFockSpace 𝕜 α) := by
  rw [representedChargedFockJ_commutator_one_negOne (𝕜 := 𝕜) α]
  simp [LinearMap.commutator]

/--
Structural mode-zero commutation:
`[J₀, Jₙ] = 0` for all `n`.
-/
theorem representedChargedFockJ_commutator_zero_any
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) (n : Int) :
    (representedChargedFockJ 𝕜 α 0).commutator
        (representedChargedFockJ 𝕜 α n)
      =
    (0 :
      VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
        VirasoroProject.ChargedFockSpace 𝕜 α) := by
  have h :=
    representedChargedFockJ_wick (𝕜 := 𝕜) α (m := 0) (n := n)
  by_cases hn : n = 0
  · subst hn
    simpa using h
  · have hsum : (0 : Int) + n ≠ 0 := by simpa [zero_add] using hn
    simpa [hsum] using h

/--
Finite-support (finite-window) commutator expansion readout from the raw-CAR
owner theorem surface.
-/
theorem finiteSupport_cutoffCurrent_commutator_expand_from_rawCAR
    {A : Type*} [Ring A]
    (C : _root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.RawCARModeCompletion A)
    (N M : Nat) (m n : Int) :
    _root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.comm
        (∑ k ∈ _root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.integerWindow N,
          C.matrixUnit k (k + m))
        (∑ l ∈ _root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.integerWindow M,
          C.matrixUnit l (l + n))
      =
      ∑ k ∈ _root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.integerWindow N,
        ∑ l ∈ _root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.integerWindow M,
          ((if k + m = l then C.matrixUnit k (l + n) else 0)
            -
            (if k = l + n then C.matrixUnit l (k + m) else 0)
            +
            (if k + m = l ∧ k = l + n then
              (_root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.occ k
                - _root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.occ (k + m)) •
                C.central
            else
              0)) := by
  simpa using
    _root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.representedCutoffCurrent_commutator_expand_from_rawCAR
      C N M m n

/-! ## Concrete source-side `J/trunc/comm` from finite CAR data -/

open InfoGeometry.Canonical.SplitCliffordTwoModeCAR

/-- Concrete source-side current family from finite Jordan-Wigner CAR data. -/
def sourceJfin (n : Int) : M4R :=
  if n = 1 then a1Dag * a2 else if n = -1 then a2Dag * a1 else 0

/--
`sourceJfin` is exactly the indexed finite current family from
`SplitCliffordFiniteCAR`.
-/
theorem sourceJfin_eq_JfinIndexed (n : Int) :
    sourceJfin n = InfoGeometry.Canonical.SplitCliffordFiniteCAR.JfinIndexed n := by
  simp [sourceJfin, InfoGeometry.Canonical.SplitCliffordFiniteCAR.JfinIndexed,
    InfoGeometry.Canonical.SplitCliffordFiniteCAR.aMode,
    InfoGeometry.Canonical.SplitCliffordFiniteCAR.adagMode]

/-- Concrete truncation of `sourceJfin` on vectors. -/
theorem sourceJfin_trunc_vector (v : Fin 4 → ℝ) :
    ∀ᶠ l : Int in Filter.atTop, Matrix.mulVec (sourceJfin l) v = 0 := by
  refine Filter.eventually_atTop.2 ?_
  refine ⟨2, ?_⟩
  intro l hl
  have hne1 : l ≠ 1 := by linarith
  have hneNeg1 : l ≠ -1 := by linarith
  simp [sourceJfin, hne1, hneNeg1]

/-- Concrete truncation of `sourceJfin` entrywise. -/
theorem sourceJfin_trunc_entry (i j : Fin 4) :
    ∀ᶠ l : Int in Filter.atTop, sourceJfin l i j = 0 := by
  refine Filter.eventually_atTop.2 ?_
  refine ⟨2, ?_⟩
  intro l hl
  have hne1 : l ≠ 1 := by linarith
  have hneNeg1 : l ≠ -1 := by linarith
  simp [sourceJfin, hne1, hneNeg1]

/--
Entrywise finite support of `sourceJfin`, transported from indexed finite CAR.
-/
theorem sourceJfin_support_entry_finite (i j : Fin 4) :
    (Function.support (fun n : Int => sourceJfin n i j)).Finite := by
  let S : Finset Int := {1, (-1 : Int)}
  have hsubset :
      Function.support (fun n : Int => sourceJfin n i j) ⊆ ((S : Set Int)) := by
    intro n hn
    by_contra hnin
    have hne1 : n ≠ 1 := by intro h; exact hnin (by simp [S, h])
    have hneNeg1 : n ≠ -1 := by intro h; exact hnin (by simp [S, h])
    have hz : sourceJfin n = 0 := by simp [sourceJfin, hne1, hneNeg1]
    have hentry : sourceJfin n i j ≠ 0 := by simpa [Function.mem_support] using hn
    exact hentry (by simpa [hz])
  exact (Finset.finite_toSet S).subset hsubset

/-- Explicit concrete commutator at the nontrivial mode pair. -/
theorem sourceJfin_commutator_one_neg_one :
    sourceJfin 1 * sourceJfin (-1) - sourceJfin (-1) * sourceJfin 1 =
      !![0, 0, 0, 0;
         0, -1, 0, 0;
         0, 0, 1, 0;
         0, 0, 0, 0] := by
  have hcomm :=
    InfoGeometry.Canonical.SplitCliffordFiniteCAR.Jmode_comm_01_10
  have h1 : sourceJfin 1 =
      InfoGeometry.Canonical.SplitCliffordFiniteCAR.Jmode 0 1 := by
    simpa [InfoGeometry.Canonical.SplitCliffordFiniteCAR.JfinIndexed_eval_one]
      using sourceJfin_eq_JfinIndexed (1 : Int)
  have hneg1 : sourceJfin (-1) =
      InfoGeometry.Canonical.SplitCliffordFiniteCAR.Jmode 1 0 := by
    simpa [InfoGeometry.Canonical.SplitCliffordFiniteCAR.JfinIndexed_eval_neg_one]
      using sourceJfin_eq_JfinIndexed (-1 : Int)
  have hcomm' :
      InfoGeometry.Canonical.SplitCliffordFiniteCAR.commM4
        (sourceJfin 1) (sourceJfin (-1))
      =
      !![0, 0, 0, 0;
         0, -1, 0, 0;
         0, 0, 1, 0;
         0, 0, 0, 0] := by
    simpa [h1, hneg1] using hcomm
  simpa [InfoGeometry.Canonical.SplitCliffordFiniteCAR.commM4] using hcomm'

/-- Source commutator vanishes when one mode is outside support `±1`. -/
theorem sourceJfin_commutator_zero_of_outside_support
    (m n : Int)
    (h : (m ≠ 1 ∧ m ≠ -1) ∨ (n ≠ 1 ∧ n ≠ -1)) :
    sourceJfin m * sourceJfin n - sourceJfin n * sourceJfin m = 0 := by
  rcases h with hm | hn
  · simp [sourceJfin, hm.1, hm.2]
  · simp [sourceJfin, hn.1, hn.2]

/--
Same finite-window `J/trunc/comm` table, lifted directly from the indexed finite
CAR theorem surface.
-/
theorem sourceJfin_constructive_window_J_trunc_comm_from_finiteCAR :
    (∀ n : Int, n ≠ 1 → n ≠ -1 → sourceJfin n = 0) ∧
    (∀ v : Fin 4 → ℝ, ∀ᶠ l : Int in Filter.atTop, Matrix.mulVec (sourceJfin l) v = 0) ∧
    (∀ i j : Fin 4, ∀ᶠ l : Int in Filter.atTop, sourceJfin l i j = 0) ∧
    (sourceJfin 1 * sourceJfin 1 - sourceJfin 1 * sourceJfin 1 = 0) ∧
    (sourceJfin (-1) * sourceJfin (-1) - sourceJfin (-1) * sourceJfin (-1) = 0) ∧
    (sourceJfin 1 * sourceJfin (-1) - sourceJfin (-1) * sourceJfin 1 =
      !![0, 0, 0, 0;
         0, -1, 0, 0;
         0, 0, 1, 0;
         0, 0, 0, 0]) ∧
    (sourceJfin (-1) * sourceJfin 1 - sourceJfin 1 * sourceJfin (-1) =
      - !![0, 0, 0, 0;
           0, -1, 0, 0;
           0, 0, 1, 0;
           0, 0, 0, 0]) := by
  rcases
      InfoGeometry.Canonical.SplitCliffordFiniteCAR.JfinIndexed_constructive_window_J_trunc_comm
    with ⟨hSupp, hTruncV, hTruncE, h11, hNegNeg, h1Neg, hNeg1⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n h1 hm1
    rw [sourceJfin_eq_JfinIndexed]
    exact hSupp n h1 hm1
  · intro v
    filter_upwards [hTruncV v] with n hn
    simpa [sourceJfin_eq_JfinIndexed] using hn
  · intro i j
    filter_upwards [hTruncE i j] with n hn
    simpa [sourceJfin_eq_JfinIndexed] using hn
  · simpa [sourceJfin_eq_JfinIndexed] using h11
  · simpa [sourceJfin_eq_JfinIndexed] using hNegNeg
  · simpa [sourceJfin_eq_JfinIndexed] using h1Neg
  · simpa [sourceJfin_eq_JfinIndexed] using hNeg1

/--
Concrete two-mode source-side `J/trunc/comm` table from finite CAR data.

This is the real constructed finite witness shape (table form), not an imported
Heisenberg packet.
-/
theorem sourceJfin_constructed_table :
    (∀ v : Fin 4 → ℝ, ∀ᶠ l : Int in Filter.atTop, Matrix.mulVec (sourceJfin l) v = 0) ∧
    (∀ i j : Fin 4, ∀ᶠ l : Int in Filter.atTop, sourceJfin l i j = 0) ∧
    (sourceJfin 1 * sourceJfin 1 - sourceJfin 1 * sourceJfin 1 = 0) ∧
    (sourceJfin (-1) * sourceJfin (-1) - sourceJfin (-1) * sourceJfin (-1) = 0) ∧
    (sourceJfin 1 * sourceJfin (-1) - sourceJfin (-1) * sourceJfin 1 =
      !![0, 0, 0, 0;
         0, -1, 0, 0;
         0, 0, 1, 0;
         0, 0, 0, 0]) ∧
    (sourceJfin (-1) * sourceJfin 1 - sourceJfin 1 * sourceJfin (-1) =
      - !![0, 0, 0, 0;
           0, -1, 0, 0;
           0, 0, 1, 0;
           0, 0, 0, 0]) := by
  refine ⟨sourceJfin_trunc_vector, sourceJfin_trunc_entry, ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · exact sourceJfin_commutator_one_neg_one
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [sourceJfin, a1, a1Dag, a2, a2Dag, Matrix.mul_apply, Fin.sum_univ_four]

/--
Constructive finite-window source-side `J/trunc/comm` theorem from finite CAR.

This is an explicit finite completion statement:
* support is exactly in `±1`,
* truncation holds at `atTop`,
* commutator table is piecewise explicit.
It is intentionally not a full Heisenberg representation claim.
-/
theorem sourceJfin_constructive_window_J_trunc_comm :
    (∀ n : Int, n ≠ 1 → n ≠ -1 → sourceJfin n = 0) ∧
    (∀ v : Fin 4 → ℝ, ∀ᶠ l : Int in Filter.atTop, Matrix.mulVec (sourceJfin l) v = 0) ∧
    (∀ i j : Fin 4, ∀ᶠ l : Int in Filter.atTop, sourceJfin l i j = 0) ∧
    (sourceJfin 1 * sourceJfin 1 - sourceJfin 1 * sourceJfin 1 = 0) ∧
    (sourceJfin (-1) * sourceJfin (-1) - sourceJfin (-1) * sourceJfin (-1) = 0) ∧
    (sourceJfin 1 * sourceJfin (-1) - sourceJfin (-1) * sourceJfin 1 =
      !![0, 0, 0, 0;
         0, -1, 0, 0;
         0, 0, 1, 0;
         0, 0, 0, 0]) ∧
    (sourceJfin (-1) * sourceJfin 1 - sourceJfin 1 * sourceJfin (-1) =
      - !![0, 0, 0, 0;
           0, -1, 0, 0;
           0, 0, 1, 0;
           0, 0, 0, 0]) := by
  refine ⟨?_, sourceJfin_trunc_vector, sourceJfin_trunc_entry, ?_, ?_, ?_, ?_⟩
  · intro n h1 hm1
    simp [sourceJfin, h1, hm1]
  · simp
  · simp
  · exact sourceJfin_commutator_one_neg_one
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [sourceJfin, a1, a1Dag, a2, a2Dag, Matrix.mul_apply, Fin.sum_univ_four]

/--
Explicit source-side infinite indexed current completion from finite CAR data.

This is an actual `∃ J : Int → M4R` theorem (with `J := sourceJfin`) carrying:
support, truncation, and concrete commutator table. It intentionally does not
assert the full Heisenberg central law.
-/
theorem sourceJfin_infinite_completion_exists :
    ∃ J : Int → M4R,
      (∀ n : Int, n ≠ 1 → n ≠ -1 → J n = 0) ∧
      (∀ v : Fin 4 → ℝ, ∀ᶠ l : Int in Filter.atTop, Matrix.mulVec (J l) v = 0) ∧
      (∀ i j : Fin 4, ∀ᶠ l : Int in Filter.atTop, J l i j = 0) ∧
      (J 1 * J 1 - J 1 * J 1 = 0) ∧
      (J (-1) * J (-1) - J (-1) * J (-1) = 0) ∧
      (J 1 * J (-1) - J (-1) * J 1 =
        !![0, 0, 0, 0;
           0, -1, 0, 0;
           0, 0, 1, 0;
           0, 0, 0, 0]) ∧
      (J (-1) * J 1 - J 1 * J (-1) =
        - !![0, 0, 0, 0;
             0, -1, 0, 0;
             0, 0, 1, 0;
             0, 0, 0, 0]) := by
  refine ⟨sourceJfin, ?_⟩
  exact sourceJfin_constructive_window_J_trunc_comm

/--
External Heisenberg-law shape (scalar central term) over `M4R`.

This mirrors the downstream consumer shape `[J_m,J_n] = m δ_{m+n,0} · 1`
at the concrete matrix level.
-/
def scalarHeisenbergShape (J : Int → M4R) : Prop :=
  ∀ m n : Int,
    J m * J n - J n * J m =
      (if m + n = 0 then (m : ℝ) else 0) • (1 : M4R)

/--
The finite `sourceJfin` table is not the scalar Heisenberg law.

At `(m,n) = (1,-1)`, the commutator is the finite diagonal charge operator,
not `1 • 1`.
-/
theorem sourceJfin_not_scalarHeisenbergShape :
    ¬ scalarHeisenbergShape sourceJfin := by
  have h2 : sourceJfin 2 = 0 := by
    simp [sourceJfin]
  have hm2 : sourceJfin (-2) = 0 := by
    simp [sourceJfin]
  exact
    InfoGeometry.Canonical.SplitCliffordFiniteCAR.not_scalarHeisenbergShape_of_zero_opposite_modes
      sourceJfin 2 (by norm_num) h2 hm2

/--
Concrete opposite-mode vanishing for `sourceJfin` at mode `2`.
-/
theorem sourceJfin_mode_two_zero :
    sourceJfin 2 = 0 := by
  simp [sourceJfin]

/--
Concrete opposite-mode vanishing for `sourceJfin` at mode `-2`.
-/
theorem sourceJfin_mode_neg_two_zero :
    sourceJfin (-2) = 0 := by
  simp [sourceJfin]

/--
Finite-to-infinite reduction for the local source-side pair commutator kernel:
the infinite `finsum` equals the finite sum over the two-point window.
-/
theorem sourceJfin_pairComm_finsum_eq_sum_window
    (m n : Int) :
    (∑ᶠ k : Int, (sourceJfin (m - k) * sourceJfin (n + k) - sourceJfin (n + k) * sourceJfin (m - k)))
      =
    Finset.sum ({m - 1, m + 1} : Finset Int)
      (fun k => (sourceJfin (m - k) * sourceJfin (n + k) - sourceJfin (n + k) * sourceJfin (m - k))) := by
  simpa [InfoGeometry.Canonical.SplitCliffordFiniteCAR.completedCurrentModeJW,
    sourceJfin_eq_JfinIndexed, InfoGeometry.Canonical.SplitCliffordFiniteCAR.commM4]
    using InfoGeometry.Canonical.SplitCliffordFiniteCAR.completedCurrentModeJW_pairComm_finsum_eq_sum_window m n

/--
Finite support of the source-side pair-commutator kernel.

This is the structural finiteness fact behind the source-side `finsum`
reductions.
-/
theorem sourceJfin_pairComm_support_finite
    (m n : Int) :
    (Function.support
      (fun k : Int =>
        (sourceJfin (m - k) * sourceJfin (n + k) -
          sourceJfin (n + k) * sourceJfin (m - k)))).Finite := by
  simpa [InfoGeometry.Canonical.SplitCliffordFiniteCAR.completedCurrentModeJW,
    sourceJfin_eq_JfinIndexed, InfoGeometry.Canonical.SplitCliffordFiniteCAR.commM4]
    using InfoGeometry.Canonical.SplitCliffordFiniteCAR.completedCurrentModeJW_pairComm_support_finite m n

/--
Source-side support subset for the pair-commutator kernel.

For fixed `m n`, any nonzero value of
`k ↦ [J_{m-k}, J_{n+k}]`
can only occur at `k = m-1` or `k = m+1`.
-/
theorem sourceJfin_pairComm_support_subset
    (m n : Int) :
    Function.support
      (fun k : Int =>
        (sourceJfin (m - k) * sourceJfin (n + k) -
          sourceJfin (n + k) * sourceJfin (m - k)))
      ⊆ ({m - 1, m + 1} : Set Int) := by
  simpa [InfoGeometry.Canonical.SplitCliffordFiniteCAR.completedCurrentModeJW,
    sourceJfin_eq_JfinIndexed, InfoGeometry.Canonical.SplitCliffordFiniteCAR.commM4]
    using InfoGeometry.Canonical.SplitCliffordFiniteCAR.completedCurrentModeJW_pairComm_support_subset m n

/--
Pointwise off-window vanishing for the source-side pair-commutator kernel.

If `k` is not one of the two support points `m-1` or `m+1`, then the local
kernel term is exactly zero.
-/
theorem sourceJfin_pairComm_term_eq_zero_of_outside_window
    (m n k : Int)
    (hk1 : k ≠ m - 1) (hk2 : k ≠ m + 1) :
    (sourceJfin (m - k) * sourceJfin (n + k) -
      sourceJfin (n + k) * sourceJfin (m - k)) = 0 := by
  by_contra hne
  have hkSupp : k ∈ Function.support
      (fun t : Int =>
        (sourceJfin (m - t) * sourceJfin (n + t) -
          sourceJfin (n + t) * sourceJfin (m - t))) := by
    simpa [Function.mem_support] using hne
  have hkWin : k ∈ ({m - 1, m + 1} : Set Int) :=
    sourceJfin_pairComm_support_subset m n hkSupp
  rcases hkWin with hkWin | hkWin
  · exact hk1 hkWin
  · exact hk2 hkWin

/--
Two-term reduction of the local source-side pair-commutator `finsum`.

This is the direct finite→infinite reduction at the source side:
the infinite indexed commutator sum collapses to the two mode crossings.
-/
theorem sourceJfin_pairComm_finsum_eq_two_terms
    (m n : Int) :
    (∑ᶠ k : Int, (sourceJfin (m - k) * sourceJfin (n + k) - sourceJfin (n + k) * sourceJfin (m - k)))
      =
    (sourceJfin 1 * sourceJfin (m + n - 1) - sourceJfin (m + n - 1) * sourceJfin 1)
      +
    (sourceJfin (-1) * sourceJfin (m + n + 1) - sourceJfin (m + n + 1) * sourceJfin (-1)) := by
  simpa [InfoGeometry.Canonical.SplitCliffordFiniteCAR.completedCurrentModeJW,
    sourceJfin_eq_JfinIndexed, InfoGeometry.Canonical.SplitCliffordFiniteCAR.commM4]
    using InfoGeometry.Canonical.SplitCliffordFiniteCAR.completedCurrentModeJW_pairComm_finsum_eq_two_terms m n

/--
Piecewise commutator table for the concrete `sourceJfin` family.
-/
theorem sourceJfin_comm_table_piecewise
    (p q : Int) :
    sourceJfin p * sourceJfin q - sourceJfin q * sourceJfin p =
      if p = 1 ∧ q = -1 then
        !![0, 0, 0, 0;
           0, -1, 0, 0;
           0, 0, 1, 0;
           0, 0, 0, 0]
      else if p = -1 ∧ q = 1 then
        - !![0, 0, 0, 0;
             0, -1, 0, 0;
             0, 0, 1, 0;
             0, 0, 0, 0]
      else
        0 := by
  simpa [sourceJfin_eq_JfinIndexed, InfoGeometry.Canonical.SplitCliffordFiniteCAR.commM4]
    using InfoGeometry.Canonical.SplitCliffordFiniteCAR.JfinIndexed_comm_table_piecewise p q

/--
Closed-form source-side pair-commutator kernel: the indexed `finsum` vanishes.

This is the explicit piecewise closure of the local finite current kernel after
the two-term reduction.
-/
theorem sourceJfin_pairComm_finsum_eq_zero
    (m n : Int) :
    (∑ᶠ k : Int, (sourceJfin (m - k) * sourceJfin (n + k) - sourceJfin (n + k) * sourceJfin (m - k)))
      = 0 := by
  rw [sourceJfin_pairComm_finsum_eq_two_terms]
  by_cases h0 : m + n = 0
  · have hA :
      sourceJfin 1 * sourceJfin (m + n - 1) - sourceJfin (m + n - 1) * sourceJfin 1
        =
      !![0, 0, 0, 0;
         0, -1, 0, 0;
         0, 0, 1, 0;
         0, 0, 0, 0] := by
      have hm : m + n - 1 = -1 := by omega
      simpa [hm] using sourceJfin_comm_table_piecewise 1 (m + n - 1)
    have hB :
      sourceJfin (-1) * sourceJfin (m + n + 1) - sourceJfin (m + n + 1) * sourceJfin (-1)
        =
      - !![0, 0, 0, 0;
           0, -1, 0, 0;
           0, 0, 1, 0;
           0, 0, 0, 0] := by
      have hm : m + n + 1 = 1 := by omega
      simpa [hm] using sourceJfin_comm_table_piecewise (-1) (m + n + 1)
    rw [hA, hB]
    ext i j <;> fin_cases i <;> fin_cases j <;> norm_num
  · have hA :
      sourceJfin 1 * sourceJfin (m + n - 1) - sourceJfin (m + n - 1) * sourceJfin 1 = 0 := by
      have hm : m + n - 1 ≠ -1 := by
        intro h
        apply h0
        omega
      simpa [hm] using sourceJfin_comm_table_piecewise 1 (m + n - 1)
    have hB :
      sourceJfin (-1) * sourceJfin (m + n + 1) - sourceJfin (m + n + 1) * sourceJfin (-1) = 0 := by
      have hm : m + n + 1 ≠ 1 := by
        intro h
        apply h0
        omega
      simpa [hm] using sourceJfin_comm_table_piecewise (-1) (m + n + 1)
    simp [hA, hB]

/--
Off-diagonal pair-kernel vanishing (`m + n ≠ 0`) for the local source current.
-/
theorem sourceJfin_pairComm_finsum_eq_zero_of_add_ne_zero
    (m n : Int) (hmn : m + n ≠ 0) :
    (∑ᶠ k : Int, (sourceJfin (m - k) * sourceJfin (n + k) - sourceJfin (n + k) * sourceJfin (m - k)))
      = 0 := by
  simpa using sourceJfin_pairComm_finsum_eq_zero m n

/--
Diagonal pair-kernel value (`m + n = 0`) for the local source current.

In the finite two-mode model this is still zero after summing the two
Jordan-Wigner crossings.
-/
theorem sourceJfin_pairComm_finsum_eq_zero_of_add_eq_zero
    (m n : Int) (hmn : m + n = 0) :
    (∑ᶠ k : Int, (sourceJfin (m - k) * sourceJfin (n + k) - sourceJfin (n + k) * sourceJfin (m - k)))
      = 0 := by
  simpa using sourceJfin_pairComm_finsum_eq_zero m n

/--
Piecewise normal form for the local source-side pair-kernel `finsum`.

This is packaged for downstream rewriting in one lemma.
-/
theorem sourceJfin_pairComm_finsum_piecewise
    (m n : Int) :
    (∑ᶠ k : Int, (sourceJfin (m - k) * sourceJfin (n + k) - sourceJfin (n + k) * sourceJfin (m - k)))
      =
    (if m + n = 0 then (0 : M4R) else 0) := by
  by_cases hmn : m + n = 0
  · simp [hmn, sourceJfin_pairComm_finsum_eq_zero_of_add_eq_zero, hmn]
  · simp [hmn, sourceJfin_pairComm_finsum_eq_zero_of_add_ne_zero, hmn]

/-! ## External infinite-current completion (honest Heisenberg law) -/

/--
Heisenberg-law shape on an arbitrary endomorphism family.

This is the true infinite current-algebra target:
`[J_m, J_n] = m δ_{m+n,0} · id`.
-/
def scalarHeisenbergShapeEnd
    {𝕜 V : Type*}
    [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    (J : Int → V →ₗ[𝕜] V) : Prop :=
  ∀ m n : Int,
    (J m).commutator (J n) =
      (if m + n = 0 then (m : 𝕜) else 0) • (1 : V →ₗ[𝕜] V)

/--
Concrete infinite current family from the external charged-Fock Heisenberg
construction.
-/
noncomputable def externalInfiniteJ
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    Int →
      VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
        VirasoroProject.ChargedFockSpace 𝕜 α :=
  representedChargedFockJ 𝕜 α

/--
External infinite current completion theorem (constructive data package,
without introducing a new wrapper structure).

This is the honest infinite/source-current closure:
* truncation,
* full Heisenberg commutator law for all integer modes.
-/
theorem external_infinite_current_completion
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    ∃ J :
      Int →
        VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
          VirasoroProject.ChargedFockSpace 𝕜 α,
      (∀ v, ∀ᶠ n : Int in Filter.atTop, J n v = 0) ∧
      scalarHeisenbergShapeEnd J := by
  refine ⟨externalInfiniteJ 𝕜 α, ?_, ?_⟩
  · simpa [externalInfiniteJ] using representedChargedFockJ_trunc (𝕜 := 𝕜) α
  · intro m n
    have hWick := representedChargedFockJ_wick (𝕜 := 𝕜) α m n
    by_cases hmn : m + n = 0
    · simpa [scalarHeisenbergShapeEnd, hmn] using hWick
    · simpa [scalarHeisenbergShapeEnd, hmn] using hWick

/--
The finite two-mode table and the external infinite Heisenberg family are
different closure levels:

* `sourceJfin` is finite-support with diagonal charge commutator;
* `externalInfiniteJ` satisfies the scalar central Heisenberg law.
-/
theorem finite_vs_external_closure_boundary
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (¬ scalarHeisenbergShape sourceJfin) ∧
    scalarHeisenbergShapeEnd (externalInfiniteJ 𝕜 α) := by
  refine ⟨sourceJfin_not_scalarHeisenbergShape, ?_⟩
  intro m n
  have hWick := representedChargedFockJ_wick (𝕜 := 𝕜) α m n
  by_cases hmn : m + n = 0
  · simpa [externalInfiniteJ, scalarHeisenbergShapeEnd, hmn] using hWick
  · simpa [externalInfiniteJ, scalarHeisenbergShapeEnd, hmn] using hWick

/-! ## Repo-native infinite/current completion from raw CAR -/

/--
Repo-native infinite/current completion (formal completed-current lane).

This is the constructive source-side infinite family coming directly from the
raw CAR owner surface:

`J n := normalOrderedCurrent C n`.

No external represented witness packet is used here.
-/
theorem rawCAR_infinite_current_completion
    {A : Type*} [Ring A]
    (C : _root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.RawCARModeCompletion A)
    (m n : Int) :
    _root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.CCRBracketCompleted
      C
      (_root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.normalOrderedCurrent C m)
      (_root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.normalOrderedCurrent C n)
      =
      if m + n = 0 then
        m • _root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.completedCentral C
      else
        0 := by
  simpa using
    _root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.normalOrderedCurrent_heisenberg_from_rawCAR
      C m n

/--
Constructive (non-existential) infinite current law from raw CAR data.

This is the same closure as `rawCAR_infinite_current_completion`, but with the
current family fixed explicitly to `normalOrderedCurrent C`.
-/
theorem rawCAR_infinite_current_completion_constructive
    {A : Type*} [Ring A]
    (C : _root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.RawCARModeCompletion A)
    (m n : Int) :
    _root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.CCRBracketCompleted
      C
      (_root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.normalOrderedCurrent C m)
      (_root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.normalOrderedCurrent C n)
      =
      if m + n = 0 then
        m • _root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.completedCentral C
      else
        0 := by
  simpa using
    _root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.normalOrderedCurrent_heisenberg_from_rawCAR
      C m n

/--
Off-diagonal Heisenberg commutator in the raw-CAR infinite current lane.
-/
theorem rawCAR_heisenberg_comm_zero_offdiag
    {A : Type*} [Ring A]
    (C : _root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.RawCARModeCompletion A)
    (m n : Int) (hmn : m + n ≠ 0) :
    _root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.CCRBracketCompleted
      C
      (_root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.normalOrderedCurrent C m)
      (_root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.normalOrderedCurrent C n)
      = 0 := by
  simpa [hmn] using rawCAR_infinite_current_completion_constructive C m n

/--
Diagonal Heisenberg commutator in the raw-CAR infinite current lane.
-/
theorem rawCAR_heisenberg_comm_central_diag
    {A : Type*} [Ring A]
    (C : _root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.RawCARModeCompletion A)
    (m n : Int) (hmn : m + n = 0) :
    _root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.CCRBracketCompleted
      C
      (_root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.normalOrderedCurrent C m)
      (_root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.normalOrderedCurrent C n)
      =
      m • _root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.completedCentral C := by
  simpa [hmn] using rawCAR_infinite_current_completion_constructive C m n

/--
Full Heisenberg commutator law in the raw-CAR infinite current lane.

This is the piecewise combination of the off-diagonal and diagonal cases.
-/
theorem rawCAR_heisenberg_comm_full
    {A : Type*} [Ring A]
    (C : _root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.RawCARModeCompletion A)
    (m n : Int) :
    _root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.CCRBracketCompleted
      C
      (_root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.normalOrderedCurrent C m)
      (_root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.normalOrderedCurrent C n)
      =
      if m + n = 0 then
        m • _root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.completedCentral C
      else
        0 := by
  by_cases hmn : m + n = 0
  · simpa [hmn] using rawCAR_heisenberg_comm_central_diag (C := C) (m := m) (n := n) hmn
  · simpa [hmn] using rawCAR_heisenberg_comm_zero_offdiag (C := C) (m := m) (n := n) hmn

/--
Repo-native infinite/current completion with explicit Problem-7 well-definedness
data from cutoff stabilization.
-/
theorem rawCAR_infinite_current_completion_with_cutoff_data
    {A : Type*} [Ring A]
    (C : _root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.RawCARModeCompletion A)
    (m n : Int) :
    (forall i j : Int, ∃ N0 : Nat, ∀ N : Nat, N0 ≤ N ->
      (_root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.cutoffDiagonalCurrent N m).coeff i j =
      (_root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.completedCurrent m).coeff i j) ∧
    (forall i j : Int, ∃ N0 : Nat, ∀ N : Nat, N0 ≤ N ->
      (_root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.cutoffDiagonalCurrent N n).coeff i j =
      (_root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.completedCurrent n).coeff i j) ∧
    (forall i j : Int,
      _root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.formalCurrentNoncentralCoeff m n i j = 0) ∧
    (_root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.formalCurrentCentralCoeff m n =
      if m + n = 0 then m else 0) ∧
    (_root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.CCRBracketCompleted
      C
      (_root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.normalOrderedCurrent C m)
      (_root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.normalOrderedCurrent C n)
      =
      if m + n = 0 then
        m • _root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.completedCentral C
      else 0) := by
  simpa [_root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.completedCentral]
    using
      _root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.constructiveHeisenbergCurrent_from_completedCurrent
        C m n

/--
Finite-vs-repo-native-infinite closure boundary.

`sourceJfin` fails scalar Heisenberg shape, while the raw-CAR completed-current
family satisfies the completed Heisenberg current law.
-/
theorem finite_vs_rawCAR_infinite_closure_boundary
    {A : Type*} [Ring A]
    (C : _root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.RawCARModeCompletion A) :
    (¬ scalarHeisenbergShape sourceJfin) ∧
    (∀ m n : Int,
      _root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.CCRBracketCompleted
        C
        (_root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.normalOrderedCurrent C m)
        (_root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.normalOrderedCurrent C n)
        =
        if m + n = 0 then
          m • _root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.completedCentral C
        else
          0) := by
  exact ⟨sourceJfin_not_scalarHeisenbergShape, rawCAR_infinite_current_completion C⟩

/--
Finite-vs-infinite closure boundary in constructive form.

No existential current packet is used: the infinite family is explicitly
`normalOrderedCurrent C`.
-/
theorem finite_vs_rawCAR_infinite_closure_boundary_constructive
    {A : Type*} [Ring A]
    (C : _root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.RawCARModeCompletion A) :
    (¬ scalarHeisenbergShape sourceJfin) ∧
    (∀ m n : Int,
      _root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.CCRBracketCompleted
        C
        (_root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.normalOrderedCurrent C m)
        (_root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.normalOrderedCurrent C n)
        =
        if m + n = 0 then
          m • _root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.completedCentral C
        else
          0) := by
  refine ⟨sourceJfin_not_scalarHeisenbergShape, ?_⟩
  intro m n
  exact rawCAR_infinite_current_completion_constructive C m n

/-! ## Finite-cutoff stabilization consumed from local finite-CAR infrastructure -/

/--
Finite cutoff commutator stabilization (local JW infrastructure).

This is the concrete finite-to-completed transition for the local indexed
current family: eventually in the cutoff parameter, the finite cutoff
commutator equals the completed commutator.
-/
theorem sourceJfin_cutoff_comm_eventually_eq_completed
    (m n : Int) :
    ∀ᶠ N : Nat in Filter.atTop,
      InfoGeometry.Canonical.SplitCliffordFiniteCAR.commM4
        (InfoGeometry.Canonical.SplitCliffordFiniteCAR.cutoffCurrentModeJW N m)
        (InfoGeometry.Canonical.SplitCliffordFiniteCAR.cutoffCurrentModeJW N n)
        =
      InfoGeometry.Canonical.SplitCliffordFiniteCAR.commM4
        (InfoGeometry.Canonical.SplitCliffordFiniteCAR.completedCurrentModeJW m)
        (InfoGeometry.Canonical.SplitCliffordFiniteCAR.completedCurrentModeJW n) := by
  simpa using
    InfoGeometry.Canonical.SplitCliffordFiniteCAR.cutoffCurrentModeJW_comm_eventually_eq_completed m n

/--
Completed commutator table for the local JW completed current family, consumed
through the local finite-CAR infrastructure.
-/
theorem sourceJfin_completed_comm_table_piecewise
    (m n : Int) :
    InfoGeometry.Canonical.SplitCliffordFiniteCAR.commM4
      (InfoGeometry.Canonical.SplitCliffordFiniteCAR.completedCurrentModeJW m)
      (InfoGeometry.Canonical.SplitCliffordFiniteCAR.completedCurrentModeJW n)
      =
      if m = 1 ∧ n = -1 then
        !![0, 0, 0, 0;
           0, -1, 0, 0;
           0, 0, 1, 0;
           0, 0, 0, 0]
      else if m = -1 ∧ n = 1 then
        - !![0, 0, 0, 0;
             0, -1, 0, 0;
             0, 0, 1, 0;
             0, 0, 0, 0]
      else
        0 := by
  simpa using
    InfoGeometry.Canonical.SplitCliffordFiniteCAR.completedCurrentModeJW_comm_table_piecewise m n

/--
Finite-to-completed commutator closure in one statement:

eventually in cutoff, the finite commutator equals the explicit piecewise
completed JW commutator table.
-/
theorem sourceJfin_cutoff_comm_eventually_eq_piecewise
    (m n : Int) :
    ∀ᶠ N : Nat in Filter.atTop,
      InfoGeometry.Canonical.SplitCliffordFiniteCAR.commM4
        (InfoGeometry.Canonical.SplitCliffordFiniteCAR.cutoffCurrentModeJW N m)
        (InfoGeometry.Canonical.SplitCliffordFiniteCAR.cutoffCurrentModeJW N n)
        =
      (if m = 1 ∧ n = -1 then
        !![0, 0, 0, 0;
           0, -1, 0, 0;
           0, 0, 1, 0;
           0, 0, 0, 0]
      else if m = -1 ∧ n = 1 then
        - !![0, 0, 0, 0;
             0, -1, 0, 0;
             0, 0, 1, 0;
             0, 0, 0, 0]
      else
        0) := by
  filter_upwards [sourceJfin_cutoff_comm_eventually_eq_completed m n] with N hN
  simpa [sourceJfin_completed_comm_table_piecewise (m := m) (n := n)] using hN

/--
Constructive finite-window current completion with explicit eventual commutator
closure.

This packages one concrete `J : Int → M4R` together with:
* support in `±1`,
* truncation at `atTop` (vector and coefficient forms),
* and eventual equality of cutoff commutators to the explicit piecewise
  completed commutator table.
-/
theorem sourceJfin_constructive_completion_with_eventual_piecewise_comm :
    ∃ J : Int → M4R,
      (∀ n : Int, n ≠ 1 → n ≠ -1 → J n = 0) ∧
      (∀ v : Fin 4 → ℝ, ∀ᶠ l : Int in Filter.atTop, Matrix.mulVec (J l) v = 0) ∧
      (∀ i j : Fin 4, ∀ᶠ l : Int in Filter.atTop, J l i j = 0) ∧
      (∀ m n : Int,
        ∀ᶠ N : Nat in Filter.atTop,
          InfoGeometry.Canonical.SplitCliffordFiniteCAR.commM4
            (InfoGeometry.Canonical.SplitCliffordFiniteCAR.cutoffCurrentModeJW N m)
            (InfoGeometry.Canonical.SplitCliffordFiniteCAR.cutoffCurrentModeJW N n)
            =
          (if m = 1 ∧ n = -1 then
            !![0, 0, 0, 0;
               0, -1, 0, 0;
               0, 0, 1, 0;
               0, 0, 0, 0]
          else if m = -1 ∧ n = 1 then
            - !![0, 0, 0, 0;
                 0, -1, 0, 0;
                 0, 0, 1, 0;
                 0, 0, 0, 0]
          else
            0)) := by
  refine ⟨sourceJfin, ?_⟩
  refine ⟨?_, sourceJfin_trunc_vector, sourceJfin_trunc_entry, ?_⟩
  · intro n h1 hm1
    simp [sourceJfin, h1, hm1]
  · intro m n
    exact sourceJfin_cutoff_comm_eventually_eq_piecewise m n

/--
`SplitLiftTruncation` instantiation for the concrete external infinite current.

This discharges the owner-surface truncation shape from the explicit current
family `externalInfiniteJ`.
-/
theorem externalInfiniteJ_splitLiftTruncation
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    _root_.InfoGeometry.Canonical.SplitCliffordSourceCurrent.SplitLiftTruncation
      𝕜
      (VirasoroProject.ChargedFockSpace 𝕜 α)
      (externalInfiniteJ 𝕜 α) := by
  intro v
  simpa [externalInfiniteJ]
    using representedChargedFockJ_trunc (𝕜 := 𝕜) α v

/--
Wick/Heisenberg commutator owner-surface instantiation for the concrete
external infinite current family.
-/
theorem externalInfiniteJ_splitSourceEndWickLaw
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    SplitSourceEndWickLaw (externalInfiniteJ 𝕜 α) := by
  simpa [externalInfiniteJ] using representedChargedFockJ_wick (𝕜 := 𝕜) α

/--
Explicit full Heisenberg commutator law for the concrete infinite source
current `externalInfiniteJ`.
-/
theorem externalInfiniteJ_heisenberg_comm_full
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜)
    (m n : Int) :
    (externalInfiniteJ 𝕜 α m).commutator (externalInfiniteJ 𝕜 α n) =
      if m + n = 0 then
        (m : 𝕜) •
          (1 :
            VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
              VirasoroProject.ChargedFockSpace 𝕜 α)
      else
        0 := by
  exact externalInfiniteJ_splitSourceEndWickLaw (𝕜 := 𝕜) α m n

/--
Off-diagonal readout for `externalInfiniteJ`.
-/
theorem externalInfiniteJ_heisenberg_comm_offdiag
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜)
    {m n : Int} (hmn : m + n ≠ 0) :
    (externalInfiniteJ 𝕜 α m).commutator (externalInfiniteJ 𝕜 α n) = 0 := by
  exact
    commutator_eq_zero_of_add_ne_zero
      (hWick := externalInfiniteJ_splitSourceEndWickLaw (𝕜 := 𝕜) α)
      hmn

/--
Diagonal central readout for `externalInfiniteJ`.
-/
theorem externalInfiniteJ_heisenberg_comm_diag
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜)
    {m n : Int} (hmn : m + n = 0) :
    (externalInfiniteJ 𝕜 α m).commutator (externalInfiniteJ 𝕜 α n) =
      (m : 𝕜) •
        (1 :
          VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
            VirasoroProject.ChargedFockSpace 𝕜 α) := by
  exact
    commutator_eq_central_of_add_eq_zero
      (hWick := externalInfiniteJ_splitSourceEndWickLaw (𝕜 := 𝕜) α)
      hmn

/--
Mode-swap antisymmetry consistency for the concrete infinite Heisenberg current:
the two diagonal central readouts are negatives of each other when `m + n = 0`.
-/
theorem externalInfiniteJ_heisenberg_comm_diag_swap_neg
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜)
    {m n : Int} (hmn : m + n = 0) :
    (externalInfiniteJ 𝕜 α n).commutator (externalInfiniteJ 𝕜 α m) =
      -((externalInfiniteJ 𝕜 α m).commutator (externalInfiniteJ 𝕜 α n)) := by
  have hnm : n + m = 0 := by simpa [add_comm] using hmn
  rw [externalInfiniteJ_heisenberg_comm_diag (𝕜 := 𝕜) α (m := n) (n := m) hnm]
  rw [externalInfiniteJ_heisenberg_comm_diag (𝕜 := 𝕜) α (m := m) (n := n) hmn]
  have hnm_cast : (n : 𝕜) = -(m : 𝕜) := by
    have hInt : n = -m := by omega
    norm_num [hInt]
  rw [hnm_cast]
  simp [smul_neg]

/--
Combined owner-surface closure payload for the concrete external infinite
current family: truncation and full Wick/Heisenberg commutator law.
-/
theorem externalInfiniteJ_owner_surface_payload
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    _root_.InfoGeometry.Canonical.SplitCliffordSourceCurrent.SplitLiftTruncation
      𝕜
      (VirasoroProject.ChargedFockSpace 𝕜 α)
      (externalInfiniteJ 𝕜 α)
    ∧
    SplitSourceEndWickLaw (externalInfiniteJ 𝕜 α) := by
  exact ⟨externalInfiniteJ_splitLiftTruncation (𝕜 := 𝕜) α,
    externalInfiniteJ_splitSourceEndWickLaw (𝕜 := 𝕜) α⟩

/--
Explicit source-side closure theorem in owner-surface existential form:
there exists a current family with both truncation and Wick commutator law.
-/
theorem externalInfiniteJ_exists_trunc_and_wick
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    ∃ J :
      Int →
        VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
          VirasoroProject.ChargedFockSpace 𝕜 α,
      _root_.InfoGeometry.Canonical.SplitCliffordSourceCurrent.SplitLiftTruncation
        𝕜
        (VirasoroProject.ChargedFockSpace 𝕜 α)
        J
      ∧
      SplitSourceEndWickLaw J := by
  refine ⟨externalInfiniteJ 𝕜 α, ?_⟩
  exact externalInfiniteJ_owner_surface_payload (𝕜 := 𝕜) α

/--
Explicit existential closure with the full commutator equation expanded.

This is the owner-surface `∃ J` form with truncation and the concrete
Heisenberg formula (not just a named predicate).
-/
theorem externalInfiniteJ_exists_trunc_and_heisenberg_full
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    ∃ J :
      Int →
        VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
          VirasoroProject.ChargedFockSpace 𝕜 α,
      _root_.InfoGeometry.Canonical.SplitCliffordSourceCurrent.SplitLiftTruncation
        𝕜
        (VirasoroProject.ChargedFockSpace 𝕜 α)
        J
      ∧
      (∀ m n : Int,
        (J m).commutator (J n) =
          if m + n = 0 then
            (m : 𝕜) •
              (1 :
                VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
                  VirasoroProject.ChargedFockSpace 𝕜 α)
          else
            0) := by
  refine ⟨externalInfiniteJ 𝕜 α, ?_⟩
  refine ⟨externalInfiniteJ_splitLiftTruncation (𝕜 := 𝕜) α, ?_⟩
  exact externalInfiniteJ_heisenberg_comm_full (𝕜 := 𝕜) α

/--
Sharper owner-side existence theorem tailored to the upstream level-one debt.

This does not identify the symbolic prime-OPE carrier with the concrete source
current. It only states that there exists a truncating current family whose low
modes satisfy the level-one resonant and off-diagonal Heisenberg laws.
-/
theorem externalInfiniteJ_exists_trunc_and_level_one_heisenberg
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    ∃ J :
      Int →
        VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
          VirasoroProject.ChargedFockSpace 𝕜 α,
      _root_.InfoGeometry.Canonical.SplitCliffordSourceCurrent.SplitLiftTruncation
        𝕜
        (VirasoroProject.ChargedFockSpace 𝕜 α)
        J
      ∧ (J 1).commutator (J (-1)) =
          (1 :
            VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
              VirasoroProject.ChargedFockSpace 𝕜 α)
      ∧ (J 1).commutator (J 0) = 0 := by
  refine ⟨externalInfiniteJ 𝕜 α, ?_⟩
  refine ⟨externalInfiniteJ_splitLiftTruncation (𝕜 := 𝕜) α, ?_, ?_⟩
  · simpa using externalInfiniteJ_heisenberg_comm_full (𝕜 := 𝕜) α 1 (-1)
  · simpa using externalInfiniteJ_heisenberg_comm_full (𝕜 := 𝕜) α 1 0

/--
Typed non-fake closure guard:
no current family supported only on `±1` can be upgraded to a full
`CurrentHeisenbergRep`.
-/
theorem no_fake_currentRep_from_finite_support
    {𝕜 V : Type*}
    [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V] [Nontrivial V]
    (J : Int → V →ₗ[𝕜] V)
    (hSupport : ∀ n : Int, n ≠ 1 → n ≠ -1 → J n = 0) :
    ¬ ∃ H :
      _root_.InfoGeometry.Canonical.CurrentSugawaraBridge.CurrentHeisenbergRep 𝕜 V,
      H.J = J := by
  rintro ⟨H, hJ⟩
  have hJ2 : H.J 2 = 0 := by
    rw [hJ]
    exact hSupport 2 (by norm_num) (by norm_num)
  have hJneg2 : H.J (-2) = 0 := by
    rw [hJ]
    exact hSupport (-2) (by norm_num) (by norm_num)
  have hcomm_zero :
      (H.J 2).commutator (H.J (-2)) = 0 := by
    rw [hJ2, hJneg2]
    simp [LinearMap.commutator]
  have hcomm_heis :
      (H.J 2).commutator (H.J (-2))
        =
      (2 : 𝕜) • (1 : V →ₗ[𝕜] V) := by
    simpa using H.comm 2 (-2)
  have hscalar_zero :
      (2 : 𝕜) • (1 : V →ₗ[𝕜] V) = 0 := by
    rw [← hcomm_heis]
    exact hcomm_zero
  have h2_ne : (2 : 𝕜) ≠ 0 := by norm_num
  have hone_zero : (1 : V →ₗ[𝕜] V) = 0 :=
    (smul_eq_zero.mp hscalar_zero).resolve_left h2_ne
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have : v = 0 := by
    have happly := congrArg (fun f : V →ₗ[𝕜] V => f v) hone_zero
    simpa using happly
  exact hv this

/--
Concrete `CurrentHeisenbergRep` built from the explicit infinite current
`externalInfiniteJ`.
-/
noncomputable def externalInfiniteJ_currentHeisenbergRep
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    _root_.InfoGeometry.Canonical.CurrentSugawaraBridge.CurrentHeisenbergRep
      𝕜
      (VirasoroProject.ChargedFockSpace 𝕜 α) where
  J := externalInfiniteJ 𝕜 α
  trunc := externalInfiniteJ_splitLiftTruncation (𝕜 := 𝕜) α
  comm := externalInfiniteJ_heisenberg_comm_full (𝕜 := 𝕜) α

/--
Direct full Heisenberg commutator law read from the constructed
`CurrentHeisenbergRep` field `comm`.
-/
theorem externalInfiniteJ_currentHeisenbergRep_comm_full
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) (m n : Int) :
    ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).J m).commutator
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).J n)
      =
      if m + n = 0 then
        (m : 𝕜) •
          (1 :
            VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
              VirasoroProject.ChargedFockSpace 𝕜 α)
      else
        0 := by
  exact (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).comm m n

/--
Resonant source-current commutator at modes `(1,-1)`.

This is the first concrete Heisenberg readback from the explicit source-side
current: the resonant pair activates exactly the central channel.
-/
theorem externalInfiniteJ_currentHeisenbergRep_comm_one_neg_one
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).J 1).commutator
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).J (-1))
      =
      (1 :
        VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
          VirasoroProject.ChargedFockSpace 𝕜 α) := by
  simpa using externalInfiniteJ_currentHeisenbergRep_comm_full (𝕜 := 𝕜) α 1 (-1)

/--
Off-diagonal source-current commutator at modes `(1,0)`.

Away from the resonant diagonal `m + n = 0`, the explicit source current has no
central contribution and the commutator vanishes.
-/
theorem externalInfiniteJ_currentHeisenbergRep_comm_one_zero
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).J 1).commutator
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).J 0)
      =
      0 := by
  simpa using externalInfiniteJ_currentHeisenbergRep_comm_full (𝕜 := 𝕜) α 1 0

/--
Single-shot closure theorem for the explicit source-side Heisenberg object:
the constructed `CurrentHeisenbergRep` has the intended current family `J`,
the truncation law, and the full Heisenberg commutator law.
-/
theorem externalInfiniteJ_currentHeisenbergRep_J_trunc_comm
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).J = externalInfiniteJ 𝕜 α)
      ∧
    (∀ v : VirasoroProject.ChargedFockSpace 𝕜 α,
      ∀ᶠ n : Int in Filter.atTop,
        (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).J n v = 0)
      ∧
    (∀ m n : Int,
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).J m).commutator
        ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).J n)
        =
      if m + n = 0 then
        (m : 𝕜) •
          (1 :
            VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
              VirasoroProject.ChargedFockSpace 𝕜 α)
      else 0) := by
  refine ⟨rfl, ?_, ?_⟩
  · exact (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).trunc
  · intro m n
    exact (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).comm m n

/--
Concrete Virasoro bracket law for the Sugawara stress modes attached to
`externalInfiniteJ`.
-/
theorem externalInfiniteJ_sugawara_stress_virasoroBracket
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) (m n : Int) :
    ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).sugawaraStressMode m).commutator
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).sugawaraStressMode n)
      =
      (m - n) • (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).sugawaraStressMode (m + n)
        + if m + n = 0 then
            (((m ^ 3 - m : 𝕜) / (12 : 𝕜)) •
              (1 :
                VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
                  VirasoroProject.ChargedFockSpace 𝕜 α))
          else 0 := by
  simpa using
    _root_.InfoGeometry.Canonical.CurrentSugawaraBridge.CurrentHeisenbergRep.sugawaraStressMode_virasoroBracket
      (H := externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α) m n

/--
Central Virasoro generator acts as identity in the concrete Sugawara
representation built from `externalInfiniteJ`.
-/
theorem externalInfiniteJ_currentSugawara_central
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.cgen 𝕜)
      =
    (1 :
      VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
        VirasoroProject.ChargedFockSpace 𝕜 α) := by
  simpa using
    _root_.InfoGeometry.Canonical.CurrentSugawaraBridge.CurrentHeisenbergRep.currentSugawaraRepresentation_central
      (H := externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α)

/--
The Virasoro `lgen` action equals the Sugawara stress mode in the concrete
`externalInfiniteJ` representation.
-/
theorem externalInfiniteJ_currentSugawara_lgen_apply
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) (n : Int) :
    (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n)
      =
    (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).sugawaraStressMode n := by
  simpa using
    _root_.InfoGeometry.Canonical.CurrentSugawaraBridge.CurrentHeisenbergRep.currentSugawaraRepresentation_lgen_apply
      (H := externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α) n

/--
Concrete Virasoro `lgen` commutator in the Sugawara representation generated
from `externalInfiniteJ`.
-/
theorem externalInfiniteJ_currentSugawara_lgen_commutator
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) (m n : Int) :
    ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 m)).commutator
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n))
      =
      (m - n) •
        (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
          (VirasoroProject.VirasoroAlgebra.lgen 𝕜 (m + n))
      +
      if m + n = 0 then
        (((m ^ 3 - m : 𝕜) / (12 : 𝕜)) •
          (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
            (VirasoroProject.VirasoroAlgebra.cgen 𝕜))
      else
        0 := by
  rw [externalInfiniteJ_currentSugawara_lgen_apply (𝕜 := 𝕜) α m]
  rw [externalInfiniteJ_currentSugawara_lgen_apply (𝕜 := 𝕜) α n]
  rw [externalInfiniteJ_sugawara_stress_virasoroBracket (𝕜 := 𝕜) α m n]
  rw [externalInfiniteJ_currentSugawara_lgen_apply (𝕜 := 𝕜) α (m + n)]
  by_cases hmn : m + n = 0
  · simp [hmn, externalInfiniteJ_currentSugawara_central (𝕜 := 𝕜) α]
  · simp [hmn]

/--
Resonant Virasoro `lgen` commutator at modes `(1,-1)` in the explicit
Sugawara representation generated from `externalInfiniteJ`.
-/
theorem externalInfiniteJ_currentSugawara_lgen_commutator_one_neg_one
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 1)).commutator
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 (-1)))
      =
      (2 : 𝕜) •
        (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
          (VirasoroProject.VirasoroAlgebra.lgen 𝕜 0) := by
  simpa using externalInfiniteJ_currentSugawara_lgen_commutator (𝕜 := 𝕜) α 1 (-1)

/--
Off-diagonal Virasoro `lgen` commutator at modes `(1,0)` in the explicit
Sugawara representation generated from `externalInfiniteJ`.
-/
theorem externalInfiniteJ_currentSugawara_lgen_commutator_one_zero
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 1)).commutator
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 0))
      =
      (1 : 𝕜) •
        (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
          (VirasoroProject.VirasoroAlgebra.lgen 𝕜 1) := by
  simpa using externalInfiniteJ_currentSugawara_lgen_commutator (𝕜 := 𝕜) α 1 0

/--
Skew-symmetry of the concrete Virasoro `lgen` commutator in the
`externalInfiniteJ` Sugawara representation.
-/
theorem externalInfiniteJ_currentSugawara_lgen_commutator_skew
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) (m n : Int) :
    ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 m)).commutator
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n))
    =
    -(((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n)).commutator
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 m))) := by
  simp [LinearMap.commutator, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

/-! ## Closure Checklist: Section 1 (Infinite Source Current Construction) -/

theorem jw_mode_family_well_defined
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    ∀ n : Int,
      ∃ T :
        VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
          VirasoroProject.ChargedFockSpace 𝕜 α,
        T = externalInfiniteJ 𝕜 α n := by
  intro n
  exact ⟨externalInfiniteJ 𝕜 α n, rfl⟩

theorem jw_mode_family_linear
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    ∀ n : Int, ∀ u v : VirasoroProject.ChargedFockSpace 𝕜 α, ∀ c : 𝕜,
      externalInfiniteJ 𝕜 α n (u + v) = externalInfiniteJ 𝕜 α n u + externalInfiniteJ 𝕜 α n v
      ∧
      externalInfiniteJ 𝕜 α n (c • u) = c • externalInfiniteJ 𝕜 α n u := by
  intro n u v c
  exact ⟨map_add (externalInfiniteJ 𝕜 α n) u v, map_smul (externalInfiniteJ 𝕜 α n) c u⟩

theorem jw_mode_cutoff_stabilizes
    (n : Int) :
    ∀ᶠ N : Nat in Filter.atTop,
      InfoGeometry.Canonical.SplitCliffordFiniteCAR.cutoffCurrentModeJW N n =
        InfoGeometry.Canonical.SplitCliffordFiniteCAR.completedCurrentModeJW n := by
  simpa [InfoGeometry.Canonical.SplitCliffordFiniteCAR.completedCurrentModeJW] using
    InfoGeometry.Canonical.SplitCliffordFiniteCAR.cutoffCurrentModeJW_eventually_eq_J n

theorem jw_mode_cutoff_stabilizes_apply
    (n : Int) (v : Fin 4 → ℝ) :
    ∀ᶠ N : Nat in Filter.atTop,
      Matrix.mulVec
        (InfoGeometry.Canonical.SplitCliffordFiniteCAR.cutoffCurrentModeJW N n) v
      =
      Matrix.mulVec
        (InfoGeometry.Canonical.SplitCliffordFiniteCAR.completedCurrentModeJW n) v := by
  filter_upwards [jw_mode_cutoff_stabilizes n] with N hN
  simpa [hN]

theorem jw_mode_trunc_vector :
    ∀ v : Fin 4 → ℝ, ∀ᶠ n : Int in Filter.atTop,
      Matrix.mulVec (InfoGeometry.Canonical.SplitCliffordFiniteCAR.completedCurrentModeJW n) v = 0 := by
  intro v
  simpa [InfoGeometry.Canonical.SplitCliffordFiniteCAR.completedCurrentModeJW] using
    InfoGeometry.Canonical.SplitCliffordFiniteCAR.JfinIndexed_trunc_vector v

theorem jw_mode_trunc_entry
    (i j : Fin 4) :
    ∀ᶠ n : Int in Filter.atTop,
      (InfoGeometry.Canonical.SplitCliffordFiniteCAR.completedCurrentModeJW n) i j = 0 := by
  simpa [InfoGeometry.Canonical.SplitCliffordFiniteCAR.completedCurrentModeJW] using
    InfoGeometry.Canonical.SplitCliffordFiniteCAR.JfinIndexed_trunc_entry i j

theorem jw_mode_trunc_vector_infinite
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜)
    (v : VirasoroProject.ChargedFockSpace 𝕜 α) :
    ∀ᶠ n : Int in Filter.atTop, externalInfiniteJ 𝕜 α n v = 0 := by
  simpa [externalInfiniteJ] using representedChargedFockJ_trunc (𝕜 := 𝕜) α v

/-! ## Closure Checklist: Section 2 (Heisenberg Law) -/

theorem current_comm_support_finite
    (m n : Int) :
    (Function.support
      (fun k : Int =>
        InfoGeometry.Canonical.SplitCliffordFiniteCAR.commM4
          (InfoGeometry.Canonical.SplitCliffordFiniteCAR.completedCurrentModeJW (m - k))
          (InfoGeometry.Canonical.SplitCliffordFiniteCAR.completedCurrentModeJW (n + k)))).Finite := by
  simpa using
    InfoGeometry.Canonical.SplitCliffordFiniteCAR.completedCurrentModeJW_pairComm_support_finite m n

theorem current_comm_finsum_to_window
    (m n : Int) :
    (∑ᶠ k : Int,
      InfoGeometry.Canonical.SplitCliffordFiniteCAR.commM4
        (InfoGeometry.Canonical.SplitCliffordFiniteCAR.completedCurrentModeJW (m - k))
        (InfoGeometry.Canonical.SplitCliffordFiniteCAR.completedCurrentModeJW (n + k)))
      = Finset.sum ({m - 1, m + 1} : Finset Int) (fun k =>
          InfoGeometry.Canonical.SplitCliffordFiniteCAR.commM4
            (InfoGeometry.Canonical.SplitCliffordFiniteCAR.completedCurrentModeJW (m - k))
            (InfoGeometry.Canonical.SplitCliffordFiniteCAR.completedCurrentModeJW (n + k))) := by
  simpa using
    InfoGeometry.Canonical.SplitCliffordFiniteCAR.completedCurrentModeJW_pairComm_finsum_eq_sum_window m n

theorem current_comm_window_eval
    (m n : Int) :
    (∑ᶠ k : Int,
      InfoGeometry.Canonical.SplitCliffordFiniteCAR.commM4
        (InfoGeometry.Canonical.SplitCliffordFiniteCAR.completedCurrentModeJW (m - k))
        (InfoGeometry.Canonical.SplitCliffordFiniteCAR.completedCurrentModeJW (n + k)))
      =
    InfoGeometry.Canonical.SplitCliffordFiniteCAR.commM4
      (InfoGeometry.Canonical.SplitCliffordFiniteCAR.completedCurrentModeJW 1)
      (InfoGeometry.Canonical.SplitCliffordFiniteCAR.completedCurrentModeJW (m + n - 1))
    +
    InfoGeometry.Canonical.SplitCliffordFiniteCAR.commM4
      (InfoGeometry.Canonical.SplitCliffordFiniteCAR.completedCurrentModeJW (-1))
      (InfoGeometry.Canonical.SplitCliffordFiniteCAR.completedCurrentModeJW (m + n + 1)) := by
  simpa using
    InfoGeometry.Canonical.SplitCliffordFiniteCAR.completedCurrentModeJW_pairComm_finsum_eq_two_terms m n

theorem heisenberg_comm_zero_offdiag
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜)
    {m n : Int} (hmn : m + n ≠ 0) :
    (externalInfiniteJ 𝕜 α m).commutator (externalInfiniteJ 𝕜 α n) = 0 := by
  have hfull :=
    externalInfiniteJ_currentHeisenbergRep_comm_full (𝕜 := 𝕜) α m n
  simpa [externalInfiniteJ_currentHeisenbergRep, hmn] using hfull

theorem heisenberg_comm_central_diag
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜)
    {m n : Int} (hmn : m + n = 0) :
    (externalInfiniteJ 𝕜 α m).commutator (externalInfiniteJ 𝕜 α n) =
      (m : 𝕜) •
        (1 :
          VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
            VirasoroProject.ChargedFockSpace 𝕜 α) := by
  have hfull :=
    externalInfiniteJ_currentHeisenbergRep_comm_full (𝕜 := 𝕜) α m n
  simpa [externalInfiniteJ_currentHeisenbergRep, hmn] using hfull

theorem heisenberg_comm_full
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) (m n : Int) :
    (externalInfiniteJ 𝕜 α m).commutator (externalInfiniteJ 𝕜 α n) =
      if m + n = 0 then
        (m : 𝕜) •
          (1 :
            VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
              VirasoroProject.ChargedFockSpace 𝕜 α)
      else
        0 := by
  simpa [externalInfiniteJ_currentHeisenbergRep] using
    externalInfiniteJ_currentHeisenbergRep_comm_full (𝕜 := 𝕜) α m n

/--
Level-one resonant Heisenberg law for the explicit source current `externalInfiniteJ`.

This is the minimal owner-side readback matching the outstanding current-current
level-one debt shape upstream: the source current itself satisfies the resonant
Heisenberg commutator with unit central coefficient.
-/
theorem heisenberg_comm_one_neg_one
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (externalInfiniteJ 𝕜 α 1).commutator (externalInfiniteJ 𝕜 α (-1)) =
      (1 :
        VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
          VirasoroProject.ChargedFockSpace 𝕜 α) := by
  simpa using heisenberg_comm_full (𝕜 := 𝕜) α 1 (-1)

/--
Off-diagonal low-mode Heisenberg law for the explicit source current `externalInfiniteJ`.
-/
theorem heisenberg_comm_one_zero
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (externalInfiniteJ 𝕜 α 1).commutator (externalInfiniteJ 𝕜 α 0) = 0 := by
  simpa using heisenberg_comm_full (𝕜 := 𝕜) α 1 0

/--
Jacobi closure for the explicit infinite current family.

This is a direct `J/trunc/comm` consequence: each inner bracket is central,
so all three nested commutators vanish.
-/
theorem externalInfiniteJ_jacobi
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜)
    (m n k : Int) :
    (externalInfiniteJ 𝕜 α m).commutator
        ((externalInfiniteJ 𝕜 α n).commutator (externalInfiniteJ 𝕜 α k))
      +
      (externalInfiniteJ 𝕜 α n).commutator
        ((externalInfiniteJ 𝕜 α k).commutator (externalInfiniteJ 𝕜 α m))
      +
      (externalInfiniteJ 𝕜 α k).commutator
        ((externalInfiniteJ 𝕜 α m).commutator (externalInfiniteJ 𝕜 α n))
      =
    (0 :
      VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
        VirasoroProject.ChargedFockSpace 𝕜 α) := by
  rw [heisenberg_comm_full (𝕜 := 𝕜) α n k]
  rw [heisenberg_comm_full (𝕜 := 𝕜) α k m]
  rw [heisenberg_comm_full (𝕜 := 𝕜) α m n]
  simp [LinearMap.commutator, add_assoc, add_left_comm, add_comm]

/--
Global commutator skew-symmetry for the explicit infinite source current family.

This is proved from the full Heisenberg law in both diagonal and off-diagonal
branches.
-/
theorem externalInfiniteJ_commutator_skew
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜)
    (m n : Int) :
    (externalInfiniteJ 𝕜 α m).commutator (externalInfiniteJ 𝕜 α n)
      =
    -((externalInfiniteJ 𝕜 α n).commutator (externalInfiniteJ 𝕜 α m)) := by
  by_cases hmn : m + n = 0
  · have hnm : n + m = 0 := by simpa [add_comm] using hmn
    rw [heisenberg_comm_central_diag (𝕜 := 𝕜) α (m := m) (n := n) hmn]
    rw [heisenberg_comm_central_diag (𝕜 := 𝕜) α (m := n) (n := m) hnm]
    have hn : n = -m := by linarith
    simp [hn]
  · have hnm : n + m ≠ 0 := by simpa [add_comm] using hmn
    rw [heisenberg_comm_zero_offdiag (𝕜 := 𝕜) α (m := m) (n := n) hmn]
    rw [heisenberg_comm_zero_offdiag (𝕜 := 𝕜) α (m := n) (n := m) hnm]
    simp

/--
Packaged Lie-algebra closure for the explicit infinite current family:
global commutator skew-symmetry and Jacobi identity.
-/
theorem externalInfiniteJ_lie_closure
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (∀ m n : Int,
      (externalInfiniteJ 𝕜 α m).commutator (externalInfiniteJ 𝕜 α n)
        =
      -((externalInfiniteJ 𝕜 α n).commutator (externalInfiniteJ 𝕜 α m)))
    ∧
    (∀ m n k : Int,
      (externalInfiniteJ 𝕜 α m).commutator
          ((externalInfiniteJ 𝕜 α n).commutator (externalInfiniteJ 𝕜 α k))
        +
        (externalInfiniteJ 𝕜 α n).commutator
          ((externalInfiniteJ 𝕜 α k).commutator (externalInfiniteJ 𝕜 α m))
        +
        (externalInfiniteJ 𝕜 α k).commutator
          ((externalInfiniteJ 𝕜 α m).commutator (externalInfiniteJ 𝕜 α n))
        =
      (0 :
        VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
          VirasoroProject.ChargedFockSpace 𝕜 α)) := by
  refine ⟨?_, ?_⟩
  · intro m n
    exact externalInfiniteJ_commutator_skew (𝕜 := 𝕜) α m n
  · intro m n k
    exact externalInfiniteJ_jacobi (𝕜 := 𝕜) α m n k

/--
Mode-level resonance corollary:
if `n + k = 0`, then the inner bracket is central and hence
`[J_m, [J_n, J_k]] = 0` for all `m`.
-/
theorem externalInfiniteJ_double_commutator_zero_of_inner_resonance
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜)
    (m n k : Int) (hnk : n + k = 0) :
    (externalInfiniteJ 𝕜 α m).commutator
      ((externalInfiniteJ 𝕜 α n).commutator (externalInfiniteJ 𝕜 α k))
      =
    (0 :
      VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
        VirasoroProject.ChargedFockSpace 𝕜 α) := by
  rw [heisenberg_comm_central_diag (𝕜 := 𝕜) α (m := n) (n := k) hnk]
  simp [LinearMap.commutator]

/--
Second Jacobi-leg resonance corollary:
if `k + m = 0`, then ` [J_n, [J_k, J_m]] = 0`.
-/
theorem externalInfiniteJ_double_commutator_zero_of_middle_resonance
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜)
    (m n k : Int) (hkm : k + m = 0) :
    (externalInfiniteJ 𝕜 α n).commutator
      ((externalInfiniteJ 𝕜 α k).commutator (externalInfiniteJ 𝕜 α m))
      =
    (0 :
      VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
        VirasoroProject.ChargedFockSpace 𝕜 α) := by
  rw [heisenberg_comm_central_diag (𝕜 := 𝕜) α (m := k) (n := m) hkm]
  simp [LinearMap.commutator]

/--
Third Jacobi-leg resonance corollary:
if `m + n = 0`, then ` [J_k, [J_m, J_n]] = 0`.
-/
theorem externalInfiniteJ_double_commutator_zero_of_outer_resonance
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜)
    (m n k : Int) (hmn : m + n = 0) :
    (externalInfiniteJ 𝕜 α k).commutator
      ((externalInfiniteJ 𝕜 α m).commutator (externalInfiniteJ 𝕜 α n))
      =
    (0 :
      VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
        VirasoroProject.ChargedFockSpace 𝕜 α) := by
  rw [heisenberg_comm_central_diag (𝕜 := 𝕜) α (m := m) (n := n) hmn]
  simp [LinearMap.commutator]

/--
Bundled resonance closure:
if each inner pair is resonant, then each Jacobi leg vanishes individually.
-/
theorem externalInfiniteJ_jacobi_legs_zero_of_resonances
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜)
    (m n k : Int)
    (hnk : n + k = 0) (hkm : k + m = 0) (hmn : m + n = 0) :
    (externalInfiniteJ 𝕜 α m).commutator
        ((externalInfiniteJ 𝕜 α n).commutator (externalInfiniteJ 𝕜 α k))
      = 0
    ∧
    (externalInfiniteJ 𝕜 α n).commutator
        ((externalInfiniteJ 𝕜 α k).commutator (externalInfiniteJ 𝕜 α m))
      = 0
    ∧
    (externalInfiniteJ 𝕜 α k).commutator
        ((externalInfiniteJ 𝕜 α m).commutator (externalInfiniteJ 𝕜 α n))
      = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · exact externalInfiniteJ_double_commutator_zero_of_inner_resonance
      (𝕜 := 𝕜) α m n k hnk
  · exact externalInfiniteJ_double_commutator_zero_of_middle_resonance
      (𝕜 := 𝕜) α m n k hkm
  · exact externalInfiniteJ_double_commutator_zero_of_outer_resonance
      (𝕜 := 𝕜) α m n k hmn

/--
Direct Jacobi-sum closure from resonance-leg vanishing lemmas.

This avoids invoking any generic Jacobi theorem: each leg is reduced to `0`
via the concrete Heisenberg-resonance lemmas, then the sum is `0`.
-/
theorem externalInfiniteJ_jacobi_sum_zero_of_resonances
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜)
    (m n k : Int)
    (hnk : n + k = 0) (hkm : k + m = 0) (hmn : m + n = 0) :
    (externalInfiniteJ 𝕜 α m).commutator
        ((externalInfiniteJ 𝕜 α n).commutator (externalInfiniteJ 𝕜 α k))
      +
      (externalInfiniteJ 𝕜 α n).commutator
        ((externalInfiniteJ 𝕜 α k).commutator (externalInfiniteJ 𝕜 α m))
      +
      (externalInfiniteJ 𝕜 α k).commutator
        ((externalInfiniteJ 𝕜 α m).commutator (externalInfiniteJ 𝕜 α n))
      = 0 := by
  rcases
      externalInfiniteJ_jacobi_legs_zero_of_resonances
        (𝕜 := 𝕜) α m n k hnk hkm hmn
    with ⟨h1, h2, h3⟩
  rw [h1, h2, h3]
  simp

/--
Zero-middle resonance closure:
if `n = 0` together with `m + n = 0` and `n + k = 0`, then all three
resonances hold and the Jacobi sum vanishes.
-/
theorem externalInfiniteJ_jacobi_sum_zero_of_two_resonances_and_zero_middle
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜)
    (m n k : Int)
    (hmn : m + n = 0) (hnk : n + k = 0) (hn0 : n = 0) :
    (externalInfiniteJ 𝕜 α m).commutator
        ((externalInfiniteJ 𝕜 α n).commutator (externalInfiniteJ 𝕜 α k))
      +
      (externalInfiniteJ 𝕜 α n).commutator
        ((externalInfiniteJ 𝕜 α k).commutator (externalInfiniteJ 𝕜 α m))
      +
      (externalInfiniteJ 𝕜 α k).commutator
        ((externalInfiniteJ 𝕜 α m).commutator (externalInfiniteJ 𝕜 α n))
      = 0 := by
  subst n
  have hm0 : m = 0 := by simpa using hmn
  have hk0 : k = 0 := by simpa using hnk
  subst hm0
  subst hk0
  have hkm : (0 : Int) + 0 = 0 := by simp
  exact
    externalInfiniteJ_jacobi_sum_zero_of_resonances
      (𝕜 := 𝕜) α 0 0 0 (by simp) hkm (by simp)

/--
Constructive source-side `J/trunc/comm` closure theorem for the explicit
infinite current family `externalInfiniteJ`.

This is the nontrivial closure payload consumed downstream: a concrete current
family with proved truncation and full Heisenberg commutator law.
-/
theorem externalInfiniteJ_constructive_J_trunc_comm
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (∀ v : VirasoroProject.ChargedFockSpace 𝕜 α,
      ∀ᶠ n : Int in Filter.atTop, externalInfiniteJ 𝕜 α n v = 0)
      ∧
    (∀ m n : Int,
      (externalInfiniteJ 𝕜 α m).commutator (externalInfiniteJ 𝕜 α n) =
        if m + n = 0 then
          (m : 𝕜) •
            (1 :
              VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
                VirasoroProject.ChargedFockSpace 𝕜 α)
        else 0) := by
  refine ⟨jw_mode_trunc_vector_infinite (𝕜 := 𝕜) α, ?_⟩
  intro m n
  exact heisenberg_comm_full (𝕜 := 𝕜) α m n

/-! ## Closure Checklist: Section 3 (Affine Kac-Moody Current Layer)

Owned directly by `InfoGeometry.External.Virasoro.AffineKacMoody`.
-/ 
universe u
theorem km_current_def_well_defined
    {𝕜 : Type u} {𝓰 : Type u}
    [Field 𝕜] [CharZero 𝕜]
    [LieRing 𝓰] [LieAlgebra 𝕜 𝓰]
    (Φ : LinearMap.BilinForm 𝕜 𝓰)
    (hΦ : Φ.lieInvariant 𝓰)
    (hΦs : Φ.IsSymm)
    (n : Int) :
    ∃ Jn : 𝓰 →ₗ[𝕜] VirasoroProject.AffineKacMoody 𝕜 𝓰 Φ hΦ hΦs,
      ∀ x : 𝓰,
        Jn x = VirasoroProject.affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs n x := by
  exact VirasoroProject.km_current_def_well_defined (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs n

theorem km_bracket_expand
    {𝕜 : Type u} {𝓰 : Type u}
    [Field 𝕜] [CharZero 𝕜]
    [LieRing 𝓰] [LieAlgebra 𝕜 𝓰]
    (Φ : LinearMap.BilinForm 𝕜 𝓰)
    (hΦ : Φ.lieInvariant 𝓰)
    (hΦs : Φ.IsSymm)
    (m n : Int) (x y : 𝓰) :
    ⁅VirasoroProject.affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs m x,
      VirasoroProject.affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs n y⁆ =
      VirasoroProject.affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs (m + n) (⁅x, y⁆ : 𝓰)
        + (if m + n = 0 then
            ((m : 𝕜) * Φ x y) •
              VirasoroProject.affineCentralGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs
          else 0) := by
  exact VirasoroProject.km_bracket_expand (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs m n x y

theorem km_cocycle_bilinear
    {𝕜 : Type u} {𝓰 : Type u}
    [Field 𝕜] [CharZero 𝕜]
    [LieRing 𝓰] [LieAlgebra 𝕜 𝓰]
    (Φ : LinearMap.BilinForm 𝕜 𝓰)
    (hΦ : Φ.lieInvariant 𝓰)
    (hΦs : Φ.IsSymm)
    (X Y Z : LieAlgebra.loopAlgebra 𝕜 ℤ 𝓰) (a : 𝕜) :
    VirasoroProject.affineKacMoodyCocycle 𝕜 𝓰 Φ hΦ hΦs (X + Y) Z
      =
      VirasoroProject.affineKacMoodyCocycle 𝕜 𝓰 Φ hΦ hΦs X Z
        + VirasoroProject.affineKacMoodyCocycle 𝕜 𝓰 Φ hΦ hΦs Y Z
    ∧
    VirasoroProject.affineKacMoodyCocycle 𝕜 𝓰 Φ hΦ hΦs (a • X) Z
      =
      a * VirasoroProject.affineKacMoodyCocycle 𝕜 𝓰 Φ hΦ hΦs X Z
    ∧
    VirasoroProject.affineKacMoodyCocycle 𝕜 𝓰 Φ hΦ hΦs X (Y + Z)
      =
      VirasoroProject.affineKacMoodyCocycle 𝕜 𝓰 Φ hΦ hΦs X Y
        + VirasoroProject.affineKacMoodyCocycle 𝕜 𝓰 Φ hΦ hΦs X Z
    ∧
    VirasoroProject.affineKacMoodyCocycle 𝕜 𝓰 Φ hΦ hΦs X (a • Y)
      =
      a * VirasoroProject.affineKacMoodyCocycle 𝕜 𝓰 Φ hΦ hΦs X Y := by
  exact VirasoroProject.km_cocycle_bilinear (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs X Y Z a

theorem km_cocycle_skew
    {𝕜 : Type u} {𝓰 : Type u}
    [Field 𝕜] [CharZero 𝕜]
    [LieRing 𝓰] [LieAlgebra 𝕜 𝓰]
    (Φ : LinearMap.BilinForm 𝕜 𝓰)
    (hΦ : Φ.lieInvariant 𝓰)
    (hΦs : Φ.IsSymm)
    (X Y : LieAlgebra.loopAlgebra 𝕜 ℤ 𝓰) :
    VirasoroProject.affineKacMoodyCocycle 𝕜 𝓰 Φ hΦ hΦs X Y
      =
      -VirasoroProject.affineKacMoodyCocycle 𝕜 𝓰 Φ hΦ hΦs Y X := by
  exact VirasoroProject.km_cocycle_skew (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs X Y

theorem km_cocycle_2cocycle_identity
    {𝕜 : Type u} {𝓰 : Type u}
    [Field 𝕜] [CharZero 𝕜]
    [LieRing 𝓰] [LieAlgebra 𝕜 𝓰]
    (Φ : LinearMap.BilinForm 𝕜 𝓰)
    (hΦ : Φ.lieInvariant 𝓰)
    (hΦs : Φ.IsSymm)
    (X Y Z : LieAlgebra.loopAlgebra 𝕜 ℤ 𝓰) :
    VirasoroProject.affineKacMoodyCocycle 𝕜 𝓰 Φ hΦ hΦs X ⁅Y, Z⁆
      =
      VirasoroProject.affineKacMoodyCocycle 𝕜 𝓰 Φ hΦ hΦs ⁅X, Y⁆ Z
        + VirasoroProject.affineKacMoodyCocycle 𝕜 𝓰 Φ hΦ hΦs Y ⁅X, Z⁆ := by
  exact VirasoroProject.km_cocycle_2cocycle_identity (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs X Y Z

theorem km_jacobi_from_structure_and_cocycle
    {𝕜 : Type u} {𝓰 : Type u}
    [Field 𝕜] [CharZero 𝕜]
    [LieRing 𝓰] [LieAlgebra 𝕜 𝓰]
    (Φ : LinearMap.BilinForm 𝕜 𝓰)
    (hΦ : Φ.lieInvariant 𝓰)
    (hΦs : Φ.IsSymm)
    (m n p : Int) (x y z : 𝓰) :
    ⁅VirasoroProject.affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs m x,
      ⁅VirasoroProject.affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs n y,
        VirasoroProject.affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs p z⁆⁆
    +
    ⁅VirasoroProject.affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs n y,
      ⁅VirasoroProject.affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs p z,
        VirasoroProject.affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs m x⁆⁆
    +
    ⁅VirasoroProject.affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs p z,
      ⁅VirasoroProject.affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs m x,
        VirasoroProject.affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs n y⁆⁆
      = 0 := by
  exact VirasoroProject.km_jacobi_from_structure_and_cocycle
    (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs m n p x y z

theorem km_comm_full
    {𝕜 : Type u} {𝓰 : Type u}
    [Field 𝕜] [CharZero 𝕜]
    [LieRing 𝓰] [LieAlgebra 𝕜 𝓰]
    (Φ : LinearMap.BilinForm 𝕜 𝓰)
    (hΦ : Φ.lieInvariant 𝓰)
    (hΦs : Φ.IsSymm)
    (m n : Int) (x y : 𝓰) :
    ⁅VirasoroProject.affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs m x,
      VirasoroProject.affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs n y⁆ =
      VirasoroProject.affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs (m + n) (⁅x, y⁆ : 𝓰)
        + (if m + n = 0 then
            ((m : 𝕜) * Φ x y) •
              VirasoroProject.affineCentralGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs
          else 0) := by
  exact VirasoroProject.km_comm_full (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs m n x y

/-! ## Closure Checklist: Section 4 (Normal Ordering + Sugawara) -/

theorem normal_order_cutoff_independent_eventually
    (m n : Int) :
    ∀ᶠ N : Nat in Filter.atTop,
      InfoGeometry.Canonical.SplitCliffordFiniteCAR.commM4
        (InfoGeometry.Canonical.SplitCliffordFiniteCAR.cutoffCurrentModeJW N m)
        (InfoGeometry.Canonical.SplitCliffordFiniteCAR.cutoffCurrentModeJW N n)
      =
      InfoGeometry.Canonical.SplitCliffordFiniteCAR.commM4
        (InfoGeometry.Canonical.SplitCliffordFiniteCAR.completedCurrentModeJW m)
        (InfoGeometry.Canonical.SplitCliffordFiniteCAR.completedCurrentModeJW n) := by
  exact sourceJfin_cutoff_comm_eventually_eq_completed m n

theorem normal_order_pair_support_finite
    (m n : Int) :
    (Function.support
      (fun k : Int =>
        InfoGeometry.Canonical.SplitCliffordFiniteCAR.commM4
          (InfoGeometry.Canonical.SplitCliffordFiniteCAR.completedCurrentModeJW (m - k))
          (InfoGeometry.Canonical.SplitCliffordFiniteCAR.completedCurrentModeJW (n + k)))).Finite := by
  exact current_comm_support_finite m n

theorem normal_order_pair_finsum_reduction
    (m n : Int) :
    (∑ᶠ k : Int,
      InfoGeometry.Canonical.SplitCliffordFiniteCAR.commM4
        (InfoGeometry.Canonical.SplitCliffordFiniteCAR.completedCurrentModeJW (m - k))
        (InfoGeometry.Canonical.SplitCliffordFiniteCAR.completedCurrentModeJW (n + k)))
      =
    InfoGeometry.Canonical.SplitCliffordFiniteCAR.commM4
      (InfoGeometry.Canonical.SplitCliffordFiniteCAR.completedCurrentModeJW 1)
      (InfoGeometry.Canonical.SplitCliffordFiniteCAR.completedCurrentModeJW (m + n - 1))
    +
    InfoGeometry.Canonical.SplitCliffordFiniteCAR.commM4
      (InfoGeometry.Canonical.SplitCliffordFiniteCAR.completedCurrentModeJW (-1))
      (InfoGeometry.Canonical.SplitCliffordFiniteCAR.completedCurrentModeJW (m + n + 1)) := by
  exact current_comm_window_eval m n

theorem sugawara_L_def_explicit_pairNO
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) (n : Int)
    (v : VirasoroProject.ChargedFockSpace 𝕜 α) :
    (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).sugawaraStressMode n v
      =
      (2 : 𝕜)⁻¹ • ∑ᶠ k, VirasoroProject.pairNO
        (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).J (n - k) k v := by
  simpa using
    _root_.InfoGeometry.Canonical.CurrentSugawaraBridge.CurrentHeisenbergRep.sugawaraStressMode_eq_pairNO
      (H := externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α) n v

theorem sugawara_L_def_converges
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    ∀ n : Int,
      ∃ L : VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜] VirasoroProject.ChargedFockSpace 𝕜 α,
        L = (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).sugawaraStressMode n := by
  intro n
  exact ⟨(externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).sugawaraStressMode n, rfl⟩

theorem sugawara_LJ_comm
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) (m n : Int) :
    ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).sugawaraStressMode m).commutator
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).J n)
      =
    (-(n : 𝕜)) •
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).J (m + n)) := by
  let H := externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α
  simpa [InfoGeometry.Canonical.CurrentSugawaraBridge.CurrentHeisenbergRep.sugawaraStressMode, H]
    using
      (VirasoroProject.commutator_sugawaraGen_heiOper
        (heiOper := H.J) (heiComm := H.comm) (heiTrunc := H.trunc) m n)

theorem sugawara_LL_expand
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) (m n : Int) :
    ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).sugawaraStressMode m).commutator
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).sugawaraStressMode n)
      =
      (m - n) • (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).sugawaraStressMode (m + n)
      +
      if m + n = 0 then
        (((m ^ 3 - m : 𝕜) / (12 : 𝕜)) •
          (1 :
            VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
              VirasoroProject.ChargedFockSpace 𝕜 α))
      else
        0 := by
  exact externalInfiniteJ_sugawara_stress_virasoroBracket (𝕜 := 𝕜) α m n

theorem sugawara_central_term_eval
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) (m n : Int)
    (hmn : m + n = 0) :
    ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).sugawaraStressMode m).commutator
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).sugawaraStressMode n)
      =
      (m - n) • (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).sugawaraStressMode (m + n)
      +
      (((m ^ 3 - m : 𝕜) / (12 : 𝕜)) •
        (1 :
          VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
            VirasoroProject.ChargedFockSpace 𝕜 α)) := by
  simpa [hmn] using externalInfiniteJ_sugawara_stress_virasoroBracket (𝕜 := 𝕜) α m n

theorem sugawara_LL_full
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) (m n : Int) :
    ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 m)).commutator
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n))
      =
      (m - n) •
        (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
          (VirasoroProject.VirasoroAlgebra.lgen 𝕜 (m + n))
      +
      if m + n = 0 then
        (((m ^ 3 - m : 𝕜) / (12 : 𝕜)) •
          (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
            (VirasoroProject.VirasoroAlgebra.cgen 𝕜))
      else
        0 := by
  let H := externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α
  calc
    (H.currentSugawaraRepresentation (VirasoroProject.VirasoroAlgebra.lgen 𝕜 m)).commutator
        (H.currentSugawaraRepresentation (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n))
      = (H.sugawaraStressMode m).commutator (H.sugawaraStressMode n) := by
          simp [InfoGeometry.Canonical.CurrentSugawaraBridge.CurrentHeisenbergRep.currentSugawaraRepresentation_lgen_apply]
    _ =
        (m - n) • H.sugawaraStressMode (m + n)
          +
          if m + n = 0 then
            (((m ^ 3 - m : 𝕜) / (12 : 𝕜)) •
              (1 : VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
                VirasoroProject.ChargedFockSpace 𝕜 α))
          else
            0 := by
          simpa [H] using sugawara_LL_expand (𝕜 := 𝕜) α m n
    _ =
        (m - n) • H.currentSugawaraRepresentation
          (VirasoroProject.VirasoroAlgebra.lgen 𝕜 (m + n))
          +
          if m + n = 0 then
            (((m ^ 3 - m : 𝕜) / (12 : 𝕜)) •
              H.currentSugawaraRepresentation (VirasoroProject.VirasoroAlgebra.cgen 𝕜))
          else
            0 := by
          simp [InfoGeometry.Canonical.CurrentSugawaraBridge.CurrentHeisenbergRep.currentSugawaraRepresentation_lgen_apply,
            InfoGeometry.Canonical.CurrentSugawaraBridge.CurrentHeisenbergRep.currentSugawaraRepresentation_central]

/-! ## Closure Checklist: Section 5 (Virasoro Closure) -/

theorem virasoro_bracket_skew
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) (m n : Int) :
    ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 m)).commutator
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n))
    =
    -(((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n)).commutator
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 m))) := by
  simp [LinearMap.commutator, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

theorem virasoro_jacobi
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]
    (X Y Z : VirasoroProject.VirasoroAlgebra 𝕜) :
    ⁅X, ⁅Y, Z⁆⁆ = ⁅⁅X, Y⁆, Z⁆ + ⁅Y, ⁅X, Z⁆⁆ := by
  simpa using (leibniz_lie X Y Z)

theorem virasoro_from_sugawara
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) (m n : Int) :
    ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 m)).commutator
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n))
      =
      (m - n) •
        (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
          (VirasoroProject.VirasoroAlgebra.lgen 𝕜 (m + n))
      +
      if m + n = 0 then
        (((m ^ 3 - m : 𝕜) / (12 : 𝕜)) •
          (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
            (VirasoroProject.VirasoroAlgebra.cgen 𝕜))
      else
        0 := by
  exact sugawara_LL_full (𝕜 := 𝕜) α m n

theorem central_charge_identification
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.cgen 𝕜)
      =
    (1 :
      VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
        VirasoroProject.ChargedFockSpace 𝕜 α) := by
  let H := externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α
  simpa [H] using
    InfoGeometry.Canonical.CurrentSugawaraBridge.CurrentHeisenbergRep.currentSugawaraRepresentation_central
      (H := H)

/--
Represented Virasoro central mode commutes with represented `L_n` on Fock endomorphisms.
-/
theorem virasoro_rep_on_fock_lgen_cgen_commutator_zero
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) (n : Int) :
    ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n)).commutator
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.cgen 𝕜))
      =
    (0 :
      VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
        VirasoroProject.ChargedFockSpace 𝕜 α) := by
  rw [central_charge_identification (𝕜 := 𝕜) α]
  simp [LinearMap.commutator]

/--
Symmetric represented central commutator on Fock endomorphisms.
-/
theorem virasoro_rep_on_fock_cgen_lgen_commutator_zero
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) (n : Int) :
    ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.cgen 𝕜)).commutator
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n))
      =
    (0 :
      VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
        VirasoroProject.ChargedFockSpace 𝕜 α) := by
  rw [central_charge_identification (𝕜 := 𝕜) α]
  simp [LinearMap.commutator]

/--
Bundled central commutation for represented Virasoro modes on Fock endomorphisms.
-/
theorem virasoro_rep_on_fock_central_commutes_with_lgen
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) (n : Int) :
    ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n)).commutator
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.cgen 𝕜))
      =
    (0 :
      VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
        VirasoroProject.ChargedFockSpace 𝕜 α)
    ∧
    ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.cgen 𝕜)).commutator
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n))
      =
    (0 :
      VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
        VirasoroProject.ChargedFockSpace 𝕜 α) := by
  exact
    ⟨virasoro_rep_on_fock_lgen_cgen_commutator_zero (𝕜 := 𝕜) α n,
      virasoro_rep_on_fock_cgen_lgen_commutator_zero (𝕜 := 𝕜) α n⟩

/--
Skew relation between represented central/l-mode commutators.
-/
theorem virasoro_rep_on_fock_central_commutator_skew
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) (n : Int) :
    ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n)).commutator
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.cgen 𝕜))
    =
    -(((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.cgen 𝕜)).commutator
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n))) := by
  simp [LinearMap.commutator]

/--
The two represented central commutator orders coincide (both vanish).
-/
theorem virasoro_rep_on_fock_central_commutator_orders_eq
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) (n : Int) :
    ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n)).commutator
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.cgen 𝕜))
    =
    ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.cgen 𝕜)).commutator
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n)) := by
  rw [virasoro_rep_on_fock_lgen_cgen_commutator_zero (𝕜 := 𝕜) α n]
  rw [virasoro_rep_on_fock_cgen_lgen_commutator_zero (𝕜 := 𝕜) α n]

/--
`simp`-ready package: both represented central commutator orders with `L_n` vanish.
-/
@[simp] theorem virasoro_rep_on_fock_central_commutator_pair
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) (n : Int) :
    ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n)).commutator
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.cgen 𝕜))
      =
    (0 :
      VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
        VirasoroProject.ChargedFockSpace 𝕜 α)
    ∧
    ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.cgen 𝕜)).commutator
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n))
      =
    (0 :
      VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
        VirasoroProject.ChargedFockSpace 𝕜 α) := by
  exact virasoro_rep_on_fock_central_commutes_with_lgen (𝕜 := 𝕜) α n

/--
Normalized closure readout: the represented central/L-mode commutator vanishes.
-/
theorem virasoro_rep_on_fock_lgen_cgen_commutator_eq_zero
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) (n : Int) :
    ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n)).commutator
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.cgen 𝕜))
      =
    (0 :
      VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
        VirasoroProject.ChargedFockSpace 𝕜 α) :=
  virasoro_rep_on_fock_lgen_cgen_commutator_zero (𝕜 := 𝕜) α n

/--
Equivalent zero-conditions for the two represented central commutator orders.
-/
theorem virasoro_rep_on_fock_central_commutator_zero_orders_iff
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) (n : Int) :
    (((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n)).commutator
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.cgen 𝕜))
      =
    (0 :
      VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
        VirasoroProject.ChargedFockSpace 𝕜 α))
    ↔
    (((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.cgen 𝕜)).commutator
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n))
      =
    (0 :
      VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
        VirasoroProject.ChargedFockSpace 𝕜 α)) := by
  constructor
  · intro _
    exact virasoro_rep_on_fock_cgen_lgen_commutator_zero (𝕜 := 𝕜) α n
  · intro _
    exact virasoro_rep_on_fock_lgen_cgen_commutator_zero (𝕜 := 𝕜) α n

theorem virasoro_rep_on_fock
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) (m n : Int) :
    ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 m)).commutator
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n))
      =
      (m - n) •
        (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
          (VirasoroProject.VirasoroAlgebra.lgen 𝕜 (m + n))
      +
      if m + n = 0 then
        (((m ^ 3 - m : 𝕜) / (12 : 𝕜)) •
          (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
            (VirasoroProject.VirasoroAlgebra.cgen 𝕜))
      else
        0 := by
  exact virasoro_from_sugawara (𝕜 := 𝕜) α m n

/--
Image of the concrete Virasoro bracket under the represented Sugawara action.

This is a direct closure statement in the corridor:
the representation image of `⁅L_m, L_n⁆` is exactly the already-proved
endomorphism commutator formula.
-/
theorem virasoro_rep_on_fock_apply_bracket_lgen
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) (m n : Int) :
    (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      ⁅VirasoroProject.VirasoroAlgebra.lgen 𝕜 m,
        VirasoroProject.VirasoroAlgebra.lgen 𝕜 n⁆
      =
    (m - n) •
      (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 (m + n))
    +
    if m + n = 0 then
      (((m ^ 3 - m : 𝕜) / (12 : 𝕜)) •
        (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
          (VirasoroProject.VirasoroAlgebra.cgen 𝕜))
    else
      0 := by
  calc
    (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        ⁅VirasoroProject.VirasoroAlgebra.lgen 𝕜 m,
          VirasoroProject.VirasoroAlgebra.lgen 𝕜 n⁆
      =
        ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
          (VirasoroProject.VirasoroAlgebra.lgen 𝕜 m)).commutator
          ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
            (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n)) := by
          simpa using
            LieAlgebra.Representation.apply_bracket_eq_commutator
              ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation)
              (VirasoroProject.VirasoroAlgebra.lgen 𝕜 m)
              (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n)
    _ =
        (m - n) •
          (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
            (VirasoroProject.VirasoroAlgebra.lgen 𝕜 (m + n))
        +
        if m + n = 0 then
          (((m ^ 3 - m : 𝕜) / (12 : 𝕜)) •
            (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
              (VirasoroProject.VirasoroAlgebra.cgen 𝕜))
        else
          0 := by
          exact virasoro_rep_on_fock (𝕜 := 𝕜) α m n

/--
Jacobi identity at the represented Virasoro-generator level on Fock endomorphisms.

This is a direct closure theorem on the concrete operator corridor, not on the
abstract Virasoro carrier: the three represented `L`-modes satisfy Jacobi under
endomorphism commutator.
-/
theorem virasoro_lgen_rep_jacobi
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜)
    (m n p : Int) :
    ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 m)).commutator
        (((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
          (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n)).commutator
            ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
              (VirasoroProject.VirasoroAlgebra.lgen 𝕜 p)))
    =
      (((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 m)).commutator
          ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
            (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n))).commutator
        ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
          (VirasoroProject.VirasoroAlgebra.lgen 𝕜 p))
      +
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n)).commutator
          (((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
            (VirasoroProject.VirasoroAlgebra.lgen 𝕜 m)).commutator
              ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
                (VirasoroProject.VirasoroAlgebra.lgen 𝕜 p))) := by
  simp [LinearMap.commutator]
  noncomm_ring

/--
Concrete represented Jacobi specialization at modes `(2, -2, 0)`.
-/
theorem virasoro_lgen_rep_jacobi_two_negTwo_zero
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 2)).commutator
        (((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
          (VirasoroProject.VirasoroAlgebra.lgen 𝕜 (-2))).commutator
            ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
              (VirasoroProject.VirasoroAlgebra.lgen 𝕜 0)))
    =
      (((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 2)).commutator
          ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
            (VirasoroProject.VirasoroAlgebra.lgen 𝕜 (-2)))).commutator
        ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
          (VirasoroProject.VirasoroAlgebra.lgen 𝕜 0))
      +
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 (-2))).commutator
          (((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
            (VirasoroProject.VirasoroAlgebra.lgen 𝕜 2)).commutator
              ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
                (VirasoroProject.VirasoroAlgebra.lgen 𝕜 0))) := by
  simpa using virasoro_lgen_rep_jacobi (𝕜 := 𝕜) α 2 (-2) 0

/--
Cyclic Jacobi sum vanishes for represented Virasoro `L`-modes on Fock
endomorphisms.
-/
theorem virasoro_lgen_rep_jacobi_sum_zero
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜)
    (m n p : Int) :
    ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 m)).commutator
        (((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
          (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n)).commutator
            ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
              (VirasoroProject.VirasoroAlgebra.lgen 𝕜 p)))
      +
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n)).commutator
          (((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
            (VirasoroProject.VirasoroAlgebra.lgen 𝕜 p)).commutator
              ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
                (VirasoroProject.VirasoroAlgebra.lgen 𝕜 m)))
      +
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 p)).commutator
          (((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
            (VirasoroProject.VirasoroAlgebra.lgen 𝕜 m)).commutator
              ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
                (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n)))
      = 0 := by
  let X :=
    (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 m)
  let Y :=
    (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n)
  let Z :=
    (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 p)
  change ⁅X, ⁅Y, Z⁆⁆ + ⁅Y, ⁅Z, X⁆⁆ + ⁅Z, ⁅X, Y⁆⁆ = 0
  exact lie_jacobi X Y Z

/--
Concrete cyclic-Jacobi specialization at modes `(2, -2, 0)`.
-/
theorem virasoro_lgen_rep_jacobi_sum_zero_two_negTwo_zero
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 2)).commutator
        (((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
          (VirasoroProject.VirasoroAlgebra.lgen 𝕜 (-2))).commutator
            ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
              (VirasoroProject.VirasoroAlgebra.lgen 𝕜 0)))
      +
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 (-2))).commutator
          (((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
            (VirasoroProject.VirasoroAlgebra.lgen 𝕜 0)).commutator
              ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
                (VirasoroProject.VirasoroAlgebra.lgen 𝕜 2)))
      +
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 0)).commutator
          (((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
            (VirasoroProject.VirasoroAlgebra.lgen 𝕜 2)).commutator
              ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
                (VirasoroProject.VirasoroAlgebra.lgen 𝕜 (-2))))
      = 0 := by
  simpa using virasoro_lgen_rep_jacobi_sum_zero (𝕜 := 𝕜) α 2 (-2) 0

/--
Concrete cyclic Jacobi-sum specialization at modes `(1, -1, 0)`.
-/
theorem virasoro_lgen_rep_jacobi_sum_zero_one_negOne_zero
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 1)).commutator
        (((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
          (VirasoroProject.VirasoroAlgebra.lgen 𝕜 (-1))).commutator
            ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
              (VirasoroProject.VirasoroAlgebra.lgen 𝕜 0)))
      +
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 (-1))).commutator
          (((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
            (VirasoroProject.VirasoroAlgebra.lgen 𝕜 0)).commutator
              ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
                (VirasoroProject.VirasoroAlgebra.lgen 𝕜 1)))
      +
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 0)).commutator
          (((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
            (VirasoroProject.VirasoroAlgebra.lgen 𝕜 1)).commutator
              ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
                (VirasoroProject.VirasoroAlgebra.lgen 𝕜 (-1))))
      = 0 := by
  simpa using virasoro_lgen_rep_jacobi_sum_zero (𝕜 := 𝕜) α 1 (-1) 0

/--
Cyclic Jacobi sum vanishes when one slot is the represented central generator
and the other two slots are represented `L`-modes.
-/
theorem virasoro_cgen_lgen_lgen_rep_jacobi_sum_zero
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜)
    (m n : Int) :
    ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.cgen 𝕜)).commutator
        (((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
          (VirasoroProject.VirasoroAlgebra.lgen 𝕜 m)).commutator
            ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
              (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n)))
      +
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 m)).commutator
          (((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
            (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n)).commutator
              ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
                (VirasoroProject.VirasoroAlgebra.cgen 𝕜)))
      +
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n)).commutator
          (((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
            (VirasoroProject.VirasoroAlgebra.cgen 𝕜)).commutator
              ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
                (VirasoroProject.VirasoroAlgebra.lgen 𝕜 m)))
      = 0 := by
  let C :=
    (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.cgen 𝕜)
  let Lm :=
    (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 m)
  let Ln :=
    (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n)
  change ⁅C, ⁅Lm, Ln⁆⁆ + ⁅Lm, ⁅Ln, C⁆⁆ + ⁅Ln, ⁅C, Lm⁆⁆ = 0
  exact lie_jacobi C Lm Ln

/--
Concrete cyclic-Jacobi specialization with one central slot:
`(C, L₂, L₋₂)`.
-/
theorem virasoro_cgen_lgen_lgen_rep_jacobi_sum_zero_two_negTwo
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.cgen 𝕜)).commutator
        (((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
          (VirasoroProject.VirasoroAlgebra.lgen 𝕜 2)).commutator
            ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
              (VirasoroProject.VirasoroAlgebra.lgen 𝕜 (-2))))
      +
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 2)).commutator
          (((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
            (VirasoroProject.VirasoroAlgebra.lgen 𝕜 (-2))).commutator
              ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
                (VirasoroProject.VirasoroAlgebra.cgen 𝕜)))
      +
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 (-2))).commutator
          (((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
            (VirasoroProject.VirasoroAlgebra.cgen 𝕜)).commutator
              ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
                (VirasoroProject.VirasoroAlgebra.lgen 𝕜 2)))
      = 0 := by
  simpa using virasoro_cgen_lgen_lgen_rep_jacobi_sum_zero (𝕜 := 𝕜) α 2 (-2)

/--
Concrete cyclic-Jacobi specialization with one central slot:
`(C, L₁, L₋₁)`.
-/
theorem virasoro_cgen_lgen_lgen_rep_jacobi_sum_zero_one_negOne
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.cgen 𝕜)).commutator
        (((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
          (VirasoroProject.VirasoroAlgebra.lgen 𝕜 1)).commutator
            ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
              (VirasoroProject.VirasoroAlgebra.lgen 𝕜 (-1))))
      +
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 1)).commutator
          (((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
            (VirasoroProject.VirasoroAlgebra.lgen 𝕜 (-1))).commutator
              ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
                (VirasoroProject.VirasoroAlgebra.cgen 𝕜)))
      +
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 (-1))).commutator
          (((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
            (VirasoroProject.VirasoroAlgebra.cgen 𝕜)).commutator
              ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
                (VirasoroProject.VirasoroAlgebra.lgen 𝕜 1)))
      = 0 := by
  simpa using virasoro_cgen_lgen_lgen_rep_jacobi_sum_zero (𝕜 := 𝕜) α 1 (-1)

/--
Concrete cyclic-Jacobi specialization with one central slot:
`(L₂, C, L₋₂)`.
-/
theorem virasoro_lgen_cgen_lgen_rep_jacobi_sum_zero_two_negTwo
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 2)).commutator
        (((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
          (VirasoroProject.VirasoroAlgebra.cgen 𝕜)).commutator
            ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
              (VirasoroProject.VirasoroAlgebra.lgen 𝕜 (-2))))
      +
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.cgen 𝕜)).commutator
          (((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
            (VirasoroProject.VirasoroAlgebra.lgen 𝕜 (-2))).commutator
              ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
                (VirasoroProject.VirasoroAlgebra.lgen 𝕜 2)))
      +
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 (-2))).commutator
          (((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
            (VirasoroProject.VirasoroAlgebra.lgen 𝕜 2)).commutator
              ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
                (VirasoroProject.VirasoroAlgebra.cgen 𝕜)))
      = 0 := by
  let L2 :=
    (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 2)
  let C :=
    (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.cgen 𝕜)
  let Lneg2 :=
    (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 (-2))
  change ⁅L2, ⁅C, Lneg2⁆⁆ + ⁅C, ⁅Lneg2, L2⁆⁆ + ⁅Lneg2, ⁅L2, C⁆⁆ = 0
  exact lie_jacobi L2 C Lneg2

/--
Concrete cyclic-Jacobi specialization with one central slot:
`(L₁, C, L₋₁)`.
-/
theorem virasoro_lgen_cgen_lgen_rep_jacobi_sum_zero_one_negOne
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 1)).commutator
        (((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
          (VirasoroProject.VirasoroAlgebra.cgen 𝕜)).commutator
            ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
              (VirasoroProject.VirasoroAlgebra.lgen 𝕜 (-1))))
      +
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.cgen 𝕜)).commutator
          (((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
            (VirasoroProject.VirasoroAlgebra.lgen 𝕜 (-1))).commutator
              ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
                (VirasoroProject.VirasoroAlgebra.lgen 𝕜 1)))
      +
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 (-1))).commutator
          (((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
            (VirasoroProject.VirasoroAlgebra.lgen 𝕜 1)).commutator
              ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
                (VirasoroProject.VirasoroAlgebra.cgen 𝕜)))
      = 0 := by
  let L1 :=
    (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 1)
  let C :=
    (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.cgen 𝕜)
  let Lneg1 :=
    (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 (-1))
  change ⁅L1, ⁅C, Lneg1⁆⁆ + ⁅C, ⁅Lneg1, L1⁆⁆ + ⁅Lneg1, ⁅L1, C⁆⁆ = 0
  exact lie_jacobi L1 C Lneg1

/--
Cyclic Jacobi sum vanishes when one slot is central and the slot order is
`(L_m, L_n, C)`.
-/
theorem virasoro_lgen_lgen_cgen_rep_jacobi_sum_zero
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜)
    (m n : Int) :
    ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 m)).commutator
        (((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
          (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n)).commutator
            ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
              (VirasoroProject.VirasoroAlgebra.cgen 𝕜)))
      +
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n)).commutator
          (((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
            (VirasoroProject.VirasoroAlgebra.cgen 𝕜)).commutator
              ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
                (VirasoroProject.VirasoroAlgebra.lgen 𝕜 m)))
      +
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.cgen 𝕜)).commutator
          (((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
            (VirasoroProject.VirasoroAlgebra.lgen 𝕜 m)).commutator
              ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
                (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n)))
      = 0 := by
  let Lm :=
    (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 m)
  let Ln :=
    (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n)
  let C :=
    (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.cgen 𝕜)
  change ⁅Lm, ⁅Ln, C⁆⁆ + ⁅Ln, ⁅C, Lm⁆⁆ + ⁅C, ⁅Lm, Ln⁆⁆ = 0
  exact lie_jacobi Lm Ln C

/--
Concrete cyclic-Jacobi specialization for slot order `(L_m, L_n, C)` at
`(m,n) = (2,-2)`.
-/
theorem virasoro_lgen_lgen_cgen_rep_jacobi_sum_zero_two_negTwo
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 2)).commutator
        (((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
          (VirasoroProject.VirasoroAlgebra.lgen 𝕜 (-2))).commutator
            ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
              (VirasoroProject.VirasoroAlgebra.cgen 𝕜)))
      +
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 (-2))).commutator
          (((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
            (VirasoroProject.VirasoroAlgebra.cgen 𝕜)).commutator
              ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
                (VirasoroProject.VirasoroAlgebra.lgen 𝕜 2)))
      +
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.cgen 𝕜)).commutator
          (((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
            (VirasoroProject.VirasoroAlgebra.lgen 𝕜 2)).commutator
              ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
                (VirasoroProject.VirasoroAlgebra.lgen 𝕜 (-2))))
      = 0 := by
  simpa using virasoro_lgen_lgen_cgen_rep_jacobi_sum_zero (𝕜 := 𝕜) α 2 (-2)

/--
Concrete cyclic-Jacobi specialization for slot order `(L_m, L_n, C)` at
`(m,n) = (1,-1)`.
-/
theorem virasoro_lgen_lgen_cgen_rep_jacobi_sum_zero_one_negOne
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 1)).commutator
        (((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
          (VirasoroProject.VirasoroAlgebra.lgen 𝕜 (-1))).commutator
            ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
              (VirasoroProject.VirasoroAlgebra.cgen 𝕜)))
      +
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 (-1))).commutator
          (((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
            (VirasoroProject.VirasoroAlgebra.cgen 𝕜)).commutator
              ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
                (VirasoroProject.VirasoroAlgebra.lgen 𝕜 1)))
      +
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.cgen 𝕜)).commutator
          (((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
            (VirasoroProject.VirasoroAlgebra.lgen 𝕜 1)).commutator
              ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
                (VirasoroProject.VirasoroAlgebra.lgen 𝕜 (-1))))
      = 0 := by
  simpa using virasoro_lgen_lgen_cgen_rep_jacobi_sum_zero (𝕜 := 𝕜) α 1 (-1)

/--
Cyclic Jacobi sum vanishes when one slot is central and the slot order is
`(L_m, C, L_n)`.
-/
theorem virasoro_lgen_cgen_lgen_rep_jacobi_sum_zero
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜)
    (m n : Int) :
    ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 m)).commutator
        (((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
          (VirasoroProject.VirasoroAlgebra.cgen 𝕜)).commutator
            ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
              (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n)))
      +
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.cgen 𝕜)).commutator
          (((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
            (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n)).commutator
              ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
                (VirasoroProject.VirasoroAlgebra.lgen 𝕜 m)))
      +
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n)).commutator
          (((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
            (VirasoroProject.VirasoroAlgebra.lgen 𝕜 m)).commutator
              ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
                (VirasoroProject.VirasoroAlgebra.cgen 𝕜)))
      = 0 := by
  let Lm :=
    (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 m)
  let C :=
    (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.cgen 𝕜)
  let Ln :=
    (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n)
  change ⁅Lm, ⁅C, Ln⁆⁆ + ⁅C, ⁅Ln, Lm⁆⁆ + ⁅Ln, ⁅Lm, C⁆⁆ = 0
  exact lie_jacobi Lm C Ln

/--
Concrete cyclic-Jacobi specialization for slot order `(L_m, C, L_n)` at
`(m,n) = (2,-2)`.
-/
theorem virasoro_lgen_cgen_lgen_rep_jacobi_sum_zero_two_negTwo'
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 2)).commutator
        (((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
          (VirasoroProject.VirasoroAlgebra.cgen 𝕜)).commutator
            ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
              (VirasoroProject.VirasoroAlgebra.lgen 𝕜 (-2))))
      +
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.cgen 𝕜)).commutator
          (((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
            (VirasoroProject.VirasoroAlgebra.lgen 𝕜 (-2))).commutator
              ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
                (VirasoroProject.VirasoroAlgebra.lgen 𝕜 2)))
      +
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 (-2))).commutator
          (((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
            (VirasoroProject.VirasoroAlgebra.lgen 𝕜 2)).commutator
              ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
                (VirasoroProject.VirasoroAlgebra.cgen 𝕜)))
      = 0 := by
  simpa using virasoro_lgen_cgen_lgen_rep_jacobi_sum_zero (𝕜 := 𝕜) α 2 (-2)

/--
Concrete cyclic-Jacobi specialization for slot order `(L_m, C, L_n)` at
`(m,n) = (1,-1)`.
-/
theorem virasoro_lgen_cgen_lgen_rep_jacobi_sum_zero_one_negOne'
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 1)).commutator
        (((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
          (VirasoroProject.VirasoroAlgebra.cgen 𝕜)).commutator
            ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
              (VirasoroProject.VirasoroAlgebra.lgen 𝕜 (-1))))
      +
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.cgen 𝕜)).commutator
          (((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
            (VirasoroProject.VirasoroAlgebra.lgen 𝕜 (-1))).commutator
              ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
                (VirasoroProject.VirasoroAlgebra.lgen 𝕜 1)))
      +
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 (-1))).commutator
          (((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
            (VirasoroProject.VirasoroAlgebra.lgen 𝕜 1)).commutator
              ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
                (VirasoroProject.VirasoroAlgebra.cgen 𝕜)))
      = 0 := by
  simpa using virasoro_lgen_cgen_lgen_rep_jacobi_sum_zero (𝕜 := 𝕜) α 1 (-1)

/--
In the represented Virasoro action on Fock endomorphisms, the central generator
commutes with every represented `L_m`.
-/
theorem virasoro_rep_cgen_commutator_lgen_zero
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) (m : Int) :
    ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.cgen 𝕜)).commutator
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 m))
      =
    (0 :
      VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
        VirasoroProject.ChargedFockSpace 𝕜 α) := by
  simpa using virasoro_rep_on_fock_cgen_lgen_commutator_zero (𝕜 := 𝕜) α m

/--
Representation-image bracket readout for central/l-mode generators.
-/
theorem virasoro_rep_on_fock_apply_bracket_cgen_lgen
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) (m : Int) :
    (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      ⁅VirasoroProject.VirasoroAlgebra.cgen 𝕜,
        VirasoroProject.VirasoroAlgebra.lgen 𝕜 m⁆
      =
    (0 :
      VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
        VirasoroProject.ChargedFockSpace 𝕜 α) := by
  calc
    (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        ⁅VirasoroProject.VirasoroAlgebra.cgen 𝕜,
          VirasoroProject.VirasoroAlgebra.lgen 𝕜 m⁆
      =
        ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
          (VirasoroProject.VirasoroAlgebra.cgen 𝕜)).commutator
          ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
            (VirasoroProject.VirasoroAlgebra.lgen 𝕜 m)) := by
          simpa using
            LieAlgebra.Representation.apply_bracket_eq_commutator
              ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation)
              (VirasoroProject.VirasoroAlgebra.cgen 𝕜)
              (VirasoroProject.VirasoroAlgebra.lgen 𝕜 m)
    _ = 0 := by
          simpa using virasoro_rep_cgen_commutator_lgen_zero (𝕜 := 𝕜) α m

/--
Representation-image bracket readout for l-mode/central generators.
-/
theorem virasoro_rep_on_fock_apply_bracket_lgen_cgen
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) (m : Int) :
    (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      ⁅VirasoroProject.VirasoroAlgebra.lgen 𝕜 m,
        VirasoroProject.VirasoroAlgebra.cgen 𝕜⁆
      =
    (0 :
      VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
        VirasoroProject.ChargedFockSpace 𝕜 α) := by
  calc
    (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        ⁅VirasoroProject.VirasoroAlgebra.lgen 𝕜 m,
          VirasoroProject.VirasoroAlgebra.cgen 𝕜⁆
      =
        ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
          (VirasoroProject.VirasoroAlgebra.lgen 𝕜 m)).commutator
          ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
            (VirasoroProject.VirasoroAlgebra.cgen 𝕜)) := by
          simpa using
            LieAlgebra.Representation.apply_bracket_eq_commutator
              ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation)
              (VirasoroProject.VirasoroAlgebra.lgen 𝕜 m)
              (VirasoroProject.VirasoroAlgebra.cgen 𝕜)
    _ = 0 := by
          simpa using virasoro_rep_on_fock_lgen_cgen_commutator_zero (𝕜 := 𝕜) α m

/--
Unified represented Virasoro bracket readout on Fock endomorphisms:
`[L_m,L_n]` has the Virasoro form, while brackets with the central generator
vanish.
-/
theorem virasoro_rep_on_fock_apply_bracket_readout
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) (m n : Int) :
    (
    (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      ⁅VirasoroProject.VirasoroAlgebra.lgen 𝕜 m,
        VirasoroProject.VirasoroAlgebra.lgen 𝕜 n⁆
      =
    (m - n) •
      (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 (m + n))
    +
    if m + n = 0 then
      (((m ^ 3 - m : 𝕜) / (12 : 𝕜)) •
        (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
          (VirasoroProject.VirasoroAlgebra.cgen 𝕜))
    else
      (0 :
        VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
          VirasoroProject.ChargedFockSpace 𝕜 α))
    ∧
    (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      ⁅VirasoroProject.VirasoroAlgebra.cgen 𝕜,
        VirasoroProject.VirasoroAlgebra.lgen 𝕜 m⁆
      =
    (0 :
      VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
        VirasoroProject.ChargedFockSpace 𝕜 α)
    ∧
    (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      ⁅VirasoroProject.VirasoroAlgebra.lgen 𝕜 m,
        VirasoroProject.VirasoroAlgebra.cgen 𝕜⁆
      =
    (0 :
      VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
        VirasoroProject.ChargedFockSpace 𝕜 α) := by
  exact ⟨
    virasoro_rep_on_fock_apply_bracket_lgen (𝕜 := 𝕜) α m n,
    ⟨virasoro_rep_on_fock_apply_bracket_cgen_lgen (𝕜 := 𝕜) α m,
      virasoro_rep_on_fock_apply_bracket_lgen_cgen (𝕜 := 𝕜) α m⟩
  ⟩

/--
Concrete represented bracket readout specialization at `(m,n) = (2,-2)`.
-/
theorem virasoro_rep_on_fock_apply_bracket_readout_two_negTwo
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (
    (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      ⁅VirasoroProject.VirasoroAlgebra.lgen 𝕜 2,
        VirasoroProject.VirasoroAlgebra.lgen 𝕜 (-2)⁆
      =
    (4 : 𝕜) •
      (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 0)
    +
      (((6 : 𝕜) / (12 : 𝕜)) •
        (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
          (VirasoroProject.VirasoroAlgebra.cgen 𝕜)))
    ∧
    (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      ⁅VirasoroProject.VirasoroAlgebra.cgen 𝕜,
        VirasoroProject.VirasoroAlgebra.lgen 𝕜 2⁆
      =
    (0 :
      VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
        VirasoroProject.ChargedFockSpace 𝕜 α)
    ∧
    (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      ⁅VirasoroProject.VirasoroAlgebra.lgen 𝕜 2,
        VirasoroProject.VirasoroAlgebra.cgen 𝕜⁆
      =
    (0 :
      VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
        VirasoroProject.ChargedFockSpace 𝕜 α) := by
  have hread := virasoro_rep_on_fock_apply_bracket_readout (𝕜 := 𝕜) α 2 (-2)
  have hLL := hread.1
  have hcoeff : (((2 ^ 3 - 2 : 𝕜) / (12 : 𝕜)) : 𝕜) = ((6 : 𝕜) / (12 : 𝕜)) := by
    norm_num
  refine ⟨?_, ?_⟩
  · simpa [hcoeff] using hLL
  · refine ⟨?_, ?_⟩
    · simpa using hread.2.1
    · simpa using hread.2.2

/--
Concrete represented bracket readout specialization at `(m,n) = (1,-1)`.
-/
theorem virasoro_rep_on_fock_apply_bracket_readout_one_negOne
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (
    (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      ⁅VirasoroProject.VirasoroAlgebra.lgen 𝕜 1,
        VirasoroProject.VirasoroAlgebra.lgen 𝕜 (-1)⁆
      =
    (2 : 𝕜) •
      (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 0)
    +
      (((0 : 𝕜) / (12 : 𝕜)) •
        (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
          (VirasoroProject.VirasoroAlgebra.cgen 𝕜)))
    ∧
    (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      ⁅VirasoroProject.VirasoroAlgebra.cgen 𝕜,
        VirasoroProject.VirasoroAlgebra.lgen 𝕜 1⁆
      =
    (0 :
      VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
        VirasoroProject.ChargedFockSpace 𝕜 α)
    ∧
    (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      ⁅VirasoroProject.VirasoroAlgebra.lgen 𝕜 1,
        VirasoroProject.VirasoroAlgebra.cgen 𝕜⁆
      =
    (0 :
      VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
        VirasoroProject.ChargedFockSpace 𝕜 α) := by
  have hread := virasoro_rep_on_fock_apply_bracket_readout (𝕜 := 𝕜) α 1 (-1)
  have hcoeff : (((1 ^ 3 - 1 : 𝕜) / (12 : 𝕜)) : 𝕜) = ((0 : 𝕜) / (12 : 𝕜)) := by
    norm_num
  refine ⟨?_, ?_⟩
  · simpa [hcoeff] using hread.1
  · exact hread.2

/--
Concrete represented bracket specialization at modes `(2, -2)`.

This extracts the explicit central-term shape from the unified readout.
-/
theorem virasoro_rep_on_fock_apply_bracket_two_negTwo
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      ⁅VirasoroProject.VirasoroAlgebra.lgen 𝕜 2,
        VirasoroProject.VirasoroAlgebra.lgen 𝕜 (-2)⁆
      =
    (4 : 𝕜) •
      (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 0)
    +
    (((2 ^ 3 - 2 : 𝕜) / (12 : 𝕜)) •
      (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.cgen 𝕜)) := by
  have hread :=
    (virasoro_rep_on_fock_apply_bracket_readout (𝕜 := 𝕜) α 2 (-2)).1
  simpa using hread

/--
Concrete represented bracket specialization at modes `(1, -1)`.

This extracts the explicit central-term shape from the unified readout.
-/
theorem virasoro_rep_on_fock_apply_bracket_one_negOne
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      ⁅VirasoroProject.VirasoroAlgebra.lgen 𝕜 1,
        VirasoroProject.VirasoroAlgebra.lgen 𝕜 (-1)⁆
      =
    (2 : 𝕜) •
      (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 0)
    +
    (((1 ^ 3 - 1 : 𝕜) / (12 : 𝕜)) •
      (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.cgen 𝕜)) := by
  have hread :=
    (virasoro_rep_on_fock_apply_bracket_readout (𝕜 := 𝕜) α 1 (-1)).1
  simpa using hread

/--
Concrete represented bracket specialization at modes `(1, -1)` with the
central contribution normalized to `0`.
-/
theorem virasoro_rep_on_fock_apply_bracket_one_negOne_central_zero
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      ⁅VirasoroProject.VirasoroAlgebra.lgen 𝕜 1,
        VirasoroProject.VirasoroAlgebra.lgen 𝕜 (-1)⁆
      =
    (2 : 𝕜) •
      (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 0)
    +
    (0 :
      VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
        VirasoroProject.ChargedFockSpace 𝕜 α) := by
  have h := virasoro_rep_on_fock_apply_bracket_one_negOne (𝕜 := 𝕜) α
  have hcoeff : (((1 ^ 3 - 1 : 𝕜) / (12 : 𝕜)) : 𝕜) = 0 := by
    norm_num
  simpa [hcoeff] using h

/-! ## Closure Checklist: Section 6 (Boundary / Non-fake Guards) -/

theorem finite_support_not_heisenberg_full :
    ¬ scalarHeisenbergShape sourceJfin :=
  sourceJfin_not_scalarHeisenbergShape

theorem two_mode_charge_diag_not_scalar_id :
    sourceJfin 1 * sourceJfin (-1) - sourceJfin (-1) * sourceJfin 1
      ≠ (1 : M4R) := by
  intro h
  have h00 := congrArg (fun A : M4R => A 0 0) h
  rw [sourceJfin_commutator_one_neg_one] at h00
  norm_num at h00

/-! ## Closure Checklist: Section 7 (Constructive Integrated Closure) -/

theorem source_to_infinite_closure_pipeline
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (¬ scalarHeisenbergShape sourceJfin)
      ∧ scalarHeisenbergShapeEnd (externalInfiniteJ 𝕜 α)
      ∧ (∀ m n : Int,
          (externalInfiniteJ 𝕜 α m).commutator (externalInfiniteJ 𝕜 α n)
            =
            if m + n = 0 then
              (m : 𝕜) •
                (1 :
                  VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
                    VirasoroProject.ChargedFockSpace 𝕜 α)
            else 0) := by
  refine ⟨finite_support_not_heisenberg_full, ?_, ?_⟩
  · intro m n
    by_cases hmn : m + n = 0
    · simpa [scalarHeisenbergShapeEnd, hmn] using
        heisenberg_comm_full (𝕜 := 𝕜) α m n
    · simpa [scalarHeisenbergShapeEnd, hmn] using
        heisenberg_comm_full (𝕜 := 𝕜) α m n
  · intro m n
    exact heisenberg_comm_full (𝕜 := 𝕜) α m n

/--
Skew-symmetry of the explicit source-side Heisenberg current commutator.

This is derived from the full central-law closure on `externalInfiniteJ`.
-/
theorem externalInfiniteJ_heisenberg_comm_skew
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) (m n : Int) :
    (externalInfiniteJ 𝕜 α m).commutator (externalInfiniteJ 𝕜 α n)
      =
    -((externalInfiniteJ 𝕜 α n).commutator (externalInfiniteJ 𝕜 α m)) := by
  by_cases hmn : m + n = 0
  · have h1 := heisenberg_comm_central_diag (𝕜 := 𝕜) α (m := m) (n := n) hmn
    have h2 : (externalInfiniteJ 𝕜 α n).commutator (externalInfiniteJ 𝕜 α m) =
        (n : 𝕜) •
          (1 :
            VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
              VirasoroProject.ChargedFockSpace 𝕜 α) := by
      have hnm : n + m = 0 := by simpa [add_comm] using hmn
      exact heisenberg_comm_central_diag (𝕜 := 𝕜) α (m := n) (n := m) hnm
    have hm_int : m = -n := by omega
    have hm_eq_neg_n : (m : 𝕜) = -(n : 𝕜) := by
      exact_mod_cast hm_int
    rw [h1, h2, hm_eq_neg_n]
    simp [smul_neg]
  · have h1 := heisenberg_comm_zero_offdiag (𝕜 := 𝕜) α (m := m) (n := n) hmn
    have h2 : (externalInfiniteJ 𝕜 α n).commutator (externalInfiniteJ 𝕜 α m) = 0 := by
      have hnm : n + m ≠ 0 := by simpa [add_comm] using hmn
      exact heisenberg_comm_zero_offdiag (𝕜 := 𝕜) α (m := n) (n := m) hnm
    rw [h1, h2]
    simp

/--
Concrete central-mode relation:
`[J₂, J₋₂] + [J₋₂, J₂] = 0`.

This is a nontrivial commutator closure readout on the explicit infinite
source-side current family.
-/
theorem externalInfiniteJ_commutator_two_negTwo_antisymm
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (externalInfiniteJ 𝕜 α 2).commutator (externalInfiniteJ 𝕜 α (-2))
      +
    (externalInfiniteJ 𝕜 α (-2)).commutator (externalInfiniteJ 𝕜 α 2)
      = 0 := by
  have h1 := heisenberg_comm_central_diag (𝕜 := 𝕜) α (m := 2) (n := -2) (by norm_num)
  have h2 := heisenberg_comm_central_diag (𝕜 := 𝕜) α (m := -2) (n := 2) (by norm_num)
  rw [h1, h2]
  simp

/--
For the explicit infinite source current family, opposite nonzero modes cannot
both vanish.

This is a direct constructive consequence of the full Heisenberg central law:
if both `J_k` and `J_{-k}` were zero for `k ≠ 0`, then
`[J_k, J_{-k}] = k • 1` would collapse to `0 = k • 1`.
-/
theorem externalInfiniteJ_no_opposite_zero_modes
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]
    (α : 𝕜)
    [Nontrivial (VirasoroProject.ChargedFockSpace 𝕜 α)]
    (k : Int) (hk : k ≠ 0) :
    ¬
      ((externalInfiniteJ 𝕜 α k =
          (0 :
            VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
              VirasoroProject.ChargedFockSpace 𝕜 α))
        ∧
        (externalInfiniteJ 𝕜 α (-k) =
          (0 :
            VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
              VirasoroProject.ChargedFockSpace 𝕜 α))) := by
  intro hzero
  exact
    InfoGeometry.Canonical.SplitCliffordFiniteCurrentObstruction.currentHeisenbergRep_no_opposite_zero_modes
      (H := externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α)
      (k := k) hk hzero.1 hzero.2

/--
For nonzero mode `k`, the explicit infinite current central commutator
`[J_k, J_{-k}]` is nonzero.

This is a direct closure consequence of the Heisenberg diagonal law
`[J_k, J_{-k}] = k • 1` with `k ≠ 0`.
-/
theorem externalInfiniteJ_commutator_k_negk_ne_zero
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]
    (α : 𝕜)
    [Nontrivial (VirasoroProject.ChargedFockSpace 𝕜 α)]
    (k : Int) (hk : k ≠ 0) :
    (externalInfiniteJ 𝕜 α k).commutator (externalInfiniteJ 𝕜 α (-k))
      ≠
    (0 :
      VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
        VirasoroProject.ChargedFockSpace 𝕜 α) := by
  have hcomm :
      (externalInfiniteJ 𝕜 α k).commutator (externalInfiniteJ 𝕜 α (-k))
        =
      (k : 𝕜) •
        (1 :
          VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
            VirasoroProject.ChargedFockSpace 𝕜 α) := by
    have hsum : k + (-k) = 0 := by omega
    exact heisenberg_comm_central_diag (𝕜 := 𝕜) α (m := k) (n := -k) hsum
  rw [hcomm]
  have hk0 : (k : 𝕜) ≠ 0 := by exact_mod_cast hk
  intro hzero
  have happly :
      ((k : 𝕜) •
          (1 :
            VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
              VirasoroProject.ChargedFockSpace 𝕜 α))
        =
      0 := hzero
  have hscalar :
      (k : 𝕜) = 0 := by
    -- evaluate on a nonzero vector and cancel scalar
    obtain ⟨v, hv⟩ := exists_ne (0 : VirasoroProject.ChargedFockSpace 𝕜 α)
    have hv0 :
        (((k : 𝕜) •
            (1 :
              VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
                VirasoroProject.ChargedFockSpace 𝕜 α)) v)
          = 0 := by
      simpa using congrArg (fun f => f v) happly
    have : (k : 𝕜) • v = 0 := by simpa using hv0
    exact (smul_eq_zero.mp this).resolve_right hv
  exact hk0 hscalar

/--
Mode-level nontriviality consequence:
for `k ≠ 0`, at least one of `J_k`, `J_{-k}` is nonzero.
-/
theorem externalInfiniteJ_exists_nonzero_in_opposite_pair
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]
    (α : 𝕜)
    [Nontrivial (VirasoroProject.ChargedFockSpace 𝕜 α)]
    (k : Int) (hk : k ≠ 0) :
    (externalInfiniteJ 𝕜 α k ≠
        (0 :
          VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
            VirasoroProject.ChargedFockSpace 𝕜 α))
      ∨
    (externalInfiniteJ 𝕜 α (-k) ≠
        (0 :
          VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
            VirasoroProject.ChargedFockSpace 𝕜 α)) := by
  by_contra h
  push_neg at h
  exact externalInfiniteJ_no_opposite_zero_modes (𝕜 := 𝕜) α k hk ⟨h.1, h.2⟩

/--
Exact diagonal-resonance vanishing criterion for the explicit infinite current:
`[J_k, J_{-k}] = 0` if and only if `k = 0`.
-/
theorem externalInfiniteJ_commutator_k_negk_eq_zero_iff
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]
    (α : 𝕜)
    [Nontrivial (VirasoroProject.ChargedFockSpace 𝕜 α)]
    (k : Int) :
    (externalInfiniteJ 𝕜 α k).commutator (externalInfiniteJ 𝕜 α (-k))
      =
    (0 :
      VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
        VirasoroProject.ChargedFockSpace 𝕜 α)
      ↔
    k = 0 := by
  constructor
  · intro hcomm0
    by_contra hk
    exact externalInfiniteJ_commutator_k_negk_ne_zero (𝕜 := 𝕜) α k hk hcomm0
  · intro hk
    subst hk
    have hdiag :
        (externalInfiniteJ 𝕜 α 0).commutator (externalInfiniteJ 𝕜 α 0) =
          (0 : 𝕜) •
            (1 :
              VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
                VirasoroProject.ChargedFockSpace 𝕜 α) := by
      have hsum : (0 : Int) + 0 = 0 := by norm_num
      simpa using heisenberg_comm_central_diag (𝕜 := 𝕜) α (m := 0) (n := 0) hsum
    simpa using hdiag

theorem finite_model_is_not_full_heisenberg_but_converges_to_current_completion
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (¬ scalarHeisenbergShape sourceJfin)
      ∧ scalarHeisenbergShapeEnd (externalInfiniteJ 𝕜 α) := by
  exact finite_vs_external_closure_boundary (𝕜 := 𝕜) α

theorem finite_to_infinite_agreement_on_low_energy_window
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (externalInfiniteJ 𝕜 α 1).commutator (externalInfiniteJ 𝕜 α (-1))
      =
      (1 : 𝕜) •
        (1 :
          VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
            VirasoroProject.ChargedFockSpace 𝕜 α) := by
  simpa using
    heisenberg_comm_central_diag (𝕜 := 𝕜) α (m := 1) (n := -1) (by norm_num)

theorem sugawara_commutator_two_neg_two
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).sugawaraStressMode 2).commutator
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).sugawaraStressMode (-2))
      =
      ((2 - (-2) : Int) : 𝕜) •
        (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).sugawaraStressMode 0
      + (((2 ^ 3 - 2 : 𝕜) / (12 : 𝕜)) •
          (1 :
            VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
              VirasoroProject.ChargedFockSpace 𝕜 α)) := by
  have h :=
    sugawara_central_term_eval (𝕜 := 𝕜) α (m := 2) (n := -2) (by norm_num)
  simpa using h

theorem sugawara_commutator_three_neg_three
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).sugawaraStressMode 3).commutator
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).sugawaraStressMode (-3))
      =
      ((3 - (-3) : Int) : 𝕜) •
        (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).sugawaraStressMode 0
      + (((3 ^ 3 - 3 : 𝕜) / (12 : 𝕜)) •
          (1 :
            VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
              VirasoroProject.ChargedFockSpace 𝕜 α)) := by
  have h :=
    sugawara_central_term_eval (𝕜 := 𝕜) α (m := 3) (n := -3) (by norm_num)
  simpa using h

theorem virasoro_lgen_commutator_two_neg_two
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 2)).commutator
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 (-2)))
      =
      ((2 - (-2) : Int) : 𝕜) •
        (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
          (VirasoroProject.VirasoroAlgebra.lgen 𝕜 0)
      +
      (((2 ^ 3 - 2 : 𝕜) / (12 : 𝕜)) •
        (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
          (VirasoroProject.VirasoroAlgebra.cgen 𝕜)) := by
  have h := sugawara_LL_full (𝕜 := 𝕜) α (m := 2) (n := -2)
  simpa using h

end SplitCliffordSourceCurrentWick
