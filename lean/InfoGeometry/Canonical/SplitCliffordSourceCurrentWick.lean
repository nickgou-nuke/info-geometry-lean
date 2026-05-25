import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import InfoGeometry.Canonical.BosonizationConstructiveCurrent
import InfoGeometry.Canonical.CurrentSugawaraBridge
import InfoGeometry.Canonical.SplitCliffordFiniteCAR
import InfoGeometry.Canonical.SplitCliffordJordanWignerTwoModeCurrent
import InfoGeometry.Canonical.SplitCliffordSourceCurrent

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

namespace InfoGeometry.Canonical.SplitCliffordSourceCurrentWick

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

/-- Explicit concrete commutator at the nontrivial mode pair. -/
theorem sourceJfin_commutator_one_neg_one :
    sourceJfin 1 * sourceJfin (-1) - sourceJfin (-1) * sourceJfin 1 =
      !![0, 0, 0, 0;
         0, -1, 0, 0;
         0, 0, 1, 0;
         0, 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sourceJfin, a1, a1Dag, a2, a2Dag, Matrix.mul_apply, Fin.sum_univ_four]

/-- Source commutator vanishes when one mode is outside support `±1`. -/
theorem sourceJfin_commutator_zero_of_outside_support
    (m n : Int)
    (h : (m ≠ 1 ∧ m ≠ -1) ∨ (n ≠ 1 ∧ n ≠ -1)) :
    sourceJfin m * sourceJfin n - sourceJfin n * sourceJfin m = 0 := by
  rcases h with hm | hn
  · simp [sourceJfin, hm.1, hm.2]
  · simp [sourceJfin, hn.1, hn.2]

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
  intro hshape
  have h11 :=
    hshape 1 (-1)
  have hcomm :
      sourceJfin 1 * sourceJfin (-1) - sourceJfin (-1) * sourceJfin 1
        =
      (1 : ℝ) • (1 : M4R) := by
    simpa using h11
  have h00 := congrArg (fun M : M4R => M 0 0) hcomm
  rw [sourceJfin_commutator_one_neg_one] at h00
  norm_num at h00

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

end InfoGeometry.Canonical.SplitCliffordSourceCurrentWick
