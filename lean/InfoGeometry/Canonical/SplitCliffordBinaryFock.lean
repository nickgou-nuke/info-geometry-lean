import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Bool.Basic

/-!
# InfoGeometry.Canonical.SplitCliffordBinaryFock

Infinite binary-word model of the finite-excitation Fock sector.
-/

namespace InfoGeometry.Canonical.SplitCliffordBinaryFock

/-- Dirac vacuum word: negative/zero indices filled, positive empty. -/
def diracVacuum (n : ℤ) : Bool :=
  decide (n ≤ 0)

/--
A physical Fock word differs from the Dirac vacuum at only finitely many indices.
-/
structure FockWord where
  word : ℤ → Bool
  finite_excitations : ∃ s : Finset ℤ, ∀ n, n ∉ s → word n = diracVacuum n

/-- Local ladder action as a single-index bit flip. -/
def bitFlip (k : ℤ) (w : ℤ → Bool) : ℤ → Bool :=
  fun n => if n = k then !(w n) else w n

/--
Bit flips preserve finite-excitation support: only index `k` can newly differ.
-/
theorem bitFlip_preserves_fock (w : FockWord) (k : ℤ) :
    ∃ s' : Finset ℤ, ∀ n, n ∉ s' → bitFlip k w.word n = diracVacuum n := by
  rcases w.finite_excitations with ⟨s, hs⟩
  refine ⟨insert k s, ?_⟩
  intro n hn
  have hnk : n ≠ k := by
    intro hEq
    apply hn
    simpa [hEq] using Finset.mem_insert_self k s
  have hns : n ∉ s := by
    intro hmem
    apply hn
    exact Finset.mem_insert_of_mem hmem
  unfold bitFlip
  rw [if_neg hnk]
  exact hs n hns

/-- Packaged closed operator on the Fock sector. -/
def applyOperator (k : ℤ) (w : FockWord) : FockWord :=
  ⟨bitFlip k w.word, bitFlip_preserves_fock w k⟩

end InfoGeometry.Canonical.SplitCliffordBinaryFock

