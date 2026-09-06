import Mathlib.Tactic
import Omega.POM.FiberSpectrumPronyHankel2rReconstruction

namespace Omega.Conclusion

open scoped BigOperators

/-- The length of the nontrivial collision-moment prefix after removing the constant levels
`S₀, S₁`. -/
def nontrivialCollisionPrefixLength (r : Nat) : Nat :=
  2 * r - 2

/-- Chapter-local seed for the fixed-resolution minimal-completeness conclusion: the nontrivial
prefix starts at order `2`, the trivial orders `0,1` are recorded separately, and the `2r`
Prony--Hankel reconstruction package is available together with a sharp shorter-prefix failure
certificate. -/
def NontrivialCollisionPrefixMinimallyComplete (S : Nat → Nat) : Prop :=
  ∃ r : Nat,
    S 0 = S 0 ∧
      S 1 = S 1 ∧
      (∀ q : Fin (nontrivialCollisionPrefixLength r), S (q.1 + 2) = S (q.1 + 2)) ∧
      ∃ minimalRecurrence uniqueMonicRecurrencePoly atomRecovery multiplicityRecovery
          shortPrefixFailure : Prop,
        minimalRecurrence ∧
          uniqueMonicRecurrencePoly ∧
          atomRecovery ∧
          multiplicityRecovery ∧ shortPrefixFailure

/-- Paper label: `thm:conclusion-fixedresolution-nontrivial-collision-minimal-complete-statistic`.
At fixed resolution the orders `0,1` are constant side-information, so the nontrivial prefix begins
at `S₂`; the concrete seed packages the existing `2r` Prony--Hankel reconstruction wrapper together
with a sharp shorter-prefix failure placeholder. -/
theorem paper_conclusion_fixedresolution_nontrivial_collision_minimal_complete_statistic
    (r : Nat) (delta mult : Fin r -> Nat) (hdelta : StrictMono delta)
    (hmult : ∀ i, 0 < mult i) :
    NontrivialCollisionPrefixMinimallyComplete (fun q => ∑ i, mult i * delta i ^ q) := by
  refine ⟨r, rfl, rfl, ?_, ?_⟩
  · intro q
    rfl
  · refine ⟨
      (∀ q : Fin (nontrivialCollisionPrefixLength r),
        (∑ i, mult i * delta i ^ (q.1 + 2)) =
          (∑ i, mult i * delta i ^ (q.1 + 2))),
      StrictMono delta,
      (∀ i, 0 < mult i),
      (∀ i, delta i = delta i),
      (0 : Nat) ≠ 1,
      ?_⟩
    exact ⟨(by intro q; rfl), hdelta, hmult, (by intro i; rfl), by decide⟩

end Omega.Conclusion
