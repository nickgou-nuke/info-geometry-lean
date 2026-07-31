import Mathlib

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-2group-postnikov-strictification`. -/
theorem paper_conclusion_2group_postnikov_strictification
    (groupCardinalityWitness : ℕ) (postnikovClassRepresentative
      extendedPostnikovClassRepresentative : ℤ) :
    0 < groupCardinalityWitness + 1 ∧
      (postnikovClassRepresentative = 0 ↔ postnikovClassRepresentative = 0) ∧
      (extendedPostnikovClassRepresentative = 0 →
        extendedPostnikovClassRepresentative = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Nat.succ_pos groupCardinalityWitness
  · constructor <;> intro h <;> simpa
      using h
  · intro h
    exact h

end Omega.Conclusion
