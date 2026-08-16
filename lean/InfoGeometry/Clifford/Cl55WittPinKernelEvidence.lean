import InfoGeometry.Clifford.Cl55WittPinCoverEvidence

namespace InfoGeometry.Clifford.Clifford55

/-!
# Central-kernel evidence for the native Pin action

The scalar `-1` is constructed inside `Pin55` as the square of one negative
Witt reflection vector.  Its action is the identity.  The converse kernel
classification is intentionally not asserted here.
-/

noncomputable def negOnePin : Pin55 := fNegPin 0 * fNegPin 0

theorem negOnePin_coe : (negOnePin : Cl55) = -1 := by
  change (fNegPin 0 : Cl55) * (fNegPin 0 : Cl55) = -1
  rw [fNegPin_coe, ← pow_two, f_neg_sq]

theorem pinTwistedOrthogonalAction_negOnePin :
    pinTwistedOrthogonalAction negOnePin = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change pinTwistedActionEquiv negOnePin v = v
  rw [negOnePin, pinTwistedActionEquiv_mul_all,
    pinTwistedActionEquiv_fNegPin_eq_negativeReflection]
  change negativeReflectionLinearEquiv 0
      (negativeReflectionLinearEquiv 0 v) = v
  simpa only [negativeReflectionLinearEquiv_apply] using
    negativeReflection_involutive 0 v

theorem negOnePin_mem_kernel :
    negOnePin ∈ (pinTwistedOrthogonalAction).ker := by
  change pinTwistedOrthogonalAction negOnePin = 1
  exact pinTwistedOrthogonalAction_negOnePin

theorem negOnePin_ne_one : negOnePin ≠ 1 := by
  intro h
  have hcoe : (negOnePin : Cl55) = (1 : Cl55) := by
    exact congrArg (fun g : Pin55 => (g : Cl55)) h
  rw [negOnePin_coe] at hcoe
  have htwo : (2 : Cl55) = 0 := by
    calc
      (2 : Cl55) = 1 - (-1 : Cl55) := by norm_num
      _ = 1 - 1 := by rw [hcoe]
      _ = 0 := sub_self _
  have htwo' : (2 : Cl55) ≠ 0 := by
    intro hzero
    have hsmul : (2 : ℝ) • (1 : Cl55) = 0 := by
      rw [Algebra.smul_def, mul_one]
      exact hzero
    rcases smul_eq_zero.mp hsmul with h2 | h1
    · norm_num at h2
    · exact one_ne_zero h1
  exact htwo' htwo

theorem negOnePin_sq : negOnePin * negOnePin = 1 := by
  apply Subtype.ext
  change (negOnePin : Cl55) * (negOnePin : Cl55) = (1 : Cl55)
  rw [negOnePin_coe]
  simp

theorem negOnePin_commute (g : Pin55) :
    negOnePin * g = g * negOnePin := by
  apply Subtype.ext
  change (negOnePin : Cl55) * (g : Cl55) =
    (g : Cl55) * (negOnePin : Cl55)
  rw [negOnePin_coe]
  simp

def pinSignSubgroup : Subgroup Pin55 :=
  Subgroup.closure ({1, negOnePin} : Set Pin55)

theorem mem_pinSignSubgroup_iff (g : Pin55) :
    g ∈ pinSignSubgroup ↔ g = 1 ∨ g = negOnePin := by
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction'' with
    | mem g hg =>
        rcases hg with rfl | hg
        · exact Or.inl rfl
        · exact Or.inr (Set.mem_singleton_iff.mp hg)
    | one =>
        exact Or.inl rfl
    | mul g h hg hh hG hH =>
        rcases hG with rfl | rfl <;> rcases hH with rfl | rfl
        · simp
        · simp
        · simp
        · exact Or.inl negOnePin_sq
    | inv_mem g hg =>
        rcases hg with rfl | rfl
        · simp
        · right
          calc
            negOnePin⁻¹ = negOnePin⁻¹ * 1 := by simp
            _ = negOnePin⁻¹ * (negOnePin * negOnePin) := by
              rw [negOnePin_sq]
            _ = (negOnePin⁻¹ * negOnePin) * negOnePin := by
              rw [mul_assoc]
            _ = negOnePin := by simp
  · intro hg
    rcases hg with rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (Set.mem_insert_iff.mpr (Or.inr rfl))

theorem pinSignSubgroup_le_kernel :
    pinSignSubgroup ≤ (pinTwistedOrthogonalAction).ker := by
  refine (Subgroup.closure_le (pinTwistedOrthogonalAction).ker).2 ?_
  intro g hg
  rcases hg with rfl | rfl
  · simp
  · exact negOnePin_mem_kernel

end InfoGeometry.Clifford.Clifford55
