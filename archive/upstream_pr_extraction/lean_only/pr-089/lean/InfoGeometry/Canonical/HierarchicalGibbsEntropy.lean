import InfoGeometry.Canonical.HierarchicalGibbsDecomposition

open scoped BigOperators

namespace InfoGeometry.Canonical

namespace HierarchicalGrandCanonical

variable {Sector : Type*} [Fintype Sector] [Nonempty Sector]
variable (State : Sector → Type*)
variable [∀ s, Fintype (State s)] [∀ s, Nonempty (State s)]

/-- Shannon entropy of a finite, not-necessarily-normalized weight function. -/
noncomputable def finiteEntropy {α : Type*} [Fintype α] (p : α → ℝ) : ℝ :=
  -∑ x, p x * Real.log (p x)

/-- Entropy of the outer sector distribution. -/
noncomputable def sectorEntropy
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (β μ : ℝ) : ℝ :=
  finiteEntropy (fun s => sectorWeight State energy particleNumber β μ s)

/-- Conditional entropy inside one canonical sector. -/
noncomputable def conditionalEntropy
    (energy : ∀ s, State s → ℝ) (β : ℝ) (s : Sector) : ℝ :=
  finiteEntropy (fun x => conditionalWeight State energy β s x)

/-- Entropy of the full joint hierarchical distribution. -/
noncomputable def jointEntropy
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (β μ : ℝ) : ℝ :=
  -∑ s, ∑ x, jointWeight State energy particleNumber β μ s x *
    Real.log (jointWeight State energy particleNumber β μ s x)

/-- Every conditional canonical weight is strictly positive. -/
theorem canonicalWeight_pos
    (energy : ∀ s, State s → ℝ) (β : ℝ) (s : Sector) (x : State s) :
    0 < canonicalWeight State energy β s x := by
  unfold canonicalWeight
  exact Real.exp_pos _

/-- Every conditional canonical weight is strictly positive. -/
theorem conditionalWeight_pos
    (energy : ∀ s, State s → ℝ) (β : ℝ) (s : Sector) (x : State s) :
    0 < conditionalWeight State energy β s x := by
  unfold conditionalWeight
  exact div_pos (canonicalWeight_pos State energy β s x)
    (canonicalPartition_pos State energy β s)

/-- Every outer sector weight is strictly positive. -/
theorem sectorWeight_pos
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (β μ : ℝ) (s : Sector) :
    0 < sectorWeight State energy particleNumber β μ s := by
  unfold sectorWeight sectorNumerator
  exact div_pos (mul_pos (Real.exp_pos _) (canonicalPartition_pos State energy β s))
    (grandPartition_pos State energy particleNumber β μ)

/-- Every joint hierarchical weight is strictly positive. -/
theorem jointWeight_pos
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (β μ : ℝ) (s : Sector) (x : State s) :
    0 < jointWeight State energy particleNumber β μ s x := by
  rw [jointWeight_eq_sectorWeight_mul_conditionalWeight]
  exact mul_pos (sectorWeight_pos State energy particleNumber β μ s)
    (conditionalWeight_pos State energy β s x)

theorem sum_jointEntropyTerm_eq
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (β μ : ℝ) (s : Sector) :
    (∑ x, jointWeight State energy particleNumber β μ s x *
      Real.log (jointWeight State energy particleNumber β μ s x)) =
      sectorWeight State energy particleNumber β μ s *
        Real.log (sectorWeight State energy particleNumber β μ s) +
      sectorWeight State energy particleNumber β μ s *
        (∑ x, conditionalWeight State energy β s x *
          Real.log (conditionalWeight State energy β s x)) := by
  classical
  let q := sectorWeight State energy particleNumber β μ s
  let r := fun x => conditionalWeight State energy β s x
  have hq : q ≠ 0 := ne_of_gt (sectorWeight_pos State energy particleNumber β μ s)
  have hr : ∀ x, r x ≠ 0 := fun x =>
    ne_of_gt (conditionalWeight_pos State energy β s x)
  have hpoint : ∀ x, jointWeight State energy particleNumber β μ s x *
      Real.log (jointWeight State energy particleNumber β μ s x) =
      (q * Real.log q) * r x + q * (r x * Real.log (r x)) := by
    intro x
    rw [jointWeight_eq_sectorWeight_mul_conditionalWeight]
    rw [Real.log_mul hq (hr x)]
    dsimp [q, r]
    ring
  apply Eq.trans (Finset.sum_congr rfl (fun x _ => hpoint x))
  rw [Finset.sum_add_distrib]
  have hr_sum : (∑ x, r x) = 1 := by
    dsimp [r]
    exact sum_conditionalWeight_eq_one State energy β s
  calc
    _ = (q * Real.log q) * (∑ x, r x) +
        q * (∑ x, r x * Real.log (r x)) := by
          rw [Finset.mul_sum, Finset.mul_sum]
    _ = sectorWeight State energy particleNumber β μ s *
        Real.log (sectorWeight State energy particleNumber β μ s) +
        sectorWeight State energy particleNumber β μ s *
          (∑ x, conditionalWeight State energy β s x *
            Real.log (conditionalWeight State energy β s x)) := by
          rw [hr_sum]
          dsimp [q, r]
          ring

/-- The finite Shannon entropy obeys the exact sector/conditional chain rule. -/
theorem jointEntropy_eq_sectorEntropy_add_expectedConditionalEntropy
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (β μ : ℝ) :
    jointEntropy State energy particleNumber β μ =
      sectorEntropy State energy particleNumber β μ +
        ∑ s, sectorWeight State energy particleNumber β μ s *
          conditionalEntropy State energy β s := by
  classical
  unfold jointEntropy sectorEntropy conditionalEntropy finiteEntropy
  rw [Finset.sum_congr rfl (fun s _ => sum_jointEntropyTerm_eq State energy particleNumber β μ s)]
  rw [Finset.sum_add_distrib]
  simp only [mul_neg]
  rw [← Finset.sum_neg_distrib]
  rw [Finset.sum_neg_distrib, Finset.sum_neg_distrib]
  ring

end HierarchicalGrandCanonical

end InfoGeometry.Canonical
