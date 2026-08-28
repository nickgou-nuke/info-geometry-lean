import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint
import InfoGeometry.Analysis.FractalMeasure.Basic
import InfoGeometry.Canonical.CantorProjectiveBernoulliMeasure
import InfoGeometry.Canonical.CuntzCantorBoundaryShift

/-!
# The Hilbert-level Cantor transport

The fair Bernoulli boundary is represented on `Lp ℂ 2`.  The tail map is
proved measure-preserving from the finite-box characterization of the
infinite product measure, and therefore induces a genuine `Lp` isometry.
Branch shifts are deliberately kept separate: their normalization and
adjoint theory requires the branch-density theorem and is not identified with
the algebraic `star_S_*` operators here.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorBernoulliL2OperatorTransport

open MeasureTheory
open scoped ENNReal
open InfoGeometry.Analysis.FractalMeasure.Basic
open InfoGeometry.Canonical.CuntzCantorBoundaryShift
open InfoGeometry.Canonical.CantorProjectiveBernoulliMeasure

abbrev Boundary := ℕ → Bool
abbrev μC : Measure Boundary := fractalMeasure
abbrev L2Boundary := Lp ℂ 2 μC

theorem prependBit_preimage_cylinder_of_zero_not_mem
    (b : Bool) (s : Finset ℕ) (t : ℕ → Set Bool)
    (h0 : 0 ∉ s) :
    prependBit b ⁻¹' Set.pi s t =
      Set.pi (s.preimage Nat.succ Nat.succ_injective.injOn)
        (fun i => t (Nat.succ i)) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_pi]
  constructor
  · intro h i hi
    have hi' : Nat.succ i ∈ s := Finset.mem_preimage.mp hi
    simpa [prependBit] using h (Nat.succ i) hi'
  · intro h i hi
    have hi0 : i ≠ 0 := by
      intro hi0'
      subst i
      exact h0 hi
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
    have hj : j ∈ s.preimage Nat.succ Nat.succ_injective.injOn :=
      Finset.mem_preimage.mpr hi
    have hj' := h j hj
    simpa [prependBit, tail] using hj'

theorem prependBit_preimage_cylinder_of_zero_mem
    (b : Bool) (s : Finset ℕ) (t : ℕ → Set Bool)
    (hb : b ∈ t 0) :
    prependBit b ⁻¹' Set.pi s t =
      Set.pi (s.preimage Nat.succ Nat.succ_injective.injOn)
        (fun i => t (Nat.succ i)) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_pi]
  constructor
  · intro h i hi
    have hi' : Nat.succ i ∈ s := Finset.mem_preimage.mp hi
    simpa [prependBit] using h (Nat.succ i) hi'
  · intro h i hi
    by_cases hi0 : i = 0
    · simpa [hi0] using hb
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
      have hj : j ∈ s.preimage Nat.succ Nat.succ_injective.injOn :=
        Finset.mem_preimage.mpr hi
      have hj' := h j hj
      simpa [prependBit, tail] using hj'

theorem prependBit_preimage_cylinder_zero_mem_empty
    (b : Bool) (s : Finset ℕ) (t : ℕ → Set Bool)
    (h0 : 0 ∈ s) (hb : b ∉ t 0) :
    prependBit b ⁻¹' Set.pi s t = ∅ := by
  ext x
  simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
  intro h
  exact hb (h 0 h0)

theorem prependBit_branch_mass (b : Bool) :
    μC (Set.range (prependBit b)) = (1 / 2 : ℝ≥0∞) := by
  have hrange :
      Set.range (prependBit b) =
        InfoGeometry.Analysis.FractalMeasure.Basic.cylinderSet
          (Finset.range 1) (fun _ : ℕ => b) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩ i hi
      have hi' : i < 1 := Finset.mem_range.mp hi
      have hi0 : i = 0 := by omega
      subst i
      simp [prependBit]
    · intro hx
      refine ⟨tail x, ?_⟩
      apply prependBit_tail_of_head
      have hx0 := hx 0 (by simp)
      simpa [prependBit] using hx0
  rw [hrange, measure_cylinderSet]
  simp

/-! The finite-coordinate measure calculation needed for normalized branch
operators.  The first-coordinate-free case is measure preserving; imposing a
singleton first coordinate contributes exactly the missing factor `2`. -/
theorem prependBit_preimage_cylinder_measure_of_zero_not_mem
    (b : Bool) (s : Finset ℕ) (t : ℕ → Set Bool)
    (h0 : 0 ∉ s) (ht : ∀ i ∈ s, MeasurableSet (t i)) :
    μC (prependBit b ⁻¹' Set.pi s t) = μC (Set.pi s t) := by
  rw [prependBit_preimage_cylinder_of_zero_not_mem b s t h0]
  have hleft :
      μC (Set.pi (s.preimage Nat.succ Nat.succ_injective.injOn)
        (fun i => t (Nat.succ i))) =
        ∏ i ∈ s.preimage Nat.succ Nat.succ_injective.injOn,
          bernoulliHalf (t (Nat.succ i)) := by
    change Measure.infinitePi (fun _ : ℕ => bernoulliHalf) _ = _
    rw [Measure.infinitePi_pi]
    intro i hi
    exact ht (Nat.succ i) (Finset.mem_preimage.mp hi)
  have hright :
      μC (Set.pi s t) =
        ∏ i ∈ s, bernoulliHalf (t i) := by
    change Measure.infinitePi (fun _ : ℕ => bernoulliHalf) _ = _
    rw [Measure.infinitePi_pi]
    intro i hi
    exact ht i hi
  rw [hleft, hright]
  apply Finset.prod_bij
      (fun i hi => Nat.succ i)
      (fun i hi => Finset.mem_preimage.mp hi)
      (by
        intro a ha b hb h
        exact Nat.succ.inj h)
      (by
        intro j hj
        have hj0 : j ≠ 0 := by
          intro hj0
          exact h0 (hj0 ▸ hj)
        obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
        exact ⟨i, Finset.mem_preimage.mpr hj, rfl⟩)
  intro i hi
  rfl

theorem prependBit_preimage_cylinder_measure_of_singleton_zero
    (b : Bool) (s : Finset ℕ) (t : ℕ → Set Bool)
    (h0 : 0 ∈ s) (ht : ∀ i ∈ s, MeasurableSet (t i))
    (hb : t 0 = {b}) :
    μC (prependBit b ⁻¹' Set.pi s t) =
      2 * μC (Set.pi s t) := by
  rw [prependBit_preimage_cylinder_of_zero_mem b s t
    (by rw [hb]; simp)]
  have hleft :
      μC (Set.pi (s.preimage Nat.succ Nat.succ_injective.injOn)
        (fun i => t (Nat.succ i))) =
        ∏ i ∈ s.preimage Nat.succ Nat.succ_injective.injOn,
          bernoulliHalf (t (Nat.succ i)) := by
    change Measure.infinitePi (fun _ : ℕ => bernoulliHalf) _ = _
    rw [Measure.infinitePi_pi]
    intro i hi
    exact ht (Nat.succ i) (Finset.mem_preimage.mp hi)
  have hright :
      μC (Set.pi s t) =
        ∏ i ∈ s, bernoulliHalf (t i) := by
    change Measure.infinitePi (fun _ : ℕ => bernoulliHalf) _ = _
    rw [Measure.infinitePi_pi]
    intro i hi
    exact ht i hi
  rw [hleft, hright]
  have hprod :
      (∏ i ∈ s, bernoulliHalf (t i)) =
        bernoulliHalf (t 0) *
          ∏ i ∈ s.erase 0, bernoulliHalf (t i) := by
    rw [← Finset.prod_erase_mul s (fun i => bernoulliHalf (t i)) h0]
    rw [mul_comm]
  have hpre :
      (∏ i ∈ s.preimage Nat.succ Nat.succ_injective.injOn,
        bernoulliHalf (t (Nat.succ i))) =
        ∏ i ∈ s.erase 0, bernoulliHalf (t i) := by
    apply Finset.prod_bij
        (fun i hi => Nat.succ i)
        (fun i hi => by
          exact Finset.mem_erase.mpr
            ⟨Nat.succ_ne_zero i, Finset.mem_preimage.mp hi⟩)
        (by
          intro a ha b hb h
          exact Nat.succ.inj h)
        (by
          intro j hj
          have hj0 : j ≠ 0 := (Finset.mem_erase.mp hj).1
          obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
          exact ⟨i, Finset.mem_preimage.mpr (Finset.mem_erase.mp hj).2, rfl⟩)
    intro i hi
    rfl
  rw [hpre, hprod, hb, bernoulliHalf_singleton]
  have hhalf : (2 : ℝ≥0∞) * (1 / 2 : ℝ≥0∞) = 1 := by
    simpa [one_div] using
      (ENNReal.mul_inv_cancel (a := (2 : ℝ≥0∞)) (by norm_num)
        (ENNReal.ofNat_ne_top (n := 2)))
  rw [← mul_assoc, hhalf, one_mul]

theorem tail_preimage_pi (s : Finset ℕ) (t : ℕ → Set Bool) :
    tail ⁻¹' Set.pi s t =
      Set.pi (s.image Nat.succ)
        (fun j => if h : ∃ i ∈ s, Nat.succ i = j then
          t (Classical.choose h) else Set.univ) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_pi]
  constructor
  · intro h j hj
    rcases Finset.mem_image.mp hj with ⟨i, hi, rfl⟩
    have hh : ∃ k ∈ s, Nat.succ k = Nat.succ i := ⟨i, hi, rfl⟩
    have hchoose : Classical.choose hh = i := by
      apply Nat.succ.inj
      exact (Classical.choose_spec hh).2
    rw [dif_pos hh]
    rw [hchoose]
    simpa [tail] using h i hi
  · intro h i hi
    have hj : Nat.succ i ∈ s.image Nat.succ :=
      Finset.mem_image.mpr ⟨i, hi, rfl⟩
    have hh : ∃ k ∈ s, Nat.succ k = Nat.succ i := ⟨i, hi, rfl⟩
    have hji := h (Nat.succ i) hj
    simp only [dif_pos hh] at hji
    have hchoose : Classical.choose hh = i := by
      apply Nat.succ.inj
      exact (Classical.choose_spec hh).2
    rw [hchoose] at hji
    simpa [tail] using hji

def prependBitBranchProductMeasure (b : Bool) : Measure Boundary :=
  Measure.infinitePi (fun i : ℕ => if i = 0 then Measure.dirac b else bernoulliHalf)

instance prependBitBranchProductMeasure_isProbabilityMeasure (b : Bool) :
    IsProbabilityMeasure (prependBitBranchProductMeasure b) := by
  unfold prependBitBranchProductMeasure
  infer_instance

theorem prependBitBranchProductMeasure_univ (b : Bool) :
    prependBitBranchProductMeasure b Set.univ = 1 := by
  exact measure_univ

theorem prependBit_measure_map_eq_branchProductMeasure (b : Bool) :
    Measure.map (prependBit b) μC = prependBitBranchProductMeasure b := by
  apply Measure.eq_infinitePi
  intro s t ht
  have hpre : Measurable (prependBit b : Boundary → Boundary) :=
    continuous_prependBit b |>.measurable
  have hpi : MeasurableSet (Set.pi s t) :=
    MeasurableSet.pi s.countable_toSet (fun i hi => ht i)
  rw [Measure.map_apply hpre hpi]
  by_cases h0 : 0 ∈ s
  · by_cases hb : b ∈ t 0
    · rw [prependBit_preimage_cylinder_of_zero_mem b s t hb]
      change Measure.infinitePi (fun _ : ℕ => bernoulliHalf) _ = _
      have hleft :
          Measure.infinitePi (fun _ : ℕ => bernoulliHalf)
              (Set.pi (s.preimage Nat.succ Nat.succ_injective.injOn)
                (fun i => t (Nat.succ i))) =
            ∏ i ∈ s.preimage Nat.succ Nat.succ_injective.injOn,
              bernoulliHalf (t (Nat.succ i)) := by
        apply Measure.infinitePi_pi
        intro i hi
        exact ht (Nat.succ i)
      rw [hleft]
      have hzero :
          (if (0 : ℕ) = 0 then Measure.dirac b else bernoulliHalf) (t 0) = 1 := by
        simp [hb]
      rw [← Finset.prod_erase s hzero]
      apply Finset.prod_bij
        (s := s.preimage Nat.succ Nat.succ_injective.injOn)
        (t := s.erase 0)
        (f := fun i : ℕ => bernoulliHalf (t (Nat.succ i)))
        (g := fun j : ℕ =>
          (if j = 0 then Measure.dirac b else bernoulliHalf) (t j))
        (fun i _ => Nat.succ i)
        (fun i hi => Finset.mem_erase.mpr
          ⟨Nat.succ_ne_zero i, Finset.mem_preimage.mp hi⟩)
        (fun a₁ ha₁ a₂ ha₂ h => Nat.succ.inj h)
        (fun j hj => by
          obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
            (Finset.mem_erase.mp hj).1
          refine ⟨i, Finset.mem_preimage.mpr (Finset.mem_erase.mp hj).2, rfl⟩)
        (fun i hi => by simp)
    · rw [prependBit_preimage_cylinder_zero_mem_empty b s t h0 hb]
      simp only [measure_empty]
      symm
      refine Finset.prod_eq_zero
        (f := fun i : ℕ =>
          (if i = 0 then Measure.dirac b else bernoulliHalf) (t i)) h0 ?_
      have hzero :
          (if (0 : ℕ) = 0 then Measure.dirac b else bernoulliHalf) (t 0) = 0 := by
        simp [hb]
      simpa using hzero
  · rw [prependBit_preimage_cylinder_of_zero_not_mem b s t h0]
    change Measure.infinitePi (fun _ : ℕ => bernoulliHalf) _ = _
    have hleft :
        Measure.infinitePi (fun _ : ℕ => bernoulliHalf)
            (Set.pi (s.preimage Nat.succ Nat.succ_injective.injOn)
              (fun i => t (Nat.succ i))) =
          ∏ i ∈ s.preimage Nat.succ Nat.succ_injective.injOn,
            bernoulliHalf (t (Nat.succ i)) := by
      apply Measure.infinitePi_pi
      intro i hi
      exact ht (Nat.succ i)
    rw [hleft]
    apply Finset.prod_bij
      (s := s.preimage Nat.succ Nat.succ_injective.injOn)
      (t := s)
      (f := fun i : ℕ => bernoulliHalf (t (Nat.succ i)))
      (g := fun j : ℕ =>
        (if j = 0 then Measure.dirac b else bernoulliHalf) (t j))
      (fun i _ => Nat.succ i)
      (fun i hi => Finset.mem_preimage.mp hi)
      (fun a₁ ha₁ a₂ ha₂ h => Nat.succ.inj h)
      (fun j hj => by
        obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by
          intro hj0
          exact h0 (hj0 ▸ hj))
        refine ⟨i, Finset.mem_preimage.mpr hj, rfl⟩)
      (fun i hi => by simp)

theorem prependBit_measure_map_eq_two_restrict_branch (b : Bool) :
    Measure.map (prependBit b) μC =
      (2 : ℝ≥0∞) • μC.restrict (Set.range (prependBit b)) := by
  rw [prependBit_measure_map_eq_branchProductMeasure b]
  symm
  apply Measure.eq_infinitePi
  intro s t ht
  have hpi : MeasurableSet (Set.pi s t) :=
    MeasurableSet.pi s.countable_toSet (fun i _ => ht i)
  have hbranch : Set.range (prependBit b) =
      Set.univ.pi (fun i : ℕ => if i = 0 then ({b} : Set Bool) else Set.univ) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩ i hi
      by_cases hi0 : i = 0
      · subst i; simp [prependBit]
      · simp [prependBit, hi0]
    · intro hx
      refine ⟨tail x, ?_⟩
      apply prependBit_tail_of_head
      have hx0 : x 0 = b := by simpa using hx 0 (by simp)
      simpa [prependBit] using hx0
  rw [hbranch]
  simp only [Measure.smul_apply, Measure.restrict_apply hpi, smul_eq_mul]
  change ((2 : ℝ≥0∞) • μC _) = _
  by_cases h0 : 0 ∈ s
  · have hinter :
        Set.pi s t ∩ Set.univ.pi
            (fun i : ℕ => if i = 0 then ({b} : Set Bool) else Set.univ) =
          Set.pi s (fun i => if i = 0 then t i ∩ {b} else t i) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_pi, Set.mem_univ]
      constructor
      · intro hx i hi
        by_cases hi0 : i = 0
        · subst i; exact ⟨hx.1 0 h0, hx.2 0 (by simp)⟩
        · simpa [hi0] using hx.1 i hi
      · intro hx
        refine ⟨?_, ?_⟩
        · intro i hi
          by_cases hi0 : i = 0
          · subst i
            have hxi : x 0 ∈ t 0 ∩ {b} := hx 0 h0
            exact hxi.1
          · simpa [hi0] using hx i hi
        · intro i hi
          by_cases hi0 : i = 0
          · subst i
            have hxi : x 0 ∈ t 0 ∩ {b} := hx 0 h0
            exact hxi.2
          · simp [hi0]
    rw [hinter]
    change ((2 : ℝ≥0∞) • μC _) = _
    simp only [smul_eq_mul]
    change (2 : ℝ≥0∞) * Measure.infinitePi (fun _ : ℕ => bernoulliHalf) _ = _
    rw [Measure.infinitePi_pi]
    · by_cases hb : b ∈ t 0
      · have hset : t 0 ∩ {b} = {b} := by
          ext z
          simp [hb]
        have hleft :
            (∏ i ∈ s, bernoulliHalf (if i = 0 then t i ∩ {b} else t i)) =
              bernoulliHalf (t 0 ∩ {b}) *
                ∏ i ∈ s.erase 0, bernoulliHalf (t i) := by
          rw [← Finset.prod_erase_mul s
            (fun i => bernoulliHalf (if i = 0 then t i ∩ {b} else t i)) h0]
          rw [mul_comm]
          congr 1
          apply Finset.prod_congr rfl
          intro i hi
          simp [Finset.mem_erase.mp hi]
        have hright :
            (∏ i ∈ s, (if i = 0 then Measure.dirac b else bernoulliHalf) (t i)) =
              (Measure.dirac b) (t 0) *
                ∏ i ∈ s.erase 0, bernoulliHalf (t i) := by
          rw [← Finset.prod_erase_mul s
            (fun i => (if i = 0 then Measure.dirac b else bernoulliHalf) (t i)) h0]
          rw [mul_comm]
          congr 1
          apply Finset.prod_congr rfl
          intro i hi
          simp [Finset.mem_erase.mp hi]
        rw [hleft, hright, hset]
        have hhalf : (2 : ℝ≥0∞) * (1 / 2 : ℝ≥0∞) = 1 := by
          simpa [one_div] using
            (ENNReal.mul_inv_cancel (a := (2 : ℝ≥0∞)) (by norm_num)
              (ENNReal.ofNat_ne_top (n := 2)))
        have hdirac : (Measure.dirac b) (t 0) = 1 := by simp [hb]
        rw [hdirac]
        rw [bernoulliHalf_singleton]
        rw [← mul_assoc, hhalf, one_mul]
      · have hzero : bernoulliHalf (t 0 ∩ {b}) = 0 := by
          have hset : t 0 ∩ {b} = (∅ : Set Bool) := by
            ext z
            simp [hb]
          rw [hset, measure_empty]
        have hleftzero :
            (∏ i ∈ s, bernoulliHalf (if i = 0 then t i ∩ {b} else t i)) = 0 := by
          apply Finset.prod_eq_zero (f := fun i =>
            bernoulliHalf (if i = 0 then t i ∩ {b} else t i)) h0
          simpa using hzero
        have hrightzero :
            (∏ i ∈ s, (if i = 0 then Measure.dirac b else bernoulliHalf) (t i)) = 0 := by
          apply Finset.prod_eq_zero (f := fun i =>
            (if i = 0 then Measure.dirac b else bernoulliHalf) (t i)) h0
          simp [Measure.dirac_apply' b (ht 0), hb]
        rw [hleftzero, hrightzero]
        simp
    · intro i hi
      by_cases hi0 : i = 0
      · subst i; exact (ht 0).inter (measurableSet_singleton b)
      · exact ht i
  · have hinter :
        Set.pi s t ∩ Set.univ.pi
            (fun i : ℕ => if i = 0 then ({b} : Set Bool) else Set.univ) =
          Set.pi ((insert 0 s : Finset ℕ) : Set ℕ)
            (fun i => if i = 0 then ({b} : Set Bool) else t i) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_pi, Set.mem_univ]
      constructor
      · intro hx i hi
        by_cases hi0 : i = 0
        · subst i; exact hx.2 0 (by simp)
        · simpa [hi0] using hx.1 i (by simpa [hi0] using hi)
      · intro hx
        refine ⟨?_, ?_⟩
        · intro i hi
          by_cases hi0 : i = 0
          · subst i; exact False.elim (h0 (by simpa using hi))
          · simpa [hi0] using hx i (by simpa [hi] using hi)
        · intro i hi
          by_cases hi0 : i = 0
          · subst i
            have hxi := hx 0 (by simp)
            simpa using hxi
          · simp [hi0]
    rw [hinter]
    change ((2 : ℝ≥0∞) • μC _) = _
    simp only [smul_eq_mul]
    change (2 : ℝ≥0∞) * Measure.infinitePi (fun _ : ℕ => bernoulliHalf) _ = _
    rw [Measure.infinitePi_pi
      (μ := fun _ : ℕ => bernoulliHalf) (s := insert 0 s)]
    · have hleft :
          (∏ i ∈ insert 0 s, bernoulliHalf (if i = 0 then {b} else t i)) =
            bernoulliHalf {b} * ∏ i ∈ s, bernoulliHalf (t i) := by
          rw [Finset.prod_insert h0]
          congr 1
          apply Finset.prod_congr rfl
          intro i hi
          have hi0 : i ≠ 0 := by
            intro hi0
            apply h0
            simpa [hi0] using hi
          simp [hi0]
      have hright :
          (∏ i ∈ s, (if i = 0 then Measure.dirac b else bernoulliHalf) (t i)) =
            ∏ i ∈ s, bernoulliHalf (t i) := by
        apply Finset.prod_congr rfl
        intro i hi
        have hi0 : i ≠ 0 := by
          intro hi0
          apply h0
          simpa [hi0] using hi
        simp [hi0]
      rw [hleft]
      rw [hright]
      have hhalf : (2 : ℝ≥0∞) * (1 / 2 : ℝ≥0∞) = 1 := by
        simpa [one_div] using
          (ENNReal.mul_inv_cancel (a := (2 : ℝ≥0∞)) (by norm_num)
            (ENNReal.ofNat_ne_top (n := 2)))
      rw [bernoulliHalf_singleton, ← mul_assoc, hhalf, one_mul]
    · intro i hi
      by_cases hi0 : i = 0
      · subst i; simp
      · exact ht i

theorem prependBit_restrict_branch_eq_half_smul_measure (b : Bool) :
    μC.restrict (Set.range (prependBit b)) =
      (1 / 2 : ℝ≥0∞) • prependBitBranchProductMeasure b := by
  rw [← prependBit_measure_map_eq_branchProductMeasure b]
  rw [prependBit_measure_map_eq_two_restrict_branch b]
  apply Measure.ext
  intro s hs
  simp only [Measure.smul_apply, smul_eq_mul]
  have hhalf : (1 / 2 : ℝ≥0∞) * 2 = 1 := by
    simpa [one_div] using
      (ENNReal.inv_mul_cancel (a := (2 : ℝ≥0∞)) (by norm_num)
        (ENNReal.ofNat_ne_top (n := 2)))
  calc
    μC.restrict (Set.range (prependBit b)) s =
        ((1 / 2 : ℝ≥0∞) * 2) *
          (μC.restrict (Set.range (prependBit b)) s) := by rw [hhalf, one_mul]
    _ = (1 / 2 : ℝ≥0∞) *
          (2 * (μC.restrict (Set.range (prependBit b)) s)) := by rw [mul_assoc]

theorem tail_measure_map_branchProductMeasure (b : Bool) :
    Measure.map tail (prependBitBranchProductMeasure b) = μC := by
  rw [← prependBit_measure_map_eq_branchProductMeasure b]
  rw [Measure.map_map (μ := μC) (f := prependBit b) (g := tail)
    InfoGeometry.Canonical.UHFInductiveColimitBoundaryTopology.continuous_tail.measurable
    (InfoGeometry.Canonical.UHFInductiveColimitBoundaryTopology.continuous_prependBit b).measurable]
  simpa [Function.comp_def, tail_prependBit] using
    (Measure.map_id (μ := μC))

theorem tail_measure_map_restrict_prependBitBranch (b : Bool) :
    Measure.map tail (μC.restrict (Set.range (prependBit b))) =
      (1 / 2 : ℝ≥0∞) • μC := by
  have hcomp :
      Measure.map tail (Measure.map (prependBit b) μC) = μC := by
    rw [Measure.map_map
      InfoGeometry.Canonical.UHFInductiveColimitBoundaryTopology.continuous_tail.measurable
      (InfoGeometry.Canonical.UHFInductiveColimitBoundaryTopology.continuous_prependBit b).measurable]
    simpa [Function.comp_def, tail_prependBit] using
      (Measure.map_id (μ := μC))
  rw [prependBit_measure_map_eq_two_restrict_branch b,
    Measure.map_smul] at hcomp
  apply Measure.ext
  intro s hs
  have h := congrArg (fun ν : Measure Boundary => ν s) hcomp
  simp only [Measure.smul_apply, smul_eq_mul] at h ⊢
  rw [← h]
  rw [one_div, ← mul_assoc,
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

def prependBitMeasurePreserving (b : Bool) :
    MeasurePreserving (prependBit b) μC (prependBitBranchProductMeasure b) :=
  { measurable :=
      (InfoGeometry.Canonical.UHFInductiveColimitBoundaryTopology.continuous_prependBit b).measurable
    map_eq := prependBit_measure_map_eq_branchProductMeasure b }

def tailBranchMeasurePreserving (b : Bool) :
    MeasurePreserving tail (prependBitBranchProductMeasure b) μC :=
  { measurable :=
      InfoGeometry.Canonical.UHFInductiveColimitBoundaryTopology.continuous_tail.measurable
    map_eq := tail_measure_map_branchProductMeasure b }

abbrev BranchL2 (b : Bool) :=
  Lp ℂ 2 (prependBitBranchProductMeasure b)

def branchTailLpIsometry (b : Bool) :
    L2Boundary →ₗᵢ[ℂ] BranchL2 b :=
  Lp.compMeasurePreservingₗᵢ ℂ tail (tailBranchMeasurePreserving b)

def branchPrependLpIsometry (b : Bool) :
    BranchL2 b →ₗᵢ[ℂ] L2Boundary :=
  Lp.compMeasurePreservingₗᵢ ℂ (prependBit b) (prependBitMeasurePreserving b)

theorem branchTailLpIsometry_norm (b : Bool) (f : L2Boundary) :
    ‖branchTailLpIsometry b f‖ = ‖f‖ := by
  exact Lp.norm_compMeasurePreserving f (tailBranchMeasurePreserving b)

theorem branchPrependLpIsometry_norm (b : Bool) (f : BranchL2 b) :
    ‖branchPrependLpIsometry b f‖ = ‖f‖ := by
  exact Lp.norm_compMeasurePreserving f (prependBitMeasurePreserving b)

theorem branchPrependLpIsometry_comp_branchTailLpIsometry (b : Bool)
    (f : L2Boundary) :
    branchPrependLpIsometry b (branchTailLpIsometry b f) = f := by
  apply Lp.ext
  have hout := Lp.coeFn_compMeasurePreserving
    (branchTailLpIsometry b f) (prependBitMeasurePreserving b)
  have hin := Lp.coeFn_compMeasurePreserving f (tailBranchMeasurePreserving b)
  have hin' := hin.comp_tendsto
    (prependBitMeasurePreserving b).quasiMeasurePreserving.tendsto_ae
  filter_upwards [hout, hin'] with x hx houtx
  calc
    branchPrependLpIsometry b (branchTailLpIsometry b f) x =
        branchTailLpIsometry b f (prependBit b x) := by
          simpa [Function.comp_apply] using hx
    _ = f (tail (prependBit b x)) := by
          simpa [Function.comp_apply] using houtx
    _ = f x := by rw [tail_prependBit]

theorem tail_measure_map : Measure.map tail μC = μC := by
  apply Measure.eq_infinitePi
  intro s t ht
  have htail : Measurable (tail : Boundary → Boundary) :=
    InfoGeometry.Canonical.UHFInductiveColimitBoundaryTopology.continuous_tail.measurable
  have hpi : MeasurableSet (Set.pi s t) :=
    MeasurableSet.pi s.countable_toSet (fun i hi => ht i)
  rw [Measure.map_apply htail hpi]
  rw [tail_preimage_pi s t]
  change Measure.infinitePi (fun _ : ℕ => bernoulliHalf) _ = _
  have hleft :
      Measure.infinitePi (fun _ : ℕ => bernoulliHalf)
          (Set.pi (s.image Nat.succ)
            (fun j => if h : ∃ i ∈ s, Nat.succ i = j then
              t (Classical.choose h) else Set.univ)) =
        ∏ j ∈ s.image Nat.succ,
          bernoulliHalf
            (if h : ∃ i ∈ s, Nat.succ i = j then
              t (Classical.choose h) else Set.univ) := by
    apply Measure.infinitePi_pi
    intro j hj
    split_ifs with h
    · exact ht _
    · exact MeasurableSet.univ
  rw [hleft, Finset.prod_image]
  · apply Finset.prod_congr rfl
    intro i hi
    have hh : ∃ k ∈ s, Nat.succ k = Nat.succ i := ⟨i, hi, rfl⟩
    have hchoose : Classical.choose hh = i := by
      apply Nat.succ.inj
      exact (Classical.choose_spec hh).2
    rw [dif_pos hh, hchoose]
  · intro a ha b hb h
    exact Nat.succ.inj h

theorem tail_measurePreserving : MeasurePreserving tail μC μC :=
  { measurable :=
      InfoGeometry.Canonical.UHFInductiveColimitBoundaryTopology.continuous_tail.measurable
    map_eq := tail_measure_map }

def tailLpIsometry
    (hTail : MeasurePreserving tail μC μC) :
    L2Boundary →ₗᵢ[ℂ] L2Boundary :=
  Lp.compMeasurePreservingₗᵢ ℂ tail hTail

def canonicalTailLpIsometry : L2Boundary →ₗᵢ[ℂ] L2Boundary :=
  Lp.compMeasurePreservingₗᵢ ℂ tail tail_measurePreserving

theorem tailLpIsometry_apply
    (hTail : MeasurePreserving tail μC μC) (f : L2Boundary) :
    tailLpIsometry hTail f = Lp.compMeasurePreserving tail hTail f :=
  rfl

theorem tailLpIsometry_norm
    (hTail : MeasurePreserving tail μC μC) (f : L2Boundary) :
    ‖tailLpIsometry hTail f‖ = ‖f‖ := by
  exact Lp.norm_compMeasurePreserving f hTail

theorem canonicalTailLpIsometry_apply (f : L2Boundary) :
    canonicalTailLpIsometry f =
      Lp.compMeasurePreserving tail tail_measurePreserving f :=
  rfl

theorem canonicalTailLpIsometry_norm (f : L2Boundary) :
    ‖canonicalTailLpIsometry f‖ = ‖f‖ := by
  exact Lp.norm_compMeasurePreserving f tail_measurePreserving

theorem canonicalTailLpIsometry_isometry :
    Isometry canonicalTailLpIsometry := by
  exact Lp.isometry_compMeasurePreserving tail_measurePreserving

def prependBitBranch (b : Bool) : Set Boundary :=
  Set.pi ({0} : Finset ℕ) (fun _ => ({b} : Set Bool))

theorem prependBitBranch_eq_range (b : Bool) :
    prependBitBranch b = Set.range (prependBit b) := by
  ext x
  constructor
  · intro hx
    have hx0 : x 0 = b := by
      simpa [prependBitBranch] using hx 0 (by simp)
    exact ⟨tail x, prependBit_tail_of_head hx0⟩
  · rintro ⟨y, rfl⟩
    intro i hi
    have hi0 : i = 0 := by
      have : i ∈ ({0} : Finset ℕ) := hi
      simpa using this
    subst i
    simp [prependBit]

theorem measurableSet_prependBitBranch (b : Bool) :
    MeasurableSet (prependBitBranch b) := by
  apply MeasurableSet.pi (by simp)
  intro i hi
  simp

theorem prependBit_inter_branch_insert (b : Bool) (s : Finset ℕ)
    (t : ℕ → Set Bool) (h0 : 0 ∉ s) :
    Set.pi s t ∩ prependBitBranch b =
      Set.pi (↑(insert 0 s) : Set ℕ)
        (fun i => if i = 0 then ({b} : Set Bool) else t i) := by
  have hQ : Set.pi s t =
      Set.pi Set.univ (fun i => if i ∈ s then t i else Set.univ) := by
    exact (Set.pi_univ_ite (s : Set ℕ) t).symm
  have hB : prependBitBranch b =
      Set.pi Set.univ (fun i => if i = 0 then ({b} : Set Bool) else Set.univ) := by
    rw [prependBitBranch, ← Set.pi_univ_ite]
    congr 1
    funext i
    by_cases hi : i = 0 <;> simp [hi]
  rw [hQ, hB, ← Set.pi_inter_distrib]
  have hfun :
      (fun i => (if i ∈ s then t i else Set.univ) ∩
          (if i = 0 then ({b} : Set Bool) else Set.univ)) =
        (fun i => if i ∈ insert 0 s then
          (if i = 0 then ({b} : Set Bool) else t i) else Set.univ) := by
    funext i
    by_cases hi : i = 0
    · subst i
      simp [h0]
    · by_cases his : i ∈ s
      · have hins : i ∈ insert 0 s := by simp [his]
        simp only [if_pos his, if_neg hi, if_pos hins, Set.inter_univ]
      · have hins : i ∉ insert 0 s := by simp [hi, his]
        simp [hi, his, hins]
  rw [hfun]
  simpa [Set.mem_insert_iff] using
    (Set.pi_univ_ite (↑(insert 0 s) : Set ℕ)
      (fun i => if i = 0 then ({b} : Set Bool) else t i))

theorem prependBit_inter_branch_existing (b : Bool) (s : Finset ℕ)
    (t : ℕ → Set Bool) (h0 : 0 ∈ s) (hb : b ∈ t 0) :
    Set.pi s t ∩ prependBitBranch b =
      Set.pi s (fun i => if i = 0 then ({b} : Set Bool) else t i) := by
  have hQ : Set.pi s t =
      Set.pi Set.univ (fun i => if i ∈ s then t i else Set.univ) := by
    exact (Set.pi_univ_ite (s : Set ℕ) t).symm
  have hB : prependBitBranch b =
      Set.pi Set.univ (fun i => if i = 0 then ({b} : Set Bool) else Set.univ) := by
    rw [prependBitBranch, ← Set.pi_univ_ite]
    congr 1
    funext i
    by_cases hi : i = 0 <;> simp [hi]
  rw [hQ, hB, ← Set.pi_inter_distrib]
  have hfun :
      (fun i => (if i ∈ s then t i else Set.univ) ∩
          (if i = 0 then ({b} : Set Bool) else Set.univ)) =
        (fun i => if i ∈ s then
          (if i = 0 then ({b} : Set Bool) else t i) else Set.univ) := by
    funext i
    by_cases hi : i = 0
    · subst i
      simp [h0, hb]
    · by_cases his : i ∈ s
      · simp only [if_pos his, if_neg hi, Set.inter_univ]
      · simp [hi, his]
  rw [hfun]
  exact (Set.pi_univ_ite (s : Set ℕ)
    (fun i => if i = 0 then ({b} : Set Bool) else t i))

theorem prependBit_measure_map_eq_two_restrict_branch_via_cylinder_helpers (b : Bool) :
    Measure.map (prependBit b) μC =
      2 • μC.restrict (prependBitBranch b) := by
  rw [prependBit_measure_map_eq_branchProductMeasure b]
  symm
  apply Measure.eq_infinitePi
  intro s t ht
  symm
  have hpi : MeasurableSet (Set.pi s t) :=
    MeasurableSet.pi s.countable_toSet (fun i hi => ht i)
  simp only [Measure.coe_smul, Pi.smul_apply, Measure.restrict_apply hpi]
  by_cases h0 : 0 ∈ s
  · by_cases hb : b ∈ t 0
    · have hinter := prependBit_inter_branch_existing b s t h0 hb
      rw [hinter]
      rw [show μC = Measure.infinitePi (fun _ : ℕ => bernoulliHalf) from rfl,
        Measure.infinitePi_pi]
      · have hprod :
            (∏ i ∈ s, (if i = 0 then Measure.dirac b else bernoulliHalf) (t i)) =
              ∏ i ∈ s.erase 0, bernoulliHalf (t i) := by
          rw [← Finset.prod_erase_mul s
            (fun i => (if i = 0 then Measure.dirac b else bernoulliHalf) (t i)) h0]
          simp [hb]
          apply Finset.prod_congr rfl
          intro i hi
          have hi0 : i ≠ 0 := (Finset.mem_erase.mp hi).1
          simp [hi0]
        rw [hprod]
        rw [← Finset.prod_erase_mul s
          (fun i => bernoulliHalf (if i = 0 then ({b} : Set Bool) else t i)) h0]
        have hrest :
            (∏ i ∈ s.erase 0,
              bernoulliHalf (if i = 0 then ({b} : Set Bool) else t i)) =
              ∏ i ∈ s.erase 0, bernoulliHalf (t i) := by
          apply Finset.prod_congr rfl
          intro i hi
          have hi0 : i ≠ 0 := (Finset.mem_erase.mp hi).1
          simp [hi0]
        rw [hrest]
        rw [two_nsmul]
        simp only [if_true, bernoulliHalf_singleton]
        have hhalf : (2 : ℝ≥0∞) * (1 / 2 : ℝ≥0∞) = 1 := by
          simpa [one_div] using
            (ENNReal.mul_inv_cancel (a := (2 : ℝ≥0∞)) (by norm_num)
              (ENNReal.ofNat_ne_top (n := 2)))
        calc
          (∏ i ∈ s.erase 0, bernoulliHalf (t i)) =
              (2 * (1 / 2 : ℝ≥0∞)) *
                (∏ i ∈ s.erase 0, bernoulliHalf (t i)) := by rw [hhalf, one_mul]
          _ = 2 * ((∏ i ∈ s.erase 0, bernoulliHalf (t i)) * (1 / 2 : ℝ≥0∞)) := by
            ring
          _ = (∏ i ∈ s.erase 0, bernoulliHalf (t i)) * (1 / 2 : ℝ≥0∞) +
              (∏ i ∈ s.erase 0, bernoulliHalf (t i)) * (1 / 2 : ℝ≥0∞) := by
            exact two_mul _
      · intro i hi
        by_cases hi0 : i = 0
        · subst i; exact measurableSet_singleton b
        · simpa [hi0] using ht i hi
    · have hempty : Set.pi s t ∩ prependBitBranch b = ∅ := by
        rw [show prependBitBranch b = Set.pi ({0} : Finset ℕ)
          (fun _ => ({b} : Set Bool)) from rfl]
        ext x
        simp only [Set.mem_inter_iff, Set.mem_pi, Set.mem_empty_iff_false, iff_false]
        intro hx
        have hxb : x 0 = b := by simpa using hx.2 0 (by simp)
        exact hb (hxb ▸ hx.1 0 (by exact h0))
      rw [hempty, measure_empty]
      simpa using (Finset.prod_eq_zero (f := fun i : ℕ =>
          (if i = 0 then Measure.dirac b else bernoulliHalf) (t i)) h0
          (by simp [hb]))
  · have hinter := prependBit_inter_branch_insert b s t h0
    rw [hinter]
    rw [two_nsmul]
    rw [show μC = Measure.infinitePi (fun _ : ℕ => bernoulliHalf) from rfl,
      Measure.infinitePi_pi]
    · rw [Finset.prod_insert h0]
      simp only [if_true, bernoulliHalf_singleton]
      have hrest :
          (∏ i ∈ s, bernoulliHalf (if i = 0 then ({b} : Set Bool) else t i)) =
            ∏ i ∈ s, bernoulliHalf (t i) := by
        apply Finset.prod_congr rfl
        intro i hi
        have hi0 : i ≠ 0 := by exact fun hi0 => h0 (hi0 ▸ hi)
        simp [hi0]
      rw [hrest]
      have hleft :
          (∏ i ∈ s, (if i = 0 then Measure.dirac b else bernoulliHalf) (t i)) =
            ∏ i ∈ s, bernoulliHalf (t i) := by
        apply Finset.prod_congr rfl
        intro i hi
        have hi0 : i ≠ 0 := by exact fun hi0 => h0 (hi0 ▸ hi)
        simp [hi0]
      rw [hleft]
      rw [← two_mul]
      have hhalf : (2 : ℝ≥0∞) * (1 / 2 : ℝ≥0∞) = 1 := by
        simpa [one_div] using
          (ENNReal.mul_inv_cancel (a := (2 : ℝ≥0∞)) (by norm_num)
            (ENNReal.ofNat_ne_top (n := 2)))
      calc
        (∏ i ∈ s, bernoulliHalf (t i)) =
            (2 * (1 / 2 : ℝ≥0∞)) * (∏ i ∈ s, bernoulliHalf (t i)) := by
              rw [hhalf, one_mul]
        _ = 2 * ((1 / 2 : ℝ≥0∞) * (∏ i ∈ s, bernoulliHalf (t i))) := by ring
    · intro i hi
      by_cases hi0 : i = 0
      · subst i; exact measurableSet_singleton b
      · simpa [hi0] using ht i hi

def rawPrependBitFunction (b : Bool) (f : L2Boundary) : Boundary → ℂ :=
  (prependBitBranch b).indicator (fun x => f (tail x))

theorem rawPrependBitFunction_eLpNorm (b : Bool) (f : L2Boundary) :
    eLpNorm (rawPrependBitFunction b f) 2 μC =
      (1 / 2 : ℝ≥0∞) ^ (1 / (2 : ℝ≥0∞)).toReal *
        eLpNorm (f : Boundary →ₘ[μC] ℂ) 2 μC := by
  rw [rawPrependBitFunction,
    eLpNorm_indicator_eq_eLpNorm_restrict (measurableSet_prependBitBranch b),
    prependBitBranch_eq_range b,
    prependBit_restrict_branch_eq_half_smul_measure b]
  rw [eLpNorm_smul_measure_of_ne_zero (by norm_num : (1 / 2 : ℝ≥0∞) ≠ 0)]
  simp only [smul_eq_mul]
  have hnorm := eLpNorm_comp_measurePreserving (p := (2 : ℝ≥0∞))
      (Lp.aestronglyMeasurable f)
      (tailBranchMeasurePreserving b)
  simpa [Function.comp_def] using congrArg
    (fun z : ℝ≥0∞ => (1 / 2 : ℝ≥0∞) ^ (1 / (2 : ℝ≥0∞)).toReal * z) hnorm

theorem rawPrependBitFunction_memLp (b : Bool) (f : L2Boundary) :
    MemLp (rawPrependBitFunction b f) 2 μC := by
  apply MemLp.indicator (measurableSet_prependBitBranch b)
  have hcomp :
      MemLp ((fun x : Boundary => f x) ∘ tail) 2 μC :=
    (Lp.memLp f).comp_measurePreserving tail_measurePreserving
  simpa [rawPrependBitFunction] using hcomp

theorem rawPrependBitFunction_ae_congr (b : Bool)
    {f g : L2Boundary} (h : f =ᵐ[μC] g) :
    rawPrependBitFunction b f =ᵐ[μC] rawPrependBitFunction b g := by
  have hcomp :=
    h.comp_tendsto tail_measurePreserving.quasiMeasurePreserving.tendsto_ae
  filter_upwards [hcomp] with x hx
  by_cases hxb : x ∈ prependBitBranch b
  · simpa [rawPrependBitFunction, hxb, Function.comp_def] using hx
  · simp [rawPrependBitFunction, hxb]

def rawPrependBitLp (b : Bool) (f : L2Boundary) : L2Boundary :=
  (rawPrependBitFunction_memLp b f).toLp (rawPrependBitFunction b f)

theorem rawPrependBitLp_eLpNorm (b : Bool) (f : L2Boundary) :
    eLpNorm (rawPrependBitLp b f) 2 μC =
      (1 / 2 : ℝ≥0∞) ^ (1 / (2 : ℝ≥0∞)).toReal *
        eLpNorm (f : Boundary →ₘ[μC] ℂ) 2 μC := by
  rw [rawPrependBitLp]
  rw [eLpNorm_congr_ae (MemLp.coeFn_toLp (rawPrependBitFunction_memLp b f))]
  exact rawPrependBitFunction_eLpNorm b f

theorem rawPrependBitLp_norm_eq (b : Bool) (f : L2Boundary) :
    ‖rawPrependBitLp b f‖ =
      ((1 / 2 : ℝ≥0∞) ^ (1 / (2 : ℝ≥0∞)).toReal).toReal * ‖f‖ := by
  rw [rawPrependBitLp, Lp.norm_toLp, rawPrependBitFunction_eLpNorm,
    Lp.norm_def]
  rw [ENNReal.toReal_mul]

theorem rawPrependBitLp_norm_le (b : Bool) (f : L2Boundary) :
    ‖rawPrependBitLp b f‖ ≤ ‖f‖ := by
  rw [rawPrependBitLp, Lp.norm_toLp, Lp.norm_def]
  apply ENNReal.toReal_mono (Lp.eLpNorm_ne_top _)
  calc
    eLpNorm (rawPrependBitFunction b f) 2 μC ≤
        eLpNorm ((fun x : Boundary => f x) ∘ tail) 2 μC := by
      exact eLpNorm_indicator_le _
    _ = eLpNorm (f : Boundary →ₘ[μC] ℂ) 2 μC := by
      rw [← AEEqFun.eLpNorm_compMeasurePreserving
        (f : Boundary →ₘ[μC] ℂ) tail_measurePreserving]
      exact eLpNorm_congr_ae
        (Lp.coeFn_compMeasurePreserving f tail_measurePreserving).symm

theorem rawPrependBitLp_add (b : Bool) (f g : L2Boundary) :
    rawPrependBitLp b (f + g) =
      rawPrependBitLp b f + rawPrependBitLp b g := by
  rw [rawPrependBitLp, rawPrependBitLp, rawPrependBitLp]
  rw [← MemLp.toLp_add]
  apply (MemLp.toLp_eq_toLp_iff _ _).2
  have hfg := (Lp.coeFn_add f g).comp_tendsto
    tail_measurePreserving.quasiMeasurePreserving.tendsto_ae
  filter_upwards [hfg] with x hx
  by_cases hxb : x ∈ prependBitBranch b
  · simpa only [rawPrependBitFunction, Set.indicator_of_mem hxb,
      Function.comp_apply, Pi.add_apply] using hx
  · simp [rawPrependBitFunction, hxb]

theorem rawPrependBitLp_smul (b : Bool) (c : ℂ) (f : L2Boundary) :
    rawPrependBitLp b (c • f) = c • rawPrependBitLp b f := by
  rw [rawPrependBitLp, rawPrependBitLp]
  rw [← MemLp.toLp_const_smul]
  apply (MemLp.toLp_eq_toLp_iff _ _).2
  have hcf := (Lp.coeFn_smul c f).comp_tendsto
    tail_measurePreserving.quasiMeasurePreserving.tendsto_ae
  filter_upwards [hcf] with x hx
  by_cases hxb : x ∈ prependBitBranch b
  · simpa only [rawPrependBitFunction, Set.indicator_of_mem hxb,
      Function.comp_apply, Pi.smul_apply, smul_eq_mul] using hx
  · simp [rawPrependBitFunction, hxb]

def rawPrependBitLpLinearMap (b : Bool) : L2Boundary →ₗ[ℂ] L2Boundary where
  toFun := rawPrependBitLp b
  map_add' := rawPrependBitLp_add b
  map_smul' := rawPrependBitLp_smul b

def rawPrependBitLpContinuousLinearMap (b : Bool) : L2Boundary →L[ℂ] L2Boundary :=
  (rawPrependBitLpLinearMap b).mkContinuous 1 (by
    intro f
    simpa using rawPrependBitLp_norm_le b f)

noncomputable def prependBitLpNormFactor : ℝ :=
  ((1 / 2 : ℝ≥0∞) ^ (1 / (2 : ℝ≥0∞)).toReal).toReal

theorem prependBitLpNormFactor_pos : 0 < prependBitLpNormFactor := by
  unfold prependBitLpNormFactor
  apply ENNReal.toReal_pos
  · norm_num
  · finiteness

theorem prependBitLpNormFactor_sq :
    prependBitLpNormFactor ^ 2 = (1 / 2 : ℝ) := by
  unfold prependBitLpNormFactor
  rw [pow_two]
  let x : ℝ≥0∞ := (1 / 2 : ℝ≥0∞) ^ (1 / (2 : ℝ≥0∞)).toReal
  have hmul : (x * x).toReal = x.toReal * x.toReal := by
    rw [ENNReal.toReal_mul] <;> norm_num
  change x.toReal * x.toReal = (1 / 2 : ℝ)
  rw [← hmul]
  dsimp [x]
  rw [← ENNReal.rpow_add]
  all_goals norm_num [ENNReal.toReal_ofNat]

noncomputable def normalizedPrependBitLpContinuousLinearMap (b : Bool) :
    L2Boundary →L[ℂ] L2Boundary :=
  (prependBitLpNormFactor⁻¹ : ℂ) • rawPrependBitLpContinuousLinearMap b

theorem normalizedPrependBitLpContinuousLinearMap_apply
    (b : Bool) (f : L2Boundary) :
    normalizedPrependBitLpContinuousLinearMap b f =
      (prependBitLpNormFactor⁻¹ : ℂ) • rawPrependBitLp b f := by
  rfl

theorem normalizedPrependBitLpContinuousLinearMap_norm
    (b : Bool) (f : L2Boundary) :
    ‖normalizedPrependBitLpContinuousLinearMap b f‖ = ‖f‖ := by
  rw [normalizedPrependBitLpContinuousLinearMap_apply,
    norm_smul, rawPrependBitLp_norm_eq]
  have hpos := prependBitLpNormFactor_pos
  have hne : prependBitLpNormFactor ≠ 0 := ne_of_gt hpos
  have hnorm : ‖(prependBitLpNormFactor⁻¹ : ℂ)‖ = prependBitLpNormFactor⁻¹ := by
    simp [Complex.norm_real, norm_inv, abs_of_pos hpos]
  rw [hnorm]
  have hfactor :
      ((1 / 2 : ℝ≥0∞) ^ (1 / (2 : ℝ≥0∞)).toReal).toReal =
        prependBitLpNormFactor := rfl
  have hfactor0 :
      ((1 / 2 : ℝ≥0∞) ^ (1 / (2 : ℝ≥0∞)).toReal).toReal ≠ 0 := by
    rw [hfactor]
    exact hne
  rw [hfactor, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

theorem normalizedPrependBitLpContinuousLinearMap_isometry :
    Isometry (normalizedPrependBitLpContinuousLinearMap b) := by
  intro f g
  have hnormf := normalizedPrependBitLpContinuousLinearMap_norm b (f - g)
  rw [Lp.edist_dist, Lp.edist_dist, dist_eq_norm, dist_eq_norm, ← map_sub]
  exact congrArg ENNReal.ofReal hnormf

def normalizedPrependBitLpAdjoint (b : Bool) :
    L2Boundary →L[ℂ] L2Boundary :=
  ContinuousLinearMap.adjoint (normalizedPrependBitLpContinuousLinearMap b)

theorem normalizedPrependBitLpAdjoint_inner_left (b : Bool)
    (f g : L2Boundary) :
    inner ℂ (normalizedPrependBitLpAdjoint b f) g =
      inner ℂ f (normalizedPrependBitLpContinuousLinearMap b g) := by
  exact ContinuousLinearMap.adjoint_inner_left
    (normalizedPrependBitLpContinuousLinearMap b) g f

theorem normalizedPrependBitLpAdjoint_comp_self (b : Bool) :
    (normalizedPrependBitLpAdjoint b).comp
        (normalizedPrependBitLpContinuousLinearMap b) =
      ContinuousLinearMap.id ℂ L2Boundary := by
  exact (ContinuousLinearMap.norm_map_iff_adjoint_comp_self
    (normalizedPrependBitLpContinuousLinearMap b)).mp (by
      intro f
      exact normalizedPrependBitLpContinuousLinearMap_norm b f)

theorem rawPrependBitLp_inner_zero {b c : Bool} (hbc : b ≠ c)
    (f g : L2Boundary) :
    inner ℂ (rawPrependBitLp b f) (rawPrependBitLp c g) = 0 := by
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  have hfb := MemLp.coeFn_toLp (rawPrependBitFunction_memLp b f)
  have hgc := MemLp.coeFn_toLp (rawPrependBitFunction_memLp c g)
  filter_upwards [hfb, hgc] with x hfx hgx
  rw [rawPrependBitLp, rawPrependBitLp, hfx, hgx]
  by_cases hxb : x ∈ prependBitBranch b
  · have hxc : x ∉ prependBitBranch c := by
      intro hxc
      have hb : x 0 = b := by
        simpa [prependBitBranch] using hxb 0 (by simp)
      have hc : x 0 = c := by
        simpa [prependBitBranch] using hxc 0 (by simp)
      exact hbc (hb.symm.trans hc)
    simp [rawPrependBitFunction, hxb, hxc]
  · simp [rawPrependBitFunction, hxb]

theorem normalizedPrependBitLpContinuousLinearMap_inner_zero
    {b c : Bool} (hbc : b ≠ c) (f g : L2Boundary) :
    inner ℂ (normalizedPrependBitLpContinuousLinearMap b f)
      (normalizedPrependBitLpContinuousLinearMap c g) = 0 := by
  rw [normalizedPrependBitLpContinuousLinearMap_apply,
    normalizedPrependBitLpContinuousLinearMap_apply]
  rw [inner_smul_left, inner_smul_right, rawPrependBitLp_inner_zero hbc]
  simp

theorem normalizedPrependBitLpAdjoint_comp_cross_eq_zero
    {b c : Bool} (hbc : b ≠ c) :
    (normalizedPrependBitLpAdjoint b).comp
        (normalizedPrependBitLpContinuousLinearMap c) = 0 := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right ℂ
  intro g
  rw [ContinuousLinearMap.comp_apply]
  calc
    inner ℂ (normalizedPrependBitLpAdjoint b
        (normalizedPrependBitLpContinuousLinearMap c f)) g =
        inner ℂ (normalizedPrependBitLpContinuousLinearMap c f)
          (normalizedPrependBitLpContinuousLinearMap b g) :=
      normalizedPrependBitLpAdjoint_inner_left b
        (normalizedPrependBitLpContinuousLinearMap c f) g
    _ = 0 := normalizedPrependBitLpContinuousLinearMap_inner_zero hbc.symm f g
    _ = inner ℂ (0 : L2Boundary) g := by simp

def prependBitFunction (b : Bool) (f : L2Boundary) : Boundary → ℂ :=
  fun x => f (prependBit b x)

theorem prependBitFunction_memLp (b : Bool) (f : L2Boundary) :
    MemLp (prependBitFunction b f) 2 μC := by
  have hbranch : prependBitBranchProductMeasure b =
      (2 : ℝ≥0∞) • μC.restrict (prependBitBranch b) := by
    rw [prependBitBranch_eq_range,
      ← prependBit_measure_map_eq_branchProductMeasure b,
      prependBit_measure_map_eq_two_restrict_branch]
  have hrestrict :
      MemLp (fun x : Boundary => f x) 2 (μC.restrict (prependBitBranch b)) :=
    (Lp.memLp f).restrict (prependBitBranch b)
  have hbranch_memLp :
      MemLp (fun x : Boundary => f x) 2
        (prependBitBranchProductMeasure b) := by
    rw [hbranch]
    exact hrestrict.smul_measure (by simp)
  have hcomp := hbranch_memLp.comp_measurePreserving
    (prependBitMeasurePreserving b)
  simpa [prependBitFunction, Function.comp_def] using hcomp

def prependBitLp (b : Bool) (f : L2Boundary) : L2Boundary :=
  (prependBitFunction_memLp b f).toLp (prependBitFunction b f)

def branchIndicatorFunction (b : Bool) (f : L2Boundary) : Boundary → ℂ :=
  (prependBitBranch b).indicator (fun x => f x)

theorem branchIndicatorFunction_memLp (b : Bool) (f : L2Boundary) :
    MemLp (branchIndicatorFunction b f) 2 μC := by
  apply MemLp.indicator (measurableSet_prependBitBranch b)
  exact Lp.memLp f

def branchIndicatorLp (b : Bool) (f : L2Boundary) : L2Boundary :=
  (branchIndicatorFunction_memLp b f).toLp (branchIndicatorFunction b f)

theorem rawPrependBitLp_prependBitLp (b : Bool) (f : L2Boundary) :
    rawPrependBitLp b (prependBitLp b f) = branchIndicatorLp b f := by
  apply Lp.ext
  rw [rawPrependBitLp, branchIndicatorLp]
  have hraw := MemLp.coeFn_toLp
    (rawPrependBitFunction_memLp b (prependBitLp b f))
  have hpre := MemLp.coeFn_toLp (prependBitFunction_memLp b f)
  have hpre_tail := hpre.comp_tendsto
    tail_measurePreserving.quasiMeasurePreserving.tendsto_ae
  have hleft := MemLp.coeFn_toLp (branchIndicatorFunction_memLp b f)
  filter_upwards [hraw, hpre_tail, hleft] with x hrawx hprex hleftx
  rw [hrawx, hleftx]
  by_cases hxb : x ∈ prependBitBranch b
  · rw [rawPrependBitFunction, Set.indicator_of_mem hxb]
    rw [branchIndicatorFunction, Set.indicator_of_mem hxb]
    rw [prependBitLp]
    have hxhead : x 0 = b := by
      simpa [prependBitBranch] using hxb 0 (by simp)
    calc
      (MemLp.toLp (prependBitFunction b f) (prependBitFunction_memLp b f))
          (tail x) = prependBitFunction b f (tail x) := by
            simpa [Function.comp_apply] using hprex
      _ = f (prependBit b (tail x)) := rfl
      _ = f x := by rw [prependBit_tail_of_head hxhead]
  · simp [rawPrependBitFunction, branchIndicatorFunction, hxb]

theorem branchIndicatorLp_partition (f : L2Boundary) :
    branchIndicatorLp false f + branchIndicatorLp true f = f := by
  apply Lp.ext
  have h0 :
      ((branchIndicatorLp false f : L2Boundary) : Boundary → ℂ) =ᵐ[μC]
        branchIndicatorFunction false f := by
    exact MemLp.coeFn_toLp (branchIndicatorFunction_memLp false f)
  have h1 :
      ((branchIndicatorLp true f : L2Boundary) : Boundary → ℂ) =ᵐ[μC]
        branchIndicatorFunction true f := by
    exact MemLp.coeFn_toLp (branchIndicatorFunction_memLp true f)
  have hsum := Lp.coeFn_add (branchIndicatorLp false f)
    (branchIndicatorLp true f)
  have hf := MemLp.coeFn_toLp (Lp.memLp f)
  filter_upwards [hsum, h0, h1, hf] with x hsumx h0x h1x hfx
  rw [hsumx]
  change branchIndicatorLp false f x + branchIndicatorLp true f x = f x
  calc
    branchIndicatorLp false f x + branchIndicatorLp true f x =
        branchIndicatorFunction false f x +
          branchIndicatorFunction true f x := by rw [h0x, h1x]
    _ = f x := by
      by_cases hx : x 0 = false
      · have hx0 : x ∈ prependBitBranch false := by
          simpa [prependBitBranch] using hx
        have hx1 : x ∉ prependBitBranch true := by
          intro hx1
          have : x 0 = true := by
            simpa [prependBitBranch] using hx1 0 (by simp)
          exact Bool.noConfusion (hx.symm.trans this)
        simp [branchIndicatorFunction, hx0, hx1]
      · have hx1bit : x 0 = true := by
          match h : x 0 with
          | true => rfl
          | false => contradiction
        have hx1 : x ∈ prependBitBranch true := by
          simpa [prependBitBranch] using hx1bit
        have hx0 : x ∉ prependBitBranch false := by
          intro hx0
          have : x 0 = false := by
            simpa [prependBitBranch] using hx0 0 (by simp)
          exact Bool.noConfusion (hx1bit.symm.trans this)
        simp [branchIndicatorFunction, hx0, hx1]
def rawPrependBitLpAdjoint (b : Bool) : L2Boundary →L[ℂ] L2Boundary :=
  ContinuousLinearMap.adjoint (rawPrependBitLpContinuousLinearMap b)

theorem rawPrependBitLpAdjoint_inner_left (b : Bool) (f g : L2Boundary) :
    inner ℂ (rawPrependBitLpAdjoint b f) g =
      inner ℂ f (rawPrependBitLpContinuousLinearMap b g) := by
  exact ContinuousLinearMap.adjoint_inner_left
    (rawPrependBitLpContinuousLinearMap b) g f

theorem normalizedPrependBitLp_range_decomposition (f : L2Boundary) :
    ∃ f₀ f₁ : L2Boundary,
      normalizedPrependBitLpContinuousLinearMap false f₀ +
          normalizedPrependBitLpContinuousLinearMap true f₁ = f := by
  let k : ℂ := prependBitLpNormFactor
  have hk : k ≠ 0 := by
    dsimp [k]
    exact_mod_cast (ne_of_gt prependBitLpNormFactor_pos)
  refine ⟨k • prependBitLp false f, k • prependBitLp true f, ?_⟩
  rw [normalizedPrependBitLpContinuousLinearMap_apply,
    normalizedPrependBitLpContinuousLinearMap_apply,
    rawPrependBitLp_smul, rawPrependBitLp_smul,
    rawPrependBitLp_prependBitLp, rawPrependBitLp_prependBitLp]
  change (k⁻¹ : ℂ) • (k • branchIndicatorLp false f) +
      (k⁻¹ : ℂ) • (k • branchIndicatorLp true f) = f
  rw [inv_smul_smul₀ hk, inv_smul_smul₀ hk,
    branchIndicatorLp_partition]

theorem normalizedPrependBitLp_partition :
    (normalizedPrependBitLpContinuousLinearMap false).comp (normalizedPrependBitLpAdjoint false) +
    (normalizedPrependBitLpContinuousLinearMap true).comp (normalizedPrependBitLpAdjoint true) =
    ContinuousLinearMap.id ℂ L2Boundary := by
  apply ContinuousLinearMap.ext
  intro f
  let k : ℂ := prependBitLpNormFactor
  have hk : k ≠ 0 := by
    dsimp [k]
    exact_mod_cast (ne_of_gt prependBitLpNormFactor_pos)
  let f₀ := k • prependBitLp false f
  let f₁ := k • prependBitLp true f
  have hf : normalizedPrependBitLpContinuousLinearMap false f₀ + normalizedPrependBitLpContinuousLinearMap true f₁ = f := by
    rw [normalizedPrependBitLpContinuousLinearMap_apply,
      normalizedPrependBitLpContinuousLinearMap_apply,
      rawPrependBitLp_smul, rawPrependBitLp_smul,
      rawPrependBitLp_prependBitLp, rawPrependBitLp_prependBitLp]
    change (k⁻¹ : ℂ) • (k • branchIndicatorLp false f) +
        (k⁻¹ : ℂ) • (k • branchIndicatorLp true f) = f
    rw [inv_smul_smul₀ hk, inv_smul_smul₀ hk,
      branchIndicatorLp_partition]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
  rw [← hf]
  have hF : (normalizedPrependBitLpAdjoint false) (normalizedPrependBitLpContinuousLinearMap false f₀ + normalizedPrependBitLpContinuousLinearMap true f₁) = f₀ := by
    rw [map_add]
    have hself : (normalizedPrependBitLpAdjoint false) (normalizedPrependBitLpContinuousLinearMap false f₀) = f₀ := by
      have hcomp := ContinuousLinearMap.ext_iff.mp (normalizedPrependBitLpAdjoint_comp_self false) f₀
      exact hcomp
    have hcross : (normalizedPrependBitLpAdjoint false) (normalizedPrependBitLpContinuousLinearMap true f₁) = 0 := by
      have hcomp := ContinuousLinearMap.ext_iff.mp (normalizedPrependBitLpAdjoint_comp_cross_eq_zero (by decide : false ≠ true)) f₁
      exact hcomp
    rw [hself, hcross, add_zero]
  have hT : (normalizedPrependBitLpAdjoint true) (normalizedPrependBitLpContinuousLinearMap false f₀ + normalizedPrependBitLpContinuousLinearMap true f₁) = f₁ := by
    rw [map_add]
    have hcross : (normalizedPrependBitLpAdjoint true) (normalizedPrependBitLpContinuousLinearMap false f₀) = 0 := by
      have hcomp := ContinuousLinearMap.ext_iff.mp (normalizedPrependBitLpAdjoint_comp_cross_eq_zero (by decide : true ≠ false)) f₀
      exact hcomp
    have hself : (normalizedPrependBitLpAdjoint true) (normalizedPrependBitLpContinuousLinearMap true f₁) = f₁ := by
      have hcomp := ContinuousLinearMap.ext_iff.mp (normalizedPrependBitLpAdjoint_comp_self true) f₁
      exact hcomp
    rw [hcross, hself, zero_add]
  rw [hF, hT]

end InfoGeometry.Canonical.CantorBernoulliL2OperatorTransport
