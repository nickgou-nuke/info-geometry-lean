import Mathlib
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prod

namespace InfoGeometry.Analysis.FractalMeasure

/-- The Cantor space as the product of countably many copies of the two-point discrete space. -/
def CantorSpace : Type := Nat → Bool

/-- The Bernoulli(1/2) measure on Bool. -/
def bernoulliHalf : MeasureTheory.Measure Bool :=
  MeasureTheory.probabilityMeasure (MeasureTheory.uniformMeasure Bool)

/-- The product measure on CantorSpace giving each coordinate weight 1/2 independently. -/
def fractalMeasure : MeasureTheory.Measure CantorSpace :=
  MeasureTheory.prod (fun _ : Nat => bernoulliHalf)

/-- The fractal measure is a probability measure. -/
instance : MeasureTheory.ProbabilityMeasure CantorSpace :=
  ⟨fractalMeasure, by
    -- Prove that the total mass is 1.
    have h : MeasureTheory.measure (Set.univ : Set CantorSpace) fractalMeasure = 1 := by
      -- The product of probability measures is a probability measure.
      rw [MeasureTheory.measure_eq_one_of_probability]
      <;>
      (try infer_instance) <;>
      (try
        {
          apply MeasureTheory.probabilityMeasure.prod
          <;>
          simp_all [bernoulliHalf]
          <;>
          norm_num
        })
    exact h⟩

/-- A cylinder set in CantorSpace depending on a finite set of coordinates. -/
def cylinderSet (s : Finset Nat) (f : Finset Nat → Bool) : Set CantorSpace :=
  {x : CantorSpace | ∀ i ∈ s, x i = f i}

/-- The measure of a cylinder set is (1/2)^{|s|}. -/
theorem measure_cylinderSet (s : Finset Nat) (f : Finset Nat → Bool) :
    MeasureTheory.measure (cylinderSet s f) fractalMeasure = (1 / 2 : ℝ) ^ s.card := by
  have h₁ : MeasureTheory.measure (cylinderSet s f) fractalMeasure =
      ∏ i in s, MeasureTheory.measure ({x : Bool | x = f i}) (bernoulliHalf : MeasureTheory.Measure Bool) := by
    -- Use the product measure formula for measurable rectangles.
    have h₂ : (cylinderSet s f : Set CantorSpace) = ∏ i in s, ({x : Bool | x = f i} : Set Bool) := by
      apply Set.ext
      intro x
      constructor
      · -- Prove the forward direction: if x is in the product, then forall i in s, x i = f i
        intro h
        have h₃ : ∀ i ∈ s, x i ∈ ({x : Bool | x = f i} : Set Bool) := by
          simp only [Set.mem_iProd, Finset.mem_coe] at h
          exact h
        intro i hi
        have h₄ : x i ∈ ({x : Bool | x = f i} : Set Bool) := h₃ i hi
        simp only [Set.mem_setOf_eq] at h₄
        exact h₄
      · -- Prove the reverse direction: if forall i in s, x i = f i, then x is in the product
        intro h
        have h₃ : ∀ i ∈ s, x i ∈ ({x : Bool | x = f i} : Set Bool) := by
          intro i hi
          have h₄ : x i = f i := h i hi
          exact Set.mem_setOf.mpr h₄
        -- Now we need to show that x is in the product set.
        apply Set.mem_iProd.mpr
        intro i _
        exact h₃ i
    rw [h₂]
    -- The measure of a product set is the product of measures.
    rw [MeasureTheory.measure_iProd]
    <;>
    (try {
      apply Finset.measurableSet
    }) <;>
    (try {
      apply Finset.measurableSet
    }) <;>
    (try {
      intro i _
      measurable
    })
  -- Each factor is the measure of a singleton in Bool under bernoulliHalf, which is 1/2.
  apply Finset.prod_congr rfl
  intro i _
  have h₃ : MeasureTheory.measure ({x : Bool | x = f i} : Set Bool) (bernoulliHalf : MeasureTheory.Measure Bool) = (1 / 2 : ℝ) := by
    have h₄ : MeasureTheory.measure ({x : Bool | x = f i} : Set Bool) (bernoulliHalf : MeasureTheory.Measure Bool) =
        MeasureTheory.measure ({f i} : Set Bool) (bernoulliHalf : MeasureTheory.Measure Bool) := by
      congr
      ext x
      simp [f i]
    rw [h₄]
    -- The measure of a singleton under the uniform measure on a two-point space is 1/2.
    have h₅ : MeasureTheory.measure ({f i} : Set Bool) (bernoulliHalf : MeasureTheory.Measure Bool) = 1 / 2 := by
      have h₆ : bernoulliHalf = MeasureTheory.probabilityMeasure (MeasureTheory.uniformMeasure Bool) := rfl
      rw [h₆]
      -- The uniform measure on a fintype gives each point mass 1 / cardinality.
      have h₇ : MeasureTheory.measure ({f i} : Set Bool) (MeasureTheory.uniformMeasure Bool) = 1 / 2 := by
        simp [MeasureTheory.uniformMeasure_apply, Fintype.card_fin]
        <;>
        norm_num
        <;>
        field_simp
        <;>
        ring
      exact h₇
    exact h₅
  <;>
  simp [Finset.card_pos]
  <;>
  field_simp
  <;>
  ring_nf
  <;>
  norm_cast
  <;>
  simp_all [Finset.card_pos]
  <;>
  linarith

end InfoGeometry.Analysis.FractalMeasure