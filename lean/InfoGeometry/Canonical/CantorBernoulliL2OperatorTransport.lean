import Mathlib.MeasureTheory.Function.LpSpace.Basic
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

theorem tail_measure_map_branchProductMeasure (b : Bool) :
    Measure.map tail (prependBitBranchProductMeasure b) = μC := by
  rw [← prependBit_measure_map_eq_branchProductMeasure b]
  rw [Measure.map_map (μ := μC) (f := prependBit b) (g := tail)
    InfoGeometry.Canonical.UHFInductiveColimitBoundaryTopology.continuous_tail.measurable
    (InfoGeometry.Canonical.UHFInductiveColimitBoundaryTopology.continuous_prependBit b).measurable]
  simpa [Function.comp_def, tail_prependBit] using
    (Measure.map_id (μ := μC))

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

/-! The normalized binary branch operators on the canonical Bernoulli `L²`
carrier.  The intermediate branch carrier is essential: it records the
half-mass change of a prepend map without identifying the raw algebraic
prepend map with a Hilbert adjoint. -/

def cantorL2Branch (b : Bool) : L2Boundary →ₗᵢ[ℂ] L2Boundary :=
  (branchPrependLpIsometry b).comp (branchTailLpIsometry b)

theorem cantorL2Branch_norm (b : Bool) (f : L2Boundary) :
    ‖cantorL2Branch b f‖ = ‖f‖ := by
  exact (cantorL2Branch b).norm_map f

theorem cantorL2Branch_isometry (b : Bool) :
    Isometry (cantorL2Branch b) := by
  exact (cantorL2Branch b).isometry

def cantorL2Left : L2Boundary →ₗᵢ[ℂ] L2Boundary :=
  cantorL2Branch false

def cantorL2Right : L2Boundary →ₗᵢ[ℂ] L2Boundary :=
  cantorL2Branch true

def cantorL2LeftCLM : L2Boundary →L[ℂ] L2Boundary :=
  (cantorL2Left : L2Boundary →ₗᵢ[ℂ] L2Boundary).toContinuousLinearMap

def cantorL2RightCLM : L2Boundary →L[ℂ] L2Boundary :=
  (cantorL2Right : L2Boundary →ₗᵢ[ℂ] L2Boundary).toContinuousLinearMap

def cantorL2LeftAdjoint : L2Boundary →L[ℂ] L2Boundary :=
  ContinuousLinearMap.adjoint cantorL2LeftCLM

def cantorL2RightAdjoint : L2Boundary →L[ℂ] L2Boundary :=
  ContinuousLinearMap.adjoint cantorL2RightCLM

theorem cantorL2Left_adjoint_inner_left (f g : L2Boundary) :
    inner ℂ (cantorL2LeftAdjoint f) g =
      inner ℂ f (cantorL2LeftCLM g) := by
  exact ContinuousLinearMap.adjoint_inner_left cantorL2LeftCLM g f

theorem cantorL2Right_adjoint_inner_left (f g : L2Boundary) :
    inner ℂ (cantorL2RightAdjoint f) g =
      inner ℂ f (cantorL2RightCLM g) := by
  exact ContinuousLinearMap.adjoint_inner_left cantorL2RightCLM g f

theorem cantorL2Left_adjoint_comp_self :
    cantorL2LeftAdjoint.comp cantorL2LeftCLM =
      ContinuousLinearMap.id ℂ L2Boundary := by
  apply (ContinuousLinearMap.norm_map_iff_adjoint_comp_self
    cantorL2LeftCLM).mp
  intro f
  exact cantorL2Branch_norm false f

theorem cantorL2Right_adjoint_comp_self :
    cantorL2RightAdjoint.comp cantorL2RightCLM =
      ContinuousLinearMap.id ℂ L2Boundary := by
  apply (ContinuousLinearMap.norm_map_iff_adjoint_comp_self
    cantorL2RightCLM).mp
  intro f
  exact cantorL2Branch_norm true f

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
  simp [hi]

def rawPrependBitFunction (b : Bool) (f : L2Boundary) : Boundary → ℂ :=
  (prependBitBranch b).indicator (fun x => f (tail x))

theorem rawPrependBitFunction_memLp (b : Bool) (f : L2Boundary) :
    MemLp (rawPrependBitFunction b f) 2 μC := by
  apply MemLp.indicator (measurableSet_prependBitBranch b)
  have hcomp :
      MemLp ((fun x : Boundary => f x) ∘ tail) 2 μC :=
    (Lp.memLp f).comp_measurePreserving tail_measurePreserving
  simpa [rawPrependBitFunction] using hcomp

end InfoGeometry.Canonical.CantorBernoulliL2OperatorTransport
