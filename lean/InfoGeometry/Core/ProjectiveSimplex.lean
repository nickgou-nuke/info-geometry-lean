import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Between
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Cone.Basic

/-!
# Projective Simplex Foundation

This module establishes the canonical link between projective geometry and 
information theory. The probability simplex is implemented as a specific 
gauge-fixing section of the projectivization of the positive cone.

Mathematical Hierarchy:
1. Carrier Space (Vector Space V)
2. Unnormalized States (Positive Cone interior)
3. Projective State Space (ℙ ℝ V)
4. Normalized Distributions (stdSimplex via gauge-fixing)
-/

namespace InfoGeometry.Core

open LinearAlgebra
open scoped LinearAlgebra.Projectivization

section StdSimplexCorners

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A simplex point that saturates one coordinate at `1` is the corresponding vertex. -/
lemma stdSimplex_eq_single_of_coord_eq_one {f : ι → ℝ} (hf : f ∈ stdSimplex ℝ ι)
    {i : ι} (hi : f i = 1) :
    f = Pi.single i 1 := by
  ext j
  by_cases hji : j = i
  · subst hji
    simp [Pi.single_eq_same, hi]
  · have hsum : f i + (Finset.erase Finset.univ i).sum f = 1 := by
      have hsum' : (Finset.erase Finset.univ i).sum f + f i = ∑ x, f x := by
        exact Finset.sum_erase_add (s := Finset.univ) (f := f) (a := i) (Finset.mem_univ i)
      nlinarith [hsum', hf.2, hi]
    have hzero : (Finset.erase Finset.univ i).sum f = 0 := by
      linarith
    have hne : ∀ j ∈ Finset.erase Finset.univ i, f j = 0 := by
      have hnonneg : ∀ j ∈ Finset.erase Finset.univ i, 0 ≤ f j := by
        intro j hj
        exact hf.1 j
      simpa using (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 hzero
    simp [Pi.single_eq_of_ne hji, hne j (by simp [hji])]

theorem stdSimplex_coord_eq_one_iff_single {f : ι → ℝ}
    (hf : f ∈ stdSimplex ℝ ι) (i : ι) :
    f i = 1 ↔ f = Pi.single i 1 := by
  constructor
  · exact stdSimplex_eq_single_of_coord_eq_one hf
  · intro h
    rw [h]
    simp

/-- Points of the simplex that are not a fixed vertex have that vertex-coordinate strictly below `1`. -/
lemma stdSimplex_coord_lt_one_of_ne_single {f : ι → ℝ} (hf : f ∈ stdSimplex ℝ ι)
    (hneq : f ≠ Pi.single i 1) :
    f i < 1 := by
  have hi_le : f i ≤ 1 := (mem_Icc_of_mem_stdSimplex hf i).2
  by_contra h
  have hi_eq : f i = 1 := le_antisymm hi_le (le_of_not_gt h)
  exact hneq (stdSimplex_eq_single_of_coord_eq_one (ι := ι) hf hi_eq)

theorem stdSimplex_coord_lt_one_iff_ne_single {f : ι → ℝ}
    (hf : f ∈ stdSimplex ℝ ι) (i : ι) :
    f i < 1 ↔ f ≠ Pi.single i 1 := by
  constructor
  · intro hlt heq
    rw [heq] at hlt
    simp at hlt
  · exact stdSimplex_coord_lt_one_of_ne_single hf

/-- A canonical vertex of the standard simplex is an extreme point. -/
theorem stdSimplex_single_extremePoints (i : ι) :
    Pi.single i 1 ∈ Set.extremePoints ℝ (stdSimplex ℝ ι) := by
  classical
  rw [mem_extremePoints_iff_forall_segment (𝕜 := ℝ) (A := stdSimplex ℝ ι) (x := Pi.single i 1)]
  constructor
  · exact single_mem_stdSimplex ℝ i
  · intro f hf g hg hseg
    rw [mem_segment_iff_div] at hseg
    rcases hseg with ⟨a, b, ha, hb, hab, hEq⟩
    by_cases hf' : f = Pi.single i 1
    · exact Or.inl hf'
    · by_cases hg' : g = Pi.single i 1
      · exact Or.inr hg'
      · have hf_lt : f i < 1 := stdSimplex_coord_lt_one_of_ne_single (ι := ι) hf hf'
        have hg_lt : g i < 1 := stdSimplex_coord_lt_one_of_ne_single (ι := ι) hg hg'
        have hza : 0 ≤ a / (a + b) := by
          exact div_nonneg ha (le_of_lt hab)
        have hzb : 0 ≤ b / (a + b) := by
          exact div_nonneg hb (le_of_lt hab)
        have hsum : a / (a + b) + b / (a + b) = 1 := by
          field_simp [hab.ne']
        have hlt : a / (a + b) * f i + b / (a + b) * g i < 1 := by
          have hMle : a / (a + b) * f i + b / (a + b) * g i ≤ max (f i) (g i) := by
            have hfM : f i ≤ max (f i) (g i) := le_max_left _ _
            have hgM : g i ≤ max (f i) (g i) := le_max_right _ _
            have h1 : a / (a + b) * f i ≤ a / (a + b) * max (f i) (g i) :=
              mul_le_mul_of_nonneg_left hfM hza
            have h2 : b / (a + b) * g i ≤ b / (a + b) * max (f i) (g i) :=
              mul_le_mul_of_nonneg_left hgM hzb
            nlinarith [h1, h2, hsum]
          have hmax : max (f i) (g i) < 1 := by
            exact max_lt_iff.mpr ⟨hf_lt, hg_lt⟩
          linarith
        have h1 : a / (a + b) * f i + b / (a + b) * g i = 1 := by
          have hcoord := congrArg (fun h : ι → ℝ => h i) hEq
          simpa [Pi.smul_apply, Pi.single_eq_same, mul_comm, mul_left_comm, mul_assoc] using hcoord
        linarith

end StdSimplexCorners

/-- Every normalized distribution in the standard simplex defines a unique projective state. -/
noncomputable def fromStdSimplex {ι : Type*} [Fintype ι] (f : stdSimplex ℝ ι) : ℙ ℝ (ι → ℝ) :=
  let v : ι → ℝ := f.1
  let hv : v ≠ 0 := by
    intro h
    have hsum := f.2.2
    have h_zero_sum : ∑ i, v i = 0 := by
      rw [h]
      simp
    rw [h_zero_sum] at hsum
    exact zero_ne_one hsum
  Projectivization.mk ℝ v hv

/-- Choice of a normalized representative from a projective ray (Gauge Fixing). -/
noncomputable def gaugeFix {ι : Type*} [Fintype ι] (p : ℙ ℝ (ι → ℝ)) (h_mass : ∑ i, p.rep i ≠ 0) :
    { f : ι → ℝ // ∑ i, f i = 1 } :=
  let v : ι → ℝ := p.rep
  ⟨(∑ i, v i)⁻¹ • v, by
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum]
    exact inv_mul_cancel₀ h_mass⟩

end InfoGeometry.Core
