/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ...
-/


/-!
# Positive measures (strictly positive weights)

`PositiveMeasure α R` is a bundled function `α → R` that is strictly positive everywhere.

For finite `α` we define the total mass `Z` (partition function) and a normalization
(to a function summing to `1`).

For `R = ℝ` and finite `α`, we define the generalized Kullback–Leibler divergence on the positive
cone and prove:
* nonnegativity;
* zero iff equality.
-/

open scoped BigOperators

universe u v

/-- A `PositiveMeasure α R` is a function `α → R` that is strictly positive everywhere. -/
@[ext]
structure PositiveMeasure (α : Type u) (R : Type v) [Preorder R] [Zero R] where
  /-- The mass assigned to each point. -/
  mass : α → R
  /-- Pointwise strict positivity. -/
  pos : ∀ a, 0 < mass a

namespace PositiveMeasure

section Basic

variable {α : Type u} {R : Type v} [Preorder R] [Zero R]

instance : CoeFun (PositiveMeasure α R) (fun _ => α → R) where
  coe μ := μ.mass

@[simp] lemma pos_apply (μ : PositiveMeasure α R) (a : α) : 0 < μ a :=
  μ.pos a

end Basic

section Algebra

variable {α : Type u} {R : Type v} [Semiring R] [LinearOrder R] [IsStrictOrderedRing R]

instance : Add (PositiveMeasure α R) where
  add μ ν :=
    ⟨fun a => μ a + ν a, fun a => add_pos (μ.pos a) (ν.pos a)⟩

@[simp] lemma add_apply (μ ν : PositiveMeasure α R) (a : α) :
    (μ + ν) a = μ a + ν a := rfl

instance : AddCommSemigroup (PositiveMeasure α R) where
  add := (· + ·)
  add_assoc μ ν κ := by ext a; simp [add_assoc]
  add_comm μ ν := by ext a; simp [add_comm]

/-- Scale a positive measure by a strictly positive scalar. -/
def scale (c : R) (hc : 0 < c) (μ : PositiveMeasure α R) : PositiveMeasure α R :=
  ⟨fun a => c * μ a, fun a => mul_pos hc (μ.pos a)⟩

@[simp] lemma scale_apply (c : R) (hc : 0 < c) (μ : PositiveMeasure α R) (a : α) :
    scale c hc μ a = c * μ a := rfl

end Algebra

section Fintype

variable {α : Type u} {R : Type v} [Preorder R] [Zero R] [Fintype α] [AddCommMonoid R]

/-- Total mass (partition function) `Z = ∑ a, μ a`. -/
noncomputable def Z (μ : PositiveMeasure α R) : R :=
  ∑ a, μ a

@[simp] lemma Z_def (μ : PositiveMeasure α R) :
    Z μ = ∑ a, μ a := rfl

end Fintype

section Normalize

variable {α : Type u} {R : Type v}
variable [Fintype α] [Nonempty α] [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- `Z` is strictly positive for a `PositiveMeasure` on a nonempty finite type. -/
lemma Z_pos (μ : PositiveMeasure α R) : 0 < Z μ := by
  classical
  -- Z μ = ∑ a, μ a, and all μ a > 0
  apply Finset.sum_pos
  · intros a ha
    exact μ.pos a
  · exact Finset.univ_nonempty

lemma Z_ne_zero (μ : PositiveMeasure α R) : Z μ ≠ 0 :=
  ne_of_gt (Z_pos μ)

/-- The normalized function `a ↦ μ a / Z μ`. -/
noncomputable def toProbabilityFun (μ : PositiveMeasure α R) : α → R :=
  fun a => μ a / Z μ

lemma toProbabilityFun_pos (μ : PositiveMeasure α R) (a : α) :
    0 < toProbabilityFun μ a := by
  dsimp [toProbabilityFun]
  exact div_pos (μ.pos a) (Z_pos μ)

/-- Normalization as a `PositiveMeasure` (still pointwise strictly positive). -/
noncomputable def normalize (μ : PositiveMeasure α R) : PositiveMeasure α R :=
  ⟨toProbabilityFun μ, toProbabilityFun_pos μ⟩

@[simp] lemma normalize_apply (μ : PositiveMeasure α R) (a : α) :
    normalize μ a = μ a / Z μ := rfl

/-- The total mass of `normalize μ` is `1`. -/
lemma Z_normalize (μ : PositiveMeasure α R) :
    Z (normalize μ) = 1 := by
  classical
  have hZ0 : Z μ ≠ 0 := Z_ne_zero μ
  calc
    Z (normalize μ)
        = ∑ a : α, μ a / Z μ := by
            simp [Z, normalize, toProbabilityFun]
    _ = (∑ a : α, μ a) / Z μ := by
            simpa using
              (Finset.sum_div (s := (Finset.univ : Finset α))
                (f := fun a => μ a) (a := Z μ)).symm
    _ = Z μ / Z μ := by
            simp [Z]
    _ = 1 := by exact div_self hZ0

end Normalize

section GeneralizedKL

variable {α : Type u} [Fintype α]

/-- The generalized KL summand `x * log (x / y) - x + y`. -/
noncomputable def gklTerm (x y : ℝ) : ℝ :=
  x * Real.log (x / y) - x + y

lemma gklTerm_eq (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    gklTerm x y = (y - x) - x * Real.log (y / x) := by
  have hlog : Real.log (x / y) = - Real.log (y / x) := by
    calc
      Real.log (x / y) = Real.log x - Real.log y := Real.log_div hx hy
      _ = - (Real.log y - Real.log x) := by rw [neg_sub]
      _ = - Real.log (y / x) := by rw [Real.log_div hy hx]
  rw [gklTerm, hlog]
  ring

lemma gklTerm_nonneg (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    0 ≤ gklTerm x y := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hy0 : y ≠ 0 := ne_of_gt hy
  -- Show equivalence of forms
  have eq_forms : gklTerm x y = (y - x) - x * Real.log (y / x) := gklTerm_eq x y hx0 hy0
  rw [eq_forms]
  -- Now prove 0 ≤ (y - x) - x * Real.log (y / x)
  have ht : 0 < y / x := div_pos hy hx
  have hlog : Real.log (y / x) ≤ y / x - 1 := Real.log_le_sub_one_of_pos ht
  have hxmul : x * (y / x - 1) = y - x := by
    field_simp [hx0]
  have hmul : x * Real.log (y / x) ≤ y - x := by
    rw [←hxmul]
    exact mul_le_mul_of_nonneg_left hlog (le_of_lt hx)
  exact sub_nonneg.mpr hmul

lemma gklTerm_pos_of_ne (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) :
    0 < gklTerm x y := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have ht : 0 < y / x := div_pos hy hx
  have ht_ne_one : y / x ≠ (1 : ℝ) := by
    intro h1
    have : y = x := (div_eq_one_iff_eq hx0).1 h1
    exact hxy this.symm
  have hlog : Real.log (y / x) < y / x - 1 :=
    Real.log_lt_sub_one_of_pos ht ht_ne_one
  have hmul : x * Real.log (y / x) < x * (y / x - 1) :=
    mul_lt_mul_of_pos_left hlog hx
  have hmul' : x * Real.log (y / x) < y - x := by
    have hxmul : x * (y / x - 1) = y - x := by
      calc
        x * (y / x - 1) = x * (y / x) - x := by ring
        _ = y - x := by
          have : x * (y / x) = y := by field_simp [hx0]
          simp [this]
    simp [hxmul] at hmul; exact hmul
  have : 0 < (y - x) - x * Real.log (y / x) := sub_pos.mpr hmul'
  simpa [gklTerm_eq x y hx0 (ne_of_gt hy)] using this

lemma gklTerm_eq_zero_iff (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    gklTerm x y = 0 ↔ x = y := by
  constructor
  · intro h
    by_contra hxy
    have hpos : 0 < gklTerm x y := gklTerm_pos_of_ne x y hx hy hxy
    exact (ne_of_gt hpos) h
  · rintro rfl
    simp [gklTerm]

/-- Generalized KL divergence on the positive cone. -/
noncomputable def generalizedKL (μ ν : PositiveMeasure α ℝ) : ℝ :=
  ∑ a ∈ (Finset.univ : Finset α), gklTerm (μ a) (ν a)

theorem generalizedKL_nonneg (μ ν : PositiveMeasure α ℝ) :
    0 ≤ generalizedKL μ ν := by
  classical
  unfold generalizedKL
  refine Finset.sum_nonneg ?_
  intro a ha
  exact gklTerm_nonneg (μ a) (ν a) (μ.pos a) (ν.pos a)

theorem generalizedKL_eq_zero_iff (μ ν : PositiveMeasure α ℝ) :
    generalizedKL μ ν = 0 ↔ μ = ν := by
  classical
  constructor
  · intro h
    have hterms :
        ∀ a, gklTerm (μ a) (ν a) = 0 := by
      have h' :
          ∑ a ∈ (Finset.univ : Finset α), gklTerm (μ a) (ν a) = 0 := by
        simpa [generalizedKL] using h
      have hzero := (Finset.sum_eq_zero_iff_of_nonneg
        (s := (Finset.univ : Finset α))
        (f := fun a => gklTerm (μ a) (ν a))
        (by
          intro a ha
          exact gklTerm_nonneg (μ a) (ν a) (μ.pos a) (ν.pos a))).1 h'
      intro a
      exact hzero a (by simp)
    ext a
    exact (gklTerm_eq_zero_iff (μ a) (ν a) (μ.pos a) (ν.pos a)).1 (hterms a)
  · rintro rfl
    simp [generalizedKL, gklTerm]

end GeneralizedKL

end PositiveMeasure
