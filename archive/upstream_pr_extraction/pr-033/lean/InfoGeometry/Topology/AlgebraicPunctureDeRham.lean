import Mathlib.Tactic
import InfoGeometry.Algebra.EulerLaurentDerivation

/-!
# Algebraic Puncture de Rham Cohomology

Finite algebraic replacement for the local Laurent expansion and de Rham
cohomology of a punctured multiplicative coordinate.  No contour integrals,
no complex logarithm, no analytic continuation.

Core results:
* `residue_differential_zero` — exact forms have zero residue;
* `du_u_not_exact` — `u⁻¹ du` is nontrivial in `H¹`;
* `residue_eq_zero_of_mem_range` — residue is a necessary obstruction to
  exactness.
* `mem_range_differential_iff_residue_zero` — over a characteristic-zero
  field, residue is the complete obstruction to exactness.
-/

noncomputable section

namespace InfoGeometry.Topology.AlgebraicPunctureDeRham

open InfoGeometry.Algebra.EulerLaurentDerivation

variable {R : Type*} [Ring R]

/-! ## Residue of exact forms vanishes -/

/-- The residue of an exact form `d(f)` is zero. -/
theorem residue_differential_zero (f : LaurentPoly R) :
    residue (differential f) = 0 := by
  classical
  rw [differential, residue, Finsupp.sum_apply]
  refine Finset.sum_eq_zero (fun n hn => ?_)
  change (Finsupp.single (n - 1) ((n : R) * f n)) (-1) = 0
  rw [Finsupp.single_apply]
  by_cases h : n - 1 = -1
  · have h' : n = 0 := by omega
    simp [h, h']
  · simp [h]

/-! ## The class of `du/u` is nontrivial -/

/-- The one-form `u⁻¹ du` is not exact. -/
theorem du_u_not_exact [Nontrivial R] :
    ¬ ∃ f : LaurentPoly R, differential f = Finsupp.single (-1) (1 : R) := by
  intro h
  rcases h with ⟨f, hf⟩
  have hres : residue (differential f) = 1 := by
    rw [hf]
    simp [residue]
  rw [residue_differential_zero f] at hres
  exact zero_ne_one hres

/-! ## Exact-range separation -/

/-- Every member of the exact range has zero residue. -/
theorem residue_eq_zero_of_mem_range (ω : LaurentOneForm R)
    (hω : ω ∈ Set.range differential) :
    residue ω = 0 := by
  rcases hω with ⟨f, rfl⟩
  exact residue_differential_zero f

/-- The distinguished residue-one form is separated from the exact range. -/
theorem residue_one_not_mem_range [Nontrivial R] :
    Finsupp.single (-1) (1 : R) ∉ Set.range differential := by
  intro hω
  exact du_u_not_exact hω

/-- Every Laurent one-form with zero residue is exact.  This is the finite
    algebraic form of the Mittag-Leffler theorem: the residue is the only
    obstruction to exactness in the Laurent polynomial de Rham cohomology. -/
theorem zero_residue_implies_exact
    {R : Type*} [Field R] [CharZero R]
    (ω : LaurentOneForm R)
    (hres : residue ω = 0) :
    ∃ f : LaurentPoly R, differential f = ω := by
  classical
  -- Write ω = Σ_{n≠-1} a_n u^n du + a_{-1} u^{-1} du
  -- Since residue = a_{-1} = 0, ω = Σ_{n≠-1} a_n u^n du
  -- For n ≠ -1, u^n du = d(u^{n+1}/(n+1)), so ω is exact
  let f : LaurentPoly R :=
    ω.sum (fun n a =>
      if hne : n + 1 ≠ 0 then
        Finsupp.single (n + 1) (a / (n + 1 : R))
      else 0)
  have hh_zero : ∀ n : ℤ,
      Finsupp.single (n - 1) ((n : R) * 0) = 0 := by
    intro n
    simp
  have hh_add : ∀ (n : ℤ) (a b : R),
      Finsupp.single (n - 1) ((n : R) * (a + b)) =
        Finsupp.single (n - 1) ((n : R) * a) +
          Finsupp.single (n - 1) ((n : R) * b) := by
    intro n a b
    ext k
    simp [mul_add]
  have hdiff : differential f = ω := by
    unfold f differential
    rw [Finsupp.sum_sum_index hh_zero hh_add]
    calc
      ω.sum (fun n a =>
          (if hne : n + 1 ≠ 0 then
            Finsupp.single (n + 1) (a / (n + 1 : R))
          else 0).sum (fun m b =>
            Finsupp.single (m - 1) ((m : R) * b))) =
          ω.sum (fun n a => Finsupp.single n a) := by
            apply Finsupp.sum_congr
            intro n hn
            by_cases hne : n + 1 ≠ 0
            · have hnR : (n + 1 : R) ≠ 0 := by
                exact_mod_cast hne
              have hcoef : (n + 1 : R) * (ω n / (n + 1 : R)) = ω n := by
                field_simp
              rw [dif_pos hne, Finsupp.sum_single_index (by simp)]
              change Finsupp.single ((n + 1) - 1)
                ((↑(n + 1) : R) * (ω n / (n + 1 : R))) =
                  Finsupp.single n (ω n)
              have hcoef' : (↑(n + 1) : R) * (ω n / (n + 1 : R)) = ω n := by
                simpa only [Int.cast_add, Int.cast_one] using hcoef
              rw [hcoef']
              congr 1
              omega
            · have hn' : n = -1 := by omega
              have ha : ω n = 0 := by
                rw [hn']
                simpa [residue] using hres
              rw [dif_neg hne]
              simp [ha]
      _ = ω := Finsupp.sum_single ω
  exact ⟨f, hdiff⟩

/-- Over a characteristic-zero field, a finite Laurent one-form is exact
    exactly when its algebraic residue vanishes. -/
theorem mem_range_differential_iff_residue_zero
    {R : Type*} [Field R] [CharZero R]
    (ω : LaurentOneForm R) :
    ω ∈ Set.range differential ↔ residue ω = 0 := by
  constructor
  · exact residue_eq_zero_of_mem_range ω
  · exact zero_residue_implies_exact ω

/-- The first de Rham cohomology group is exactly the line spanned by `du/u`.
    Every one-form is cohomologous to a unique multiple of `du/u`. -/
theorem H1_generated_by_du_u
    {R : Type*} [Field R] [CharZero R]
    (ω : LaurentOneForm R) :
    ∃ c : R, ω - c • Finsupp.single (-1) (1 : R) ∈ Set.range differential := by
  classical
  let c := residue ω
  use c
  have hexact : residue (ω - c • Finsupp.single (-1) (1 : R)) = 0 := by
    simp [c, residue]
  change ∃ f : LaurentPoly R,
    differential f = ω - c • Finsupp.single (-1) (1 : R)
  exact zero_residue_implies_exact (ω - c • Finsupp.single (-1) (1 : R)) hexact

/-!
The coefficient of `[du/u]` is not merely an existence choice.  The residue
map makes it canonical: exact forms cannot change that coefficient.
-/
theorem H1_du_u_coefficient_unique
    {R : Type*} [Field R] [CharZero R]
    {ω : LaurentOneForm R} {c d : R}
    (hc : ω - c • Finsupp.single (-1) (1 : R) ∈ Set.range differential)
    (hd : ω - d • Finsupp.single (-1) (1 : R) ∈ Set.range differential) :
    c = d := by
  have hc_zero : residue (ω - c • Finsupp.single (-1) (1 : R)) = 0 :=
    residue_eq_zero_of_mem_range _ hc
  have hd_zero : residue (ω - d • Finsupp.single (-1) (1 : R)) = 0 :=
    residue_eq_zero_of_mem_range _ hd
  have hc_eq : residue ω - c = 0 := by
    simpa [residue] using hc_zero
  have hd_eq : residue ω - d = 0 := by
    simpa [residue] using hd_zero
  calc
    c = residue ω := sub_eq_zero.mp hc_eq |>.symm
    _ = d := sub_eq_zero.mp hd_eq

end InfoGeometry.Topology.AlgebraicPunctureDeRham

end noncomputable section
