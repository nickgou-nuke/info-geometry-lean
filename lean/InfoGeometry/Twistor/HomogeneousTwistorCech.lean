import InfoGeometry.Twistor.PenroseIncidence
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Homogeneity and the algebraic two-chart Cech calculation

This is the standard algebraic two-chart calculation for O(-n-2) on a
spinor projective line. Overlap sections are native Laurent polynomials;
regular chart sections have exponents >= 0 and <= -n-2 respectively.
The quotient is actually constructed and computed, not supplied as data.
It does not identify algebraic Cech cohomology with the analytic twistor
sheaf or prove the global Penrose correspondence.
-/

noncomputable section
namespace InfoGeometry.Twistor.HomogeneousTwistorCech

open scoped BigOperators
open PenroseIncidence

/-- Negative homogeneous weight in Perjes (5.4). -/
def weight (n : ℕ) : ℤ := -(n : ℤ) - 2

def IsHomogeneous (w : ℤ) (f : Twistor4 → ℂ) : Prop :=
  ∀ c : ℂ, c ≠ 0 → ∀ Z : Twistor4, f (c • Z) = c ^ w * f Z

/-- The two actual spinor chart frames. -/
def firstChart (z : ℂ) : Spinor2 := ![1, z]
def secondChart (z : ℂ) : Spinor2 := ![z, 1]

theorem chart_transition (z : ℂ) (hz : z ≠ 0) :
    firstChart z = z • secondChart z⁻¹ := by
  funext i
  fin_cases i <;> simp [firstChart, secondChart, hz]

theorem homogeneous_incidence_transition (w : ℤ) (f : Twistor4 → ℂ)
    (hf : IsHomogeneous w f) (X : ComplexSpacetime) (z : ℂ) (hz : z ≠ 0) :
    f (incidenceLinearMap X (firstChart z)) =
      z ^ w * f (incidenceLinearMap X (secondChart z⁻¹)) := by
  rw [chart_transition z hz, map_smul, hf z hz]

/-- The integrand's total weight, including n spinors and the degree-two measure. -/
theorem integrand_weight_zero (n : ℕ) : (n : ℤ) + weight n + 2 = 0 := by
  simp [weight]

abbrev Laurent := LaurentPolynomial ℂ

/-- Polynomial sections on the finite chart. -/
def finitePatch : Submodule ℂ Laurent where
  carrier := {p | ∀ k : ℤ, k < 0 → p k = 0}
  zero_mem' := by simp
  add_mem' hp hq k hk := by simp [hp k hk, hq k hk]
  smul_mem' c p hp k hk := by simp [hp k hk]

/-- Polynomial sections on the infinity chart, expressed in the finite frame. -/
def infinityPatch (n : ℕ) : Submodule ℂ Laurent where
  carrier := {p | ∀ k : ℤ, weight n < k → p k = 0}
  zero_mem' := by simp
  add_mem' hp hq k hk := by simp [hp k hk, hq k hk]
  smul_mem' c p hp k hk := by simp [hp k hk]

/-- Sum of actual chart images in the overlap, hence the coboundary submodule. -/
def boundaries (n : ℕ) : Submodule ℂ Laurent := finitePatch ⊔ infinityPatch n

/-- Perjes (5.8) uses the infinity-chart section minus the finite-chart section. -/
def coboundary (n : ℕ) : finitePatch × infinityPatch n →ₗ[ℂ] Laurent where
  toFun p := p.2.val - p.1.val
  map_add' p q := by simp; abel
  map_smul' c p := by simp [smul_sub]

theorem range_coboundary (n : ℕ) : LinearMap.range (coboundary n) = boundaries n := by
  ext p
  constructor
  · rintro ⟨⟨a, b⟩, rfl⟩
    apply Submodule.mem_sup.mpr
    exact ⟨-a.val, finitePatch.neg_mem a.property, b.val, b.property, by
      simp [coboundary]; abel⟩
  · intro hp
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hp
    refine ⟨(⟨-a, finitePatch.neg_mem ha⟩, ⟨b, hb⟩), ?_⟩
    simp [coboundary]
    simpa [add_comm] using hab

/-- The surviving exponents -1, -2, ..., -(n+1). -/
def principalExponent {n : ℕ} (i : Fin (n + 1)) : ℤ := -(i.val : ℤ) - 1

@[simp] theorem principalExponent_inj {n : ℕ} (i j : Fin (n + 1)) :
    principalExponent i = principalExponent j ↔ i = j := by
  constructor
  · intro h
    apply Fin.ext
    dsimp [principalExponent] at h
    omega
  · rintro rfl; rfl

/-- The entire principal-part readout, as an actual linear map. -/
def principalPart (n : ℕ) : Laurent →ₗ[ℂ] (Fin (n + 1) → ℂ) where
  toFun p i := p (principalExponent i)
  map_add' p q := rfl
  map_smul' c p := rfl

/-- Exactly the chart coboundaries, not merely a sufficient vanishing condition. -/
theorem boundaries_eq_kernel (n : ℕ) : boundaries n = LinearMap.ker (principalPart n) := by
  ext p
  constructor
  · intro hp
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hp
    change principalPart n p = 0
    rw [← hab]
    funext i
    change a (principalExponent i) + b (principalExponent i) = 0
    have hneg : principalExponent i < 0 := by dsimp [principalExponent]; omega
    have hbound : weight n < principalExponent i := by
      dsimp [weight, principalExponent]
      omega
    rw [ha _ hneg, hb _ hbound, add_zero]
  · intro hp
    change principalPart n p = 0 at hp
    let a : Laurent := Finsupp.filter (fun k : ℤ => 0 ≤ k) p
    let b : Laurent := Finsupp.filter (fun k : ℤ => k < 0) p
    have ha : a ∈ finitePatch := by
      intro k hk
      simp [a, Finsupp.filter_apply, not_le.mpr hk]
    have hb : b ∈ infinityPatch n := by
      intro k hk
      by_cases hneg : k < 0
      · let i : Fin (n + 1) := ⟨(-k - 1).toNat, by dsimp [weight] at hk; omega⟩
        have hi : principalExponent i = k := by dsimp [principalExponent, i]; omega
        have hh := congrFun hp i
        change p (principalExponent i) = 0 at hh
        simpa [b, Finsupp.filter_apply, hneg, hi] using hh
      · simp [b, Finsupp.filter_apply, hneg]
    apply Submodule.mem_sup.mpr
    refine ⟨a, ha, b, hb, ?_⟩
    ext k
    by_cases hk : k < 0
    · simp [a, b, Finsupp.filter_apply, hk, not_le.mpr hk]
    · simp [a, b, Finsupp.filter_apply, hk, le_of_not_gt hk]

/-- Explicit reconstruction from the n+1 surviving coefficients. -/
def principalSection (n : ℕ) (v : Fin (n + 1) → ℂ) : Laurent :=
  ∑ i, Finsupp.single (principalExponent i) (v i)

theorem principalPart_section (n : ℕ) (v : Fin (n + 1) → ℂ) :
    principalPart n (principalSection n v) = v := by
  funext i
  simp [principalPart, principalSection, Finsupp.single_apply]

theorem principalPart_surjective (n : ℕ) : Function.Surjective (principalPart n) :=
  fun v => ⟨principalSection n v, principalPart_section n v⟩

abbrev CechH1 (n : ℕ) := Laurent ⧸ boundaries n

/-- Computed cohomology, via the native first isomorphism theorem. -/
def cohomologyCoordinates (n : ℕ) : CechH1 n ≃ₗ[ℂ] (Fin (n + 1) → ℂ) :=
  (Submodule.quotEquivOfEq (boundaries n) (LinearMap.ker (principalPart n))
    (boundaries_eq_kernel n)).trans
      (LinearMap.quotKerEquivOfSurjective (principalPart n) (principalPart_surjective n))

/-- Every allowed principal-part coordinate is realized, not a zero transform. -/
theorem single_principal_class_nonzero (n : ℕ) (i : Fin (n + 1)) :
    Finsupp.single (principalExponent i) (1 : ℂ) ∉ boundaries n := by
  rw [boundaries_eq_kernel]
  intro h
  have hh := congrFun h i
  norm_num [principalPart] at hh

/-- Actual Laurent evaluation, used by the contour owner. -/
def evaluate (z : ℂ) : Laurent →ₗ[ℂ] ℂ :=
  Finsupp.total ℤ ℂ ℂ (fun k => z ^ k)

@[simp] theorem evaluate_single (z : ℂ) (k : ℤ) (c : ℂ) :
    evaluate z (Finsupp.single k c) = c * z ^ k := by
  simp [evaluate, smul_eq_mul]

end InfoGeometry.Twistor.HomogeneousTwistorCech
