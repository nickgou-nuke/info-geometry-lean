/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Twistor.PenroseIncidence
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Homogeneity and the algebraic two-chart Cech calculation

Overlap sections are native Laurent polynomials. Regular chart images have
exponents >= 0 and <= -n-2 respectively. Their quotient is constructed and
computed, not supplied as a correspondence field. The construction is the
algebraic two-chart model; it does not assert an identification with the
full analytic twistor sheaf or the global Penrose correspondence.
-/

noncomputable section
namespace InfoGeometry.Twistor.HomogeneousTwistorCech

open scoped BigOperators
open PenroseIncidence

def weight (n : ℕ) : ℤ := -(n : ℤ) - 2

def IsHomogeneous (w : ℤ) (f : Twistor4 → ℂ) : Prop :=
  ∀ c : ℂ, c ≠ 0 → ∀ Z : Twistor4, f (c • Z) = c ^ w * f Z

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

theorem integrand_weight_zero (n : ℕ) : (n : ℤ) + weight n + 2 = 0 := by
  dsimp [weight]
  omega

abbrev Laurent := LaurentPolynomial ℂ

def finitePatch : Submodule ℂ Laurent where
  carrier := {p | ∀ k : ℤ, k < 0 → p.coeff k = 0}
  zero_mem' := by simp
  add_mem' hp hq k hk := by simp [hp k hk, hq k hk]
  smul_mem' c p hp k hk := by simp [hp k hk]

def infinityPatch (n : ℕ) : Submodule ℂ Laurent where
  carrier := {p | ∀ k : ℤ, weight n < k → p.coeff k = 0}
  zero_mem' := by simp
  add_mem' hp hq k hk := by simp [hp k hk, hq k hk]
  smul_mem' c p hp k hk := by simp [hp k hk]

def boundaries (n : ℕ) : Submodule ℂ Laurent := finitePatch ⊔ infinityPatch n

/-- The infinity-chart section minus the finite-chart section, as in (5.8). -/
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

def principalExponent {n : ℕ} (i : Fin (n + 1)) : ℤ := -(i.val : ℤ) - 1

@[simp] theorem principalExponent_inj {n : ℕ} (i j : Fin (n + 1)) :
    principalExponent i = principalExponent j ↔ i = j := by
  constructor
  · intro h
    apply Fin.ext
    dsimp [principalExponent] at h
    omega
  · rintro rfl; rfl

/-- The n+1 surviving principal-part coefficients. -/
def principalPart (n : ℕ) : Laurent →ₗ[ℂ] (Fin (n + 1) → ℂ) where
  toFun p i := p.coeff (principalExponent i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Exact characterization of the actual chart coboundaries. -/
theorem boundaries_eq_kernel (n : ℕ) : boundaries n = LinearMap.ker (principalPart n) := by
  ext p
  constructor
  · intro hp
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hp
    change principalPart n p = 0
    rw [← hab]
    funext i
    change a.coeff (principalExponent i) + b.coeff (principalExponent i) = 0
    have hneg : principalExponent i < 0 := by dsimp [principalExponent]; omega
    have hbound : weight n < principalExponent i := by
      dsimp [weight, principalExponent]
      omega
    rw [ha _ hneg, hb _ hbound, add_zero]
  · intro hp
    change principalPart n p = 0 at hp
    let a : Laurent := AddMonoidAlgebra.ofCoeff (Finsupp.filter (fun k : ℤ => 0 ≤ k) p.coeff)
    let b : Laurent := AddMonoidAlgebra.ofCoeff (Finsupp.filter (fun k : ℤ => k < 0) p.coeff)
    have ha : a ∈ finitePatch := by
      intro k hk
      simp [a, not_le.mpr hk]
    have hb : b ∈ infinityPatch n := by
      intro k hk
      by_cases hneg : k < 0
      · let i : Fin (n + 1) := ⟨(-k - 1).toNat, by dsimp [weight] at hk; omega⟩
        have hi : principalExponent i = k := by dsimp [principalExponent, i]; omega
        have hh := congrFun hp i
        change p.coeff (principalExponent i) = 0 at hh
        simpa [b, hneg, hi] using hh
      · simp [b, hneg]
    apply Submodule.mem_sup.mpr
    refine ⟨a, ha, b, hb, ?_⟩
    ext k
    by_cases hk : k < 0
    · simp [a, b, hk, not_le.mpr hk]
    · simp [a, b, hk, le_of_not_gt hk]

def principalSection (n : ℕ) (v : Fin (n + 1) → ℂ) : Laurent :=
  ∑ i, AddMonoidAlgebra.single (principalExponent i) (v i)

theorem principalPart_section (n : ℕ) (v : Fin (n + 1) → ℂ) :
    principalPart n (principalSection n v) = v := by
  funext i
  rw [principalSection, map_sum]
  simp only [Finset.sum_apply]
  change (∑ j, principalPart n
    (AddMonoidAlgebra.single (principalExponent j) (v j)) i) = v i
  have hterm (j : Fin (n + 1)) :
      principalPart n (AddMonoidAlgebra.single (principalExponent j) (v j)) i =
        if j = i then v i else 0 := by
    dsimp [principalPart]
    change (AddMonoidAlgebra.single (principalExponent j) (v j)).coeff
      (principalExponent i) = _
    rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    by_cases hji : j = i
    · subst i
      simp
    · have he : principalExponent j ≠ principalExponent i := by
        intro h
        exact hji ((principalExponent_inj j i).mp h)
      simp [he, hji]
  simp_rw [hterm]
  simp

theorem principalPart_surjective (n : ℕ) : Function.Surjective (principalPart n) :=
  fun v => ⟨principalSection n v, principalPart_section n v⟩

abbrev CechH1 (n : ℕ) := Laurent ⧸ boundaries n

def cohomologyCoordinates (n : ℕ) : CechH1 n ≃ₗ[ℂ] (Fin (n + 1) → ℂ) :=
  (Submodule.quotEquivOfEq (boundaries n) (LinearMap.ker (principalPart n))
    (boundaries_eq_kernel n)).trans
      (LinearMap.quotKerEquivOfSurjective (principalPart n) (principalPart_surjective n))

/-- The algebraic two-chart Cech quotient has dimension `n + 1`, as computed
from its explicit principal-part coordinates. -/
theorem cechH1_finrank (n : ℕ) : Module.finrank ℂ (CechH1 n) = n + 1 := by
  rw [(cohomologyCoordinates n).finrank_eq]
  simp

/-- For projective weights `w ≥ -1`, the two regular charts cover every
Laurent exponent. This is the algebraic vanishing range complementary to the
finite principal-part calculation above. -/
def weightInfinityPatch (w : ℤ) : Submodule ℂ Laurent where
  carrier := {p | ∀ k : ℤ, w < k → p.coeff k = 0}
  zero_mem' := by simp
  add_mem' hp hq k hk := by simp [hp k hk, hq k hk]
  smul_mem' c p hp k hk := by simp [hp k hk]

def weightBoundaries (w : ℤ) : Submodule ℂ Laurent :=
  finitePatch ⊔ weightInfinityPatch w

abbrev weightCechH1 (w : ℤ) := Laurent ⧸ weightBoundaries w

/-- The signed-weight presentation agrees definitionally with the existing
principal-part quotient on every weight `-n-2`, retaining its exact dimension. -/
theorem weightCechH1_finrank_negative (n : ℕ) :
    Module.finrank ℂ (weightCechH1 (weight n)) = n + 1 := by
  exact cechH1_finrank n

theorem weightBoundaries_eq_top_of_ge_neg_one (w : ℤ) (hw : -1 ≤ w) :
    weightBoundaries w = ⊤ := by
  apply top_unique
  intro p hp
  let a : Laurent := AddMonoidAlgebra.ofCoeff
    (Finsupp.filter (fun k : ℤ => 0 ≤ k) p.coeff)
  let b : Laurent := AddMonoidAlgebra.ofCoeff
    (Finsupp.filter (fun k : ℤ => k < 0) p.coeff)
  have ha : a ∈ finitePatch := by
    intro k hk
    simp [a, not_le.mpr hk]
  have hb : b ∈ weightInfinityPatch w := by
    intro k hk
    by_cases hneg : k < 0
    · exact False.elim (Int.not_le.mpr hk (by linarith [hw, hneg]))
    · simp [b, hneg]
  apply Submodule.mem_sup.mpr
  refine ⟨a, ha, b, hb, ?_⟩
  ext k
  by_cases hk : k < 0
  · simp [a, b, hk, not_le.mpr hk]
  · simp [a, b, hk, le_of_not_gt hk]

/-- The algebraic two-chart Cech group vanishes for all projective weights
`w ≥ -1`, including every nonnegative weight. -/
theorem weightCechH1_vanishes_of_ge_neg_one (w : ℤ) (hw : -1 ≤ w)
    (p : Laurent) :
    (Submodule.Quotient.mk (p := weightBoundaries w) p : weightCechH1 w) = 0 := by
  apply (Submodule.Quotient.mk_eq_zero _).2
  rw [weightBoundaries_eq_top_of_ge_neg_one w hw]
  trivial

/-- Every integer projective weight lies either in the vanishing range `w ≥ -1`
or has the form `-n-2` represented by the finite principal-part model. -/
theorem integer_weight_cases (w : ℤ) :
    (-1 ≤ w) ∨ ∃ n : ℕ, w = weight n := by
  by_cases hw : -1 ≤ w
  · exact Or.inl hw
  · right
    refine ⟨(-w - 2).toNat, ?_⟩
    dsimp [weight]
    have hle : w ≤ -2 := by omega
    have hnat : ((-w - 2).toNat : ℤ) = -w - 2 := by
      apply Int.toNat_of_nonneg
      omega
    omega

theorem single_principal_class_nonzero (n : ℕ) (i : Fin (n + 1)) :
    AddMonoidAlgebra.single (principalExponent i) (1 : ℂ) ∉ boundaries n := by
  rw [boundaries_eq_kernel]
  intro h
  have hh := congrFun h i
  change (AddMonoidAlgebra.single (principalExponent i) (1 : ℂ)).coeff
    (principalExponent i) = 0 at hh
  rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply] at hh
  simp at hh

/-- Coefficient extraction respects the native Laurent algebra's module structure. -/
def coefficients : Laurent →ₗ[ℂ] (ℤ →₀ ℂ) where
  toFun := AddMonoidAlgebra.coeff
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def evaluate (z : ℂ) : Laurent →ₗ[ℂ] ℂ :=
  (Finsupp.linearCombination ℂ (fun k : ℤ => z ^ k)).comp coefficients

@[simp] theorem evaluate_single (z : ℂ) (k : ℤ) (c : ℂ) :
    evaluate z (AddMonoidAlgebra.single k c) = c * z ^ k := by
  rw [evaluate, LinearMap.comp_apply]
  change Finsupp.linearCombination ℂ (fun j : ℤ => z ^ j)
    ((AddMonoidAlgebra.single k c).coeff) = _
  rw [AddMonoidAlgebra.coeff_single, Finsupp.linearCombination_single]
  simp [smul_eq_mul]

end InfoGeometry.Twistor.HomogeneousTwistorCech
