import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

namespace InfoGeometry.AmplituhedronBCFW

variable {F : Type*} [Field F]

/-! ### Scalar model for BCFW-style denominator cancellation

The declarations below are identities in a field for freely supplied scalar
data.  They do not construct external twistors, a positive cell, or a BCFW
map.  In particular, `BCFWMatchingCondition` is an explicit premise; it is
not derived here from the Plücker relation.  The names `residueCellA` and
`residueCellB` denote rational coefficients only, not analytic residues. -/

/-- Five scalar slots that may be assigned boundary-bracket values by a
separate geometric construction. -/
structure PhysicalFacets (F : Type*) where
  P₁ : F  -- ⟨Y Z₁ Z₂⟩
  P₂ : F  -- ⟨Y Z₂ Z₃⟩
  P₃ : F  -- ⟨Y Z₃ Z₄⟩
  P₄ : F  -- ⟨Y Z₄ Z₅⟩
  P₅ : F  -- ⟨Y Z₅ Z₁⟩

/-- Non-vanishing hypothesis on the physical boundary facets (interior of the Amplituhedron). -/
structure PhysicalFacetsNonzero (p : PhysicalFacets F) : Prop where
  hP₁ : p.P₁ ≠ 0
  hP₂ : p.P₂ ≠ 0
  hP₃ : p.P₃ ≠ 0
  hP₄ : p.P₄ ≠ 0
  hP₅ : p.P₅ ≠ 0

/-! ### 2. The Two BCFW Cell Densities -/

/-- Rational scalar assigned to the first denominator pattern. -/
def cellA (p : PhysicalFacets F) (S : F) (N_A : F) : F :=
  N_A / (p.P₁ * p.P₂ * p.P₅ * S)

/-- Rational scalar assigned to the second denominator pattern. -/
def cellB (p : PhysicalFacets F) (S : F) (N_B : F) : F :=
  N_B / (p.P₃ * p.P₄ * p.P₅ * S)

/-- Rational scalar with the product of the five supplied scalar slots as
denominator.  No canonical form or pole classification is defined here. -/
def globalAmplituhedronForm (p : PhysicalFacets F) (N₅ : F) : F :=
  N₅ / (p.P₁ * p.P₂ * p.P₃ * p.P₄ * p.P₅)

/-! ### 3. The Grassmann-Plücker Matching Relation -/

/-- A rearrangement of the supplied three-term Plücker equation.  This does
not identify any of the independent scalar slots above with Plücker minors. -/
theorem plucker_spurious_factor (Δ₁₂ Δ₃₄ Δ₂₃ Δ₁₄ Δ₁₃ Δ₂₄ : F)
    (h_plucker : Δ₁₂ * Δ₃₄ - Δ₁₃ * Δ₂₄ + Δ₁₄ * Δ₂₃ = 0) :
    Δ₁₂ * Δ₃₄ + Δ₂₃ * Δ₁₄ = Δ₁₃ * Δ₂₄ := by
  linear_combination h_plucker

/-- The additional numerator relation required by the scalar cancellation
theorem below.  Its geometric derivation is not part of this module. -/
def BCFWMatchingCondition (p : PhysicalFacets F) (S : F) (N_A N_B N₅ : F) : Prop :=
  N_A * (p.P₃ * p.P₄) + N_B * (p.P₁ * p.P₂) = S * N₅

/-! ### 4. Core Theorem: Algebraic Spurious Pole Cancellation -/

/-- Conditional rational identity: under nonzero denominator assumptions and
the supplied matching equation, the two scalar fractions sum to the stated
third fraction. -/
theorem bcfw_spurious_pole_cancellation
    (p : PhysicalFacets F) (S : F) (N_A N_B N₅ : F)
    (hp : PhysicalFacetsNonzero p)
    (hS : S ≠ 0)
    (h_match : BCFWMatchingCondition p S N_A N_B N₅) :
    cellA p S N_A + cellB p S N_B = globalAmplituhedronForm p N₅ := by
  dsimp [cellA, cellB, globalAmplituhedronForm]
  rcases hp with ⟨hP₁, hP₂, hP₃, hP₄, hP₅⟩
  -- 1. Put both cell fractions over the common denominator (P₁ P₂ P₃ P₄ P₅ S)
  have h_common :
      N_A / (p.P₁ * p.P₂ * p.P₅ * S) + N_B / (p.P₃ * p.P₄ * p.P₅ * S) =
      (N_A * (p.P₃ * p.P₄) + N_B * (p.P₁ * p.P₂)) / (p.P₁ * p.P₂ * p.P₃ * p.P₄ * p.P₅ * S) := by
    have hD1 : p.P₁ * p.P₂ * p.P₅ * S ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero hP₁ hP₂) hP₅) hS
    have hD2 : p.P₃ * p.P₄ * p.P₅ * S ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero hP₃ hP₄) hP₅) hS
    have h34 : p.P₃ * p.P₄ ≠ 0 := mul_ne_zero hP₃ hP₄
    have h12 : p.P₁ * p.P₂ ≠ 0 := mul_ne_zero hP₁ hP₂
    have h_eq1 : N_A / (p.P₁ * p.P₂ * p.P₅ * S) =
        (N_A * (p.P₃ * p.P₄)) / ((p.P₁ * p.P₂ * p.P₅ * S) * (p.P₃ * p.P₄)) := by
      rw [div_eq_div_iff hD1 (mul_ne_zero hD1 h34)]
      ring
    have h_eq2 : N_B / (p.P₃ * p.P₄ * p.P₅ * S) =
        (N_B * (p.P₁ * p.P₂)) / ((p.P₃ * p.P₄ * p.P₅ * S) * (p.P₁ * p.P₂)) := by
      rw [div_eq_div_iff hD2 (mul_ne_zero hD2 h12)]
      ring
    have h_den_eq : (p.P₁ * p.P₂ * p.P₅ * S) * (p.P₃ * p.P₄) =
        p.P₁ * p.P₂ * p.P₃ * p.P₄ * p.P₅ * S := by ring
    have h_den_eq2 : (p.P₃ * p.P₄ * p.P₅ * S) * (p.P₁ * p.P₂) =
        p.P₁ * p.P₂ * p.P₃ * p.P₄ * p.P₅ * S := by ring
    rw [h_eq1, h_eq2, h_den_eq, h_den_eq2, ← add_div]

  rw [h_common]
  -- 2. Substitute the BCFW matching identity: numerator = S * N₅
  dsimp [BCFWMatchingCondition] at h_match
  rw [h_match]
  -- 3. Cancel the spurious chord S from numerator and denominator
  have h_comm_denom : p.P₁ * p.P₂ * p.P₃ * p.P₄ * p.P₅ * S =
      (p.P₁ * p.P₂ * p.P₃ * p.P₄ * p.P₅) * S := by ring
  rw [h_comm_denom]
  have h_div_cancel : (S * N₅) / ((p.P₁ * p.P₂ * p.P₃ * p.P₄ * p.P₅) * S) =
      N₅ / (p.P₁ * p.P₂ * p.P₃ * p.P₄ * p.P₅) := by
    rw [mul_comm S N₅]
    exact mul_div_mul_right N₅ (p.P₁ * p.P₂ * p.P₃ * p.P₄ * p.P₅) hS
  exact h_div_cancel

/-! ### 5. Spurious Residue Cancellation -/

/-- Rational coefficient left after omitting the scalar factor `S` from the
first denominator.  It is not defined as a limit or differential-form residue. -/
def residueCellA (p : PhysicalFacets F) (N_A : F) : F :=
  N_A / (p.P₁ * p.P₂ * p.P₅)

/-- Rational coefficient left after omitting the scalar factor `S` from the
second denominator.  It is not defined as a limit or differential-form residue. -/
def residueCellB (p : PhysicalFacets F) (N_B : F) : F :=
  N_B / (p.P₃ * p.P₄ * p.P₅)

/-- At `S = 0`, the supplied matching equation makes the two rational
coefficients sum to zero after common-denominator algebra. -/
theorem spurious_residue_cancellation
    (p : PhysicalFacets F) (N_A N_B N₅ : F)
    (hp : PhysicalFacetsNonzero p)
    (h_match_zero : BCFWMatchingCondition p 0 N_A N_B N₅) :
    residueCellA p N_A + residueCellB p N_B = 0 := by
  dsimp [BCFWMatchingCondition] at h_match_zero
  rw [zero_mul] at h_match_zero
  dsimp [residueCellA, residueCellB]
  rcases hp with ⟨hP₁, hP₂, hP₃, hP₄, hP₅⟩
  have h125 : p.P₁ * p.P₂ * p.P₅ ≠ 0 := mul_ne_zero (mul_ne_zero hP₁ hP₂) hP₅
  have h345 : p.P₃ * p.P₄ * p.P₅ ≠ 0 := mul_ne_zero (mul_ne_zero hP₃ hP₄) hP₅
  have h12 : p.P₁ * p.P₂ ≠ 0 := mul_ne_zero hP₁ hP₂
  have h34 : p.P₃ * p.P₄ ≠ 0 := mul_ne_zero hP₃ hP₄
  have hall : p.P₁ * p.P₂ * p.P₃ * p.P₄ * p.P₅ ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hP₁ hP₂) hP₃) hP₄) hP₅
  have h_alg1 : (N_A / (p.P₁ * p.P₂ * p.P₅)) =
      (N_A * (p.P₃ * p.P₄)) / (p.P₁ * p.P₂ * p.P₃ * p.P₄ * p.P₅) := by
    have hD1 : (p.P₁ * p.P₂ * p.P₅) * (p.P₃ * p.P₄) = p.P₁ * p.P₂ * p.P₃ * p.P₄ * p.P₅ := by ring
    rw [div_eq_div_iff h125 hall]
    ring
  have h_alg2 : (N_B / (p.P₃ * p.P₄ * p.P₅)) =
      (N_B * (p.P₁ * p.P₂)) / (p.P₁ * p.P₂ * p.P₃ * p.P₄ * p.P₅) := by
    have hD2 : (p.P₃ * p.P₄ * p.P₅) * (p.P₁ * p.P₂) = p.P₁ * p.P₂ * p.P₃ * p.P₄ * p.P₅ := by ring
    rw [div_eq_div_iff h345 hall]
    ring
  rw [h_alg1, h_alg2, ← add_div]
  rw [h_match_zero, zero_div]

/-! ### 6. Smoothness & Positivity in the Amplituhedron Interior -/

/-- Positivity of the defined rational scalar when all five denominator slots
and its numerator are positive.  This is not a positivity theorem for a
geometrically constructed amplituhedron. -/
theorem amplituhedron_interior_positivity
    (p : PhysicalFacets ℝ) (N₅ : ℝ)
    (hP₁ : 0 < p.P₁) (hP₂ : 0 < p.P₂) (hP₃ : 0 < p.P₃)
    (hP₄ : 0 < p.P₄) (hP₅ : 0 < p.P₅)
    (hN₅ : 0 < N₅) :
    0 < globalAmplituhedronForm p N₅ := by
  dsimp [globalAmplituhedronForm]
  have h_denom : 0 < p.P₁ * p.P₂ * p.P₃ * p.P₄ * p.P₅ :=
    mul_pos (mul_pos (mul_pos (mul_pos hP₁ hP₂) hP₃) hP₄) hP₅
  exact div_pos hN₅ h_denom

end InfoGeometry.AmplituhedronBCFW
