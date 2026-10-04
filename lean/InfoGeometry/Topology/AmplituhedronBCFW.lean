import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

namespace InfoGeometry.AmplituhedronBCFW

variable {F : Type*} [Field F]

/-! ### 1. Physical Facets & Spurious Chord -/

/-- The five cyclic physical boundary brackets P_i = ⟨Y Z_i Z_{i+1}⟩ of the 5-point Amplituhedron. -/
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

/-- Rational form density of BCFW Cell A:
    Ω_A = N_A / (P₁ P₂ P₅ S).
    Contains physical poles P₁, P₂, P₅ and spurious chord S = ⟨Y Z₁ Z₃⟩. -/
def cellA (p : PhysicalFacets F) (S : F) (N_A : F) : F :=
  N_A / (p.P₁ * p.P₂ * p.P₅ * S)

/-- Rational form density of BCFW Cell B:
    Ω_B = N_B / (P₃ P₄ P₅ S).
    Contains physical poles P₃, P₄, P₅ and spurious chord S = ⟨Y Z₁ Z₃⟩. -/
def cellB (p : PhysicalFacets F) (S : F) (N_B : F) : F :=
  N_B / (p.P₃ * p.P₄ * p.P₅ * S)

/-- The canonical 5-point Amplituhedron rational form:
    Ω₅ = N₅ / (P₁ P₂ P₃ P₄ P₅).
    Manifestly pole-free at S = 0; exhibits only the five cyclic physical poles. -/
def globalAmplituhedronForm (p : PhysicalFacets F) (N₅ : F) : F :=
  N₅ / (p.P₁ * p.P₂ * p.P₃ * p.P₄ * p.P₅)

/-! ### 3. The Grassmann-Plücker Matching Relation -/

/-- The 3-term Grassmann-Plücker relation producing the factor of S:
    Δ₁₂ Δ₃₄ + Δ₂₃ Δ₁₄ = Δ₁₃ Δ₂₄.
    Identifies the spurious chord S = Δ₁₃ as the common factor. -/
theorem plucker_spurious_factor (Δ₁₂ Δ₃₄ Δ₂₃ Δ₁₄ Δ₁₃ Δ₂₄ : F)
    (h_plucker : Δ₁₂ * Δ₃₄ - Δ₁₃ * Δ₂₄ + Δ₁₄ * Δ₂₃ = 0) :
    Δ₁₂ * Δ₃₄ + Δ₂₃ * Δ₁₄ = Δ₁₃ * Δ₂₄ := by
  linear_combination h_plucker

/-- The BCFW Matching Condition:
    N_A * (P₃ * P₄) + N_B * (P₁ * P₂) = S * N₅.
    Arises from contracting the Plücker identity with kinematic twistor data. -/
def BCFWMatchingCondition (p : PhysicalFacets F) (S : F) (N_A N_B N₅ : F) : Prop :=
  N_A * (p.P₃ * p.P₄) + N_B * (p.P₁ * p.P₂) = S * N₅

/-! ### 4. Core Theorem: Algebraic Spurious Pole Cancellation -/

/-- Master Theorem: The sum of the two BCFW cells Ω_A + Ω_B identically cancels
    the spurious internal bracket S, reproducing the global 5-point Amplituhedron form Ω₅. -/
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

/-- Poincaré residue of Cell A at the spurious pole S → 0. -/
def residueCellA (p : PhysicalFacets F) (N_A : F) : F :=
  N_A / (p.P₁ * p.P₂ * p.P₅)

/-- Poincaré residue of Cell B at the spurious pole S → 0. -/
def residueCellB (p : PhysicalFacets F) (N_B : F) : F :=
  N_B / (p.P₃ * p.P₄ * p.P₅)

/-- Spurious Residue Cancellation Theorem:
    On the spurious locus S = 0, the BCFW matching condition forces the
    residues of the two cells to be exact opposites, ensuring zero net residue. -/
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

/-- Positivity Theorem:
    Even though individual BCFW cells Ω_A and Ω_B diverge as S → 0,
    the physical amplitude Ω₅ is strictly positive throughout the entire interior
    of the Amplituhedron (P_i > 0, N₅ > 0), regardless of the sign or vanishing of S. -/
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
