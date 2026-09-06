import Mathlib.Tactic

/-
#### BUCKET 1: CLOSED FINITE THEOREMS (7)
- idempotence: P₊² = P₊, P₋² = P₋, P₀² = P₀
- annihilation: P₊∘P₋ = P₋∘P₊ = 0, P₊∘P₀ = P₀∘P₊ = 0, P₋∘P₀ = P₀∘P₋ = 0
- sum to identity: P₊ + P₋ + P₀ = id

#### BUCKET 2: Conditional on O³ = O
#### BUCKET 3: None — all stated theorems proved from explicit hypotheses.
-/

import Mathlib.Tactic

namespace InfoGeometry.Canonical.TriFacetLinearMap

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable (O : V →ₗ[ℝ] V)

/-- Exact form projector P₊ = ½(O² + O). -/
noncomputable def P_hyp : V →ₗ[ℝ] V := (1/2 : ℝ) • (O ∘ₗ O + O)

/-- Coexact form projector P₋ = ½(O² - O). -/
noncomputable def P_ell : V →ₗ[ℝ] V := (1/2 : ℝ) • (O ∘ₗ O - O)

/-- Harmonic projector P₀ = id - O². -/
def P_par : V →ₗ[ℝ] V := LinearMap.id - O ∘ₗ O

/-! ### Pointwise identities (from proven scalar algebra) -/

lemma P_hyp_apply (x : V) : P_hyp O x = (1/2 : ℝ) • (O (O x) + O x) := rfl
lemma P_ell_apply (x : V) : P_ell O x = (1/2 : ℝ) • (O (O x) - O x) := rfl
lemma P_par_apply (x : V) : P_par O x = x - O (O x) := rfl

theorem P_hyp_idempotent (hO : ∀ x, O (O (O x)) = O x) : P_hyp O ∘ₗ P_hyp O = P_hyp O := by
  ext x
  simp [P_hyp_apply, hO]
  try module

theorem P_ell_idempotent (hO : ∀ x, O (O (O x)) = O x) : P_ell O ∘ₗ P_ell O = P_ell O := by
  ext x
  simp [P_ell_apply, hO]
  try module

theorem P_par_idempotent (hO : ∀ x, O (O (O x)) = O x) : P_par O ∘ₗ P_par O = P_par O := by
  ext x
  simp [P_par_apply, hO]
  try module

/-! ### Pairwise annihilation -/

theorem P_hyp_comp_P_ell (hO : ∀ x, O (O (O x)) = O x) : P_hyp O ∘ₗ P_ell O = 0 := by
  ext x
  simp [P_hyp_apply, P_ell_apply, hO]
  try module

theorem P_ell_comp_P_hyp (hO : ∀ x, O (O (O x)) = O x) : P_ell O ∘ₗ P_hyp O = 0 := by
  ext x
  simp [P_hyp_apply, P_ell_apply, hO]
  try module

theorem P_hyp_comp_P_par (hO : ∀ x, O (O (O x)) = O x) : P_hyp O ∘ₗ P_par O = 0 := by
  ext x
  simp [P_hyp_apply, P_par_apply, hO]
  try module

theorem P_par_comp_P_hyp (hO : ∀ x, O (O (O x)) = O x) : P_par O ∘ₗ P_hyp O = 0 := by
  ext x
  simp [P_hyp_apply, P_par_apply, hO]
  try module

theorem P_ell_comp_P_par (hO : ∀ x, O (O (O x)) = O x) : P_ell O ∘ₗ P_par O = 0 := by
  ext x
  simp [P_ell_apply, P_par_apply, hO]
  try module

theorem P_par_comp_P_ell (hO : ∀ x, O (O (O x)) = O x) : P_par O ∘ₗ P_ell O = 0 := by
  ext x
  simp [P_ell_apply, P_par_apply, hO]
  try module

/-! ### Sum to identity -/

theorem sum_to_id : P_hyp O + P_ell O + P_par O = LinearMap.id := by
  ext x
  simp [P_hyp_apply, P_ell_apply, P_par_apply]
  try module

end InfoGeometry.Canonical.TriFacetLinearMap

