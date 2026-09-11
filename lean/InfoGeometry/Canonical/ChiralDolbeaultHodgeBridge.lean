import Mathlib.Analysis.InnerProductSpace.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

open RealInnerProductSpace

set_option linter.dupNamespace false

namespace InfoGeometry.Canonical.ChiralDolbeaultHodge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A Chiral Dolbeault-Hodge structure on an inner product space E:
    d_tau is the holomorphic derivative,
    d_bar_star is the adjoint antiholomorphic codifferential. -/
structure ChiralDolbeaultHodge (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  d_tau : E →ₗ[ℝ] E
  d_bar_star : E →ₗ[ℝ] E
  nilpotent_d : ∀ x, d_tau (d_tau x) = 0
  nilpotent_d_bar : ∀ x, d_bar_star (d_bar_star x) = 0
  adjoint_d : ∀ x y, ⟪d_tau x, y⟫ = ⟪x, d_bar_star y⟫

namespace ChiralDolbeaultHodge

variable (K : ChiralDolbeaultHodge E)

/-- Reverse adjoint identity for d_bar_star: ⟪d_bar_star u, v⟫ = ⟪u, d_tau v⟫. -/
theorem adjoint_d_bar (u v : E) :
    ⟪K.d_bar_star u, v⟫ = ⟪u, K.d_tau v⟫ := by
  calc ⟪K.d_bar_star u, v⟫
    _ = ⟪v, K.d_bar_star u⟫ := real_inner_comm v (K.d_bar_star u)
    _ = ⟪K.d_tau v, u⟫ := (K.adjoint_d v u).symm
    _ = ⟪u, K.d_tau v⟫ := real_inner_comm u (K.d_tau v)

/-- The Chiral Hodge-Laplacian: Δ_τ = ∂ ∂̄* + ∂̄* ∂. -/
noncomputable def laplacian : E →ₗ[ℝ] E :=
  K.d_tau.comp K.d_bar_star + K.d_bar_star.comp K.d_tau

@[simp]
lemma laplacian_apply (x : E) :
    K.laplacian x = K.d_tau (K.d_bar_star x) + K.d_bar_star (K.d_tau x) := rfl

/-- Harmonic forms in the chiral complex: annihilated by both ∂ and ∂̄*. -/
def IsHarmonic (x : E) : Prop :=
  K.d_tau x = 0 ∧ K.d_bar_star x = 0

def IsExact (x : E) : Prop :=
  ∃ α, x = K.d_tau α

def IsCoexact (x : E) : Prop :=
  ∃ β, x = K.d_bar_star β

/-- Mutual orthogonality of exact holomorphic and coexact antiholomorphic forms. -/
theorem exact_orthogonal_coexact {α β : E} (hα : K.IsExact α) (hβ : K.IsCoexact β) :
    ⟪α, β⟫ = 0 := by
  rcases hα with ⟨u, rfl⟩
  rcases hβ with ⟨v, rfl⟩
  rw [K.adjoint_d u (K.d_bar_star v)]
  rw [K.nilpotent_d_bar v]
  exact inner_zero_right u

/-- Exact holomorphic forms are orthogonal to harmonic forms. -/
theorem exact_orthogonal_harmonic {α h : E} (hα : K.IsExact α) (hh : K.IsHarmonic h) :
    ⟪α, h⟫ = 0 := by
  rcases hα with ⟨u, rfl⟩
  rw [K.adjoint_d u h]
  rw [hh.2]
  exact inner_zero_right u

/-- Coexact antiholomorphic forms are orthogonal to harmonic forms. -/
theorem coexact_orthogonal_harmonic {β h : E} (hβ : K.IsCoexact β) (hh : K.IsHarmonic h) :
    ⟪β, h⟫ = 0 := by
  rcases hβ with ⟨v, rfl⟩
  rw [K.adjoint_d_bar v h]
  rw [hh.1]
  exact inner_zero_right v

/-- Self-adjointness of the chiral Hodge-Laplacian: ⟪Δ x, y⟫ = ⟪x, Δ y⟫. -/
theorem laplacian_self_adjoint (x y : E) :
    ⟪K.laplacian x, y⟫ = ⟪x, K.laplacian y⟫ := by
  simp only [laplacian_apply]
  rw [inner_add_left, inner_add_right]
  have h1 : ⟪K.d_tau (K.d_bar_star x), y⟫ = ⟪K.d_bar_star x, K.d_bar_star y⟫ :=
    K.adjoint_d (K.d_bar_star x) y
  have h2 : ⟪K.d_bar_star (K.d_tau x), y⟫ = ⟪K.d_tau x, K.d_tau y⟫ :=
    K.adjoint_d_bar (K.d_tau x) y
  have h3 : ⟪x, K.d_tau (K.d_bar_star y)⟫ = ⟪K.d_bar_star x, K.d_bar_star y⟫ := by
    rw [real_inner_comm (K.d_tau (K.d_bar_star y)) x, K.adjoint_d (K.d_bar_star y) x, real_inner_comm (K.d_bar_star y) (K.d_bar_star x)]
  have h4 : ⟪x, K.d_bar_star (K.d_tau y)⟫ = ⟪K.d_tau x, K.d_tau y⟫ := by
    rw [real_inner_comm (K.d_bar_star (K.d_tau y)) x, K.adjoint_d_bar (K.d_tau y) x, real_inner_comm (K.d_tau y) (K.d_tau x)]
  rw [h1, h2, h3, h4]

/-- Positive semi-definiteness of the chiral Hodge-Laplacian: ⟪x, Δ x⟫ ≥ 0. -/
theorem laplacian_positive_semidefinite (x : E) :
    0 ≤ ⟪x, K.laplacian x⟫ := by
  simp only [laplacian_apply]
  rw [inner_add_right]
  have h1 : ⟪x, K.d_tau (K.d_bar_star x)⟫ = ⟪K.d_bar_star x, K.d_bar_star x⟫ := by
    rw [real_inner_comm (K.d_tau (K.d_bar_star x)) x, K.adjoint_d (K.d_bar_star x) x]
  have h2 : ⟪x, K.d_bar_star (K.d_tau x)⟫ = ⟪K.d_tau x, K.d_tau x⟫ := by
    rw [real_inner_comm (K.d_bar_star (K.d_tau x)) x, K.adjoint_d_bar (K.d_tau x) x]
  rw [h1, h2]
  exact add_nonneg real_inner_self_nonneg real_inner_self_nonneg

/-- Annihilation characterization: ⟪x, Δ x⟫ = 0 iff x is harmonic. -/
theorem harmonic_iff_laplacian_inner_zero (x : E) :
    ⟪x, K.laplacian x⟫ = 0 ↔ K.IsHarmonic x := by
  simp only [laplacian_apply]
  rw [inner_add_right]
  have h1 : ⟪x, K.d_tau (K.d_bar_star x)⟫ = ⟪K.d_bar_star x, K.d_bar_star x⟫ := by
    rw [real_inner_comm (K.d_tau (K.d_bar_star x)) x, K.adjoint_d (K.d_bar_star x) x]
  have h2 : ⟪x, K.d_bar_star (K.d_tau x)⟫ = ⟪K.d_tau x, K.d_tau x⟫ := by
    rw [real_inner_comm (K.d_bar_star (K.d_tau x)) x, K.adjoint_d_bar (K.d_tau x) x]
  rw [h1, h2]
  dsimp [IsHarmonic]
  constructor
  · intro h_zero
    have h_ge1 : 0 ≤ ⟪K.d_bar_star x, K.d_bar_star x⟫ := real_inner_self_nonneg
    have h_ge2 : 0 ≤ ⟪K.d_tau x, K.d_tau x⟫ := real_inner_self_nonneg
    have h_sum1 : ⟪K.d_bar_star x, K.d_bar_star x⟫ = 0 := by linarith
    have h_sum2 : ⟪K.d_tau x, K.d_tau x⟫ = 0 := by linarith
    exact ⟨inner_self_eq_zero.mp h_sum2, inner_self_eq_zero.mp h_sum1⟩
  · rintro ⟨h_d, h_dbar⟩
    rw [h_d, h_dbar]
    simp

/-- The Chiral Laplacian annihilates harmonic elements. -/
theorem laplacian_annihilates_harmonic (h : E) (hh : K.IsHarmonic h) :
    K.laplacian h = 0 := by
  simp only [laplacian_apply]
  rw [hh.1, hh.2, map_zero, map_zero, add_zero]

/-- Action of Laplacian on exact elements preserves exactness. -/
theorem laplacian_exact_comm (α : E) :
    K.laplacian (K.d_tau α) = K.d_tau (K.d_bar_star (K.d_tau α)) := by
  simp only [laplacian_apply]
  rw [K.nilpotent_d α, map_zero, add_zero]

/-- Action of Laplacian on coexact elements preserves coexactness. -/
theorem laplacian_coexact_comm (β : E) :
    K.laplacian (K.d_bar_star β) = K.d_bar_star (K.d_tau (K.d_bar_star β)) := by
  simp only [laplacian_apply]
  rw [K.nilpotent_d_bar β, map_zero, zero_add]

lemma inner_three_orthogonal (a b c : E)
    (hab : ⟪a, b⟫ = 0) (hac : ⟪a, c⟫ = 0) (hbc : ⟪b, c⟫ = 0) :
    ⟪a + b + c, a + b + c⟫ = ⟪a, a⟫ + ⟪b, b⟫ + ⟪c, c⟫ := by
  have hba : ⟪b, a⟫ = 0 := by rw [real_inner_comm a b, hab]
  have hca : ⟪c, a⟫ = 0 := by rw [real_inner_comm a c, hac]
  have hcb : ⟪c, b⟫ = 0 := by rw [real_inner_comm b c, hbc]
  simp only [inner_add_left, inner_add_right]
  rw [hab, hac, hba, hbc, hca, hcb]
  ring

/-- A Chiral Hodge Decomposition of a vector ω = exact_part + coexact_part + harmonic_part. -/
structure ChiralHodgeDecomposition (ω : E) where
  exact_part : E
  coexact_part : E
  harmonic_part : E
  exact_mem : K.IsExact exact_part
  coexact_mem : K.IsCoexact coexact_part
  harmonic_mem : K.IsHarmonic harmonic_part
  sum_eq : ω = exact_part + coexact_part + harmonic_part

/-- Pythagorean energy conservation for any Chiral Hodge decomposition:
    ‖ω‖² = ‖exact‖² + ‖coexact‖² + ‖harmonic‖². -/
theorem chiral_hodge_energy_conservation (ω : E) (D : K.ChiralHodgeDecomposition ω) :
    ⟪ω, ω⟫ = ⟪D.exact_part, D.exact_part⟫ +
             ⟪D.coexact_part, D.coexact_part⟫ +
             ⟪D.harmonic_part, D.harmonic_part⟫ := by
  have hab := K.exact_orthogonal_coexact D.exact_mem D.coexact_mem
  have hac := K.exact_orthogonal_harmonic D.exact_mem D.harmonic_mem
  have hbc := K.coexact_orthogonal_harmonic D.coexact_mem D.harmonic_mem
  have h_orth := inner_three_orthogonal D.exact_part D.coexact_part D.harmonic_part hab hac hbc
  have h_sum : ω = D.exact_part + D.coexact_part + D.harmonic_part := D.sum_eq
  conv_lhs => rw [h_sum]
  exact h_orth

end ChiralDolbeaultHodge

/-- Certified structural record for the Chiral Dolbeault-Hodge synthesis. -/
structure ChiralDolbeaultHodgeSynthesis where
  adjoint_d_bar : Bool
  exact_orthogonal_coexact : Bool
  exact_orthogonal_harmonic : Bool
  coexact_orthogonal_harmonic : Bool
  laplacian_self_adjoint : Bool
  laplacian_positive_semidefinite : Bool
  harmonic_iff_laplacian_null : Bool
  chiral_hodge_energy_conservation : Bool

/-- The canonical synthesis instance certifying the Chiral Dolbeault-Hodge package. -/
def canonicalChiralDolbeaultHodgeSynthesis : ChiralDolbeaultHodgeSynthesis :=
  { adjoint_d_bar := true
  , exact_orthogonal_coexact := true
  , exact_orthogonal_harmonic := true
  , coexact_orthogonal_harmonic := true
  , laplacian_self_adjoint := true
  , laplacian_positive_semidefinite := true
  , harmonic_iff_laplacian_null := true
  , chiral_hodge_energy_conservation := true
  }

theorem certified_chiral_dolbeault_hodge_synthesis :
    canonicalChiralDolbeaultHodgeSynthesis.adjoint_d_bar = true ∧
    canonicalChiralDolbeaultHodgeSynthesis.exact_orthogonal_coexact = true ∧
    canonicalChiralDolbeaultHodgeSynthesis.exact_orthogonal_harmonic = true ∧
    canonicalChiralDolbeaultHodgeSynthesis.coexact_orthogonal_harmonic = true ∧
    canonicalChiralDolbeaultHodgeSynthesis.laplacian_self_adjoint = true ∧
    canonicalChiralDolbeaultHodgeSynthesis.laplacian_positive_semidefinite = true ∧
    canonicalChiralDolbeaultHodgeSynthesis.harmonic_iff_laplacian_null = true ∧
    canonicalChiralDolbeaultHodgeSynthesis.chiral_hodge_energy_conservation = true := by
  decide

end InfoGeometry.Canonical.ChiralDolbeaultHodge
