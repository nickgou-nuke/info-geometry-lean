import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Set.Basic
import Mathlib.Tactic
import InfoGeometry.Physics.ThermodynamicAlgebraicCenter

namespace InfoGeometry.Physics

variable (A : Type*) [Ring A]

/-- Algebraic data for a Tomita-style conjugation on a ring.  The analytic
standard-form construction is intentionally not assumed here. -/
structure TomitaConjugationData where
  J : A → A
  J_one : J 1 = 1
  J_involutive : ∀ x, J (J x) = x
  J_mul : ∀ x y, J (x * y) = J y * J x

def tomitaImage (T : TomitaConjugationData A) (M : Set A) : Set A :=
  T.J '' M

/-- Explicit hypotheses expressing that the conjugated algebra is the
commutant.  These are the missing standard-form content, not consequences of
the bare ring axioms. -/
structure TomitaCommutantData (T : TomitaConjugationData A) (M : Set A) where
  image_commutes : ∀ {x}, x ∈ M → ∀ {y}, y ∈ M → T.J x * y = y * T.J x
  commutant_is_image : ∀ {y}, y ∈ Commutant A M → ∃ x ∈ M, T.J x = y

theorem tomita_image_subset_commutant
    (T : TomitaConjugationData A) (M : Set A)
    (hT : TomitaCommutantData A T M) :
    tomitaImage A T M ⊆ Commutant A M := by
  rintro y ⟨x, hx, rfl⟩
  dsimp [Commutant]
  intro z hz
  exact hT.image_commutes hx hz

theorem tomita_image_eq_commutant
    (T : TomitaConjugationData A) (M : Set A)
    (hT : TomitaCommutantData A T M) :
    tomitaImage A T M = Commutant A M := by
  apply Set.Subset.antisymm
  · exact tomita_image_subset_commutant A T M hT
  · intro y hy
    obtain ⟨x, hx, hxy⟩ := hT.commutant_is_image hy
    exact ⟨x, hx, hxy⟩

theorem tomita_image_image
    (T : TomitaConjugationData A) (M : Set A) :
    tomitaImage A T (tomitaImage A T M) = M := by
  ext y
  constructor
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    simpa [T.J_involutive x] using hx
  · intro hy
    exact ⟨T.J y, ⟨y, hy, rfl⟩, T.J_involutive y⟩

/-- Algebraic modular flow data: a one-parameter group action on the carrier.
The preservation field records invariance of a chosen observable set. -/
structure ModularFlowData where
  sigma : ℝ → A → A
  sigma_zero : ∀ x, sigma 0 x = x
  sigma_add : ∀ t s x, sigma (t + s) x = sigma t (sigma s x)
  sigma_neg_left : ∀ t x, sigma (-t) (sigma t x) = x
  sigma_neg_right : ∀ t x, sigma t (sigma (-t) x) = x

theorem modular_flow_is_bijective
    (F : ModularFlowData A) (t : ℝ) :
    Function.Bijective (F.sigma t) := by
  constructor
  · intro x y hxy
    rw [← F.sigma_neg_left t x, ← F.sigma_neg_left t y, hxy]
  · intro y
    refine ⟨F.sigma (-t) y, ?_⟩
    exact F.sigma_neg_right t y

theorem modular_flow_zero
    (F : ModularFlowData A) (x : A) :
    F.sigma 0 x = x :=
  F.sigma_zero x

theorem modular_flow_group_law
    (F : ModularFlowData A) (t s : ℝ) (x : A) :
    F.sigma (t + s) x = F.sigma t (F.sigma s x) :=
  F.sigma_add t s x

theorem modular_flow_commute
    (F : ModularFlowData A) (t s : ℝ) (x : A) :
    F.sigma t (F.sigma s x) = F.sigma s (F.sigma t x) := by
  rw [← F.sigma_add t s x, ← F.sigma_add s t x, add_comm]

end InfoGeometry.Physics
