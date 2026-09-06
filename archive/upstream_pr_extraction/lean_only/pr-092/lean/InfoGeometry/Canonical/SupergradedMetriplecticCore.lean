import Mathlib.Tactic
import InfoGeometry.Canonical.MetriplecticCore

/-!
# InfoGeometry.Canonical.SupergradedMetriplecticCore

Finite supergraded metriplectic core.

This file adds grading-dependent sign data to the metriplectic interface
without introducing analytic/infinite-dimensional claims.
-/

namespace InfoGeometry.Canonical.SupergradedMetriplecticCore

structure SupergradedMetriplectic
    (A : Type*) [Ring A] (degree : A → ℤ) where
  sign : ℤ → ℤ → A
  poisson : A → A → A
  poisson_graded_skew :
    ∀ x y, poisson x y = -(sign (degree x) (degree y) * poisson y x)
  metric : A → A → A
  metric_graded_symm :
    ∀ x y, metric x y = sign (degree x) (degree y) * metric y x
  Hamiltonian : A
  Entropy : A
  hamiltonian_conserved : ∀ x, metric x Hamiltonian = 0
  entropy_casimir : ∀ x, poisson x Entropy = 0

namespace SupergradedMetriplectic

variable {A : Type*} [Ring A] {degree : A → ℤ}
variable (S : SupergradedMetriplectic A degree)

/-- Unified graded Leibniz bracket. -/
def leibniz (x y : A) : A := S.poisson x y + S.metric x y

theorem metric_H_zero (x : A) : S.metric x S.Hamiltonian = 0 :=
  S.hamiltonian_conserved x

theorem poisson_entropy_zero (x : A) : S.poisson x S.Entropy = 0 :=
  S.entropy_casimir x

/-- First-law style readback with explicit Poisson diagonal property. -/
theorem leibniz_H_H_eq_zero
    (h_poisson_diag : S.poisson S.Hamiltonian S.Hamiltonian = 0) :
    S.leibniz S.Hamiltonian S.Hamiltonian = 0 := by
  unfold leibniz
  rw [h_poisson_diag, S.metric_H_zero]
  simp

/-- Direct decomposition of `[S,H]_L` into graded Poisson + graded metric lanes. -/
theorem leibniz_entropy_H_decompose :
    S.leibniz S.Entropy S.Hamiltonian
      = S.poisson S.Entropy S.Hamiltonian + S.metric S.Entropy S.Hamiltonian := by
  rfl

/-- Casimir specialization on the entropy/Hamiltonian lane. -/
theorem leibniz_entropy_H_eq_metric
    (h_casimir_right : S.poisson S.Entropy S.Hamiltonian = 0) :
    S.leibniz S.Entropy S.Hamiltonian = S.metric S.Entropy S.Hamiltonian := by
  unfold leibniz
  rw [h_casimir_right, zero_add]

end SupergradedMetriplectic

/--
Canonical embedding of an ungraded metriplectic packet as a supergraded one
with constant sign `1` and trivial degree.
-/
def ofUngraded
    {A : Type*} [Ring A]
    (M : MetriplecticCore.MetriplecticSystem A) :
    SupergradedMetriplectic A (fun _ => (0 : ℤ)) where
  sign := fun _ _ => (1 : A)
  poisson := M.poisson
  poisson_graded_skew := by
    intro x y
    simpa [one_mul] using M.poisson_skew x y
  metric := M.metric
  metric_graded_symm := by
    intro x y
    simpa [one_mul] using M.metric_symm x y
  Hamiltonian := M.Hamiltonian
  Entropy := M.Entropy
  hamiltonian_conserved := M.hamiltonian_conserved
  entropy_casimir := M.entropy_casimir

end InfoGeometry.Canonical.SupergradedMetriplecticCore

