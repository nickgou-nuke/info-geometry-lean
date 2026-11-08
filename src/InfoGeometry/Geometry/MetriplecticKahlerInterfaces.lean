import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Order.Basic

/-!
# Metriplectic and Kähler interfaces

This keeps the metriplectic dual-bracket skeleton separate from the Kähler
complex-structure layer. Positivity is represented over an ordered scalar
codomain, not over an arbitrary `CommRing`.
-/

namespace InfoGeometry.Geometry

structure MetriplecticStructure
    (Obs R : Type*) [Ring R] [LinearOrder R] where
  H : Obs
  S : Obs
  poisson : Obs → Obs → R
  metric : Obs → Obs → R
  poisson_skew : ∀ f g, poisson f g = - poisson g f
  poisson_self : ∀ f, poisson f f = 0
  metric_symm : ∀ f g, metric f g = metric g f
  metric_H_casimir : ∀ f, metric H f = 0
  poisson_S_casimir : ∀ f, poisson S f = 0
  metric_nonneg : ∀ f, 0 ≤ metric f f

namespace MetriplecticStructure

variable {Obs R : Type*} [Ring R] [LinearOrder R]

 theorem energy_conservation (sys : MetriplecticStructure Obs R) :
    sys.poisson sys.H sys.H + sys.metric sys.H sys.S = 0 := by
  rw [sys.poisson_self, sys.metric_H_casimir, add_zero]

 theorem entropy_nonnegative (sys : MetriplecticStructure Obs R) :
    0 ≤ sys.metric sys.S sys.S :=
  sys.metric_nonneg sys.S

 theorem entropy_evolution_skeleton (sys : MetriplecticStructure Obs R) :
    sys.poisson sys.S sys.H + sys.metric sys.S sys.S = sys.metric sys.S sys.S := by
  rw [sys.poisson_S_casimir, zero_add]

theorem metric_entropy_energy_zero (sys : MetriplecticStructure Obs R) :
    sys.metric sys.S sys.H = 0 := by
  rw [sys.metric_symm, sys.metric_H_casimir]

theorem poisson_energy_entropy_zero (sys : MetriplecticStructure Obs R) :
    sys.poisson sys.H sys.S = 0 := by
  rw [sys.poisson_skew, sys.poisson_S_casimir, neg_zero]

theorem entropy_total_evolution_nonnegative
    (sys : MetriplecticStructure Obs R) :
    0 ≤ sys.poisson sys.S sys.H + sys.metric sys.S sys.S := by
  rw [sys.poisson_S_casimir, zero_add]
  exact sys.metric_nonneg sys.S

theorem energy_conservation_and_entropy_production
    (sys : MetriplecticStructure Obs R) :
    sys.poisson sys.H sys.H + sys.metric sys.H sys.S = 0 ∧
      0 ≤ sys.poisson sys.S sys.H + sys.metric sys.S sys.S :=
  ⟨sys.energy_conservation, sys.entropy_total_evolution_nonnegative⟩

theorem metriplectic_degeneracy
    (sys : MetriplecticStructure Obs R) :
    (∀ f, sys.metric sys.H f = 0) ∧
      (∀ f, sys.metric f sys.H = 0) ∧
      (∀ f, sys.poisson sys.S f = 0) ∧
      (∀ f, sys.poisson f sys.S = 0) := by
  refine ⟨sys.metric_H_casimir, ?_, sys.poisson_S_casimir, ?_⟩
  · intro f
    rw [sys.metric_symm, sys.metric_H_casimir]
  · intro f
    rw [sys.poisson_skew, sys.poisson_S_casimir, neg_zero]

end MetriplecticStructure

/-- Minimal Kähler-compatible triple over a carrier `V`. -/
structure KahlerData (V R : Type*) [Neg V] [Ring R] [LinearOrder R] where
  J : V → V
  g : V → V → R
  omega : V → V → R
  J_sq : ∀ x, J (J x) = -x
  g_symm : ∀ x y, g x y = g y x
  omega_skew : ∀ x y, omega x y = - omega y x
  omega_eq_gJ : ∀ x y, omega x y = g (J x) y
  J_isometry : ∀ x y, g (J x) (J y) = g x y

end InfoGeometry.Geometry
