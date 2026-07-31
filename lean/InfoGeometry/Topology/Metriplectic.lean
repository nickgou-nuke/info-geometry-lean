import Mathlib.Tactic

/-!
# Finite metriplectic bracket packet

This is a theorem-safe algebraic interface for a metriplectic split

`d f / d t = {f,H} + <<f,S>>`.

It does not construct a smooth manifold, super-Kähler geometry, Fisher metric,
or physical thermodynamic model.  Conservation statements are proved from
explicit bracket-annihilation fields supplied by the packet.
-/

namespace InfoGeometry.Topology.Metriplectic

/--
A finite algebraic metriplectic structure on a commutative ring of observables.

The self-zero and annihilation laws are fields, rather than derived from
antisymmetry in arbitrary characteristic.
-/
structure MetriplecticStructure (R : Type*) [CommRing R] where
  poisson : R → R → R
  metric : R → R → R
  poisson_anti_symm : ∀ f g, poisson f g = -poisson g f
  metric_symm : ∀ f g, metric f g = metric g f
  poisson_self_zero : ∀ f, poisson f f = 0
  H : R
  S : R
  metric_H_left_zero : ∀ f, metric H f = 0
  poisson_S_left_zero : ∀ f, poisson S f = 0

/-- Total algebraic metriplectic evolution of an observable. -/
def totalEvolution {R : Type*} [CommRing R] (M : MetriplecticStructure R) (f : R) : R :=
  M.poisson f M.H + M.metric f M.S

/-- Energy conservation from the explicit metriplectic annihilation laws. -/
theorem energy_conservation {R : Type*} [CommRing R] (M : MetriplecticStructure R) :
    totalEvolution M M.H = 0 := by
  simp [totalEvolution, M.poisson_self_zero, M.metric_H_left_zero]

/-- Entropy evolution has no conservative Poisson contribution. -/
theorem entropy_evolution {R : Type*} [CommRing R] (M : MetriplecticStructure R) :
    totalEvolution M M.S = M.metric M.S M.S := by
  simp [totalEvolution, M.poisson_S_left_zero]

/-- The Hamiltonian is also annihilated by the metric bracket on the right. -/
theorem metric_annihilates_H_right {R : Type*} [CommRing R]
    (M : MetriplecticStructure R) (f : R) :
    M.metric f M.H = 0 :=
  by rw [M.metric_symm]; exact M.metric_H_left_zero f

/-- The right entropy Casimir law follows from Poisson antisymmetry. -/
theorem poisson_annihilates_S_right {R : Type*} [CommRing R]
    (M : MetriplecticStructure R) (f : R) :
    M.poisson f M.S = 0 := by
  rw [M.poisson_anti_symm, M.poisson_S_left_zero, neg_zero]

/-- The entropy is also annihilated by the Poisson bracket on the left. -/
theorem poisson_annihilates_S_left {R : Type*} [CommRing R]
    (M : MetriplecticStructure R) (f : R) :
    M.poisson M.S f = 0 :=
  M.poisson_S_left_zero f

end InfoGeometry.Topology.Metriplectic
