import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CayleyBoundaryIntertwiningOnDomain

namespace InfoGeometry.Canonical

open InfoGeometry.Topology

/-!
Topological packaging of the Cayley intertwiner.  Both sides are continuous
only on the same denominator-safe real domain; the equality is not promoted
to a global statement at the Möbius pole.
-/

theorem continuousOn_cayley_real_modular_flow (s : ℝ) :
    ContinuousOn
      (fun x : ℝ => cayleyBoundary (Real.exp (2 * s) * x))
      (cayleyIntertwiningDomain s) := by
  apply continuous_cayleyBoundary.continuousOn.comp
    ((continuous_const.mul continuous_id).continuousOn.mono
      (Set.subset_univ _))
  intro x hx
  exact Set.mem_univ _

theorem continuousOn_disk_modular_flow_after_cayley (s : ℝ) :
    ContinuousOn
      (fun x : ℝ => diskBoundaryBoost s (cayleyBoundary x))
      (cayleyIntertwiningDomain s) := by
  apply (continuousOn_diskBoundaryBoost s).comp
    continuous_cayleyBoundary.continuousOn
  intro x hx
  exact cayleyBoundary_image_mem_diskBoundaryBoostDomain s x hx

theorem cayley_modular_boundary_intertwining_eqOn (s : ℝ) :
    Set.EqOn
      (fun x : ℝ => cayleyBoundary (Real.exp (2 * s) * x))
      (fun x : ℝ => diskBoundaryBoost s (cayleyBoundary x))
      (cayleyIntertwiningDomain s) := by
  intro x hx
  exact cayley_modularBoost_intertwining_on_domain s x hx

theorem continuous_cayley_modular_boundary_intertwiner (s : ℝ) :
    ContinuousOn
      (fun x : ℝ => cayleyBoundary (Real.exp (2 * s) * x))
      (cayleyIntertwiningDomain s) ∧
    ContinuousOn
      (fun x : ℝ => diskBoundaryBoost s (cayleyBoundary x))
      (cayleyIntertwiningDomain s) ∧
    Set.EqOn
      (fun x : ℝ => cayleyBoundary (Real.exp (2 * s) * x))
      (fun x : ℝ => diskBoundaryBoost s (cayleyBoundary x))
      (cayleyIntertwiningDomain s) := by
  exact ⟨continuousOn_cayley_real_modular_flow s,
    continuousOn_disk_modular_flow_after_cayley s,
    cayley_modular_boundary_intertwining_eqOn s⟩

end InfoGeometry.Canonical
