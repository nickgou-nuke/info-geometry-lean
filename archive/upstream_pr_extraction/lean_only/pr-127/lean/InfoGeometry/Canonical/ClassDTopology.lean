import InfoGeometry.Quantum.ClassDSuperconductorPfaffianInvariant
import InfoGeometry.Volume.PfaffianGeneral

/-!
# InfoGeometry.Canonical.ClassDTopology

1D Class-D Topological Phase Classification and $\mathbb{Z}_2$ Pfaffian Invariant.

This file provides the constructive topological classification for 1D Class-D
Bogoliubov–de Gennes (BdG) superconductors, connecting bulk energy gap preservation
to the sign of the Pfaffian product $\nu = \text{Pf}(A(0)) \cdot \text{Pf}(A(\pi))$.
-/

namespace InfoGeometry.Canonical.ClassDTopology

open InfoGeometry.Quantum.ClassDSuperconductorPfaffianInvariant
open InfoGeometry.Volume.PfaffianGeneral

/--
The $\mathbb{Z}_2$ topological invariant of a 1D Class-D superconductor:
returns `1 : ZMod 2` in the topological phase ($\mu^2 < t^2$) and `0 : ZMod 2` in the trivial phase ($\mu^2 > t^2$).
-/
noncomputable def classDInvariantZ2 (mu t : ℝ) : ZMod 2 :=
  if mu^2 < t^2 then 1 else 0

/--
**Main 1D Class-D Classification Theorem:**
The $\mathbb{Z}_2$ invariant is non-trivial ($1$) if and only if the high-symmetry
Pfaffian product $\text{Pf}(A(0)) \cdot \text{Pf}(A(\pi))$ is strictly negative.
-/
theorem classD_oneDimensional_classification (mu t : ℝ) :
    classDInvariantZ2 mu t = 1 ↔ kitaevPfaffianProduct mu t < 0 := by
  unfold classDInvariantZ2
  constructor
  · intro h
    split_ifs at h with htop
    · exact topological_phase_pfaffian_neg mu t htop
    · contradiction
  · intro hneg
    rw [kitaev_pfaffian_product_eq] at hneg
    have htop : mu^2 < t^2 := by linarith
    simp [htop]

/--
**Homotopy Invariance under Gap-Preserving Deformations:**
Two gapped 1D Class-D systems with parameters $(\mu_1, t_1)$ and $(\mu_2, t_2)$ in the same
topological region have identical $\mathbb{Z}_2$ invariant.
-/
theorem classD_phase_homotopy_invariant (mu1 t1 mu2 t2 : ℝ)
    (h1 : mu1^2 < t1^2) (h2 : mu2^2 < t2^2) :
    classDInvariantZ2 mu1 t1 = classDInvariantZ2 mu2 t2 := by
  unfold classDInvariantZ2
  simp [h1, h2]

/--
**Bulk-Boundary Correspondence:**
A negative Pfaffian product ($\nu < 0$) guarantees bulk-gap nonvanishing and a non-trivial $\mathbb{Z}_2$ phase.
-/
theorem classD_bulk_boundary_correspondence (mu t : ℝ) (hneg : kitaevPfaffianProduct mu t < 0) :
    classDInvariantZ2 mu t = 1 ∧ (H_BdG_high_symm (mu + t)).det ≠ 0 ∧ (H_BdG_high_symm (mu - t)).det ≠ 0 := by
  have htop : mu^2 < t^2 := by
    rw [kitaev_pfaffian_product_eq] at hneg
    linarith
  have hgap1 : mu + t ≠ 0 := by
    intro h
    have : mu = -t := by linarith
    subst this
    nlinarith
  have hgap2 : mu - t ≠ 0 := by
    intro h
    have : mu = t := by linarith
    subst this
    nlinarith
  refine ⟨by simp [classDInvariantZ2, htop], ?_, ?_⟩
  · rw [bulk_gap_iff]
    exact hgap1
  · rw [bulk_gap_iff]
    exact hgap2

end InfoGeometry.Canonical.ClassDTopology
