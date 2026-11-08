import InfoGeometry.Canonical.CantorCylinderTopology
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Clopen finite-prefix cylinders

The existing Cantor topology owner supplies the neighborhood basis and the
successor decomposition of finite-prefix cylinders.  Here we add the missing
topological fact: every such cylinder is clopen in the product topology.
-/

open Set TopologicalSpace

namespace InfoGeometry.Canonical.CantorCylinderTopology

open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.StoneCantorMathlib

theorem prefixCylinder_eq_coordinate_iInter
    (n : ℕ) (w : BitWord n) :
    prefixCylinder n w =
      ⋂ i : Fin n, (fun x : CantorStream => x i.1) ⁻¹' ({w i} : Set Bool) := by
  ext x
  simp only [prefixCylinder, mem_setOf_eq, mem_iInter, mem_preimage,
    mem_singleton_iff]
  constructor
  · intro h i
    exact congrFun h i
  · intro h
    funext i
    exact h i

theorem isOpen_prefixCylinder (n : ℕ) (w : BitWord n) :
    IsOpen (prefixCylinder n w) := by
  rw [prefixCylinder_eq_coordinate_iInter n w]
  apply isOpen_iInter_of_finite
  intro i
  exact (continuous_apply i.1).isOpen_preimage _ (isOpen_discrete _)

theorem isClosed_prefixCylinder (n : ℕ) (w : BitWord n) :
    IsClosed (prefixCylinder n w) := by
  rw [prefixCylinder_eq_coordinate_iInter n w]
  apply isClosed_iInter
  intro i
  exact IsClosed.preimage (continuous_apply i.1) (isClosed_discrete _)

theorem isClopen_prefixCylinder (n : ℕ) (w : BitWord n) :
    IsOpen (prefixCylinder n w) ∧ IsClosed (prefixCylinder n w) :=
  ⟨isOpen_prefixCylinder n w, isClosed_prefixCylinder n w⟩

theorem isCompact_prefixCylinder (n : ℕ) (w : BitWord n) :
    IsCompact (prefixCylinder n w) := by
  exact IsCompact.of_isClosed_subset isCompact_univ
    (isClosed_prefixCylinder n w) (by intro x; simp)

theorem prefixCylinder_disjoint_of_ne
    (n : ℕ) {w v : BitWord n} (hwv : w ≠ v) :
    Disjoint (prefixCylinder n w) (prefixCylinder n v) := by
  rw [Set.disjoint_left]
  intro x hx hy
  change boundaryPrefix n x = w at hx
  change boundaryPrefix n x = v at hy
  exact hwv (hx.symm.trans hy)

theorem iUnion_prefixCylinder_eq_univ (n : ℕ) :
    (⋃ w : BitWord n, prefixCylinder n w) = Set.univ := by
  ext x
  constructor
  · intro
    trivial
  · intro
    exact Set.mem_iUnion.2 ⟨boundaryPrefix n x, by rfl⟩

end InfoGeometry.Canonical.CantorCylinderTopology
