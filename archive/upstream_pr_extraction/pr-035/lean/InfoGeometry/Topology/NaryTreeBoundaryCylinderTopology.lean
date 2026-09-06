import InfoGeometry.Topology.NaryTreeBoundaryInverseLimit

/-!
# Cylinder topology on an n-ary tree boundary

For a finite discrete alphabet, finite-prefix cylinders are clopen product
sets.  This owner is deliberately independent of probability, metric, or
smooth structure: it records only the local topology of the inverse-limit
boundary carrier `ℕ → A`.
-/

noncomputable section

namespace InfoGeometry.Topology.NaryTreeBoundaryCylinderTopology

open Set Filter TopologicalSpace
open scoped Topology
open InfoGeometry.Topology.NaryTreeBoundaryInverseLimit

variable {A : Type} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]

def boundaryPrefix (n : ℕ) (x : Boundary (A := A)) : Word (A := A) n :=
  fun i => x i.1

theorem continuous_boundaryPrefix (n : ℕ) :
    Continuous (boundaryPrefix (A := A) n) := by
  apply continuous_pi
  intro i
  exact continuous_apply i.1

def prefixCylinder (n : ℕ) (w : Word (A := A) n) :
    Set (Boundary (A := A)) :=
  {x | boundaryPrefix (A := A) n x = w}

theorem mem_prefixCylinder_iff
    (n : ℕ) (w : Word (A := A) n) (x : Boundary (A := A)) :
    x ∈ prefixCylinder (A := A) n w ↔
      ∀ i : Fin n, x i.1 = w i := by
  constructor
  · intro h i
    exact congrFun h i
  · intro h
    funext i
    exact h i

theorem prefixCylinder_eq_coordinate_iInter
    (n : ℕ) (w : Word (A := A) n) :
    prefixCylinder (A := A) n w =
      ⋂ i : Fin n, (fun x : Boundary (A := A) => x i.1) ⁻¹'
        ({w i} : Set A) := by
  ext x
  simp only [prefixCylinder, boundaryPrefix, mem_setOf_eq, mem_iInter,
    mem_preimage, mem_singleton_iff]
  constructor
  · intro h i
    exact congrFun h i
  · intro h
    funext i
    exact h i

theorem isOpen_prefixCylinder
    (n : ℕ) (w : Word (A := A) n) :
    IsOpen (prefixCylinder (A := A) n w) := by
  rw [prefixCylinder_eq_coordinate_iInter]
  apply isOpen_iInter_of_finite
  intro i
  exact (continuous_apply i.1).isOpen_preimage _ (isOpen_discrete _)

theorem isClosed_prefixCylinder
    (n : ℕ) (w : Word (A := A) n) :
    IsClosed (prefixCylinder (A := A) n w) := by
  rw [prefixCylinder_eq_coordinate_iInter]
  apply isClosed_iInter
  intro i
  exact IsClosed.preimage (continuous_apply i.1) (isClosed_discrete _)

theorem isClopen_prefixCylinder
    (n : ℕ) (w : Word (A := A) n) :
    IsOpen (prefixCylinder (A := A) n w) ∧
      IsClosed (prefixCylinder (A := A) n w) :=
  ⟨isOpen_prefixCylinder n w, isClosed_prefixCylinder n w⟩

theorem prefixCylinder_mem_nhds
    (n : ℕ) (x : Boundary (A := A)) :
    prefixCylinder (A := A) n (boundaryPrefix (A := A) n x) ∈ nhds x := by
  apply (isOpen_prefixCylinder n (boundaryPrefix (A := A) n x)).mem_nhds
  rfl

theorem prefixCylinder_disjoint_of_ne
    (n : ℕ) {w v : Word (A := A) n} (hwv : w ≠ v) :
    Disjoint (prefixCylinder (A := A) n w)
      (prefixCylinder (A := A) n v) := by
  rw [Set.disjoint_left]
  intro x hx hy
  exact hwv ((show boundaryPrefix (A := A) n x = w from hx).symm.trans hy)

theorem iUnion_prefixCylinder_eq_univ (n : ℕ) :
    (⋃ w : Word (A := A) n, prefixCylinder (A := A) n w) = Set.univ := by
  ext x
  constructor
  · intro
    trivial
  · intro
    exact Set.mem_iUnion.2
      ⟨boundaryPrefix (A := A) n x, rfl⟩

end InfoGeometry.Topology.NaryTreeBoundaryCylinderTopology
