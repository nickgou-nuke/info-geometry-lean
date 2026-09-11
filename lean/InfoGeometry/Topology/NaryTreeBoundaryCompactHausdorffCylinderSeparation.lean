import InfoGeometry.Topology.NaryTreeBoundaryCompactHausdorffCylinder
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Separation by finite-prefix cylinders

For a compact Hausdorff alphabet, prefix cylinders are closed rather than
necessarily open.  They nevertheless separate distinct boundary sequences:
different sequences have different finite prefixes.
-/

noncomputable section

namespace InfoGeometry.Topology.NaryTreeBoundaryCompactHausdorffCylinder

open Set
open InfoGeometry.Topology.NaryTreeBoundaryInverseLimit

variable {A : Type} [TopologicalSpace A] [CompactSpace A] [T2Space A]

theorem mem_compactPrefixCylinder_iff
    {n : ℕ} {w : Word (A := A) n} (x : Boundary (A := A)) :
    x ∈ compactPrefixCylinder (A := A) n w ↔
      ∀ i : Fin n, x i.1 = w i := by
  constructor
  · intro hx i
    exact congrFun hx i
  · intro hx
    change compactBoundaryPrefix (A := A) n x = w
    funext i
    exact hx i

theorem disjoint_compactPrefixCylinder_of_ne
    {n : ℕ} {w v : Word (A := A) n} (hwv : w ≠ v) :
    Disjoint (compactPrefixCylinder (A := A) n w)
      (compactPrefixCylinder (A := A) n v) := by
  rw [Set.disjoint_left]
  intro x hx hy
  apply hwv
  funext i
  exact ((mem_compactPrefixCylinder_iff x).mp hx i).symm.trans
    ((mem_compactPrefixCylinder_iff x).mp hy i)

theorem exists_compactPrefixCylinder_separates
    {x y : Boundary (A := A)} (hxy : x ≠ y) :
    ∃ n : ℕ, ∃ w : Word (A := A) n,
      x ∈ compactPrefixCylinder (A := A) n w ∧
        y ∉ compactPrefixCylinder (A := A) n w := by
  by_contra h
  push_neg at h
  apply hxy
  funext n
  have hx : x ∈ compactPrefixCylinder (A := A) (n + 1)
      (compactBoundaryPrefix (A := A) (n + 1) x) := by
    apply (mem_compactPrefixCylinder_iff x).2
    intro i
    rfl
  have hy := h (n + 1) (compactBoundaryPrefix (A := A) (n + 1) x) hx
  have hy' := (mem_compactPrefixCylinder_iff y).mp hy (Fin.last n)
  simpa [compactBoundaryPrefix] using hy'.symm

theorem iUnion_compactPrefixCylinder_eq_univ (n : ℕ) :
    (⋃ w : Word (A := A) n,
      compactPrefixCylinder (A := A) n w) = Set.univ := by
  apply Set.eq_univ_iff_forall.2
  intro x
  refine Set.mem_iUnion.2 ⟨compactBoundaryPrefix (A := A) n x, ?_⟩
  exact (mem_compactPrefixCylinder_iff x).2 (by
    intro i
    rfl)

end InfoGeometry.Topology.NaryTreeBoundaryCompactHausdorffCylinder
