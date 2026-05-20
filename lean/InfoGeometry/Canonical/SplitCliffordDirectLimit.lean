import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.Algebra.Colimit.Module
import InfoGeometry.Canonical.SplitCliffordTensorBridge
import InfoGeometry.Meta.Architecture

open scoped TensorProduct

noncomputable section

/-!
# InfoGeometry.Canonical.SplitCliffordDirectLimit

The direct-limit wrapper for the existing recursive split `Cl(n,n)` tower.

This file does not invent a new infinite analytic tensor product. It packages
the canonical `n ↦ n + 1` split-tower embedding, the induced directed system,
and the corresponding direct limit in `Mathlib`'s `DirectLimit` API.
-/

namespace InfoGeometry.Canonical.SplitCliffordDirectLimit

open InfoGeometry.CliffordTower
open InfoGeometry.Clifford.ClNN
open InfoGeometry.Canonical.SplitCliffordTensorBridge

/-- Canonical one-step embedding of the split tower into the next split stage. -/
@[rep_depth krein]
noncomputable def splitCliffordStep (n : ℕ) :
    SplitClNNAlg n →ₐ[ℝ] SplitClNNAlg (n + 1) :=
  ((splitCliffordTensorStepEquiv n).symm.toAlgHom).comp
    (GradedTensorProduct.includeRight (CliffordAlgebra.evenOdd InfoGeometry.CliffordTower.Q11)
      (CliffordAlgebra.evenOdd (Qsplit n)))

/--
Iterated embedding from stage `m` to stage `n` for `m ≤ n`.

This is the directed-system transition map used to form the direct limit.
-/
@[rep_depth krein]
noncomputable def splitCliffordMap (m n : ℕ) (h : m ≤ n) :
    SplitClNNAlg m →ₐ[ℝ] SplitClNNAlg n :=
  Nat.leRecOn h
    (C := fun n => SplitClNNAlg m →ₐ[ℝ] SplitClNNAlg n)
    (fun {k} ih => (splitCliffordStep k).comp ih)
    (AlgHom.id ℝ (SplitClNNAlg m))

@[simp, rep_depth krein]
theorem splitCliffordMap_refl (m : ℕ) :
    splitCliffordMap m m le_rfl = AlgHom.id ℝ (SplitClNNAlg m) := by
  simpa [splitCliffordMap] using
    (Nat.leRecOn_self
      (C := fun n => SplitClNNAlg m →ₐ[ℝ] SplitClNNAlg n)
      (next := fun {k} ih => (splitCliffordStep k).comp ih)
      (x := AlgHom.id ℝ (SplitClNNAlg m)))

@[simp, rep_depth krein]
theorem splitCliffordMap_succ (m n : ℕ) (h : m ≤ n) :
    splitCliffordMap m (n + 1) (Nat.le_trans h (Nat.le_succ n))
      = (splitCliffordStep n).comp (splitCliffordMap m n h) := by
  unfold splitCliffordMap
  rw [Nat.leRecOn_trans h (Nat.le_succ n)]
  rw [Nat.leRecOn_succ']

@[rep_depth krein]
theorem splitCliffordMap_trans (m n k : ℕ) (hmn : m ≤ n) (hnk : n ≤ k) :
    splitCliffordMap m k (hmn.trans hnk)
      = Nat.leRecOn hnk
          (fun {k} ih => (splitCliffordStep k).comp ih)
          (splitCliffordMap m n hmn) := by
  simpa [splitCliffordMap] using
    (Nat.leRecOn_trans hmn hnk
      (next := fun {k} ih => (splitCliffordStep k).comp ih)
      (x := AlgHom.id ℝ (SplitClNNAlg m)))

@[rep_depth krein]
theorem splitCliffordMap_apply_trans (m n k : ℕ) (hmn : m ≤ n) (hnk : n ≤ k)
    (x : SplitClNNAlg m) :
    splitCliffordMap m k (hmn.trans hnk) x
      = splitCliffordMap n k hnk (splitCliffordMap m n hmn x) := by
  refine Nat.le_induction
    (m := n)
    (P := fun t ht =>
      splitCliffordMap m t (Nat.le_trans hmn ht) x
        = splitCliffordMap n t ht (splitCliffordMap m n hmn x))
    ?base ?succ k hnk
  · simpa using
      congrArg (fun φ : SplitClNNAlg m →ₐ[ℝ] SplitClNNAlg n => φ x)
        (splitCliffordMap_refl n)
  · intro t ht ih
    have hmt : m ≤ t := Nat.le_trans hmn ht
    rw [splitCliffordMap_succ (m := m) (n := t) (h := hmt),
      splitCliffordMap_succ (m := n) (n := t) (h := ht)]
    exact congrArg (fun y => splitCliffordStep t y) ih

/-- The recursive split tower is a directed system in the `Mathlib` sense. -/
@[rep_depth krein]
instance splitCliffordDirectedSystem :
    DirectedSystem SplitClNNAlg (fun m n h => splitCliffordMap m n h) where
  map_self := by
    intro m x
    simpa using congrArg (fun φ : SplitClNNAlg m →ₐ[ℝ] SplitClNNAlg m => φ x)
      (splitCliffordMap_refl m)
  map_map := by
    intro k j i hij hjk x
    simpa using (splitCliffordMap_apply_trans i j k hij hjk x).symm

/-- The direct limit of the split `Cl(n,n)` tower, as a ring object. -/
@[rep_depth krein]
abbrev SplitCliffordInfinity := _root_.DirectLimit SplitClNNAlg (fun m n h => splitCliffordMap m n h)

@[rep_depth krein]
theorem splitCliffordInfinity_exists_of [Nonempty ℕ] [IsDirectedOrder ℕ]
    (z : SplitCliffordInfinity) :
    ∃ n x, (DirectLimit.Module.of ℝ ℕ SplitClNNAlg
      (fun m n h => splitCliffordMap m n h) n x) = z := by
  rcases DirectLimit.exists_eq_mk (f := fun m n h => splitCliffordMap m n h) z with
    ⟨n, x, hx⟩
  exact ⟨n, x, by simpa [DirectLimit.Module.of] using hx.symm⟩

@[rep_depth krein]
theorem splitCliffordInfinity_induction_on [Nonempty ℕ] [IsDirectedOrder ℕ]
    {C : SplitCliffordInfinity → Prop}
    (z : SplitCliffordInfinity) (ih : ∀ n x, C (DirectLimit.Module.of ℝ ℕ SplitClNNAlg
      (fun m n h => splitCliffordMap m n h) n x)) :
    C z :=
  DirectLimit.induction (f := fun m n h => splitCliffordMap m n h) ih z

/-- Every split direct-limit element expands along an infinite tail of later stages. -/
@[rep_depth krein]
theorem splitCliffordInfinity_boundary_expands
    (z : SplitCliffordInfinity) :
    ∃ n x,
      DirectLimit.Module.of ℝ ℕ SplitClNNAlg
        (fun m n h => splitCliffordMap m n h) n x = z ∧
      ∀ k : ℕ,
        DirectLimit.Module.of ℝ ℕ SplitClNNAlg
          (fun m n h => splitCliffordMap m n h) (n + k)
          (splitCliffordMap n (n + k) (Nat.le_add_right n k) x) = z := by
  rcases splitCliffordInfinity_exists_of z with ⟨n, x, hx⟩
  refine ⟨n, x, hx, ?_⟩
  intro k
  calc
    DirectLimit.Module.of ℝ ℕ SplitClNNAlg
        (fun m n h => splitCliffordMap m n h) (n + k)
        (splitCliffordMap n (n + k) (Nat.le_add_right n k) x)
        = DirectLimit.Module.of ℝ ℕ SplitClNNAlg
            (fun m n h => splitCliffordMap m n h) n x := by
              simpa using
                (DirectLimit.Module.of_f
                  (f := fun m n h => splitCliffordMap m n h)
                  (i := n) (j := n + k) (hij := Nat.le_add_right n k) (x := x))
    _ = z := hx

/-- Infinite-dimensional split direct-limit elements have arbitrarily deep representatives. -/
@[rep_depth krein]
theorem splitCliffordInfinity_unbounded_representatives
    (z : SplitCliffordInfinity) :
    ∀ N : ℕ, ∃ n ≥ N, ∃ x : SplitClNNAlg n,
      DirectLimit.Module.of ℝ ℕ SplitClNNAlg
        (fun m n h => splitCliffordMap m n h) n x = z := by
  intro N
  rcases splitCliffordInfinity_boundary_expands z with ⟨n, x, hx, htail⟩
  refine ⟨n + N, Nat.le_add_left _ _, ?_, ?_⟩
  · exact splitCliffordMap n (n + N) (Nat.le_add_right n N) x
  · simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htail N

end InfoGeometry.Canonical.SplitCliffordDirectLimit
