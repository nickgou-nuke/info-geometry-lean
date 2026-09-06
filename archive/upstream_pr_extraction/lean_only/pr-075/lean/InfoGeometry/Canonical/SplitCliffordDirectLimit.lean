import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.Algebra.Colimit.Module
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.RingTheory.Flat.Basic
import InfoGeometry.Canonical.SplitCliffordTensorBridge
import InfoGeometry.Meta.Architecture

open scoped TensorProduct
open scoped DirectSum

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
open SplitCliffordTensorBridge

/-- Canonical one-step embedding of the split tower into the next split stage. -/
@[rep_depth krein]
noncomputable def splitCliffordStep (n : ℕ) :
    SplitClNNAlg n →ₐ[ℝ] SplitClNNAlg (n + 1) :=
  ((splitCliffordTensorStepEquiv n).symm.toAlgHom).comp
    (GradedTensorProduct.includeRight (CliffordAlgebra.evenOdd InfoGeometry.CliffordTower.Q11)
      (CliffordAlgebra.evenOdd (Qsplit n)))

/-- The canonical split-Clifford one-step map is injective. -/
theorem splitCliffordStep_injective (n : ℕ) : Function.Injective (splitCliffordStep n) := by
  classical
  set_option synthInstance.maxHeartbeats 200000 in
  let A0 : Type _ := ⨁ i, CliffordAlgebra.evenOdd InfoGeometry.CliffordTower.Q11 i
  let Bn : Type _ := ⨁ i, CliffordAlgebra.evenOdd (Qsplit n) i
  have hA0 : Function.Injective (algebraMap ℝ A0) := by
    intro r s h
    haveI : Nontrivial (CliffordAlgebra InfoGeometry.CliffordTower.Q11) :=
      (CliffordAlgebra.equivExterior InfoGeometry.CliffordTower.Q11).symm.injective.nontrivial
    have h' :=
      congrArg
        ((DirectSum.decomposeAlgEquiv
          (CliffordAlgebra.evenOdd InfoGeometry.CliffordTower.Q11)).symm) h
    have h'' :
        (algebraMap ℝ (CliffordAlgebra InfoGeometry.CliffordTower.Q11)) r =
          (algebraMap ℝ (CliffordAlgebra InfoGeometry.CliffordTower.Q11)) s := by
      simpa [A0] using h'
    haveI : Module.Free ℝ (CliffordAlgebra InfoGeometry.CliffordTower.Q11) := by
      infer_instance
    exact (FaithfulSMul.algebraMap_injective ℝ
      (CliffordAlgebra InfoGeometry.CliffordTower.Q11)) h''
  have h_right :
      Function.Injective
        (fun b : CliffordAlgebra (Qsplit n) =>
          Algebra.TensorProduct.includeRight
            (R := ℝ)
            (A := A0)
            (B := Bn)
            ((DirectSum.decomposeAlgEquiv (CliffordAlgebra.evenOdd (Qsplit n))) b)) := by
    exact
      Function.Injective.comp
        (Algebra.TensorProduct.includeRight_injective
          (R := ℝ)
          (A := A0)
          (B := Bn)
          hA0)
        ((DirectSum.decomposeAlgEquiv (CliffordAlgebra.evenOdd (Qsplit n))).injective)
  have h_inc :
      Function.Injective (GradedTensorProduct.includeRight
        (CliffordAlgebra.evenOdd InfoGeometry.CliffordTower.Q11)
        (CliffordAlgebra.evenOdd (Qsplit n))) := by
    intro b₁ b₂ h
    apply h_right
    simpa [A0, Bn, GradedTensorProduct.includeRight, GradedTensorProduct.auxEquiv_tmul] using
      congrArg
        (GradedTensorProduct.auxEquiv ℝ
          (CliffordAlgebra.evenOdd InfoGeometry.CliffordTower.Q11)
          (CliffordAlgebra.evenOdd (Qsplit n))) h
  exact (splitCliffordTensorStepEquiv n).symm.injective.comp h_inc

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
  induction k, hnk using Nat.le_induction with
  | base =>
      simp
        [splitCliffordMap_refl]
  | succ k hk ih =>
      rw [splitCliffordMap_succ (m := m) (n := k) (h := Nat.le_trans hmn hk),
        splitCliffordMap_succ (m := n) (n := k) (h := hk)]
      exact congrArg (fun y => splitCliffordStep k y) ih


/-- The recursive split tower is a directed system in the `Mathlib` sense. -/
@[rep_depth krein]
instance splitCliffordDirectedSystem :
    DirectedSystem SplitClNNAlg (fun m n h => splitCliffordMap m n h) where
  map_self := by
    intro m x
    exact congrArg (fun φ : SplitClNNAlg m →ₐ[ℝ] SplitClNNAlg m => φ x)
      (splitCliffordMap_refl m)
  map_map := by
    intro k j i hij hjk x
    simpa using (splitCliffordMap_apply_trans i j k hij hjk x).symm

/-- The direct limit of the split `Cl(n,n)` tower, as a ring object. -/
@[rep_depth krein]
abbrev SplitCliffordInfinity := _root_.DirectLimit SplitClNNAlg (fun m n h => splitCliffordMap m n h)

noncomputable instance : Module ℝ SplitCliffordInfinity :=
  DirectLimit.instModule

noncomputable instance : SMul ℝ SplitCliffordInfinity :=
  (inferInstance : Module ℝ SplitCliffordInfinity).toSMul

noncomputable instance : HSMul ℝ SplitCliffordInfinity SplitCliffordInfinity :=
  instHSMul

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
              exact
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

/--
Finite `Cl(5,5)` window absorption in the split direct limit:
adding any finite split-Clifford tail after stage `5` does not change the
represented direct-limit element.

This is the direct-limit form of the scale-invariance slogan
`Cl(5,5) ⊗ Cl(∞,∞) ≅ Cl(∞,∞)` that is supported by the current tower API.
-/
@[rep_depth krein]
theorem splitCliffordInfinity_cl55_window_absorbs_finite_tail
    (x : SplitClNNAlg 5) (k : ℕ) :
    DirectLimit.Module.of ℝ ℕ SplitClNNAlg
        (fun m n h => splitCliffordMap m n h) (5 + k)
        (splitCliffordMap 5 (5 + k) (Nat.le_add_right 5 k) x)
      =
    DirectLimit.Module.of ℝ ℕ SplitClNNAlg
        (fun m n h => splitCliffordMap m n h) 5 x := by
  exact
    (DirectLimit.Module.of_f
      (f := fun m n h => splitCliffordMap m n h)
      (i := 5) (j := 5 + k) (hij := Nat.le_add_right 5 k) (x := x))

/--
Every split direct-limit element has a representative at or beyond the finite
`Cl(5,5)` window.
-/
@[rep_depth krein]
theorem splitCliffordInfinity_has_representative_beyond_cl55_window
    (z : SplitCliffordInfinity) :
    ∃ n ≥ 5, ∃ x : SplitClNNAlg n,
      DirectLimit.Module.of ℝ ℕ SplitClNNAlg
        (fun m n h => splitCliffordMap m n h) n x = z := by
  exact splitCliffordInfinity_unbounded_representatives z 5

/--
Any direct-limit predicate proved on the `Cl(5,5)` window also holds after
adding an absorbed finite tail to that same window element.

This is the precise transport principle available from the stage-5 absorption
theorem. It does not assert that every direct-limit element comes from stage
`5`; it transports stage-5 invariants along finite tail embeddings.
-/
@[rep_depth krein]
theorem splitCliffordInfinity_cl55_predicate_lifts_to_finite_tail
    {P : SplitCliffordInfinity → Prop}
    (h5 : ∀ x : SplitClNNAlg 5,
      P (DirectLimit.Module.of ℝ ℕ SplitClNNAlg
        (fun m n h => splitCliffordMap m n h) 5 x))
    (x : SplitClNNAlg 5) (k : ℕ) :
    P (DirectLimit.Module.of ℝ ℕ SplitClNNAlg
        (fun m n h => splitCliffordMap m n h) (5 + k)
        (splitCliffordMap 5 (5 + k) (Nat.le_add_right 5 k) x)) := by
  rw [splitCliffordInfinity_cl55_window_absorbs_finite_tail]
  exact h5 x

/--
If a direct-limit predicate is proved for every representative at every finite
stage beyond the `Cl(5,5)` window, then it holds for every element of the split
Clifford direct limit.
-/
@[rep_depth krein]
theorem splitCliffordInfinity_tail_predicate_lifts_to_all
    {P : SplitCliffordInfinity → Prop}
    (hTail : ∀ n, n ≥ 5 → ∀ x : SplitClNNAlg n,
      P (DirectLimit.Module.of ℝ ℕ SplitClNNAlg
        (fun m n h => splitCliffordMap m n h) n x)) :
    ∀ z : SplitCliffordInfinity, P z := by
  intro z
  rcases splitCliffordInfinity_has_representative_beyond_cl55_window z with
    ⟨n, hn, x, hx⟩
  rw [← hx]
  exact hTail n hn x

end InfoGeometry.Canonical.SplitCliffordDirectLimit
