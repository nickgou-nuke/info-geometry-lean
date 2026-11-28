/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.FixingSubgroup
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Order.Closure

/-!
# Flow symmetries, generated subgroups, and invariant closure

A flow here is an arbitrary monoid homomorphism `T →* G`. Conjugating each
time map defines an actual action on these homomorphisms. Its stabilizer is
the centralizer of the flow range. A family is fixed pointwise as a family of
homomorphisms: relabeling or merely permuting the family is not implicit.

For any native action `MulAction G X`, the native fixing-subgroup/fixed-point
Galois connection gives a closure operator on `Subgroup G`. If every time map
in a family fixes a point, both the algebraically generated subgroup and its
invariant closure fix that point. No topological closure, flow existence,
separation/completeness theorem, or equality with a full geometric symmetry
group follows from these statements.

Outside this namespace, activate the conjugation action on `T →* G` with
`open scoped InfoGeometry.Erlangen.FlowSymmetryClosure`.
-/

namespace InfoGeometry.Erlangen.FlowSymmetryClosure

section Conjugation

variable {G T : Type*} [Group G] [Monoid T]

/-- Conjugation of each time map, by composition with the native inner automorphism. -/
def conjugateFlow (g : G) (φ : T →* G) : T →* G :=
  (MulAut.conj g).toMonoidHom.comp φ

@[simp] theorem conjugateFlow_apply (g : G) (φ : T →* G) (t : T) :
    conjugateFlow g φ t = g * φ t * g⁻¹ := rfl

/-- The actual conjugation action on time-indexed monoid homomorphisms. -/
scoped instance flowConjugationAction : MulAction G (T →* G) where
  smul := conjugateFlow
  one_smul φ := by
    apply MonoidHom.ext
    intro t
    change 1 * φ t * 1⁻¹ = φ t
    rw [inv_one, one_mul, mul_one]
  mul_smul g h φ := by
    apply MonoidHom.ext
    intro t
    change (g * h) * φ t * (g * h)⁻¹ = g * (h * φ t * h⁻¹) * g⁻¹
    simp only [mul_inv_rev, mul_assoc]

@[simp] theorem smul_flow_apply (g : G) (φ : T →* G) (t : T) :
    (g • φ) t = g * φ t * g⁻¹ := rfl

/-- Fixing the whole homomorphism is equivalent to commuting with every time map. -/
theorem mem_flow_stabilizer_iff (g : G) (φ : T →* G) :
    g ∈ MulAction.stabilizer G φ ↔ ∀ t, Commute g (φ t) := by
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro h t
    have ht := congrArg (fun ψ : T →* G => ψ t) h
    change g * φ t * g⁻¹ = φ t at ht
    exact (mul_inv_eq_iff_eq_mul.mp ht : g * φ t = φ t * g)
  · intro h
    ext t
    change g * φ t * g⁻¹ = φ t
    exact mul_inv_eq_iff_eq_mul.mpr (h t).eq

/-- The native stabilizer of a flow is exactly the centralizer of its range. -/
theorem flow_stabilizer_eq_centralizer (φ : T →* G) :
    MulAction.stabilizer G φ = Subgroup.centralizer (Set.range φ) := by
  ext g
  rw [mem_flow_stabilizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h y hy
    rcases hy with ⟨t, rfl⟩
    exact (h t).eq.symm
  · intro h t
    exact (h (φ t) ⟨t, rfl⟩).symm

/-- Changing frame conjugates the symmetry subgroup by the same native inner automorphism. -/
theorem centralizer_conjugateFlow (g : G) (φ : T →* G) :
    Subgroup.centralizer (Set.range (conjugateFlow g φ)) =
      (Subgroup.centralizer (Set.range φ)).map (MulAut.conj g).toMonoidHom := by
  calc
    Subgroup.centralizer (Set.range (conjugateFlow g φ)) =
        MulAction.stabilizer G (g • φ) :=
      (flow_stabilizer_eq_centralizer (g • φ)).symm
    _ = (MulAction.stabilizer G φ).map (MulAut.conj g).toMonoidHom :=
      MulAction.stabilizer_smul_eq_stabilizer_map_conj g φ
    _ = _ := by rw [flow_stabilizer_eq_centralizer]

variable {ι : Type*}

/-- Simultaneous pointwise flow symmetries centralize every member's time maps. -/
theorem fixingSubgroup_flowFamily_eq_centralizer (F : ι → T →* G) :
    fixingSubgroup G (Set.range F) =
      Subgroup.centralizer (⋃ i, Set.range (F i)) := by
  ext g
  rw [mem_fixingSubgroup_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h y hy
    rcases Set.mem_iUnion.mp hy with ⟨i, t, rfl⟩
    have hg : g ∈ MulAction.stabilizer G (F i) := h (F i) ⟨i, rfl⟩
    exact ((mem_flow_stabilizer_iff g (F i)).mp hg t).eq.symm
  · intro h φ hφ
    rcases hφ with ⟨i, rfl⟩
    apply (MulAction.mem_stabilizer_iff).mp
    apply (mem_flow_stabilizer_iff g (F i)).mpr
    intro t
    exact (h (F i t) (Set.mem_iUnion.mpr ⟨i, t, rfl⟩)).symm

/-- A family is acted on pointwise, so its native stabilizer fixes its range pointwise. -/
theorem flowFamily_stabilizer_eq_fixingSubgroup (F : ι → T →* G) :
    MulAction.stabilizer G F = fixingSubgroup G (Set.range F) := by
  ext g
  rw [MulAction.mem_stabilizer_iff, mem_fixingSubgroup_iff]
  constructor
  · intro h φ hφ
    rcases hφ with ⟨i, rfl⟩
    exact congrFun h i
  · intro h
    funext i
    exact h (F i) ⟨i, rfl⟩

end Conjugation

section InvariantClosure

variable (G X : Type*) [Group G] [MulAction G X]

/-- The subgroup closure induced by the native fixing-subgroup/fixed-point
Galois connection for the specified action. This is an algebraic invariant
closure, not a topological closure. -/
def invariantClosure : ClosureOperator (Subgroup G) :=
  (fixingSubgroup_fixedPoints_gc G X).dual.closureOperator

@[simp] theorem invariantClosure_apply (H : Subgroup G) :
    invariantClosure G X H = fixingSubgroup G (MulAction.fixedPoints H X) := rfl

/-- Taking the invariant closure does not change the full set of fixed points. -/
theorem fixedPoints_invariantClosure (H : Subgroup G) :
    MulAction.fixedPoints (invariantClosure G X H) X = MulAction.fixedPoints H X := by
  ext x
  constructor
  · intro hx h
    exact hx ⟨h.val, (invariantClosure G X).le_closure H h.property⟩
  · intro hx g
    exact ((mem_fixingSubgroup_iff G).mp g.property) x hx

/-- Every point stabilizer is closed under the invariant Galois closure.
Thus adjoining all symmetries forced by a subgroup's invariants preserves
each particular point already fixed by that subgroup. -/
theorem invariantClosure_le_stabilizer_iff (H : Subgroup G) (x : X) :
    invariantClosure G X H ≤ MulAction.stabilizer G x ↔
      H ≤ MulAction.stabilizer G x := by
  constructor
  · intro h
    exact ((invariantClosure G X).le_closure H).trans h
  · intro h g hg
    have hx : x ∈ MulAction.fixedPoints H X := fun k => h k.property
    exact ((mem_fixingSubgroup_iff G).mp hg) x hx

end InvariantClosure

section GeneratedFamily

variable {G T ι : Type*} [Group G] [Monoid T]

/-- The algebraic subgroup generated by all time maps of the supplied family. -/
def generatedSubgroup (F : ι → T →* G) : Subgroup G :=
  Subgroup.closure (⋃ i, Set.range (F i))

/-- The generating family controls membership in every ambient subgroup. -/
theorem generatedSubgroup_le_iff (F : ι → T →* G) (H : Subgroup G) :
    generatedSubgroup F ≤ H ↔ ∀ i t, F i t ∈ H := by
  rw [generatedSubgroup, Subgroup.closure_le]
  constructor
  · intro h i t
    exact h (Set.mem_iUnion.mpr ⟨i, t, rfl⟩)
  · intro h g hg
    rcases Set.mem_iUnion.mp hg with ⟨i, t, rfl⟩
    exact h i t

/-- The same symmetry subgroup centralizes the complete algebraically generated group. -/
theorem fixingSubgroup_flowFamily_eq_centralizer_generatedSubgroup
    (F : ι → T →* G) :
    fixingSubgroup G (Set.range F) =
      Subgroup.centralizer (generatedSubgroup F : Set G) := by
  rw [generatedSubgroup, Subgroup.centralizer_closure,
    fixingSubgroup_flowFamily_eq_centralizer]

variable {X : Type*} [MulAction G X]

/-- An invariant preserved by every supplied time map is preserved by the
entire algebraically generated subgroup. -/
theorem generatedSubgroup_le_stabilizer_iff (F : ι → T →* G) (x : X) :
    generatedSubgroup F ≤ MulAction.stabilizer G x ↔
      ∀ i t, F i t • x = x := by
  exact generatedSubgroup_le_iff F (MulAction.stabilizer G x)

/-- Family invariance persists through both algebraic generation and the
action's native Galois closure. This yields containment in the point
stabilizer without asserting that the containment is an equality. -/
theorem invariantClosure_generatedSubgroup_le_stabilizer_iff
    (F : ι → T →* G) (x : X) :
    invariantClosure G X (generatedSubgroup F) ≤ MulAction.stabilizer G x ↔
      ∀ i t, F i t • x = x := by
  rw [invariantClosure_le_stabilizer_iff, generatedSubgroup_le_stabilizer_iff]

end GeneratedFamily

end InfoGeometry.Erlangen.FlowSymmetryClosure
