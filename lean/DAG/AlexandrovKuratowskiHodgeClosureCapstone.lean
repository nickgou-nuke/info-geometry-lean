/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Order.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

/-!
# Aleksandrōv Topology, Kuratowski Closure, and Hodge Coboundary Exactness on ProofDAGs

This module formalizes the meta-mathematical topology of the repository's declaration DAG:
1. **Aleksandrōv Topology on Posets**:
   - Upper sets (future cones of consequences) and Lower sets (past cones of premises).
   - Topological duality theorem: `isUpperSet_compl_iff` and `isLowerSet_compl_iff`.

2. **Kuratowski Closure Axioms for Downward Premise Closure $\downarrow S$**:
   - Preservation of the empty set: $\downarrow \emptyset = \emptyset$.
   - Extensivity: $S \subseteq \downarrow S$.
   - Union distributivity: $\downarrow (A \cup B) = \downarrow A \cup \downarrow B$.
   - Idempotence (Fixed-point stabilization): $\downarrow (\downarrow S) = \downarrow S$.

3. **Causal Proof Corridor**:
   - Order intervals $\operatorname{corridor}(a, b) = [a, b]$.
   - Antisymmetric reflexivity: $\operatorname{corridor}(a, a) = \{a\}$.

4. **Hodge 2-Complex Coboundary Nilpotency ($d_1 \circ d_0 = 0$)**:
   - Exactness of the discrete differential on triangles: $(d_1(d_0 f))(v_0, v_1, v_2) = 0$.

All proofs are complete in native Mathlib 4 with 0 `sorry`s, 0 custom axioms, and 0 wrappers.
-/

namespace InfoGeometry.DAG.TopologicalClosure

variable {α : Type*} [PartialOrder α]

/-! ## 1. Aleksandrōv Upper and Lower Sets -/

/-- An upper set in a poset (closed under taking greater elements). -/
def IsUpperSet (U : Set α) : Prop :=
  ∀ {x y : α}, x ≤ y → x ∈ U → y ∈ U

/-- A lower set in a poset (closed under taking smaller elements). -/
def IsLowerSet (C : Set α) : Prop :=
  ∀ {x y : α}, x ≤ y → y ∈ C → x ∈ C

/-- 🏆 THEOREM: The complement of a lower set is an upper set, and vice versa. -/
theorem isUpperSet_compl_iff (s : Set α) :
    IsUpperSet sᶜ ↔ IsLowerSet s := by
  constructor
  · intro h x y hle hy
    by_contra hx
    have hxc : x ∈ sᶜ := hx
    have hyc : y ∈ sᶜ := h hle hxc
    exact hyc hy
  · intro h x y hle hx hy
    exact hx (h hle hy)

/-- 🏆 THEOREM: The complement of an upper set is a lower set. -/
theorem isLowerSet_compl_iff (s : Set α) :
    IsLowerSet sᶜ ↔ IsUpperSet s := by
  constructor
  · intro h x y hle hx
    by_contra hy
    have hyc : y ∈ sᶜ := hy
    have hxc : x ∈ sᶜ := h hle hyc
    exact hxc hx
  · intro h x y hle hy hx
    exact hy (h hle hx)

/-! ## 2. Kuratowski Closure Axioms for Downward Sets -/

/-- Downward closure operator: $\downarrow s = \{ x \mid \exists y \in s, x \le y \}$. -/
def downwardClosure (s : Set α) : Set α :=
  { x | ∃ y ∈ s, x ≤ y }

/-- 🏆 THEOREM (Kuratowski Axiom 1): Preservation of the empty set: $\downarrow \emptyset = \emptyset$. -/
theorem downwardClosure_empty :
    downwardClosure (α := α) ∅ = ∅ := by
  ext x
  simp [downwardClosure]

/-- 🏆 THEOREM (Kuratowski Axiom 2): Extensivity: $s \subseteq \downarrow s$. -/
theorem subset_downwardClosure (s : Set α) :
    s ⊆ downwardClosure s := by
  intro x hx
  exact ⟨x, hx, le_refl x⟩

/-- 🏆 THEOREM (Kuratowski Axiom 3): Union distributivity: $\downarrow (s \cup t) = \downarrow s \cup \downarrow t$. -/
theorem downwardClosure_union (s t : Set α) :
    downwardClosure (s ∪ t) = downwardClosure s ∪ downwardClosure t := by
  ext x
  constructor
  · rintro ⟨y, hy, hle⟩
    rcases hy with hys | hyt
    · left; exact ⟨y, hys, hle⟩
    · right; exact ⟨y, hyt, hle⟩
  · rintro (⟨y, hy, hle⟩ | ⟨y, hy, hle⟩)
    · exact ⟨y, Or.inl hy, hle⟩
    · exact ⟨y, Or.inr hy, hle⟩

/-- 🏆 THEOREM (Kuratowski Axiom 4): Idempotence: $\downarrow (\downarrow s) = \downarrow s$. -/
theorem downwardClosure_idempotent (s : Set α) :
    downwardClosure (downwardClosure s) = downwardClosure s := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, hyz⟩, hxy⟩
    exact ⟨z, hz, le_trans hxy hyz⟩
  · intro hx
    exact subset_downwardClosure (downwardClosure s) hx

/-- 🏆 THEOREM: The downward closure is always a valid lower set. -/
theorem downwardClosure_isLowerSet (s : Set α) :
    IsLowerSet (downwardClosure s) := by
  intro x y hxy hy
  rcases hy with ⟨z, hz, hyz⟩
  exact ⟨z, hz, le_trans hxy hyz⟩

/-! ## 3. Causal Proof Corridor -/

/-- Causal order corridor between two proofs/declarations: $[a, b] = \{ x \mid a \le x \le b \}$. -/
def causalCorridor (a b : α) : Set α :=
  { x | a ≤ x ∧ x ≤ b }

/-- 🏆 THEOREM: Self-referential causal corridor collapses to a singleton: $\operatorname{corridor}(a, a) = \{a\}$. -/
theorem causalCorridor_self (a : α) :
    causalCorridor a a = {a} := by
  ext x
  simp only [causalCorridor, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact le_antisymm h2 h1
  · rintro rfl
    exact ⟨le_rfl, le_rfl⟩

/-! ## 4. Hodge 2-Complex Coboundary Nilpotency ($d_1 \circ d_0 = 0$) -/

variable {V : Type*}

/-- Discrete 0-coboundary (gradient) on 0-cochains: $(d_0 f)(u, v) = f(v) - f(u)$. -/
def d0 (f : V → ℝ) (u v : V) : ℝ :=
  f v - f u

/-- Discrete 1-coboundary (curl) on 1-cochains evaluated on a triangle $(v_0, v_1, v_2)$:
$(d_1 g)(v_0, v_1, v_2) = g(v_1, v_2) - g(v_0, v_2) + g(v_0, v_1)$. -/
def d1 (g : V → V → ℝ) (v0 v1 v2 : V) : ℝ :=
  g v1 v2 - g v0 v2 + g v0 v1

/-- 🏆 THEOREM (Hodge Coboundary Nilpotency):
The discrete differential on 2-complexes satisfies $d_1(d_0 f) = 0$ identically on every triangle. -/
theorem coboundary_squared_zero (f : V → ℝ) (v0 v1 v2 : V) :
    d1 (d0 f) v0 v1 v2 = 0 := by
  dsimp [d1, d0]
  ring

/-! ## 5. Grand DAG Topological Closure Synthesis -/

/--
🏆 **GRAND DAG TOPOLOGICAL CLOSURE SYNTHESIS**

Combines:
1. **Aleksandrōv Duality**: $\operatorname{IsUpperSet}(s^c) \leftrightarrow \operatorname{IsLowerSet}(s)$.
2. **Kuratowski Axioms**: $\downarrow \emptyset = \emptyset$, $s \subseteq \downarrow s$, $\downarrow(s \cup t) = \downarrow s \cup \downarrow t$, $\downarrow(\downarrow s) = \downarrow s$.
3. **Causal Point-Corridor**: $\operatorname{corridor}(a, a) = \{a\}$.
4. **Hodge Exactness**: $d_1(d_0 f) = 0$.
-/
theorem grand_dag_topological_closure_synthesis
    (s t : Set α)
    (a : α)
    (f : V → ℝ)
    (v0 v1 v2 : V) :
    (IsUpperSet sᶜ ↔ IsLowerSet s) ∧
    (downwardClosure (α := α) ∅ = ∅) ∧
    (s ⊆ downwardClosure s) ∧
    (downwardClosure (s ∪ t) = downwardClosure s ∪ downwardClosure t) ∧
    (downwardClosure (downwardClosure s) = downwardClosure s) ∧
    (causalCorridor a a = {a}) ∧
    (d1 (d0 f) v0 v1 v2 = 0) := by
  refine ⟨isUpperSet_compl_iff s,
          downwardClosure_empty,
          subset_downwardClosure s,
          downwardClosure_union s t,
          downwardClosure_idempotent s,
          causalCorridor_self a,
          coboundary_squared_zero f v0 v1 v2⟩

end InfoGeometry.DAG.TopologicalClosure
