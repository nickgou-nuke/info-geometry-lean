import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
open Matrix

set_option autoImplicit false

/-!
# CausalAlgebra — The Algebra of Causal Proof Structure

## Abstract

A **causal orientation** is a linear involution O (O² = I). From it we
derive the forward/backward projectors d = (I+O)/2, δ = (I-O)/2 and the
Hodge–Dirac operator algebra. The key identity Δ_H = dδ + δd = 0 is the
chosen projector-side analogue of a no-loop condition; identifying it
with a dependency DAG requires an explicit graph-to-operator model.

## Dictionary

| Proof DAG concept | Operator | Identity |
|---|---|---|
| Forward cone (consequences) | d = (I+O)/2 | d² = d |
| Backward cone (dependencies) | δ = (I-O)/2 | δ² = δ |
| Operator no-loop analogue | Δ_H = dδ+δd | Δ_H = 0 |
| Reflexivity | D = d+δ = I | D = I |
| Causal reversal | O = d-δ | O² = I |

The concrete instance is the 2×2 tri-facet matrix O = [[0,1],[1,0]] over ℂ.
-/

namespace InfoGeometry.Causal.Algebra

/-!
## Section 1: Concrete 2×2 Matrix Realisation over ℂ

The tri-facet causal orientation on 2×2 matrices over ℂ with
O = σ₁ = [[0,1],[1,0]]. This is the canonical causal structure that
models the proof DAG: each 2×2 block represents the forward/backward
orientation at an edge.

All identities are proved by entrywise computation via `fin_cases` and `ring`.
-/

/-- Tri-facet matrix σ₁ = [[0,1],[1,0]] — the causal involution over ℂ. -/
def O : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

@[simp]
theorem O_mul_O : O * O = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [O, Matrix.mul_apply]

@[simp]
theorem O_cubed : O * O * O = O := by
  rw [O_mul_O, Matrix.one_mul]

/-- Forward causal projector d = (I+O)/2 over ℂ. -/
noncomputable def d : Matrix (Fin 2) (Fin 2) ℂ := !![1 / 2, 1 / 2; 1 / 2, 1 / 2]

/-- Backward causal projector δ = (I-O)/2 over ℂ. -/
noncomputable def δ : Matrix (Fin 2) (Fin 2) ℂ := !![1 / 2, -1 / 2; -1 / 2, 1 / 2]

/-- Dirac operator D = d + δ. -/
noncomputable def D : Matrix (Fin 2) (Fin 2) ℂ := d + δ

/-- Hodge Laplacian Δ_H = dδ + δd. -/
noncomputable def Δ_H : Matrix (Fin 2) (Fin 2) ℂ := d * δ + δ * d

/-- Dirac Laplacian Δ_D = D². -/
noncomputable def Δ_D : Matrix (Fin 2) (Fin 2) ℂ := D * D

section CausalIdentities

/-! **d² = d** — the future of the future is the future (transitivity). -/
theorem d_sq_eq_d : d * d = d := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [d, O, Matrix.mul_apply]

/-! **δ² = δ** — the past of the past is the past (transitivity backward). -/
theorem δ_sq_eq_δ : δ * δ = δ := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [δ, O, Matrix.mul_apply]

/-! **dδ = 0** — the future of the past is empty (acyclicity). -/
theorem d_mul_δ_zero : d * δ = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [d, δ, O, Matrix.mul_apply]

/-! **δd = 0** — the past of the future is empty (acyclicity). -/
theorem δ_mul_d_zero : δ * d = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [d, δ, O, Matrix.mul_apply]

/-! **d + δ = I** — completeness (every edge is oriented). -/
theorem d_add_δ_eq_one : d + δ = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [d, δ, Matrix.one_apply]

/-! **d - δ = O** — the difference recovers the causal involution. -/
theorem d_sub_δ_eq_O : d - δ = O := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [d, δ, O]

/-! **Δ_H = 0** — the Hodge Laplacian vanishes (harmonic causal structure). -/
theorem Δ_H_zero : Δ_H = 0 := by
  simp [Δ_H, d_mul_δ_zero, δ_mul_d_zero]

/-! **D = I** — the Dirac operator is the identity (every node is its own now). -/
theorem D_eq_one : D = 1 := by
  simp [D, d_add_δ_eq_one]

/-! **Δ_D = I** — the Dirac Laplacian (invertible time). -/
theorem Δ_D_eq_one : Δ_D = 1 := by
  simp [Δ_D, D_eq_one]

/-! **det(O) = -1** — the causal involution reverses orientation. -/
theorem det_O : det O = -1 := by
  unfold O; simp [Matrix.det_fin_two]

/-! **tr(O) = 0** — past and future are equally sized. -/
theorem tr_O : trace O = 0 := by
  unfold O; simp

end CausalIdentities

/- 2×2 matrix identities over ℝ — identical algebra. -/
section RealIdentities

/-- Tri-facet matrix over ℝ. -/
def Oℝ : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

@[simp]
theorem Oℝ_mul_Oℝ : Oℝ * Oℝ = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Oℝ, Matrix.mul_apply]

noncomputable def dℝ : Matrix (Fin 2) (Fin 2) ℝ := !![1 / 2, 1 / 2; 1 / 2, 1 / 2]

noncomputable def δℝ : Matrix (Fin 2) (Fin 2) ℝ := !![1 / 2, -1 / 2; -1 / 2, 1 / 2]

theorem dℝ_sq_eq_dℝ : dℝ * dℝ = dℝ := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [dℝ, Oℝ, Matrix.mul_apply]

theorem δℝ_sq_eq_δℝ : δℝ * δℝ = δℝ := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [δℝ, Oℝ, Matrix.mul_apply]

theorem dℝ_mul_δℝ_zero : dℝ * δℝ = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [dℝ, δℝ, Oℝ, Matrix.mul_apply]

theorem δℝ_mul_dℝ_zero : δℝ * dℝ = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [dℝ, δℝ, Oℝ, Matrix.mul_apply]

theorem dℝ_add_δℝ_eq_one : dℝ + δℝ = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [dℝ, δℝ, Matrix.one_apply]

end RealIdentities

/-!
## Section 2: CausalOrientation Structure (Abstract)

An abstract causal orientation on an ℝ-module V with an involutive
linear map O. The operators d, δ, D, Δ_H, Δ_D are derived.
-/

structure CausalOrientation (V : Type*) [AddCommGroup V] [Module ℝ V] where
  O : V →ₗ[ℝ] V
  O_sq_eq_id : O * O = 1

namespace CausalOrientation
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

noncomputable def d (c : CausalOrientation V) : V →ₗ[ℝ] V :=
  (1/2 : ℝ) • ((1 : V →ₗ[ℝ] V) + c.O)

noncomputable def δ (c : CausalOrientation V) : V →ₗ[ℝ] V :=
  (1/2 : ℝ) • ((1 : V →ₗ[ℝ] V) - c.O)

noncomputable def D (c : CausalOrientation V) : V →ₗ[ℝ] V := c.d + c.δ

noncomputable def Δ_H (c : CausalOrientation V) : V →ₗ[ℝ] V := c.d * c.δ + c.δ * c.d

noncomputable def Δ_D (c : CausalOrientation V) : V →ₗ[ℝ] V := c.D * c.D

end CausalOrientation

/-!
## Section 3: Causal Graph (Proof DAG)

A CausalGraph is a partial order representing the dependency relation
of a Lean development: `a ≤ b` means "declaration a is used in the
proof of declaration b". The forward and backward cones mirror the
projectors d and δ.
-/

class CausalGraph (α : Type*) extends PartialOrder α

namespace CausalGraph
variable {α : Type*} [CausalGraph α]

/-- The forward cone of a declaration: everything it can prove. -/
def forwardCone (a : α) : Set α := {b | a ≤ b}

/-- The backward cone of a declaration: everything needed to prove it. -/
def backwardCone (a : α) : Set α := {b | b ≤ a}

theorem forwardCone_nonempty (a : α) : (forwardCone a).Nonempty :=
  ⟨a, by simp [forwardCone]⟩

theorem backwardCone_nonempty (a : α) : (backwardCone a).Nonempty :=
  ⟨a, by simp [backwardCone]⟩

/--
**Acyclicity**: if b lies in both the forward and backward cones of a,
then a = b. This is the graph-theoretic form of dδ = 0.
-/
theorem acyclicity (a b : α) (hf : b ∈ forwardCone a) (hb : b ∈ backwardCone a) : a = b :=
  le_antisymm (by simpa [forwardCone] using hf) (by simpa [backwardCone] using hb)

/--
**Forward cone transitivity**: if a ≤ b then the forward cone of b is
contained in the forward cone of a. This is the graph-theoretic form
of d² = d.
-/
theorem forwardCone_trans (a b : α) (h : b ∈ forwardCone a) : forwardCone b ⊆ forwardCone a := by
  intro c hc; exact le_trans h hc

/--
**Backward cone transitivity**: if b ≤ a then the backward cone of b is
contained in the backward cone of a. This is the graph-theoretic form
of δ² = δ.
-/
theorem backwardCone_trans (a b : α) (h : b ∈ backwardCone a) : backwardCone b ⊆ backwardCone a := by
  intro c hc; exact le_trans hc h

/--
The forward and backward cones intersect only at the node itself.
This is the graph-theoretic form of Δ_H = 0 (acyclicity).
-/
theorem cones_intersect_at_self (a : α) : forwardCone a ∩ backwardCone a = {a} := by
  ext b; constructor
  · rintro ⟨hf, hb⟩; have h := acyclicity a b hf hb; exact Set.mem_singleton_iff.mpr h.symm
  · intro h; rcases Set.mem_singleton_iff.mp h with rfl
    exact ⟨by simp [forwardCone], by simp [backwardCone]⟩

end CausalGraph

/-!
## Section 4: Bridge — Connecting the 2×2 Algebra to the Graph

The 2×2 causal algebra models the local edge orientation at each node
of the proof DAG. The tri-facet matrix O acts on the orientation space
at an edge: it swaps the forward direction (consequence) with the
backward direction (dependency). The projectors d = (I+O)/2 and
δ = (I-O)/2 pick out the forward and backward components.

The identities mirror the graph-theoretic properties of the causal graph:

| Algebraic identity | Graph-theoretic property |
|---|---|
| d² = d | forward cone transitivity |
| δ² = δ | backward cone transitivity |
| dδ = δd = 0 | acyclicity (F ∩ B = {self}) |
| d+δ = I | completeness (every edge is oriented) |
| Δ_H = 0 | harmonic causal structure |

### Meta-Interpretation

The causal algebra formalised in this file is the **operator grammar**
used to model proof dependencies. Every Lean development can be read as
a CausalGraph, but the identification with the 2×2 projector algebra is
an interpretation layer, not a definitional equality.

The Python toolchain (`graph_hodge_spectrum.py`, `arango_dag_algorithms.py`
with `bounded_hodge_dirac_chiral_docs`, `arango_causal_chiral_cone_prompt.py`,
and the vacuity critic in `vacuity_critic.py` + `tools/leantrail/`) computes
these same invariants on the live ArangoDB topology overlay of the proof DAG.

    Causality on the graph side is a no-loop condition.
    Δ_H = dδ + δd = 0 is the corresponding 2×2 projector analogue.

-/

end InfoGeometry.Causal.Algebra
