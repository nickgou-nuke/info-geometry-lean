/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Basic.Complex.Basic
import DAG.Basic

/-!
# DAG-indexed Majorana Data Package

This module packages a hydrated graph, a Majorana family, and a binary
central-residue function. It does not define a map on paths or prove a
projective-representation law.

The edge operator below is the composite of the two endpoint generators.
-/

noncomputable section

namespace InfoGeometry.DAGMajorana

open DAG

/--
A Majorana net: a family of operators γ_i on a real vector space V
satisfying {γ_i, γ_j} = 2·δ_{ij}·id.
-/
structure MajoranaNet.{u, v} (α : Type u) where
  V : Type v
  [add : AddCommGroup V]
  [module : Module ℝ V]
  gamma : α → (V → V)
  anticomm : ∀ i j (x : V), gamma i (gamma j x) + gamma j (gamma i x) = (2 : ℝ) • x

/-- Legacy-named package of graph, Majorana-net, and binary-residue data.
It carries no path-to-operator homomorphism field. -/
structure DAGMajoranaHomomorphism.{u, v}
    (α : Type u) [BEq α] [Hashable α] where
  dag : HydratedGraph α
  net : MajoranaNet.{u, v} α
  /-- The central residue readout: values in {±1}. -/
  centralResidue : α → α → ℤ
  residue_binary : ∀ u v, centralResidue u v = 1 ∨ centralResidue u v = -1

namespace DAGMajoranaHomomorphism

/-- The operator assigned to an edge, derived from its endpoint generators. -/
def edgeToOp
    {α : Type*} [BEq α] [Hashable α]
    (F : DAGMajoranaHomomorphism α) (u v : α) : F.net.V → F.net.V :=
  F.net.gamma u ∘ F.net.gamma v

@[simp]
theorem edgeToOp_eq
    {α : Type*} [BEq α] [Hashable α]
    (F : DAGMajoranaHomomorphism α) (u v : α) :
    F.edgeToOp u v = F.net.gamma u ∘ F.net.gamma v :=
  rfl

end DAGMajoranaHomomorphism

/--
Direct readout of the defining `{±1}` range condition for the central residue.
-/
theorem central_residue_binary
    (α : Type*) [BEq α] [Hashable α]
    (F : DAGMajoranaHomomorphism α) :
    ∀ u v : α, F.centralResidue u v = 1 ∨ F.centralResidue u v = -1 := by
  intro u v
  exact F.residue_binary u v

/-- Compatibility alias for `central_residue_binary`; the range condition is
part of the package data and this theorem does not assert a cycle-sum law. -/
theorem central_residue_binary_for_obstruction_readout
    (α : Type*) [BEq α] [Hashable α]
    (F : DAGMajoranaHomomorphism α) :
    ∀ u v : α, F.centralResidue u v = 1 ∨ F.centralResidue u v = -1 := by
  intro u v
  exact F.residue_binary u v

end InfoGeometry.DAGMajorana
