/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import DAG.TwoComplex

/-! `TwoComplex` keeps raw natural-number payloads so malformed inputs can be
validated and diagnosed. This module provides typed finite-index accessors
under the explicit `HasValidIndices` contract. -/
namespace DAG.ValidTwoComplexIndices

open DAG

variable {α : Type*} [BEq α] [Hashable α]

/-- A `TwoComplex` paired with proof that all stored vertex and cell indices
are in range. -/
abbrev ValidTwoComplex := {tc : TwoComplex α // HasValidIndices tc}

/-- Source vertex of a valid indexed edge, represented in the vertex `Fin`. -/
def edgeSource (tc : TwoComplex α) (h : HasValidIndices tc)
    (i : Fin tc.edges.size) : Fin tc.base.toGraph.nodes.size :=
  ⟨(tc.edges[i.val]).1, (h.1 i).1⟩

/-- Target vertex of a valid indexed edge, represented in the vertex `Fin`. -/
def edgeTarget (tc : TwoComplex α) (h : HasValidIndices tc)
    (i : Fin tc.edges.size) : Fin tc.base.toGraph.nodes.size :=
  ⟨(tc.edges[i.val]).2, (h.1 i).2⟩

theorem edgeSource_lt (tc : TwoComplex α) (h : HasValidIndices tc)
    (i : Fin tc.edges.size) : (edgeSource tc h i).val < tc.base.toGraph.nodes.size :=
  (h.1 i).1

theorem edgeTarget_lt (tc : TwoComplex α) (h : HasValidIndices tc)
    (i : Fin tc.edges.size) : (edgeTarget tc h i).val < tc.base.toGraph.nodes.size :=
  (h.1 i).2

/-- Each face's three edge references can be safely used as finite edge indices. -/
def faceEdge₁ (tc : TwoComplex α) (h : HasValidIndices tc)
    (i : Fin tc.faces.size) : Fin tc.edges.size :=
  ⟨(tc.faces[i.val]).1, (h.2.1 i).1⟩

def faceEdge₂ (tc : TwoComplex α) (h : HasValidIndices tc)
    (i : Fin tc.faces.size) : Fin tc.edges.size :=
  ⟨(tc.faces[i.val]).2.1, (h.2.1 i).2.1⟩

def faceEdge₃ (tc : TwoComplex α) (h : HasValidIndices tc)
    (i : Fin tc.faces.size) : Fin tc.edges.size :=
  ⟨(tc.faces[i.val]).2.2, (h.2.1 i).2.2⟩

theorem faceEdge₁_lt (tc : TwoComplex α) (h : HasValidIndices tc)
    (i : Fin tc.faces.size) : (faceEdge₁ tc h i).val < tc.edges.size :=
  (h.2.1 i).1

theorem faceEdge₂_lt (tc : TwoComplex α) (h : HasValidIndices tc)
    (i : Fin tc.faces.size) : (faceEdge₂ tc h i).val < tc.edges.size :=
  (h.2.1 i).2.1

theorem faceEdge₃_lt (tc : TwoComplex α) (h : HasValidIndices tc)
    (i : Fin tc.faces.size) : (faceEdge₃ tc h i).val < tc.edges.size :=
  (h.2.1 i).2.2

/-- Both edge references in each digon are safely represented as finite indices. -/
def digonEdge₁ (tc : TwoComplex α) (h : HasValidIndices tc)
    (i : Fin tc.digons.size) : Fin tc.edges.size :=
  ⟨(tc.digons[i.val]).1, (h.2.2 i).1⟩

def digonEdge₂ (tc : TwoComplex α) (h : HasValidIndices tc)
    (i : Fin tc.digons.size) : Fin tc.edges.size :=
  ⟨(tc.digons[i.val]).2, (h.2.2 i).2⟩

theorem digonEdge₁_lt (tc : TwoComplex α) (h : HasValidIndices tc)
    (i : Fin tc.digons.size) : (digonEdge₁ tc h i).val < tc.edges.size :=
  (h.2.2 i).1

theorem digonEdge₂_lt (tc : TwoComplex α) (h : HasValidIndices tc)
    (i : Fin tc.digons.size) : (digonEdge₂ tc h i).val < tc.edges.size :=
  (h.2.2 i).2

end DAG.ValidTwoComplexIndices
