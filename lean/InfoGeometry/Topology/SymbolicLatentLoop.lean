import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentPathReversal
import InfoGeometry.Topology.SymbolicLatentPathImage

namespace InfoGeometry.Topology

/-!
# Loops in a symbolic latent space

This layer records based-loop data for the existing compact-interval path
model.  It does not identify loops modulo homotopy; that quotient belongs to a
later fundamental-group owner.
-/

def SymbolicLatentLoop
    {X : Type*} [TopologicalSpace X]
    (γ : SymbolicLatentPath X) : Prop :=
  γ.start = γ.finish

def constantSymbolicLatentPath
    {X : Type*} [TopologicalSpace X]
    (x : X) : SymbolicLatentPath X :=
  { toFun := fun _ => x
    continuous_toFun := continuous_const }

@[simp] theorem constantSymbolicLatentPath_start
    {X : Type*} [TopologicalSpace X] (x : X) :
    (constantSymbolicLatentPath x).start = x := rfl

@[simp] theorem constantSymbolicLatentPath_finish
    {X : Type*} [TopologicalSpace X] (x : X) :
    (constantSymbolicLatentPath x).finish = x := rfl

theorem constantSymbolicLatentPath_isLoop
    {X : Type*} [TopologicalSpace X] (x : X) :
    SymbolicLatentLoop (constantSymbolicLatentPath x) := by
  rfl

theorem reverseSymbolicLatentPath_isLoop
    {X : Type*} [TopologicalSpace X]
    {γ : SymbolicLatentPath X}
    (hγ : SymbolicLatentLoop γ) :
    SymbolicLatentLoop (reverseSymbolicLatentPath γ) := by
  change (reverseSymbolicLatentPath γ).start =
    (reverseSymbolicLatentPath γ).finish
  rw [reverseSymbolicLatentPath_start, reverseSymbolicLatentPath_finish]
  exact hγ.symm

theorem SymbolicLatentLoop.endpoint_eq
    {X : Type*} [TopologicalSpace X]
    {γ : SymbolicLatentPath X}
    (hγ : SymbolicLatentLoop γ) :
    γ.endpoints = (γ.start, γ.start) := by
  apply Prod.ext
  · rfl
  · exact hγ.symm

end InfoGeometry.Topology
