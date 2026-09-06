import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Data.Real.Basic

/-!
# Quantum Involution Core

Minimal owner-level algebra for a pair of real involutions.
This file is intentionally lower than the Majorana, polarization, and Clifford
layers: it records only the carrier, the two involutions, and their squares.
-/

namespace InfoGeometry.Quantum

universe u

/-- Base real-linear involution package with no interaction law yet imposed. -/
structure InvolutionCore where
  V : Type u
  [instAddCommGroup : AddCommGroup V]
  [instModule : Module ℝ V]
  J : V →ₗ[ℝ] V
  eps : V →ₗ[ℝ] V
  J_sq : J.comp J = (LinearMap.id : V →ₗ[ℝ] V)
  eps_sq : eps.comp eps = (LinearMap.id : V →ₗ[ℝ] V)

attribute [instance] InvolutionCore.instAddCommGroup
attribute [instance] InvolutionCore.instModule

instance : CoeSort InvolutionCore (Type u) := ⟨InvolutionCore.V⟩

namespace InvolutionCore

/-- The raw composite of the two involutions. -/
noncomputable def je (X : InvolutionCore) : X →ₗ[ℝ] X :=
  X.J.comp X.eps

@[simp] theorem je_def (X : InvolutionCore) :
    X.je = X.J.comp X.eps := rfl

@[simp] theorem J_sq_apply (X : InvolutionCore) (x : X) :
    X.J (X.J x) = x := by
  exact congrArg (fun f : X →ₗ[ℝ] X => f x) X.J_sq

@[simp] theorem eps_sq_apply (X : InvolutionCore) (x : X) :
    X.eps (X.eps x) = x := by
  exact congrArg (fun f : X →ₗ[ℝ] X => f x) X.eps_sq

end InvolutionCore

end InfoGeometry.Quantum
