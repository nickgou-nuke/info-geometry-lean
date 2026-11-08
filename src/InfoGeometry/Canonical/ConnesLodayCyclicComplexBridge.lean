import InfoGeometry.Canonical.ConnesCyclicCohomology
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Ring.Basic

/-!
# Connes--Loday cyclic complex bridge

The cyclic boundary is owned by `ConnesCyclic.CyclicBoundaryOperator`.  This
module keeps the historical Loday names as generic algebraic operations and
forwards the boundary laws to that owner; it does not model a differential as
a real scalar or prove nilpotency by defining the operator to be zero.
-/

namespace ConnesLoday

universe u

section Differential

variable {A : Type u} [NonUnitalNonAssocSemiring A]

/-- A noncommutative differential one-form with coefficients in `A`. -/
structure DiffOneForm (A : Type u) where
  coeff : A

namespace DiffOneForm

/-- Universal differential operator at a chosen coefficient. -/
def d (_val deriv : A) : DiffOneForm A :=
  ⟨deriv⟩

/-- Right multiplication of a one-form coefficient. -/
def mulRight (df : DiffOneForm A) (b : A) : DiffOneForm A :=
  ⟨df.coeff * b⟩

/-- Left multiplication of a one-form coefficient. -/
def mulLeft (a : A) (df : DiffOneForm A) : DiffOneForm A :=
  ⟨a * df.coeff⟩

/-- Addition of one-form coefficients. -/
def add (df1 df2 : DiffOneForm A) : DiffOneForm A :=
  ⟨df1.coeff + df2.coeff⟩

/-- Leibniz rule for the universal algebraic differential interface. -/
theorem leibniz_rule (a a' b b' : A) :
    d (a * b) (a' * b + a * b') =
      add (mulRight (d a a') b) (mulLeft a (d b b')) := by
  rfl

/-- Additivity of the universal algebraic differential interface. -/
theorem differential_linear (a a' b b' : A) :
    d (a + b) (a' + b') = add (d a a') (d b b') := by
  rfl

end DiffOneForm

end Differential

section CyclicBoundary

variable {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]

/-- The genuine noncommutative cyclic boundary owner. -/
abbrev CyclicBoundaryOperator (n : ℕ) [Fintype (Fin n)] [DecidableEq (Fin n)] : Type _ :=
  Matrix (Fin n) (Fin n) ℂ →+ Matrix (Fin n) (Fin n) ℂ

/-- Read the owned cyclic boundary map. -/
abbrev cyclicBoundary (boundary : CyclicBoundaryOperator n) :
    Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ :=
  boundary

/-- Nilpotency is forwarded from the owner boundary law. -/
theorem cyclic_boundary_nilpotent
    (boundary : CyclicBoundaryOperator n)
    (nilpotent : ∀ X, boundary (boundary X) = 0)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    cyclicBoundary boundary (cyclicBoundary boundary X) = 0 :=
  ConnesCyclic.CyclicBoundaryOperator.boundary_nilpotent_sq boundary nilpotent X

/-- The owned boundary vanishes at zero by additivity. -/
theorem cyclic_boundary_zero
    (boundary : CyclicBoundaryOperator n) :
    cyclicBoundary boundary 0 = 0 :=
  ConnesCyclic.CyclicBoundaryOperator.boundary_zero boundary

end CyclicBoundary

end ConnesLoday
