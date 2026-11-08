import InfoGeometry.Canonical.A2WeylFin3Action
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# The Type-A₂ Weyl Group as Permutations of Three Colours

## i. Overview

Uses the actual permutation group on three colours as the finite Weyl group carrier and records
its Coxeter relations and a concrete noncommuting pair.

## ii. Key results

- `rho_c_rho_eq_c_inv`
- `rho_shiftC_noncommute`

## iii. Table of contents

- Type-A₂ generators on `Fin 3`
- Involution, order-three, and conjugation relations
- Noncommutativity witness

## iv. References

- `A2WeylFin3Action`, which defines the concrete permutations and their verified relations.
-/

namespace InfoGeometry.Canonical.A2WeylPermutationAction

open InfoGeometry.Canonical.A2WeylFin3Action

/-- The permutation carrier for the Weyl group of type `A₂` on three colours. -/
abbrev WeylA2 := Equiv.Perm (Fin 3)

/-- Forgetful presentation of a colour permutation as a permutation of `Fin 3`. -/
def asPermFin3 (p : WeylA2) : Equiv.Perm (Fin 3) := p

def rho : WeylA2 := rho3
def shiftC : WeylA2 := shiftC3

/-- The reflection generator is an involution. -/
theorem rho_sq_eq_self : rho * rho = 1 := by
  exact rho3_sq

/-- The cyclic generator has order dividing three. -/
theorem shiftC_cube_eq_self : shiftC * shiftC * shiftC = 1 := by
  exact shiftC3_cube

/-- Reflection conjugates the cyclic generator to its inverse. -/
theorem rho_c_rho_eq_c_inv : rho * shiftC * rho = shiftC⁻¹ := by
  exact rho3_shiftC3_rho3

/-- The type-A₂ Weyl generators do not commute: this concrete permutation
witness is a genuine non-abelian order-sensitive action on three colours. -/
theorem rho_shiftC_noncommute : rho * shiftC ≠ shiftC * rho := by
  intro h
  have h0 := congrArg (fun p : WeylA2 => p 0) h
  have hneq : (rho * shiftC) 0 ≠ (shiftC * rho) 0 := by decide
  exact hneq h0

end InfoGeometry.Canonical.A2WeylPermutationAction
