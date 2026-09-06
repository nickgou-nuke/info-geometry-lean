import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic

-- Formalization of Wareham's Thesis (CGA) in Lean 4
-- We are aiming for a purely formal mathematical definition.

section CGA

variable {R : Type*} [CommRing R] [Invertible (2:R)]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable (Q : QuadraticForm R V)

-- The Clifford Algebra over V with quadratic form Q
def CGA := CliffordAlgebra Q

-- We will flesh this out more fully once the specific types are decided
end CGA
