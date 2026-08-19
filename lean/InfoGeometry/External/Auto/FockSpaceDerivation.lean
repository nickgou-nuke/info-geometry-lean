import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Finite Fock-sector data

This owner keeps only finite, type-safe carriers.  It does not identify an
identity map with a creation or annihilation operator, and a null determinant
is not treated as a spinor theorem.  CCR, coherent-state equations, and
analytic Fock-space constructions belong to separate owners.
-/

noncomputable section

universe u v

/-! ## Finite sectors -/

def FockSym (n : ℕ) (H : Type v) : Type v := Fin n → H

def BosonicFockSpace (H : Type v) : Type v := Σ n : ℕ, FockSym n H

/-! ## Null-matrix kernel data -/

structure NullPauliKernelData where
  matrix : Matrix (Fin 2) (Fin 2) ℂ
  null : Matrix.det matrix = (0 : ℂ)
  kernelVector : Fin 2 → ℂ
  kernelVector_nonzero : kernelVector ≠ 0
  annihilated : matrix.mulVec kernelVector = 0

/-! ## Explicit coherent-state property data -/

structure CoherentStateData (F : Type*) where
  parameter : ℂ
  state : F
  satisfies : F → Prop
  state_satisfies : satisfies state
