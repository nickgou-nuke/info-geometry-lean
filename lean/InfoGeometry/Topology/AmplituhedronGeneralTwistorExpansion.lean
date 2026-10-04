import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

open Matrix
open scoped BigOperators

namespace InfoGeometry.Amplituhedron

variable {n : ℕ} {R : Type*} [CommRing R]

/-! ### 1. 2x2 Plücker Minors and 4x4 Determinants -/

def minor2 (C : Matrix (Fin 2) (Fin n) R) (a b : Fin n) : R :=
  C 0 a * C 1 b - C 1 a * C 0 b

def det4 (M : Matrix (Fin 4) (Fin 4) R) : R :=
  M 0 0 * (M 1 1 * (M 2 2 * M 3 3 - M 2 3 * M 3 2) -
           M 1 2 * (M 2 1 * M 3 3 - M 2 3 * M 3 1) +
           M 1 3 * (M 2 1 * M 3 2 - M 2 2 * M 3 1)) -
  M 0 1 * (M 1 0 * (M 2 2 * M 3 3 - M 2 3 * M 3 2) -
           M 1 2 * (M 2 0 * M 3 3 - M 2 3 * M 3 0) +
           M 1 3 * (M 2 0 * M 3 2 - M 2 2 * M 3 0)) +
  M 0 2 * (M 1 0 * (M 2 1 * M 3 3 - M 2 3 * M 3 1) -
           M 1 1 * (M 2 0 * M 3 3 - M 2 3 * M 3 0) +
           M 1 3 * (M 2 0 * M 3 1 - M 2 1 * M 3 0)) -
  M 0 3 * (M 1 0 * (M 2 1 * M 3 2 - M 2 2 * M 3 1) -
           M 1 1 * (M 2 0 * M 3 2 - M 2 2 * M 3 0) +
           M 1 2 * (M 2 0 * M 3 1 - M 2 1 * M 3 0))

/-! ### 2. The General Kinematic Twistor Projection Y = C * Z -/

def twistorProj (C : Matrix (Fin 2) (Fin n) R) (Z : Matrix (Fin n) (Fin 4) R) :
    Matrix (Fin 2) (Fin 4) R :=
  C * Z

def twistorMatrix (Y : Matrix (Fin 2) (Fin 4) R) (Z : Matrix (Fin n) (Fin 4) R) (a b : Fin n) :
    Matrix (Fin 4) (Fin 4) R :=
  fun r c =>
    if r = 0 then Y 0 c
    else if r = 1 then Y 1 c
    else if r = 2 then Z a c
    else Z b c

def twistorBracket (Y : Matrix (Fin 2) (Fin 4) R) (Z : Matrix (Fin n) (Fin 4) R) (a b : Fin n) : R :=
  det4 (twistorMatrix Y Z a b)

def externalBracket (Z : Matrix (Fin n) (Fin 4) R) (i j a b : Fin n) : R :=
  det4 (fun r c =>
    if r = 0 then Z i c
    else if r = 1 then Z j c
    else if r = 2 then Z a c
    else Z b c)

/-! ### 3. Canonical Form Structure -/

/-- Shift an index cyclicly modulo n for the physical boundaries. -/
def cyclicNext [NeZero n] (i : Fin n) : Fin n :=
  if h : i.val + 1 < n then ⟨i.val + 1, h⟩ else ⟨0, NeZero.pos n⟩

structure AmplituhedronCanonicalForm [NeZero n] [Field R] where
  density : Matrix (Fin 2) (Fin 4) R → Matrix (Fin n) (Fin 4) R → R
  denominator_eq : ∀ (Y : Matrix (Fin 2) (Fin 4) R) (Z : Matrix (Fin n) (Fin 4) R),
    ∃ (numerator : R), density Y Z = numerator / (∏ i : Fin n, twistorBracket Y Z i (cyclicNext i))
  numerator_nonvanishing : True

end InfoGeometry.Amplituhedron
