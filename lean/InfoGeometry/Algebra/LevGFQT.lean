import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Matrix
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic

/-!
Lev's Galois Field Quantum Theory (GFQT)
Investigating the modular representations of so(1,4)
-/

namespace InfoGeometry.Algebra.LevGFQT

section SO14

variable {K : Type*} [CommRing K]

/-- The diagonal metric tensor for so(1,4) signature (+, -, -, -, -) -/
def eta : Matrix (Fin 5) (Fin 5) ℤ :=
  Matrix.diagonal ![1, -1, -1, -1, -1]

/-- The generators of the so(1,4) Lie algebra represented over K. -/
def M (a b : Fin 5) : Matrix (Fin 5) (Fin 5) K :=
  fun i j => 
    if i = a ∧ j = b then (eta b b : K)
    else if i = b ∧ j = a then -(eta a a : K)
    else 0

end SO14

section GFQT

variable {p : ℕ} [Fact p.Prime]

/-- The GFQT condition that p = 3 (mod 4) guaranteeing the imaginary quadratic extension. -/
def is_p_mod_4_eq_3 : Prop := p % 4 = 3

end GFQT

end InfoGeometry.Algebra.LevGFQT
