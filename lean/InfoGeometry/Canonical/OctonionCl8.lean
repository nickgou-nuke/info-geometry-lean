import Mathlib.Tactic

namespace InfoGeometry.Canonical.OctonionCl8

/-- The 8 basis elements of the Octonion algebra (1 real, 7 imaginary) -/
inductive OctBasis
| e0 | e1 | e2 | e3 | e4 | e5 | e6 | e7
deriving DecidableEq, Repr, Fintype

open OctBasis

/-- The Fano plane multiplication table: e_i * e_j = c * e_k -/
def octMul (x y : OctBasis) : ℝ × OctBasis :=
  match x, y with
  | e0, b => (1, b)
  | a, e0 => (1, a)
  -- e1 lines
  | e1, e1 => (-1, e0)
  | e1, e2 => (1, e4)
  | e2, e1 => (-1, e4)
  | e1, e4 => (-1, e2)
  | e4, e1 => (1, e2)
  | e2, e4 => (1, e1)
  | e4, e2 => (-1, e1)
  -- e2 lines
  | e2, e2 => (-1, e0)
  | e2, e3 => (1, e5)
  | e3, e2 => (-1, e5)
  | e2, e5 => (-1, e3)
  | e5, e2 => (1, e3)
  | e3, e5 => (1, e2)
  | e5, e3 => (-1, e2)
  -- e3 lines
  | e3, e3 => (-1, e0)
  | e3, e4 => (1, e6)
  | e4, e3 => (-1, e6)
  | e3, e6 => (-1, e4)
  | e6, e3 => (1, e4)
  | e4, e6 => (1, e3)
  | e6, e4 => (-1, e3)
  -- e4 lines
  | e4, e4 => (-1, e0)
  | e4, e5 => (1, e7)
  | e5, e4 => (-1, e7)
  | e4, e7 => (-1, e5)
  | e7, e4 => (1, e5)
  | e5, e7 => (1, e4)
  | e7, e5 => (-1, e4)
  -- e5 lines
  | e5, e5 => (-1, e0)
  | e5, e6 => (1, e1)
  | e6, e5 => (-1, e1)
  | e5, e1 => (-1, e6)
  | e1, e5 => (1, e6)
  | e6, e1 => (1, e5)
  | e1, e6 => (-1, e5)
  -- e6 lines
  | e6, e6 => (-1, e0)
  | e6, e7 => (1, e2)
  | e7, e6 => (-1, e2)
  | e6, e2 => (-1, e7)
  | e2, e6 => (1, e7)
  | e7, e2 => (1, e6)
  | e2, e7 => (-1, e6)
  -- e7 lines
  | e7, e7 => (-1, e0)
  | e7, e1 => (1, e3)
  | e1, e7 => (-1, e3)
  | e7, e3 => (-1, e1)
  | e3, e7 => (1, e1)
  | e1, e3 => (1, e7)
  | e3, e1 => (-1, e7)

/-- The Octonion algebra as an 8-dimensional real vector space -/
abbrev Octonion := OctBasis → ℝ

/-- Left multiplication operator by a basis element -/
def L (a : OctBasis) (x : Octonion) : Octonion :=
  fun k => ∑ j : OctBasis,
    let (c, res) := octMul a j
    if res = k then c * x j else 0

/-- Standard Euclidean inner product on the octonions -/
def dot (x y : Octonion) : ℝ :=
  ∑ j : OctBasis, x j * y j

/--
The 16-dimensional real space carrying the Cl(0,8) representation: O ⊕ O
-/
abbrev Spinor16 := Octonion × Octonion

/--
The 8 generators of Cl(0,8) acting on O ⊕ O (the 16D spinor space).
E_i = [0, L_i; L_i, 0] for i = 1..7
E_8 = [0, I; -I, 0]
-/
def E (i : OctBasis) (s : Spinor16) : Spinor16 :=
  match i with
  | e0 => (s.2, fun j => -s.1 j)               -- E_8 generator (using e0 as the index for the 8th generator)
  | a  => (L a s.2, L a s.1)                   -- E_1 ... E_7 generators

end InfoGeometry.Canonical.OctonionCl8
