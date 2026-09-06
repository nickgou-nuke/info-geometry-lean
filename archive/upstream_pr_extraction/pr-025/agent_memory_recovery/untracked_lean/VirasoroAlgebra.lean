import Mathlib

universe u

variable (K : Type u) [Field K] [CharZero K]

/-- The basis of the Virasoro algebra generators. -/
inductive VirasoroBasis
  | L (n : ℤ) : VirasoroBasis
  | c : VirasoroBasis
  deriving DecidableEq, Repr

/-- The Virasoro algebra over a field K of characteristic zero. -/
abbrev Virasoro := VirasoroBasis →₀ K

/-- The Lie bracket on the basis elements of the Virasoro algebra. -/
noncomputable def basisBracket (x y : VirasoroBasis) : Virasoro K :=
  match x, y with
  | VirasoroBasis.c, _ => 0
  | _, VirasoroBasis.c => 0
  | VirasoroBasis.L m, VirasoroBasis.L n =>
    let term1 := Finsupp.single (VirasoroBasis.L (m + n)) ((m - n : ℤ) : K)
    let term2 := if m + n = 0 then
                   Finsupp.single VirasoroBasis.c (((m^3 - m : ℤ) : K) / (12 : K))
                 else 0
    term1 + term2

noncomputable instance : Bracket (Virasoro K) (Virasoro K) where
  bracket x y := x.sum fun bx cx => y.sum fun by_ cy => (cx * cy) • basisBracket K bx by_

noncomputable instance : LieRing (Virasoro K) where
  add_lie := sorry
  lie_add := sorry
  lie_self := sorry
  leibniz_lie := sorry

noncomputable instance : LieAlgebra K (Virasoro K) where
  lie_smul := sorry
