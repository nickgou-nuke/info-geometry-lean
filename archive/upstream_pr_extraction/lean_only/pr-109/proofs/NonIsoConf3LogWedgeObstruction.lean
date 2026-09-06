import proofs.NonIsoConf3DeRhamCooperad

/-!
# Logarithmic wedge obstruction for the naive quadric Arnold relation

For hyperplane arrangements, the Arnold relation is an identity of logarithmic
forms.  For the three light-cone quadric divisors in `D=4`, the analogous
`dlog(q)` two-form relation is not an identity.

This file records a concrete integer evaluation: the common-denominator numerator
of

`dlog(q12)∧dlog(q23) - dlog(q12)∧dlog(q13) + dlog(q23)∧dlog(q13)`

has nonzero `dx0∧dy0` coefficient.
-/

namespace NonIsoConf3LogWedgeObstruction

/-- Four-dimensional integer vector used for the concrete evaluation. -/
structure Vec4 where
  t : ℤ
  x : ℤ
  y : ℤ
  z : ℤ
  deriving DecidableEq, Repr

/-- Minkowski-style split quadric over the integers. -/
def q4 (v : Vec4) : ℤ := v.t ^ 2 - v.x ^ 2 - v.y ^ 2 - v.z ^ 2

def sub (a b : Vec4) : Vec4 where
  t := a.t - b.t
  x := a.x - b.x
  y := a.y - b.y
  z := a.z - b.z

/-- Signature sign for coordinate `0,1,2,3`. -/
def sig : Fin 4 → ℤ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => -1
  | ⟨2, _⟩ => -1
  | ⟨3, _⟩ => -1

def coord (v : Vec4) : Fin 4 → ℤ
  | ⟨0, _⟩ => v.t
  | ⟨1, _⟩ => v.x
  | ⟨2, _⟩ => v.y
  | ⟨3, _⟩ => v.z

/-- Derivative of `q(a-b)` in coordinate `mu` of the first variable. -/
def gradFirst (a b : Vec4) (mu : Fin 4) : ℤ :=
  2 * sig mu * (coord a mu - coord b mu)

/-- Derivative of `q(a-b)` in coordinate `mu` of the second variable. -/
def gradSecond (a b : Vec4) (mu : Fin 4) : ℤ :=
  - gradFirst a b mu

def wedgeCoeff (ui uj vi vj : ℤ) : ℤ := ui * vj - uj * vi

def pointX : Vec4 := ⟨1, 0, 0, 0⟩
def pointY : Vec4 := ⟨0, 2, 0, 0⟩
def pointZ : Vec4 := ⟨0, 0, 3, 0⟩

def q12Eval : ℤ := q4 (sub pointX pointY)
def q23Eval : ℤ := q4 (sub pointY pointZ)
def q13Eval : ℤ := q4 (sub pointX pointZ)

theorem point_triple_nonisotropic :
    q12Eval = -3 ∧ q23Eval = -13 ∧ q13Eval = -8 := by
  norm_num [q12Eval, q23Eval, q13Eval, q4, sub, pointX, pointY, pointZ]

/-- Common-denominator numerator coefficient of the naive Arnold dlog
expression in the `dx0∧dy0` component. -/
def arnoldDlogNumerator_dx0dy0 : ℤ :=
  let mu0 : Fin 4 := ⟨0, by decide⟩
  let dq12x0 := gradFirst pointX pointY mu0
  let dq12y0 := gradSecond pointX pointY mu0
  let dq23x0 := 0
  let dq23y0 := gradFirst pointY pointZ mu0
  let dq13x0 := gradFirst pointX pointZ mu0
  let dq13y0 := 0
  wedgeCoeff dq12x0 dq12y0 dq23x0 dq23y0 * q13Eval -
    wedgeCoeff dq12x0 dq12y0 dq13x0 dq13y0 * q23Eval +
    wedgeCoeff dq23x0 dq23y0 dq13x0 dq13y0 * q12Eval

/-- The naive quadratic Arnold relation for the logarithmic forms is not a
literal dlog identity. -/
theorem naive_dlog_arnold_relation_obstructed :
    arnoldDlogNumerator_dx0dy0 = 52 ∧ arnoldDlogNumerator_dx0dy0 ≠ 0 := by
  norm_num [arnoldDlogNumerator_dx0dy0, wedgeCoeff, gradFirst, gradSecond,
    sig, coord, q12Eval, q23Eval, q13Eval, q4, sub, pointX, pointY, pointZ]

end NonIsoConf3LogWedgeObstruction
