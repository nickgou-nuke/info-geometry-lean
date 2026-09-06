import InfoGeometry.Algebra.Zorn.ThreeColorNativeBracketTable
import InfoGeometry.Algebra.Zorn.SplitCayleyStabilizer

/-!
# Derived chiral Lie-superbracket on the complete Zorn basis

The native Zorn multiplication is nonassociative and carries the colour
grading of the upper/lower slots.  This file defines a different operation:
the ordinary commutator on diagonal/off-diagonal mixed sectors and the
anticommutator on two off-diagonal sectors.  The resulting bracket is checked
directly on the complete eight-element basis; no associativity of the native
product is assumed.
-/

namespace InfoGeometry.Canonical

open InfoGeometry.Algebra.Zorn.ConcreteComposition
open InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell

@[ext] theorem zornCell_ext {R : Type*} [CommRing R]
    {X Y : ZornCell R}
    (hr : X.r = Y.r) (hs : X.s = Y.s)
    (hx1 : X.x1 = Y.x1) (hx2 : X.x2 = Y.x2) (hx3 : X.x3 = Y.x3)
    (hy1 : X.y1 = Y.y1) (hy2 : X.y2 = Y.y2) (hy3 : X.y3 = Y.y3) :
    X = Y := by
  cases X
  cases Y
  simp_all
open InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell.Basis8

abbrev ChiralZornCell := ZornCell ℤ

inductive ChiralParity where
  | even
  | odd
  deriving DecidableEq, Repr

inductive ChiralBasisElement where
  | unit
  | cartan
  | p0 | p1 | p2
  | q0 | q1 | q2
  deriving DecidableEq, Repr

def chiralParity : ChiralBasisElement → ChiralParity
  | .unit => .even
  | .cartan => .even
  | .p0 | .p1 | .p2 => .odd
  | .q0 | .q1 | .q2 => .odd

def chiralP (i : Fin 3) : ChiralBasisElement :=
  match i with
  | 0 => .p0
  | 1 => .p1
  | 2 => .p2

def chiralQ (i : Fin 3) : ChiralBasisElement :=
  match i with
  | 0 => .q0
  | 1 => .q1
  | 2 => .q2

def chiralCell : ChiralBasisElement → ChiralZornCell
  | .unit => addCell (cell e11) (cell e22)
  | .cartan => subCell (cell e11) (cell e22)
  | .p0 => cell u1
  | .p1 => cell u2
  | .p2 => cell u3
  | .q0 => cell v1
  | .q1 => cell v2
  | .q2 => cell v3

def chiralDiagonalPart (X : ChiralZornCell) : ChiralZornCell :=
  ⟨X.r, X.s, 0, 0, 0, 0, 0, 0⟩

def chiralOffDiagonalPart (X : ChiralZornCell) : ChiralZornCell :=
  ⟨0, 0, X.x1, X.x2, X.x3, X.y1, X.y2, X.y3⟩

def nativeChiralSuperBracket
    (X Y : ChiralZornCell) : ChiralZornCell :=
  addCell
    (addCell
      (addCell
        (commutator (chiralDiagonalPart X) (chiralDiagonalPart Y))
        (commutator (chiralDiagonalPart X) (chiralOffDiagonalPart Y)))
      (commutator (chiralOffDiagonalPart X) (chiralDiagonalPart Y)))
    (anticommutator (chiralOffDiagonalPart X) (chiralOffDiagonalPart Y))

def twiceCell (X : ChiralZornCell) : ChiralZornCell :=
  addCell X X

theorem superBracket_I (x : ChiralBasisElement) :
    nativeChiralSuperBracket (chiralCell .unit) (chiralCell x) = zeroCell := by
  cases x <;> decide

theorem superBracket_H_p (i : Fin 3) :
    nativeChiralSuperBracket (chiralCell .cartan) (chiralCell (chiralP i)) =
      twiceCell (chiralCell (chiralP i)) := by
  fin_cases i <;> decide

theorem superBracket_H_q (i : Fin 3) :
    nativeChiralSuperBracket (chiralCell .cartan) (chiralCell (chiralQ i)) =
      negCell (twiceCell (chiralCell (chiralQ i))) := by
  fin_cases i <;> decide

theorem superBracket_p_p (i j : Fin 3) :
    nativeChiralSuperBracket (chiralCell (chiralP i))
      (chiralCell (chiralP j)) = zeroCell := by
  fin_cases i <;> fin_cases j <;> decide

theorem superBracket_q_q (i j : Fin 3) :
    nativeChiralSuperBracket (chiralCell (chiralQ i))
      (chiralCell (chiralQ j)) = zeroCell := by
  fin_cases i <;> fin_cases j <;> decide

theorem superBracket_p_q (i j : Fin 3) :
    nativeChiralSuperBracket (chiralCell (chiralP i))
      (chiralCell (chiralQ j)) =
        if i = j then chiralCell .unit else zeroCell := by
  fin_cases i <;> fin_cases j <;> decide

def negativeIf (h : Prop) [Decidable h] (X : ChiralZornCell) : ChiralZornCell :=
  if h then negCell X else X

def gradedSkewRhs (x y : ChiralBasisElement) : ChiralZornCell :=
  if chiralParity x = .odd ∧ chiralParity y = .odd then
    nativeChiralSuperBracket (chiralCell y) (chiralCell x)
  else
    negCell (nativeChiralSuperBracket (chiralCell y) (chiralCell x))

theorem nativeChiralSuperBracket_graded_skew
    (x y : ChiralBasisElement) :
    nativeChiralSuperBracket (chiralCell x) (chiralCell y) =
      gradedSkewRhs x y := by
  cases x <;> cases y <;> decide

def gradedJacobiator
    (x y z : ChiralBasisElement) : ChiralZornCell :=
  let a := negativeIf (chiralParity x = .odd ∧ chiralParity z = .odd)
    (nativeChiralSuperBracket (chiralCell x)
      (nativeChiralSuperBracket (chiralCell y) (chiralCell z)))
  let b := negativeIf (chiralParity y = .odd ∧ chiralParity x = .odd)
    (nativeChiralSuperBracket (chiralCell y)
      (nativeChiralSuperBracket (chiralCell z) (chiralCell x)))
  let c := negativeIf (chiralParity z = .odd ∧ chiralParity y = .odd)
    (nativeChiralSuperBracket (chiralCell z)
      (nativeChiralSuperBracket (chiralCell x) (chiralCell y)))
  addCell (addCell a b) c

theorem nativeChiralSuperBracket_graded_jacobi
    (x y z : ChiralBasisElement) :
    gradedJacobiator x y z = zeroCell := by
  cases x <;> cases y <;> cases z <;> native_decide

/-! ## Channelwise coefficient carrier

The following carrier is the reusable `2 | 6` coefficient model.  Its four
Jacobi channels are proved directly, independently of native associativity.
-/

abbrev ChiralEven (R : Type*) := R × R
abbrev ChiralOddPlus (R : Type*) := Fin 3 → R
abbrev ChiralOddMinus (R : Type*) := Fin 3 → R
abbrev ChiralOdd (R : Type*) := ChiralOddPlus R × ChiralOddMinus R

def bracketEvenEven {R : Type*} [CommRing R]
    (_ _ : ChiralEven R) : ChiralEven R := 0

def bracketEvenOdd {R : Type*} [CommRing R]
    (e : ChiralEven R) (x : ChiralOdd R) : ChiralOdd R :=
  (fun i => 2 * e.2 * x.1 i, fun i => -2 * e.2 * x.2 i)

def bracketOddEven {R : Type*} [CommRing R]
    (x : ChiralOdd R) (e : ChiralEven R) : ChiralOdd R :=
  (- (bracketEvenOdd e x).1, - (bracketEvenOdd e x).2)

def oddPairing {R : Type*} [CommRing R]
    (x y : ChiralOdd R) : R :=
  (∑ i : Fin 3, x.1 i * y.2 i) +
    (∑ i : Fin 3, y.1 i * x.2 i)

def bracketOddOdd {R : Type*} [CommRing R]
    (x y : ChiralOdd R) : ChiralEven R :=
  (oddPairing x y, 0)

theorem oddPairing_symm {R : Type*} [CommRing R]
    (x y : ChiralOdd R) : oddPairing x y = oddPairing y x := by
  simp [oddPairing, Fin.sum_univ_three, add_comm, mul_comm]

theorem bracketEvenEven_skew {R : Type*} [CommRing R]
    (x y : ChiralEven R) :
    bracketEvenEven x y = - bracketEvenEven y x := by
  simp [bracketEvenEven]

theorem bracketOddOdd_symm {R : Type*} [CommRing R]
    (x y : ChiralOdd R) : bracketOddOdd x y = bracketOddOdd y x := by
  simp [bracketOddOdd, oddPairing_symm]

theorem bracketEvenOdd_neg {R : Type*} [CommRing R]
    (e : ChiralEven R) (x : ChiralOdd R) :
    bracketEvenOdd e x = - bracketOddEven x e := by
  ext <;> simp [bracketEvenOdd, bracketOddEven]

theorem jacobi_even_even_even {R : Type*} [CommRing R]
    (x y z : ChiralEven R) :
    bracketEvenEven x (bracketEvenEven y z) +
      bracketEvenEven y (bracketEvenEven z x) +
      bracketEvenEven z (bracketEvenEven x y) = 0 := by
  simp [bracketEvenEven]

theorem jacobi_even_even_odd {R : Type*} [CommRing R]
    (x y : ChiralEven R) (z : ChiralOdd R) :
    bracketEvenOdd x (bracketEvenOdd y z) -
      bracketEvenOdd y (bracketEvenOdd x z) =
      bracketOddEven z (bracketEvenEven x y) := by
  ext <;> simp [bracketEvenOdd, bracketOddEven, bracketEvenEven] <;> ring

theorem jacobi_even_odd_odd {R : Type*} [CommRing R]
    (e : ChiralEven R) (x y : ChiralOdd R) :
    bracketEvenEven e (bracketOddOdd x y) =
      bracketOddOdd (bracketEvenOdd e x) y +
        bracketOddOdd x (bracketEvenOdd e y) := by
  ext <;> simp [bracketEvenEven, bracketOddOdd, oddPairing,
    bracketEvenOdd, Fin.sum_univ_three] <;> ring

theorem jacobi_odd_odd_odd {R : Type*} [CommRing R]
    (x y z : ChiralOdd R) :
    bracketEvenOdd (bracketOddOdd y z) x +
      bracketEvenOdd (bracketOddOdd z x) y +
      bracketEvenOdd (bracketOddOdd x y) z = 0 := by
  ext <;> simp [bracketEvenOdd, bracketOddOdd, oddPairing,
    Fin.sum_univ_three] <;> ring

/-! ## Linear realization in the native Zorn carrier -/

open InfoGeometry.Algebra.Zorn.ConcreteComposition
open InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell

def evenToZorn {R : Type*} [CommRing R]
    (e : ChiralEven R) : ZornCell R where
  r := e.1 + e.2
  s := e.1 - e.2
  x1 := 0; x2 := 0; x3 := 0
  y1 := 0; y2 := 0; y3 := 0

def oddToZorn {R : Type*} [CommRing R]
    (x : ChiralOdd R) : ZornCell R where
  r := 0; s := 0
  x1 := x.1 0; x2 := x.1 1; x3 := x.1 2
  y1 := x.2 0; y2 := x.2 1; y3 := x.2 2

/-! The coordinate operations below deliberately avoid unfolding the
transferred additive structure on `ZornCell`.  This keeps the comparison
theorems about the native multiplication independent of implementation
details of the transported `AddCommGroup` instance. -/

def addCellR {R : Type*} [CommRing R]
    (X Y : ZornCell R) : ZornCell R where
  r := X.r + Y.r; s := X.s + Y.s
  x1 := X.x1 + Y.x1; x2 := X.x2 + Y.x2; x3 := X.x3 + Y.x3
  y1 := X.y1 + Y.y1; y2 := X.y2 + Y.y2; y3 := X.y3 + Y.y3

def negCellR {R : Type*} [CommRing R] (X : ZornCell R) : ZornCell R where
  r := -X.r; s := -X.s
  x1 := -X.x1; x2 := -X.x2; x3 := -X.x3
  y1 := -X.y1; y2 := -X.y2; y3 := -X.y3

def subCellR {R : Type*} [CommRing R]
    (X Y : ZornCell R) : ZornCell R := addCellR X (negCellR Y)

def nativeCommutatorR {R : Type*} [CommRing R]
    (x y : ZornCell R) : ZornCell R :=
  subCellR (ZornCell.mulZ x y) (ZornCell.mulZ y x)

def nativeAnticommutatorR {R : Type*} [CommRing R]
    (x y : ZornCell R) : ZornCell R :=
  addCellR (ZornCell.mulZ x y) (ZornCell.mulZ y x)

theorem evenEven_native_realization {R : Type*} [CommRing R]
    (x y : ChiralEven R) :
    nativeCommutatorR (evenToZorn x) (evenToZorn y) =
      evenToZorn (bracketEvenEven x y) := by
  ext <;> simp [nativeCommutatorR, subCellR, addCellR, negCellR,
    evenToZorn, ZornCell.mulZ, bracketEvenEven] <;> ring

theorem evenOdd_native_realization {R : Type*} [CommRing R]
    (e : ChiralEven R) (x : ChiralOdd R) :
    nativeCommutatorR (evenToZorn e) (oddToZorn x) =
      oddToZorn (bracketEvenOdd e x) := by
  ext <;> simp [nativeCommutatorR, subCellR, addCellR, negCellR,
    evenToZorn, oddToZorn, ZornCell.mulZ,
    bracketEvenOdd] <;> ring

theorem oddOdd_native_realization {R : Type*} [CommRing R]
    (x y : ChiralOdd R) :
    nativeAnticommutatorR (oddToZorn x) (oddToZorn y) =
      evenToZorn (bracketOddOdd x y) := by
  ext <;> simp [nativeAnticommutatorR, addCellR,
    evenToZorn, oddToZorn, ZornCell.mulZ,
    bracketOddOdd, oddPairing, Fin.sum_univ_three] <;> ring

end InfoGeometry.Canonical
