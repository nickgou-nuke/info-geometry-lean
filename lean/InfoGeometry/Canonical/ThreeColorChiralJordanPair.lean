import InfoGeometry.Canonical.TKKJordanPairData
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.ConcreteComposition
import Mathlib.Tactic

/-!
# The rectangular three-colour Jordan pair

The upper and lower chiral slots are copies of `R^3`.  Their mixed Peirce
pairing is the dot product.  This file proves the corresponding Jordan-pair
identities and records the direct native Zorn multiplication readout.

No Lie algebra instance is installed on the nonassociative Zorn carrier.
The TKK externalisation is a separate owner.
-/

namespace InfoGeometry.Canonical

open scoped BigOperators
open InfoGeometry.Algebra.Zorn.ConcreteComposition
open InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell
open TKKJordanPairData

noncomputable section

variable {R : Type*} [CommRing R]

abbrev ChiralVector (R : Type*) := Fin 3 → R

def chiralPairing (x y : ChiralVector R) : R :=
  ∑ i : Fin 3, x i * y i

def chiralTriplePlus (x y z : ChiralVector R) : ChiralVector R :=
  (chiralPairing x y) • z + (chiralPairing z y) • x

def chiralTripleMinus (x y z : ChiralVector R) : ChiralVector R :=
  (chiralPairing y x) • z + (chiralPairing y z) • x

theorem chiralPairing_comm (x y : ChiralVector R) :
    chiralPairing x y = chiralPairing y x := by
  simp [chiralPairing, Fin.sum_univ_three, mul_comm]

theorem chiralTriplePlus_outer (x y z : ChiralVector R) :
    chiralTriplePlus x y z = chiralTriplePlus z y x := by
  ext i
  simp [chiralTriplePlus, add_comm]

theorem chiralTripleMinus_outer (x y z : ChiralVector R) :
    chiralTripleMinus x y z = chiralTripleMinus z y x := by
  ext i
  simp [chiralTripleMinus, chiralPairing_comm, add_comm]

set_option maxHeartbeats 1000000 in
theorem chiralTriplePlus_fundamental
    (x u w : ChiralVector R) (y v : ChiralVector R) :
    chiralTriplePlus x y (chiralTriplePlus u v w) -
        chiralTriplePlus u v (chiralTriplePlus x y w) =
      chiralTriplePlus (chiralTriplePlus x y u) v w -
        chiralTriplePlus u (chiralTripleMinus y x v) w := by
  ext i
  simp [chiralTriplePlus, chiralTripleMinus, chiralPairing,
    Fin.sum_univ_three]
  ring

set_option maxHeartbeats 1000000 in
theorem chiralTripleMinus_fundamental
    (x u w : ChiralVector R) (y v : ChiralVector R) :
    chiralTripleMinus x y (chiralTripleMinus u v w) -
        chiralTripleMinus u v (chiralTripleMinus x y w) =
      chiralTripleMinus (chiralTripleMinus x y u) v w -
        chiralTripleMinus u (chiralTriplePlus y x v) w := by
  ext i
  simp [chiralTriplePlus, chiralTripleMinus, chiralPairing,
    Fin.sum_univ_three]
  ring

/-- The concrete Jordan pair carried by the two chiral three-colour slots. -/
def chiralJordanPair : JordanPair R where
  Vplus := ChiralVector R
  Vminus := ChiralVector R
  triplePlus := chiralTriplePlus
  tripleMinus := chiralTripleMinus
  triplePlus_outer := chiralTriplePlus_outer
  tripleMinus_outer := chiralTripleMinus_outer
  triplePlus_fundamental := chiralTriplePlus_fundamental
  tripleMinus_fundamental := chiralTripleMinus_fundamental

namespace ChiralZornReadout

def plusCell (x : ChiralVector R) : ZornCell R where
  r := 0; s := 0
  x1 := x 0; x2 := x 1; x3 := x 2
  y1 := 0; y2 := 0; y3 := 0

def minusCell (y : ChiralVector R) : ZornCell R where
  r := 0; s := 0
  x1 := 0; x2 := 0; x3 := 0
  y1 := y 0; y2 := y 1; y3 := y 2

def e11 : ZornCell R where
  r := 1; s := 0
  x1 := 0; x2 := 0; x3 := 0
  y1 := 0; y2 := 0; y3 := 0

def e22 : ZornCell R where
  r := 0; s := 1
  x1 := 0; x2 := 0; x3 := 0
  y1 := 0; y2 := 0; y3 := 0

def smulCell (a : R) (X : ZornCell R) : ZornCell R where
  r := a * X.r; s := a * X.s
  x1 := a * X.x1; x2 := a * X.x2; x3 := a * X.x3
  y1 := a * X.y1; y2 := a * X.y2; y3 := a * X.y3

@[ext] theorem cell_ext {X Y : ZornCell R}
    (hr : X.r = Y.r) (hs : X.s = Y.s)
    (hx1 : X.x1 = Y.x1) (hx2 : X.x2 = Y.x2) (hx3 : X.x3 = Y.x3)
    (hy1 : X.y1 = Y.y1) (hy2 : X.y2 = Y.y2) (hy3 : X.y3 = Y.y3) :
    X = Y := by
  cases X
  cases Y
  simp_all

theorem plus_mul_minus (x y : ChiralVector R) :
    mulZ (plusCell x) (minusCell y) = smulCell (chiralPairing x y) e11 := by
  ext <;> simp [mulZ, plusCell, minusCell, smulCell, e11,
    chiralPairing, Fin.sum_univ_three]

theorem minus_mul_plus (x y : ChiralVector R) :
    mulZ (minusCell y) (plusCell x) = smulCell (chiralPairing x y) e22 := by
  ext <;> simp [mulZ, plusCell, minusCell, smulCell, e22,
    chiralPairing, Fin.sum_univ_three] <;> ring

theorem triplePlus_native_readout (x y z : ChiralVector R) :
    addZ
        (mulZ (mulZ (plusCell x) (minusCell y)) (plusCell z))
        (mulZ (mulZ (plusCell z) (minusCell y)) (plusCell x)) =
      plusCell (chiralTriplePlus x y z) := by
  ext <;> simp [mulZ, addZ, plusCell, minusCell, chiralTriplePlus,
    chiralPairing, Fin.sum_univ_three]

theorem tripleMinus_native_readout (x y z : ChiralVector R) :
    addZ
        (mulZ (mulZ (minusCell x) (plusCell y)) (minusCell z))
        (mulZ (mulZ (minusCell z) (plusCell y)) (minusCell x)) =
      minusCell (chiralTripleMinus x y z) := by
  ext <;> simp [mulZ, addZ, plusCell, minusCell, chiralTripleMinus,
    chiralPairing, Fin.sum_univ_three] <;> ring

end ChiralZornReadout

end
end InfoGeometry.Canonical
