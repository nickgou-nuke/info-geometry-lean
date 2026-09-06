import Mathlib.Data.ZMod.Basic

/-! Shared coordinate carrier for the parabolic line constructions. -/

namespace InfoGeometry.Algebra.Zorn.G2ParabolicLineCarrier

abbrev OctImF2 := Fin 7 → ZMod 2

def splitQuad (x : OctImF2) : ZMod 2 :=
  x 0 * x 3 + x 1 * x 4 + x 2 * x 5 + (x 6)^2

def octCross (x y : OctImF2) : OctImF2 :=
  fun k => match k with
  | 0 => x 6 * y 0 + y 6 * x 0 + x 4 * y 5 + x 5 * y 4
  | 1 => x 6 * y 1 + y 6 * x 1 + x 5 * y 3 + x 3 * y 5
  | 2 => x 6 * y 2 + y 6 * x 2 + x 3 * y 4 + x 4 * y 3
  | 3 => x 6 * y 3 + y 6 * x 3 + x 1 * y 2 + x 2 * y 1
  | 4 => x 6 * y 4 + y 6 * x 4 + x 2 * y 0 + x 0 * y 2
  | 5 => x 6 * y 5 + y 6 * x 5 + x 0 * y 1 + x 1 * y 0
  | 6 => (x 0 * y 3 + x 1 * y 4 + x 2 * y 5) +
      (y 0 * x 3 + y 1 * x 4 + y 2 * x 5)

def canonicalBasePoint : OctImF2 := fun i => if i = 2 then 1 else 0

@[simp] theorem canonicalBasePoint_apply (i : Fin 7) :
    canonicalBasePoint i = if i = 2 then 1 else 0 := rfl

end InfoGeometry.Algebra.Zorn.G2ParabolicLineCarrier
