import InfoGeometry.OperatorAlgebra.PeirceSpine.Supercharge

/-!
# Two commuting involutive automorphisms on the unit-square level set

When `V=1`, conjugation by `Phi` is an actual ring equivalence. It commutes
with the existing parity equivalence. These relations permit an action of
the Klein four-group; they do not assert faithfulness or a Galois extension.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- Conjugation by a square-one element, with no commutativity assumption. -/
def squareOneConj (s : B) (hs : s * s = 1) : B ≃+* B where
  toFun x := s * x * s
  invFun x := s * x * s
  left_inv x := by
    calc
      s * (s * x * s) * s = (s * s) * x * (s * s) := by simp only [mul_assoc]
      _ = x := by rw [hs]; simp
  right_inv x := by
    calc
      s * (s * x * s) * s = (s * s) * x * (s * s) := by simp only [mul_assoc]
      _ = x := by rw [hs]; simp
  map_mul' x y := by
    symm
    calc
      (s * x * s) * (s * y * s) = s * x * (s * s) * y * s := by
        simp only [mul_assoc]
      _ = s * (x * y) * s := by rw [hs]; simp only [mul_one, mul_assoc]
  map_add' x y := by simp only [mul_add, add_mul]

variable {P : B} (hP : P * P = P) (A C : B)

/-- The additional hypothesis makes `Phi` a square-one unit. -/
def phiUnitSquareEquiv (hV : genV P A C = 1) : B ≃+* B :=
  squareOneConj (genPhi P A C) (by
    calc
      genPhi P A C * genPhi P A C = genV P A C := by peirce_nf hP
      _ = 1 := hV)

theorem phiUnitSquareEquiv_involutive (hV : genV P A C = 1) :
    Function.Involutive (phiUnitSquareEquiv hP A C hV) :=
  (phiUnitSquareEquiv hP A C hV).left_inv

/-- The two actual automorphisms commute on every ambient ring element. -/
theorem phiUnitSquareEquiv_commutes_parity (hV : genV P A C = 1) (X : B) :
    phiUnitSquareEquiv hP A C hV (parityConjRingEquiv hP X) =
      parityConjRingEquiv hP (phiUnitSquareEquiv hP A C hV X) := by
  change genPhi P A C * parityConj P X * genPhi P A C =
    parityConj P (genPhi P A C * X * genPhi P A C)
  simp only [parityConj]
  peirce_nf hP

end InfoGeometry.OperatorAlgebra.PeirceSpine
