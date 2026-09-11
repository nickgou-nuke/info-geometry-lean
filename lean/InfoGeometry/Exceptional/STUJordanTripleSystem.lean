import InfoGeometry.Exceptional.STUDatum
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.JordanTripleTKK

/-!
# The concrete coordinatewise STU Jordan triple system

This is the finite Jordan-triple prerequisite for a later TKK/Freudenthal
construction.  It is deliberately not identified with the full split Albert
or with an exceptional Lie algebra.
-/

noncomputable section

namespace InfoGeometry.Exceptional.STUDatum

open InfoGeometry.Algebra.TKK

def stuTripleProduct (x y z : STUCarrier) : STUCarrier :=
  fun i => x i * y i * z i

noncomputable instance : JordanTripleSystem STUCarrier where
  tripleProduct := stuTripleProduct
  jordan_identity := by
    intro x y u v w
    funext i
    dsimp [stuTripleProduct]
    ring

@[simp] theorem stuTripleProduct_apply
    (x y z : STUCarrier) (i : Fin 3) :
    stuTripleProduct x y z i = x i * y i * z i := rfl

theorem stuJordan_identity
    (x y u v w : STUCarrier) :
    stuTripleProduct x y (stuTripleProduct u v w) -
        stuTripleProduct u v (stuTripleProduct x y w) =
      stuTripleProduct (stuTripleProduct x y u) v w -
        stuTripleProduct u (stuTripleProduct y x v) w := by
  exact JordanTripleSystem.jordan_identity x y u v w

end InfoGeometry.Exceptional.STUDatum
