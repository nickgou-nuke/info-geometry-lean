import InfoGeometry.OperatorAlgebra.TKKClosure
import InfoGeometry.Canonical.SplitOctonionJordanForm

namespace InfoGeometry.Canonical.SplitOctonionSpinJordanTriple

open InfoGeometry.Canonical.SplitOctonionJordanForm
open InfoGeometry.OperatorAlgebra

abbrev Carrier := MiddleCarrier

def triple (x y z : Carrier) : Carrier :=
  beta44 x y • z + beta44 z y • x - beta44 x z • y

@[simp] theorem triple_apply (x y z : Carrier) :
    triple x y z =
      beta44 x y • z + beta44 z y • x - beta44 x z • y := rfl

theorem triple_outer_symm (x y z : Carrier) :
    triple x y z = triple z y x := by
  rw [triple, triple, beta44_symmetric x z]
  module

theorem triple_add_left (u v x y : Carrier) :
    triple (u + v) x y = triple u x y + triple v x y := by
  simp only [triple, beta44_add_left, add_smul]
  module

theorem triple_smul_left (c : ℝ) (x y z : Carrier) :
    triple (c • x) y z = c • triple x y z := by
  simp only [triple, beta44_smul_left, smul_smul]
  module

theorem triple_identity (u v x y z : Carrier) :
    triple u v (triple x y z) - triple x y (triple u v z) =
      triple (triple u v x) y z - triple x (triple v u y) z := by
  simp only [triple, beta44_symmetric]
  simp [smul_eq_mul]
  module

noncomputable def jordanTripleSystem :
    JordanTripleSystem Carrier where
  triple := triple
  outer_symm := triple_outer_symm
  triple_add_left := triple_add_left
  triple_smul_left := triple_smul_left
  triple_identity := triple_identity

end InfoGeometry.Canonical.SplitOctonionSpinJordanTriple
