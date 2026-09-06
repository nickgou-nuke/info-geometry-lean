import InfoGeometry.Canonical.OneSheetChiralAlgebra
import InfoGeometry.Canonical.SplitOctonionJordanPairTKKInput

namespace InfoGeometry.Canonical.TwoSheetChiralTKKDerivations

open InfoGeometry.Canonical.SplitOctonionJordanPairTKKInput

abbrev Sheet := InfoGeometry.Canonical.SplitOctonionJordanPairTKKInput.Sheet
abbrev Carrier := InfoGeometry.Canonical.SplitOctonionJordanPairTKKInput.TwoSheet

theorem triple_add_right (x y u v : Carrier) :
    triple x y (u + v) = triple x y u + triple x y v := by
  apply Prod.ext
  · funext i
    simp [triple, chiralTriplePlus, chiralPairing, Fin.sum_univ_three]
    ring
  · funext i
    simp [triple, chiralTripleMinus, chiralPairing, Fin.sum_univ_three]
    ring

theorem triple_smul_right (c : ℝ) (x y z : Carrier) :
    triple x y (c • z) = c • triple x y z := by
  apply Prod.ext
  · funext i
    simp [triple, chiralTriplePlus, chiralPairing, Fin.sum_univ_three]
    ring
  · funext i
    simp [triple, chiralTripleMinus, chiralPairing, Fin.sum_univ_three]
    ring

def boxOperator (x y : Carrier) : Module.End ℝ Carrier where
  toFun z := triple x y z
  map_add' z w := triple_add_right x y z w
  map_smul' c z := triple_smul_right c x y z

@[simp] theorem boxOperator_apply (x y z : Carrier) :
    boxOperator x y z = triple x y z := rfl

def degreeZeroOperator (x y : Carrier) : Module.End ℝ Carrier :=
  boxOperator x y - boxOperator y x

@[simp] theorem degreeZeroOperator_apply (x y z : Carrier) :
    degreeZeroOperator x y z = triple x y z - triple y x z := rfl

theorem box_commutator_apply (u v x y z : Carrier) :
    (boxOperator u v * boxOperator x y -
      boxOperator x y * boxOperator u v) z =
      boxOperator (triple u v x) y z -
        boxOperator x (triple v u y) z := by
  change triple u v (triple x y z) - triple x y (triple u v z) =
    triple (triple u v x) y z - triple x (triple v u y) z
  exact triple_identity u v x y z

theorem degreeZeroOperator_commutator_apply (u v x y z : Carrier) :
    (boxOperator u v * boxOperator x y -
      boxOperator x y * boxOperator u v) z =
      boxOperator (triple u v x) y z -
        boxOperator x (triple v u y) z :=
  box_commutator_apply u v x y z

theorem oneSheet_inner_operator_readout
    (x y z : InfoGeometry.Canonical.OneSheetChiralAlgebra.Carrier) :
    InfoGeometry.Canonical.SplitOctonionJordanStructure.innerJordanDerivation x y z =
      InfoGeometry.Canonical.OneSheetChiralAlgebra.product x
          (InfoGeometry.Canonical.OneSheetChiralAlgebra.product y z) -
        InfoGeometry.Canonical.OneSheetChiralAlgebra.product y
          (InfoGeometry.Canonical.OneSheetChiralAlgebra.product x z) := by
  exact InfoGeometry.Canonical.OneSheetChiralAlgebra.inner_operator_readout x y z

end InfoGeometry.Canonical.TwoSheetChiralTKKDerivations
