import InfoGeometry.Algebra.SplitCayleyF2AddMulAutomorphism
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.SplitCayleyF2CarrierAlignment
import InfoGeometry.Algebra.SplitCayleyF2MultiplicationTransport
import InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

namespace InfoGeometry.Algebra.SplitCayleyF2

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

noncomputable def AddMulAutomorphism.toSplitOctF2Equiv
    (φ : AddMulAutomorphism) : SplitOctF2 ≃ SplitOctF2 :=
  cayleySplitOctF2Equiv.symm.trans (φ.toEquiv.trans cayleySplitOctF2Equiv)

theorem AddMulAutomorphism.toSplitOctF2Equiv_one (φ : AddMulAutomorphism) :
    φ.toSplitOctF2Equiv
        InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.one =
          InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.one := by
  dsimp [AddMulAutomorphism.toSplitOctF2Equiv]
  have h1 : cayleySplitOctF2Equiv.symm InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.one = (one : Cayley) := by
    apply cayleySplitOctF2Equiv.injective
    rw [Equiv.apply_symm_apply, cayleySplitOctF2Equiv_one]
  rw [h1, φ.map_one, cayleySplitOctF2Equiv_one]

theorem AddMulAutomorphism.toSplitOctF2Equiv_add
    (φ : AddMulAutomorphism) (x y : SplitOctF2) :
    φ.toSplitOctF2Equiv
        (InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add x y) =
      InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add
        (φ.toSplitOctF2Equiv x)
        (φ.toSplitOctF2Equiv y) := by
  dsimp [AddMulAutomorphism.toSplitOctF2Equiv]
  have hadd : cayleySplitOctF2Equiv.symm (InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add x y) =
      add (cayleySplitOctF2Equiv.symm x) (cayleySplitOctF2Equiv.symm y) := by
    apply cayleySplitOctF2Equiv.injective
    rw [Equiv.apply_symm_apply]
    have h := (cayleySplitOctF2Equiv_add (cayleySplitOctF2Equiv.symm x) (cayleySplitOctF2Equiv.symm y)).symm
    change OperatorAlgebra.G2TwoAutomorphismTheorem.add
        (cayleySplitOctF2Equiv (cayleySplitOctF2Equiv.symm x))
        (cayleySplitOctF2Equiv (cayleySplitOctF2Equiv.symm y)) =
      cayleySplitOctF2Equiv (add (cayleySplitOctF2Equiv.symm x) (cayleySplitOctF2Equiv.symm y)) at h
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
    exact h
  rw [hadd, φ.map_add]
  exact cayleySplitOctF2Equiv_add (φ (cayleySplitOctF2Equiv.symm x)) (φ (cayleySplitOctF2Equiv.symm y))

theorem AddMulAutomorphism.toSplitOctF2Equiv_mul
    (φ : AddMulAutomorphism) (x y : SplitOctF2) :
    φ.toSplitOctF2Equiv
        (InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.mul x y) =
      InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.mul
        (φ.toSplitOctF2Equiv x)
        (φ.toSplitOctF2Equiv y) := by
  dsimp [AddMulAutomorphism.toSplitOctF2Equiv]
  have hmul : cayleySplitOctF2Equiv.symm (InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.mul x y) =
      (cayleySplitOctF2Equiv.symm x) * (cayleySplitOctF2Equiv.symm y) := by
    apply cayleySplitOctF2Equiv.injective
    rw [Equiv.apply_symm_apply]
    have h := (cayleySplitOctF2Equiv_mul (cayleySplitOctF2Equiv.symm x) (cayleySplitOctF2Equiv.symm y)).symm
    change OperatorAlgebra.G2TwoAutomorphismTheorem.mul
        (cayleySplitOctF2Equiv (cayleySplitOctF2Equiv.symm x))
        (cayleySplitOctF2Equiv (cayleySplitOctF2Equiv.symm y)) =
      cayleySplitOctF2Equiv (cayleySplitOctF2Equiv.symm x * cayleySplitOctF2Equiv.symm y) at h
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
    exact h
  rw [hmul, φ.map_mul]
  exact cayleySplitOctF2Equiv_mul (φ (cayleySplitOctF2Equiv.symm x)) (φ (cayleySplitOctF2Equiv.symm y))

noncomputable def AddMulAutomorphism.toSplitOctF2Aut
    (φ : AddMulAutomorphism) : SplitOctF2Aut :=
  ⟨φ.toSplitOctF2Equiv,
    ⟨φ.toSplitOctF2Equiv_one,
      φ.toSplitOctF2Equiv_add,
      φ.toSplitOctF2Equiv_mul⟩⟩

theorem AddMulAutomorphism.toSplitOctF2Equiv_cayley_readback
    (φ : AddMulAutomorphism) (x : SplitOctF2) :
    cayleySplitOctF2Equiv.symm (φ.toSplitOctF2Equiv x) =
      φ (cayleySplitOctF2Equiv.symm x) := by
  simp [AddMulAutomorphism.toSplitOctF2Equiv]

end InfoGeometry.Algebra.SplitCayleyF2
