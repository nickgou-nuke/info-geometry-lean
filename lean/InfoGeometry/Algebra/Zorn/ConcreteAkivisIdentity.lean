import InfoGeometry.Algebra.Zorn.AssociatorObstruction

/-!
# Akivis identity on arbitrary concrete Zorn cells

Contract: retain the integer ZornCell carrier, its multiplication, and the
right-nested commutator convention of AssociatorObstruction. The Jacobiator
equals the signed associator sum for every cell triple, not only basis inputs.
This does not install an associative or Lie product on the cells.
-/
namespace InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell.Basis8

theorem concrete_akivis_identity (X Y Z : ZornCell ℤ) :
    commutatorJacobiatorZ X Y Z = akivisRhsZ X Y Z := by
  have hm (a b : ZornCell ℤ) : a * b = mulZ a b := rfl
  simp only [commutatorJacobiatorZ, akivisRhsZ, commutatorZ, associatorZ,
    subZ, addZ, hm, mulZ]
  congr 1 <;> ring

theorem concrete_jacobi_iff_associator_sum_zero (X Y Z : ZornCell ℤ) :
    commutatorJacobiatorZ X Y Z = SignedBasis.cell SignedBasis.zero ↔
      akivisRhsZ X Y Z = SignedBasis.cell SignedBasis.zero := by
  rw [concrete_akivis_identity]

end InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell.Basis8
