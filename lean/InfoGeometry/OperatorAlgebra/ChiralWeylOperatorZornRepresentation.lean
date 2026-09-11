import InfoGeometry.OperatorAlgebra.AssociativeOperatorZornCartanPeirce
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-! A carrier-correct chiral action on the associative block algebra.  The
left and right factors are arbitrary unit-valued group representations; no
Lorentz or `SL(2,C)` interpretation is built in. -/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ChiralWeylOperatorZornRepresentation

open InfoGeometry.Physics
open InfoGeometry.Physics.OperatorZornMatrix
open InfoGeometry.OperatorAlgebra.AssociativeOperatorZornCartanPeirce

variable {G A : Type*} [Group G] [Ring A] [StarRing A]

structure ChiralRepresentationPair where
  left : G →* Units A
  right : G →* Units A

def blockAction (R : ChiralRepresentationPair (G := G) (A := A))
    (g : G) (X : ZornBlock A) : ZornBlock A :=
  ⟨(R.left g : A) * X.n_plus_op * ((R.left g)⁻¹ : Units A),
    (R.right g : A) * X.n_minus_op * ((R.right g)⁻¹ : Units A),
    (R.left g : A) * X.sigma_plus_op * ((R.right g)⁻¹ : Units A),
    (R.right g : A) * X.sigma_minus_op * ((R.left g)⁻¹ : Units A)⟩

theorem blockAction_comp (R : ChiralRepresentationPair (G := G) (A := A))
    (g h : G) (X : ZornBlock A) :
    blockAction R (g * h) X = blockAction R g (blockAction R h X) := by
  apply zornBlock_ext <;>
    simp [blockAction, map_mul, mul_assoc]

theorem blockAction_ePlus (R : ChiralRepresentationPair (G := G) (A := A))
    (g : G) : blockAction R g ePlus = ePlus := by
  apply zornBlock_ext <;> simp [blockAction, ePlus]

theorem blockAction_eMinus (R : ChiralRepresentationPair (G := G) (A := A))
    (g : G) : blockAction R g eMinus = eMinus := by
  apply zornBlock_ext <;> simp [blockAction, eMinus]

end InfoGeometry.OperatorAlgebra.ChiralWeylOperatorZornRepresentation

end
