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

namespace ChiralRepresentationPair

variable (R : ChiralRepresentationPair (G := G) (A := A))

/-- Opposite intertwiners for the two sheet representations. -/
structure ChiralIntertwiner where
  plus : A
  minus : A
  plus_intertwines : ∀ g : G,
    (R.left g : A) * plus = plus * (R.right g : A)
  minus_intertwines : ∀ g : G,
    (R.right g : A) * minus = minus * (R.left g : A)

/-- The pair of intertwiners in the two off-diagonal channels. -/
def pureChiralBlock (Q : R.ChiralIntertwiner) : ZornBlock A :=
  ⟨0, 0, Q.plus, Q.minus⟩

/-- The block action fixes a pure chiral block when its two entries intertwine
the corresponding left and right representations. -/
theorem blockAction_pureChiralBlock (g : G) (Q : R.ChiralIntertwiner) :
    blockAction R g (R.pureChiralBlock Q) = R.pureChiralBlock Q := by
  apply zornBlock_ext
  · simp [blockAction, pureChiralBlock]
  · simp [blockAction, pureChiralBlock]
  · calc
      (R.left g : A) * Q.plus * ((R.right g)⁻¹ : Units A) =
          (Q.plus * (R.right g : A)) * ((R.right g)⁻¹ : Units A) := by
            rw [Q.plus_intertwines]
      _ = Q.plus := by rw [mul_assoc, Units.mul_inv, mul_one]
  · calc
      (R.right g : A) * Q.minus * ((R.left g)⁻¹ : Units A) =
          (Q.minus * (R.left g : A)) * ((R.left g)⁻¹ : Units A) := by
            rw [Q.minus_intertwines]
      _ = Q.minus := by rw [mul_assoc, Units.mul_inv, mul_one]

end ChiralRepresentationPair

theorem blockAction_ePlus (R : ChiralRepresentationPair (G := G) (A := A))
    (g : G) : blockAction R g ePlus = ePlus := by
  apply zornBlock_ext <;> simp [blockAction, ePlus]

theorem blockAction_eMinus (R : ChiralRepresentationPair (G := G) (A := A))
    (g : G) : blockAction R g eMinus = eMinus := by
  apply zornBlock_ext <;> simp [blockAction, eMinus]

end InfoGeometry.OperatorAlgebra.ChiralWeylOperatorZornRepresentation

end
