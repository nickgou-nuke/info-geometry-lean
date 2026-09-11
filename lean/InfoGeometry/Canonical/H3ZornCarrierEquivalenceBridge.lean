import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.H3ZornAlgebraicSoldering
import InfoGeometry.Canonical.H3ZornAlgebraicSolderingTransport

noncomputable section

namespace InfoGeometry.Canonical.H3ZornCarrierEquivalenceBridge

open InfoGeometry.Algebra
open InfoGeometry.Canonical.H3ZornAlgebraicSoldering
open InfoGeometry.Canonical.H3ZornAlgebraicSolderingTransport


/-- The two maintained coordinate carriers are canonically identified by their
common native `H3Zorn` soldering.  This is a carrier equivalence only; no
Jordan-product compatibility is inferred from it. -/
noncomputable def h3CoordToRealAlbert :
    H3Coord ≃ₗ[ℝ] RealAlbertMatrix :=
  h3Soldering.trans
    InfoGeometry.Canonical.H3ZornAlgebraicSolderingTransport.h3Soldering.symm

@[simp] theorem h3CoordToRealAlbert_apply (X : H3Coord) :
    h3CoordToRealAlbert X =
      InfoGeometry.Canonical.H3ZornAlgebraicSolderingTransport.h3Soldering.symm
        (h3Soldering X) := by rfl

@[simp] theorem h3CoordToRealAlbert_symm_apply (X : RealAlbertMatrix) :
    h3CoordToRealAlbert.symm X =
      InfoGeometry.Canonical.H3ZornAlgebraicSoldering.h3Soldering.symm
        (InfoGeometry.Canonical.H3ZornAlgebraicSolderingTransport.h3Soldering X) := by rfl

theorem h3CoordToRealAlbert_left_inv (X : H3Coord) :
    h3CoordToRealAlbert.symm (h3CoordToRealAlbert X) = X := by
  exact h3CoordToRealAlbert.symm_apply_apply X

theorem h3CoordToRealAlbert_right_inv (X : RealAlbertMatrix) :
    h3CoordToRealAlbert (h3CoordToRealAlbert.symm X) = X := by
  exact h3CoordToRealAlbert.apply_symm_apply X

theorem h3CoordToRealAlbert_mul (X Y : H3Coord) :
    h3CoordToRealAlbert (coordJordanMul X Y) =
      RealAlbertMatrix.mul (h3CoordToRealAlbert X)
        (h3CoordToRealAlbert Y) := by
  apply InfoGeometry.Canonical.H3ZornAlgebraicSolderingTransport.h3Soldering.injective
  simp only [h3CoordToRealAlbert_apply,
    LinearEquiv.apply_symm_apply,
    InfoGeometry.Canonical.H3ZornAlgebraicSoldering.h3Soldering_jordan_intertwines,
    InfoGeometry.Canonical.H3ZornAlgebraicSolderingTransport.h3Soldering_jordan_intertwines]

end InfoGeometry.Canonical.H3ZornCarrierEquivalenceBridge
