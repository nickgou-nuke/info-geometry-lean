import InfoGeometry.Clifford.BottPeriodicity
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Cl55SpinorChirality
import InfoGeometry.Clifford.Cl55SpinBivectorImage

/-!
# `Cl(5,5)` polarization bridge

This packages the existing Bott stabilization and spinor chirality owners as
the strict Clifford endpoint of the finite polarization calculus.  It does not
promote a general operator-valued connection to a `Spin(5,5)` connection; that
requires a separate bivector-image hypothesis.
-/

noncomputable section

namespace InfoGeometry.Optics.Cl55PolarizationBridge

open scoped TensorProduct
open InfoGeometry.Clifford.BottPeriodicity
open InfoGeometry.Clifford.SpinorRep
open InfoGeometry.Clifford.Cl55SpinorChirality
open InfoGeometry.Clifford.Cl55SpinBivectorImage
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.CliffordTower

/-- The finite `Cl(5,5)` carrier data used by the polarization bridge. -/
structure Data where
  bottStep :
    SplitBottClifford 5 ≃ₐ[ℝ]
      (CliffordAlgebra.evenOdd CliffordTower.Q11 ᵍ⊗[ℝ]
        CliffordAlgebra.evenOdd (SplitBottQuad 4))
  chirality : SpinorMatrix 5
  chirality_sq : chirality * chirality = 1

/-- The canonical finite `Cl(5,5)` polarization data. -/
def canonical : Data where
  bottStep := cl55_as_splitBottStep
  chirality := chiralityMatrix
  chirality_sq := chiralityMatrix_sq

@[simp] theorem canonical_chirality_sq :
    (canonical.chirality : SpinorMatrix 5) * canonical.chirality = 1 :=
  canonical.chirality_sq

theorem canonical_bott_step_is_owner :
    canonical.bottStep = clsplit_succ_equiv 4 := by
  exact cl55_as_splitBottStep_eq_owner

theorem gammaBasis55_square (i : Fin 10) :
    gammaBasis55 i * gammaBasis55 i =
      (if i.val < 5 then (1 : ℝ) else -1) • (1 : SpinorMatrix 5) :=
  gammaBasis55_sq i

/-! ## Strict connection boundary -/

/--
A matrix coefficient together with the proof that it lies in the represented
`Spin(5,5)` Clifford-bivector Lie algebra.
-/
structure StrictSpinConnectionCoefficient where
  matrix : SpinorMatrix 5
  is_bivector_image : IsSpinConnectionCoefficient matrix

/-- Every native vector commutator gives a strict connection coefficient. -/
def commutatorConnectionCoefficient (u v : V55) :
    StrictSpinConnectionCoefficient where
  matrix := spinBivectorMatrixLinear (commutatorBivector u v)
  is_bivector_image := commutatorBivector_isSpinConnectionCoefficient u v

/-- Strict connection coefficients are closed under the gauge Lie bracket. -/
def bracketConnectionCoefficient
    (A B : StrictSpinConnectionCoefficient) :
    StrictSpinConnectionCoefficient where
  matrix := ⁅A.matrix, B.matrix⁆
  is_bivector_image :=
    lie_isSpinConnectionCoefficient A.is_bivector_image B.is_bivector_image

end InfoGeometry.Optics.Cl55PolarizationBridge
