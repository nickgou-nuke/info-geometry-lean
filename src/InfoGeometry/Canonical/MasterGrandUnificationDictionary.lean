import InfoGeometry.Modular.DeterminantTrifactorHomomorphism
import InfoGeometry.GrandUnification.PfaffianSquareRootCharacter

/-!
# A finite determinant–Pfaffian bridge

This owner records one exact relation among the existing carriers: for a
skew-symmetric two-dimensional block and an invertible second sector, the
fourth power of the signed Pfaffian equals the product determinant times the
determinant ratio. It does not bundle unrelated structures into a purported
universal geometric dictionary.
-/

namespace InfoGeometry.Canonical.MasterGrandUnification

open Matrix
open InfoGeometry.Modular.Triple
open InfoGeometry.Modular.DeterminantTrifactorHomomorphism
open InfoGeometry.GrandUnification.PfaffianSquareRootCharacter

/-- In dimension two, the Pfaffian square-root identity and sector determinant
cancellation combine into a fourth-power identity. -/
theorem pfaffian_fourth_eq_totalDet_mul_berezinian
    {F : Type*} [Field F]
    (A D : Matrix (Fin 2) (Fin 2) F)
    (hA : IsSkew2D A) (hD : Matrix.det D ≠ 0) :
    (pfaffian2D A) ^ 4 = totalDet A D * berezinian A D := by
  have hpf := det_eq_pfaffian_sq_of_isSkew2D A hA
  have hsector := totalDet_mul_berezinian_eq_det_sq A D hD
  calc
    (pfaffian2D A) ^ 4 = (Matrix.det A) ^ 2 := by rw [hpf]; ring
    _ = totalDet A D * berezinian A D := hsector.symm

end InfoGeometry.Canonical.MasterGrandUnification
