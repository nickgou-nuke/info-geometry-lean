import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Module.Basic
import InfoGeometry.Canonical.ZornSpinor
import InfoGeometry.Algebra.ZornAlternativeLaws
import InfoGeometry.Canonical.CliffordDiracAlgebra

namespace InfoGeometry.Canonical.OctonionicDiracEquivalence

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornVectorMatrix

noncomputable section

/-!
# Octonionic Dirac Equation Equivalence

This file formalizes the equivalence between different split-octonionic Dirac
equation representations, as outlined in Köplinger (2026): "The Dirac equation in 
(split-)octonions: origins, variants, and modern context".

Specifically, it addresses the reduction of the 2024 representation (Gogberashvili-Gurchumelia)
to the 2006 2-factor representation (Köplinger) via the nonassociative group conjugation 
`w ↦ (J_3 w) J_3`. We integrate this with the existing `ZornVectorMatrix` middle Moufang identity.
-/

variable {R : Type*} [CommRing R]

/-- The four historical approaches to the octonionic Dirac equation. -/
inductive OctonionicDiracRepresentation
  | TwoFactor
  | ThreeFactor
  | Projection
  | Conventional

/-- A structure-preserving rotation using a basis element `J_3` with `J_3^2 = 1`. -/
def diracRotation (J3 w : ZornVectorMatrix R) : ZornVectorMatrix R :=
  J3 * (w * J3)

/-- The 2024 Dirac operator acts on the left. -/
def diracOp2024 (D J3 m ψ : ZornVectorMatrix R) : ZornVectorMatrix R :=
  (D - J3 * m) * ψ

/-- The 2006 Dirac operator is a pure 2-factor product. -/
def diracOp2006 (Dprime m ψprime : ZornVectorMatrix R) : ZornVectorMatrix R :=
  (Dprime - m) * ψprime

/-- The rotation of the 2024 Dirac system yields the 2006 2-factor system. -/
theorem rotation_equivalence
    (D J3 m ψ : ZornVectorMatrix R)
    (hJ3 : J3 * J3 = ZornVectorMatrix.one)
    (h_assoc : J3 * (J3 * m) = (J3 * J3) * m) :
    diracRotation J3 (diracOp2024 D J3 m ψ) = 
      diracOp2006 (J3 * D) m (ψ * J3) := by
  dsimp [diracRotation, diracOp2024, diracOp2006]
  -- Applying middle Moufang identity with X = J3, Y = D - J3 * m, Z = ψ.
  have h_mouf : J3 * (((D - J3 * m) * ψ) * J3) =
      (J3 * (D - J3 * m)) * (ψ * J3) := by
    have hm := middle_moufang J3 (D - J3 * m) ψ
    exact hm.symm
  calc
    J3 * (((D - J3 * m) * ψ) * J3) =
        (J3 * (D - J3 * m)) * (ψ * J3) := h_mouf
    _ = (J3 * D - m) * (ψ * J3) := by
      congr 1
      rw [_root_.mul_sub, h_assoc, hJ3]
      have hone : ZornVectorMatrix.one * m = m := by
        simpa only [zvm_mul_def] using ZornVectorMatrix.one_mul m
      rw [hone]

end

end InfoGeometry.Canonical.OctonionicDiracEquivalence
