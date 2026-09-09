import InfoGeometry.Algebra.OperatorSymbolCore
import InfoGeometry.Bridge.QuaternionicPauliDiracSoldering

/-! Canonical readback of the concrete Pauli--Dirac bridge through the
dimension-free off-diagonal operator owner. -/

noncomputable section

namespace InfoGeometry.Bridge.QuaternionicPauliDiracCanonicalReadback

open Matrix
open scoped Matrix
open InfoGeometry.Algebra.OperatorSymbolCore
open InfoGeometry.Bridge.QuaternionicPauliDiracSoldering

theorem chiralWeylOperator_eq_offDiagonalEnd (A B : PauliBlock) :
    chiralWeylOperator A B =
      offDiagonalEnd A.mulVecLin B.mulVecLin := by
  apply LinearMap.ext
  rintro ⟨ψL, ψR⟩
  rfl

theorem chiralWeylOperator_sq_from_symbol_core
    (A B : PauliBlock) (ψ : DiracSpinor) :
    chiralWeylOperator A B (chiralWeylOperator A B ψ) =
      ((A * B) *ᵥ ψ.1, (B * A) *ᵥ ψ.2) := by
  rw [chiralWeylOperator_eq_offDiagonalEnd, offDiagonalEnd_sq_apply]
  rcases ψ with ⟨ψL, ψR⟩
  simp [Matrix.mulVecLin, Matrix.mulVec_mulVec]

theorem soldered_symbol_square_from_core
    (P : InfoGeometry.Canonical.PauliHestenesSpinMomentum.PauliParavector)
    (ψ : DiracSpinor) :
    chiralWeylOperator P.pauliMatrix (coSolderingMap P)
        (chiralWeylOperator P.pauliMatrix (coSolderingMap P) ψ) =
      (P.minkowskiNormSq : ℂ) • ψ := by
  exact soldered_chiralWeylOperator_sq_apply P ψ

end InfoGeometry.Bridge.QuaternionicPauliDiracCanonicalReadback
