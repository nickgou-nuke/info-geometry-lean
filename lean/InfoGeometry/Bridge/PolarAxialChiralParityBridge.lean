import Mathlib.Tactic
import InfoGeometry.Bridge.QuaternionicPauliDiracSoldering

/-! Finite parity bridge for diagonal and off-diagonal Weyl operators. -/

noncomputable section
namespace InfoGeometry.Bridge.PolarAxialChiralParityBridge

open Matrix
open InfoGeometry.Canonical.PauliHestenesSpinMomentum
open InfoGeometry.Bridge.QuaternionicPauliDiracSoldering

abbrev PauliBlock := QuaternionicPauliDiracSoldering.PauliBlock
abbrev DiracSpinor := QuaternionicPauliDiracSoldering.DiracSpinor

def diracChirality : Module.End ℂ DiracSpinor where
  toFun ψ := (ψ.1, -ψ.2)
  map_add' := by intro x y; ext <;> simp <;> ring
  map_smul' := by intro c x; ext <;> simp <;> ring

def chiralEvenOperator (L R : PauliBlock) : Module.End ℂ DiracSpinor where
  toFun ψ := (L *ᵥ ψ.1, R *ᵥ ψ.2)
  map_add' := by intro x y; ext <;> simp [Matrix.mulVec_add]
  map_smul' := by intro c x; ext <;> simp [Matrix.mulVec_smul]

theorem diracChirality_sq :
    diracChirality.comp diracChirality =
      (LinearMap.id : Module.End ℂ DiracSpinor) := by
  apply LinearMap.ext
  intro ψ
  rcases ψ with ⟨ψL, ψR⟩
  simp [diracChirality]

theorem chiralEvenOperator_commutes_chirality (L R : PauliBlock) :
    diracChirality.comp (chiralEvenOperator L R) =
      (chiralEvenOperator L R).comp diracChirality := by
  apply LinearMap.ext
  rintro ⟨ψL, ψR⟩
  ext <;> simp [diracChirality, chiralEvenOperator, Matrix.mulVec_neg] <;> ring

theorem chiralWeylOperator_anticommutes_chirality (A B : PauliBlock) :
    diracChirality.comp (chiralWeylOperator A B) =
      -((chiralWeylOperator A B).comp diracChirality) := by
  apply LinearMap.ext
  rintro ⟨ψL, ψR⟩
  ext <;> simp [diracChirality, chiralWeylOperator, Matrix.mulVec_neg] <;> ring

theorem chiralWeylOperator_sq_eq_even (A B : PauliBlock) :
    (chiralWeylOperator A B).comp (chiralWeylOperator A B) =
      chiralEvenOperator (A * B) (B * A) := by
  apply LinearMap.ext
  intro ψ
  rw [LinearMap.comp_apply, chiralWeylOperator_sq_apply]
  rfl

def polarAxialChiralOperator (A B : PauliParavector) : Module.End ℂ DiracSpinor :=
  chiralWeylOperator (A.pauliMatrix + B.pauliMatrix)
    (coSolderingMap A - coSolderingMap B)

theorem polarAxialChiralOperator_anticommutes_chirality
    (A B : PauliParavector) :
    diracChirality.comp (polarAxialChiralOperator A B) =
      -((polarAxialChiralOperator A B).comp diracChirality) := by
  exact chiralWeylOperator_anticommutes_chirality _ _

theorem polarAxialChiralOperator_sq_eq_even
    (A B : PauliParavector) :
    (polarAxialChiralOperator A B).comp (polarAxialChiralOperator A B) =
      chiralEvenOperator
        ((A.pauliMatrix + B.pauliMatrix) *
          (coSolderingMap A - coSolderingMap B))
        ((coSolderingMap A - coSolderingMap B) *
          (A.pauliMatrix + B.pauliMatrix)) := by
  exact chiralWeylOperator_sq_eq_even _ _

end InfoGeometry.Bridge.PolarAxialChiralParityBridge
