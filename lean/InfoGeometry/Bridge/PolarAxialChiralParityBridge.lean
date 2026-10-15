import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
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
  map_add' := by
    intro x y
    change (L *ᵥ (x.1 + y.1), R *ᵥ (x.2 + y.2)) =
      (L *ᵥ x.1 + L *ᵥ y.1, R *ᵥ x.2 + R *ᵥ y.2)
    exact Prod.ext (Matrix.mulVec_add L x.1 y.1)
      (Matrix.mulVec_add R x.2 y.2)
  map_smul' := by
    intro c x
    change (L *ᵥ (c • x.1), R *ᵥ (c • x.2)) =
      (c • (L *ᵥ x.1), c • (R *ᵥ x.2))
    exact Prod.ext (Matrix.mulVec_smul L c x.1)
      (Matrix.mulVec_smul R c x.2)

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
  apply Prod.ext
  · rfl
  · change -(R *ᵥ ψR) = R *ᵥ (-ψR)
    rw [Matrix.mulVec_neg]

theorem chiralWeylOperator_anticommutes_chirality (A B : PauliBlock) :
    diracChirality.comp (chiralWeylOperator A B) =
      -((chiralWeylOperator A B).comp diracChirality) := by
  apply LinearMap.ext
  rintro ⟨ψL, ψR⟩
  apply Prod.ext
  · change A *ᵥ ψR = -(A *ᵥ (-ψR))
    rw [Matrix.mulVec_neg]
    simp
  · rfl

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
