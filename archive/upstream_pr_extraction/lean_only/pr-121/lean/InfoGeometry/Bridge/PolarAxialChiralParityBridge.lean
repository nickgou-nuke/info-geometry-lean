import Mathlib.Tactic
import InfoGeometry.Bridge.CliffordFourExteriorGradeBridge
import InfoGeometry.Bridge.QuaternionicPauliDiracSoldering

/-!
# Polar/axial chiral operator parity bridge

This file connects the finite Pauli--Weyl symbol to the exact even/odd block
parity on the doubled Dirac carrier.

* diagonal block operators commute with chirality;
* off-diagonal Weyl operators anticommute with chirality;
* the square of every off-diagonal operator is diagonal;
* a polar Pauli paravector and an axial Pauli paravector define a concrete
  off-diagonal operator.

The results are finite linear algebra.  They do not identify an arbitrary
block with a differential connection or its square with geometric curvature.
-/

noncomputable section

namespace InfoGeometry.Bridge.PolarAxialChiralParityBridge

open Matrix
open InfoGeometry.Canonical.PauliHestenesSpinMomentum
open InfoGeometry.Bridge.QuaternionicPauliDiracSoldering

abbrev PauliBlock := QuaternionicPauliDiracSoldering.PauliBlock
abbrev DiracSpinor := QuaternionicPauliDiracSoldering.DiracSpinor

/-- Chirality on the doubled Weyl carrier. -/
def diracChirality : Module.End ℂ DiracSpinor where
  toFun ψ := (ψ.1, -ψ.2)
  map_add' := by
    intro x y
    ext <;> simp
  map_smul' := by
    intro c x
    ext <;> simp

/-- A block-diagonal, hence parity-even, endomorphism. -/
def chiralEvenOperator (L R : PauliBlock) : Module.End ℂ DiracSpinor where
  toFun ψ := (L *ᵥ ψ.1, R *ᵥ ψ.2)
  map_add' := by
    intro x y
    ext <;> simp
  map_smul' := by
    intro c x
    ext <;> simp [Matrix.mulVec_smul]

theorem diracChirality_sq :
    diracChirality.comp diracChirality =
      (LinearMap.id : Module.End ℂ DiracSpinor) := by
  apply LinearMap.ext
  intro ψ
  rcases ψ with ⟨ψL, ψR⟩
  simp [diracChirality]

/-- Every block-diagonal operator is even: it commutes with chirality. -/
theorem chiralEvenOperator_commutes_chirality (L R : PauliBlock) :
    diracChirality.comp (chiralEvenOperator L R) =
      (chiralEvenOperator L R).comp diracChirality := by
  apply LinearMap.ext
  intro ψ
  rcases ψ with ⟨ψL, ψR⟩
  ext <;> simp [diracChirality, chiralEvenOperator]

/-- Every off-diagonal Weyl operator is odd: it anticommutes with chirality. -/
theorem chiralWeylOperator_anticommutes_chirality (A B : PauliBlock) :
    diracChirality.comp (chiralWeylOperator A B) =
      -((chiralWeylOperator A B).comp diracChirality) := by
  apply LinearMap.ext
  intro ψ
  rcases ψ with ⟨ψL, ψR⟩
  ext <;> simp [diracChirality, chiralWeylOperator]

/-- Odd times odd is even on the doubled Weyl carrier. -/
theorem chiralWeylOperator_sq_eq_even (A B : PauliBlock) :
    (chiralWeylOperator A B).comp (chiralWeylOperator A B) =
      chiralEvenOperator (A * B) (B * A) := by
  apply LinearMap.ext
  intro ψ
  rw [LinearMap.comp_apply]
  rw [chiralWeylOperator_sq_apply]
  rfl

/-- Finite polar/axial odd symbol.  The vector contribution enters both Weyl
rails with the same sign, while the axial contribution enters them with
opposite signs. -/
def polarAxialChiralOperator
    (A B : PauliParavector) : Module.End ℂ DiracSpinor :=
  chiralWeylOperator
    (A.pauliMatrix + B.pauliMatrix)
    (coSolderingMap A - coSolderingMap B)

theorem polarAxialChiralOperator_anticommutes_chirality
    (A B : PauliParavector) :
    diracChirality.comp (polarAxialChiralOperator A B) =
      -((polarAxialChiralOperator A B).comp diracChirality) := by
  exact chiralWeylOperator_anticommutes_chirality _ _

/-- Squaring the polar/axial odd symbol lands exactly in the even,
block-diagonal sector. -/
theorem polarAxialChiralOperator_sq_eq_even
    (A B : PauliParavector) :
    (polarAxialChiralOperator A B).comp
        (polarAxialChiralOperator A B) =
      chiralEvenOperator
        ((A.pauliMatrix + B.pauliMatrix) *
          (coSolderingMap A - coSolderingMap B))
        ((coSolderingMap A - coSolderingMap B) *
          (A.pauliMatrix + B.pauliMatrix)) := by
  exact chiralWeylOperator_sq_eq_even _ _

end InfoGeometry.Bridge.PolarAxialChiralParityBridge
