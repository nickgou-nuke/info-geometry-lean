import Mathlib.NumberTheory.DirichletCharacter.Basic
import InfoGeometry.Arithmetic.IdeleClassZetaSymmetry

/-!
# Finite Dirichlet-character readout on the arithmetic layer

This owner uses Mathlib's native `DirichletCharacter` and the existing
`IdeleClassLayer` carrier.  It does not construct the adelic idele class
group, a profinite completion, or a class-field-theoretic isomorphism.
The arithmetic component is simply read through a finite character modulo
`q`; the logarithmic scale component is intentionally ignored.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.IdeleClassDirichletCharacterBridge

open InfoGeometry.Arithmetic.IdeleClassZetaSymmetry
open InfoGeometry.Arithmetic.IdeleClassZetaSymmetry.IdeleClassLayer

abbrev FiniteDirichletCharacter (q : ℕ) := DirichletCharacter ℂ q

/-! The finite arithmetic readout associated with a Dirichlet character. -/
def ideleClassDirichletReadout {q : ℕ}
    (χ : FiniteDirichletCharacter q)
    (A : IdeleClassLayer (ZMod q)ˣ) : ℂ :=
  χ (A.arithmetic : ZMod q)

@[simp] theorem ideleClassDirichletReadout_identity
    {q : ℕ} (χ : FiniteDirichletCharacter q) :
    ideleClassDirichletReadout χ (IdeleClassLayer.identity :
      IdeleClassLayer (ZMod q)ˣ) = 1 := by
  simp [ideleClassDirichletReadout, IdeleClassLayer.identity]

theorem ideleClassDirichletReadout_compose
    {q : ℕ} (χ : FiniteDirichletCharacter q)
    (A B : IdeleClassLayer (ZMod q)ˣ) :
    ideleClassDirichletReadout χ (IdeleClassLayer.compose A B) =
      ideleClassDirichletReadout χ A * ideleClassDirichletReadout χ B := by
  simp [ideleClassDirichletReadout, IdeleClassLayer.compose, map_mul]

theorem ideleClassDirichletReadout_inverse
    {q : ℕ} (χ : FiniteDirichletCharacter q)
    (A : IdeleClassLayer (ZMod q)ˣ) :
    ideleClassDirichletReadout χ (IdeleClassLayer.inverse A) =
      χ ((A.arithmetic : ZMod q)⁻¹) := by
  simp [ideleClassDirichletReadout, IdeleClassLayer.inverse]

end InfoGeometry.Arithmetic.IdeleClassDirichletCharacterBridge
