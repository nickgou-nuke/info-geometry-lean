/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.RealWeylCircularZornAction
import Mathlib.Tactic

/-!
# Real Majorana subrepresentation of the paired Weyl action

The real Majorana carrier is the graph of the epsilon-twisted conjugation
intertwiner between the left and right Weyl modules.  This file makes the
reality condition an actual invariant subspace of the existing paired
`SL(2,ℂ)` action, rather than merely realifying one complex Weyl module.
-/

noncomputable section

namespace InfoGeometry.Twistor.RealMajoranaLorentzRepresentation

open InfoGeometry.OperatorAlgebra.RealWeylAdjointSpinRepresentation
open InfoGeometry.Twistor.PenroseCanonicalZornSoldering
open InfoGeometry.Twistor.RealWeylCircularZornAction

/-- The epsilon-twisted conjugate of a two-component Weyl spinor. -/
def majoranaConjugate (ψ : WeylSpinor) : WeylSpinor :=
  ![star (ψ 1), -star (ψ 0)]

/-- The real Majorana subspace in the paired left/right Weyl carrier. -/
def majoranaSubspace : Submodule ℝ WeylPair where
  carrier := {ψ | ψ.2 = majoranaConjugate ψ.1}
  zero_mem' := by
    change (0 : WeylPair).2 = majoranaConjugate (0 : WeylPair).1
    ext i
    fin_cases i <;> simp [majoranaConjugate]
  add_mem' := by
    intro ψ φ hψ hφ
    change (ψ + φ).2 = majoranaConjugate (ψ + φ).1
    have h1 : ψ.2 = majoranaConjugate ψ.1 := hψ
    have h2 : φ.2 = majoranaConjugate φ.1 := hφ
    ext i
    fin_cases i <;> simp [majoranaConjugate, h1, h2, Pi.add_apply] <;> ring
  smul_mem' := by
    intro r ψ hψ
    change (r • ψ).2 = majoranaConjugate (r • ψ).1
    have h1 : ψ.2 = majoranaConjugate ψ.1 := hψ
    ext i
    fin_cases i <;> simp [majoranaConjugate, h1, Pi.smul_apply, Complex.real_smul]

/-- The Majorana reality constraint is preserved by the paired Weyl action. -/
theorem majoranaSubspace_invariant (g : SL2C) (ψ : majoranaSubspace) :
    actWeylPair g ψ.1 ∈ majoranaSubspace := by
  change (actWeylPair g ψ.1).2 = majoranaConjugate (actWeylPair g ψ.1).1
  have hψ : ψ.1.2 = majoranaConjugate ψ.1.1 := ψ.2
  have hinv : ((g⁻¹ : SL2C) : Mat2C) = Matrix.adjugate (g : Mat2C) := by
    rw [Matrix.SpecialLinearGroup.coe_inv]
  ext i
  fin_cases i <;>
    simp [actWeylPair, matrixSpinAction, rightWeyl, hinv, Matrix.adjugate_fin_two,
      majoranaConjugate, hψ, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    ring

/-- The circular Zorn model of the real Majorana carrier. -/
def majoranaZornSubspace : Submodule ℝ CanonicalZorn :=
  majoranaSubspace.comap zornWeylEquiv.toLinearMap

/-- The full paired Weyl action preserves the real Majorana subspace of the
circular Zorn carrier. -/
theorem majoranaZornSubspace_invariant (g : SL2C) (z : majoranaZornSubspace) :
    zornWeylAction g z.1 ∈ majoranaZornSubspace := by
  change zornWeylEquiv (zornWeylAction g z.1) ∈ majoranaSubspace
  rw [zornWeylAction_readout]
  exact majoranaSubspace_invariant g ⟨zornWeylEquiv z.1, z.2⟩

end InfoGeometry.Twistor.RealMajoranaLorentzRepresentation
