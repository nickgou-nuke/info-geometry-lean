/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.RealWeylCircularZornAction
import InfoGeometry.OperatorAlgebra.CanonicalZornCircularCARProjectors

/-! The real Weyl action conjugates the native circular Zorn operator algebra.
The CAR relations survive conjugation without assuming that the spin action is
an automorphism of the nonassociative Zorn multiplication. -/

noncomputable section

namespace InfoGeometry.Twistor.WeylZornMajoranaOperatorAction

open InfoGeometry.OperatorAlgebra.RealWeylAdjointSpinRepresentation
open InfoGeometry.OperatorAlgebra.CanonicalZornCircularCARProjectors
open InfoGeometry.Twistor.PenroseCanonicalZornSoldering
open InfoGeometry.Twistor.RealWeylCircularZornAction

/-- The two realified Weyl representations, acting on their product. -/
def weylPairEquiv (g : SL2C) : WeylPair ≃ₗ[ℝ] WeylPair :=
  ((Matrix.SpecialLinearGroup.toLin' g).restrictScalars ℝ).prodCongr
    ((Matrix.SpecialLinearGroup.toLin' (rightWeyl g)).restrictScalars ℝ)

theorem weylPairEquiv_apply (g : SL2C) (p : WeylPair) :
    weylPairEquiv g p = actWeylPair g p := by
  apply Prod.ext <;> rfl

/-- The spin action as an invertible real-linear map of the Zorn carrier. -/
def zornSpinEquiv (g : SL2C) : CanonicalZorn ≃ₗ[ℝ] CanonicalZorn :=
  (zornWeylEquiv.trans (weylPairEquiv g)).trans zornWeylEquiv.symm

theorem zornSpinEquiv_apply (g : SL2C) (z : CanonicalZorn) :
    zornSpinEquiv g z = zornWeylAction g z := by
  simp [zornSpinEquiv, zornWeylAction, weylPairEquiv_apply]

/-- Conjugation is an algebra automorphism of real Zorn endomorphisms. -/
def spinConjugation (g : SL2C) : EndCZ ≃ₐ[ℝ] EndCZ :=
  (zornSpinEquiv g).conjAlgEquiv ℝ

theorem spinConjugation_intertwines (g : SL2C) (T : EndCZ) (z : CanonicalZorn) :
    spinConjugation g T (zornWeylAction g z) = zornWeylAction g (T z) := by
  change zornSpinEquiv g (T ((zornSpinEquiv g).symm (zornWeylAction g z))) = _
  rw [← zornSpinEquiv_apply, LinearEquiv.symm_apply_apply, zornSpinEquiv_apply]

/-- Chirality on the Zorn carrier induced by the two Weyl factors. -/
def weylChirality (z : CanonicalZorn) : CanonicalZorn :=
  zornWeylEquiv.symm ((zornWeylEquiv z).1, -(zornWeylEquiv z).2)

theorem weylChirality_involution (z : CanonicalZorn) :
    weylChirality (weylChirality z) = z := by
  apply zornWeylEquiv.injective
  simp [weylChirality]

/-- The paired Weyl action preserves its own chiral splitting. -/
theorem weylChirality_commutes_spin (g : SL2C) (z : CanonicalZorn) :
    weylChirality (zornWeylAction g z) = zornWeylAction g (weylChirality z) := by
  apply zornWeylEquiv.injective
  simp [weylChirality, zornWeylAction_readout, actWeylPair, matrixSpinAction, add_comm]

theorem transformed_majorana_relations (g : SL2C) (i : Fin 3) :
    spinConjugation g (majoranaPlus i) * spinConjugation g (majoranaPlus i) = 1 ∧
    spinConjugation g (majoranaMinus i) * spinConjugation g (majoranaMinus i) = -1 ∧
    spinConjugation g (majoranaPlus i) * spinConjugation g (majoranaMinus i) +
      spinConjugation g (majoranaMinus i) * spinConjugation g (majoranaPlus i) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [map_mul, map_one] using congrArg (spinConjugation g) (majoranaPlus_sq i)
  · simpa only [map_mul, map_neg, map_one] using congrArg (spinConjugation g) (majoranaMinus_sq i)
  · simpa only [map_add, map_mul, map_zero] using
      congrArg (spinConjugation g) (majoranaPlus_majoranaMinus_anticomm i)

end InfoGeometry.Twistor.WeylZornMajoranaOperatorAction
