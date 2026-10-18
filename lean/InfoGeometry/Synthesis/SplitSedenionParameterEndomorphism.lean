/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.SplitOctonionParaKahlerNullCone
import InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge
import InfoGeometry.Lie.CanonicalZornDerivationDimension
import InfoGeometry.Synthesis.Cl44LeftIdealSplitSedenionSynthesis
import InfoGeometry.Synthesis.Cl44MinimalIdealInducedSedenionProductBridge
import InfoGeometry.Synthesis.G2SplitSedenionDerivationBridge
import InfoGeometry.Synthesis.SedenionSocleDirectSumSeparationBridge

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Synthesis.SplitSedenionParameterEndomorphism

open InfoGeometry.Algebra.ZornVectorMatrix
open InfoGeometry.Canonical.SplitOctonionParaKahlerNullCone
open InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge
open InfoGeometry.Lie.CanonicalZornDerivationDimension
open InfoGeometry.Synthesis.Cl44LeftIdealSplitSedenionSynthesis
open InfoGeometry.Synthesis.Cl44MinimalIdealInducedSedenionProductBridge
open InfoGeometry.Synthesis.G2SplitSedenionDerivationBridge
open InfoGeometry.Synthesis.SedenionSocleDirectSumSeparationBridge

private theorem zornG2Derivation_smul_param (r : ℝ) (p : Params)
    (x : ZornSplitOctonion ℝ) :
    zornG2Derivation (r • p) x = zornSmul r (zornG2Derivation p x) := by
  have h := congrArg (fun D : VDer => D (zornVectorMatrixEquiv.symm x))
    (parameterLinearEquiv.map_smul r p)
  change parameterAction (r • p) (zornVectorMatrixEquiv.symm x) =
    InfoGeometry.Algebra.ZornVectorMatrix.smul r (parameterAction p (zornVectorMatrixEquiv.symm x)) at h
  unfold zornG2Derivation
  rw [h, zornVectorMatrixEquiv_smul]

/-- The concrete 14-parameter family as a real-linear map into endomorphisms of
`SplitSedenion ℝ`. Its values are the already-proved split-sedenion derivations;
this is not a Lie-algebra representation or a classification of all derivations. -/
noncomputable def sedenionG2EndomorphismFamily :
    Params →ₗ[ℝ] Module.End ℝ (SplitSedenion ℝ) where
  toFun p := sedenionG2DerivationLinear p
  map_add' p q := by
    apply LinearMap.ext
    intro X
    change sedenionG2Derivation (p + q) X =
      sedenionAdd (sedenionG2Derivation p X) (sedenionG2Derivation q X)
    exact sedenionG2Derivation_add_left p q X
  map_smul' r p := by
    apply LinearMap.ext
    intro X
    rcases X with ⟨x, y⟩
    have hz (z : ZornSplitOctonion ℝ) : zornSmul r z = r • z := by
      ext <;> simp [zornSmul]
    change (zornG2Derivation (r • p) x, zornG2Derivation (r • p) y) =
      (r • zornG2Derivation p x, r • zornG2Derivation p y)
    apply Prod.ext
    · calc
        zornG2Derivation (r • p) x = zornSmul r (zornG2Derivation p x) :=
          zornG2Derivation_smul_param r p x
        _ = r • zornG2Derivation p x := hz _
    · calc
        zornG2Derivation (r • p) y = zornSmul r (zornG2Derivation p y) :=
          zornG2Derivation_smul_param r p y
        _ = r • zornG2Derivation p y := hz _

/-- The 14 coordinate parameters distinguish the associated endomorphisms. -/
theorem sedenionG2EndomorphismFamily_injective :
    Function.Injective sedenionG2EndomorphismFamily := by
  intro p q hpq
  apply sedenionG2Derivation_injective
  funext X
  have hX := congrArg (fun T : Module.End ℝ (SplitSedenion ℝ) => T X) hpq
  simpa [sedenionG2EndomorphismFamily, sedenionG2DerivationLinear] using hX

/-- The image of the concrete endomorphism family has real dimension fourteen. -/
theorem sedenionG2EndomorphismFamily_range_finrank :
    Module.finrank ℝ (LinearMap.range sedenionG2EndomorphismFamily) = 14 := by
  rw [LinearMap.finrank_range_of_inj sedenionG2EndomorphismFamily_injective,
    parameterLinearEquiv.finrank_eq, finrank_vectorDerivations]

end InfoGeometry.Synthesis.SplitSedenionParameterEndomorphism
