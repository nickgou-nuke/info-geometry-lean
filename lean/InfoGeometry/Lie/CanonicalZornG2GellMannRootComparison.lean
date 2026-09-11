import InfoGeometry.Lie.SplitOctonionGellMannCartan
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.CanonicalZornRootSystemComparison
import InfoGeometry.Lie.CanonicalZornDerivationDimension
import InfoGeometry.Lie.CanonicalZornCartanAdjointAction
import InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
import InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge

/-!
# Gell--Mann weights as coordinates on the native `G₂` Cartan plane

This owner compares the diagonal three-channel readout with the already
defined traceless Cartan parameter space.  It deliberately stops at Cartan
weights: no `SU(3)` subgroup or Weyl-group identification is asserted here.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornG2GellMannRootComparison

open InfoGeometry.Lie.SplitOctonionAxialCartanErlangen
open InfoGeometry.Lie.SplitOctonionAxialCartanFlow
open InfoGeometry.Lie.SplitOctonionCartanSixWeights
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
open InfoGeometry.Lie.SplitOctonionGellMannCartan
open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition

theorem gellMannCartan_eq_tracelessWeightEquiv (K1 K2 : ℝ) :
    gellMannCartan K1 K2 =
      tracelessWeightEquiv ![K1 + K2, -K1 + K2] := by
  apply Subtype.ext
  funext i
  fin_cases i <;>
    simp [gellMannCartan, lambda3Traceless, lambda8Traceless,
      lambda3Weights, lambda8Weights, tracelessWeightEquiv]
  <;> ring

theorem weightFunctional_eq_coordWeight (i : Fin 3) :
    weightFunctional i = coordWeight i := by
  rfl

theorem signedWeight_gellMann_apply
    (K1 K2 : ℝ) (p : SignedWeightIndex) :
    signedWeight p (gellMannCartan K1 K2) =
      (if p.1 = 0 then 1 else -1) *
        (K1 * (if p.2.val = 0 then 1 else if p.2.val = 1 then -1 else 0) +
          K2 * (if p.2.val = 0 then 1 else if p.2.val = 1 then 1 else -2)) := by
  rcases p with ⟨s, i⟩
  fin_cases s
  · simp [signedWeight, weightFunctional, gellMannCartan_apply]
  · simp [signedWeight, weightFunctional, gellMannCartan_apply]

theorem gellMannCartan_rootWeight_apply (K1 K2 : ℝ) (j : Fin 14) :
    rootWeight j (gellMannCartan K1 K2) =
    rootWeight j (tracelessWeightEquiv ![K1 + K2, -K1 + K2]) := by
  rw [gellMannCartan_eq_tracelessWeightEquiv]

theorem gellMannCartan_coordinates_surjective :
    Function.Surjective (fun p : ℝ × ℝ =>
      gellMannCartan p.1 p.2) := by
  intro k
  rcases gellMannCartan_surjective k with ⟨K1, K2, h⟩
  exact ⟨(K1, K2), h⟩

open InfoGeometry.Lie.CanonicalZornDerivationDimension
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.SplitOctonionAxialCartanDerivation
open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition

/-- The H1 Cartan generator (from Λ3) as a canonical derivation. -/
def gellMannH1 : InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations :=
  axialCartanLieEquiv (gellMannCartan 1 0)

/-- The H2 Cartan generator (from Λ8) as a canonical derivation. -/
def gellMannH2 : InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations :=
  axialCartanLieEquiv (gellMannCartan 0 1)

/-- The canonical coordinate parameter for H1. -/
def gellMannH1_param : Params :=
  canonicalParameterLinearEquiv.symm gellMannH1

/-- The canonical coordinate parameter for H2. -/
def gellMannH2_param : Params :=
  canonicalParameterLinearEquiv.symm gellMannH2

/-- Identification of H1 with the native G2 Cartan derivations. -/
theorem gellMannH1_eq_canonicalCartanCombination :
    gellMannH1_param = parameterUnit 6 := by
  apply EquivLike.injective canonicalParameterLinearEquiv
  change canonicalParameterLinearEquiv
      (canonicalParameterLinearEquiv.symm gellMannH1) = _
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  apply LinearMap.ext
  intro X
  have hX : X = canonicalVectorEquiv.symm (canonicalVectorEquiv X) :=
    (Equiv.symm_apply_apply canonicalVectorEquiv X).symm
  nth_rw 1 [hX]
  change _ = canonicalVectorEquiv.symm
    (parameterAction (parameterUnit 6) (canonicalVectorEquiv X))
  set Y := canonicalVectorEquiv X
  ext i
  all_goals try fin_cases i
  all_goals simp [gellMannH1, parameterUnit,
    axialCartanLieEquiv,
    gellMannCartan, lambda3Traceless, lambda3Weights,
    axialCartanDerivationIntoLie, axialCartanDerivationLinear,
    axialCartanDerivation, axialCartanEnd,
    parameterAction, canonicalVectorEquiv]

/-- Identification of H2 with the native G2 Cartan derivations. -/
theorem gellMannH2_eq_canonicalCartanCombination :
    gellMannH2_param = -parameterUnit 6 + 2 • parameterUnit 13 := by
  apply EquivLike.injective canonicalParameterLinearEquiv
  change canonicalParameterLinearEquiv
      (canonicalParameterLinearEquiv.symm gellMannH2) = _
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  apply LinearMap.ext
  intro X
  have hX : X = canonicalVectorEquiv.symm (canonicalVectorEquiv X) :=
    (Equiv.symm_apply_apply canonicalVectorEquiv X).symm
  nth_rw 1 [hX]
  change _ = canonicalVectorEquiv.symm
    (parameterAction (-parameterUnit 6 + 2 • parameterUnit 13)
      (canonicalVectorEquiv X))
  set Y := canonicalVectorEquiv X
  ext i
  all_goals try fin_cases i
  all_goals simp [gellMannH2, parameterUnit,
    axialCartanLieEquiv,
    gellMannCartan, lambda8Traceless, lambda8Weights,
    axialCartanDerivationIntoLie, axialCartanDerivationLinear,
    axialCartanDerivation, axialCartanEnd,
    parameterAction, canonicalVectorEquiv]
  all_goals try split_ifs
  all_goals try ring
  all_goals try simp

/-- The canonical coordinate representation of the general Gell-Mann Cartan derivation. -/
noncomputable def gellMannCartan_param (K1 K2 : ℝ) : Params :=
  canonicalParameterLinearEquiv.symm (axialCartanLieEquiv (gellMannCartan K1 K2))

/-- Identification of the general Gell-Mann Cartan derivation with native G2 Cartan parameters. -/
theorem gellMannCartan_param_eq (K1 K2 : ℝ) :
    gellMannCartan_param K1 K2 =
      (K1 - K2) • parameterUnit 6 + (2 * K2) • parameterUnit 13 := by
  apply EquivLike.injective canonicalParameterLinearEquiv
  change canonicalParameterLinearEquiv (canonicalParameterLinearEquiv.symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  apply LinearMap.ext
  intro X
  have hX : X = canonicalVectorEquiv.symm (canonicalVectorEquiv X) :=
    (Equiv.symm_apply_apply canonicalVectorEquiv X).symm
  nth_rw 1 [hX]
  change _ = canonicalVectorEquiv.symm
    (parameterAction ((K1 - K2) • parameterUnit 6 + (2 * K2) • parameterUnit 13)
      (canonicalVectorEquiv X))
  set Y := canonicalVectorEquiv X
  ext i
  all_goals try fin_cases i
  all_goals simp [parameterUnit,
    axialCartanLieEquiv,
    gellMannCartan, lambda3Traceless, lambda8Traceless,
    lambda3Weights, lambda8Weights,
    axialCartanDerivationIntoLie, axialCartanDerivationLinear,
    axialCartanDerivation, axialCartanEnd,
    parameterAction, canonicalVectorEquiv]
  all_goals try split_ifs
  all_goals try ring
  all_goals try simp

theorem gellMannCartan_parameter_readout (K1 K2 : ℝ) :
    canonicalParameterLinearEquiv.symm
        (axialCartanLieEquiv (gellMannCartan K1 K2)) =
      K1 • parameterUnit 6 +
        K2 • (-parameterUnit 6 + 2 • parameterUnit 13) := by
  have hdecomp :
      gellMannCartan K1 K2 =
        K1 • gellMannCartan 1 0 + K2 • gellMannCartan 0 1 := by
    ext i
    fin_cases i <;>
      simp [gellMannCartan, lambda3Traceless, lambda8Traceless,
        lambda3Weights, lambda8Weights]
      <;> ring
  change canonicalParameterLinearEquiv.symm
      (axialCartanDerivationLinear (gellMannCartan K1 K2)) = _
  rw [hdecomp]
  simp only [map_add, map_smul]
  change K1 • gellMannH1_param + K2 • gellMannH2_param = _
  rw [gellMannH1_eq_canonicalCartanCombination,
    gellMannH2_eq_canonicalCartanCombination]

theorem gellMannCartan_exp_weights_product (t w1 w2 w3 : ℝ)
    (hw : w1 + w2 + w3 = 0) :
    Real.exp (t * w1) * Real.exp (t * w2) * Real.exp (t * w3) = 1 := by
  rw [← Real.exp_add, ← Real.exp_add]
  have harg : t * w1 + t * w2 + t * w3 = 0 := by
    calc
      t * w1 + t * w2 + t * w3 = t * (w1 + w2 + w3) := by ring
      _ = t * 0 := by rw [hw]
      _ = 0 := by ring
  rw [harg, Real.exp_zero]

theorem gellMannCartan_exp_product_eq_one (t K1 K2 : ℝ) :
    ∏ i : Fin 3, Real.exp (t * (gellMannCartan K1 K2).1 i) = 1 := by
  have H := (gellMannCartan K1 K2).2
  have hprod : ∏ i : Fin 3, Real.exp (t * (gellMannCartan K1 K2).1 i) =
      Real.exp (t * (gellMannCartan K1 K2).1 0) *
      Real.exp (t * (gellMannCartan K1 K2).1 1) *
      Real.exp (t * (gellMannCartan K1 K2).1 2) := by
    rw [Fin.prod_univ_three]
  rw [hprod]
  apply gellMannCartan_exp_weights_product
  change ∑ i : Fin 3, _ = 0 at H
  rw [Fin.sum_univ_three] at H
  exact H

theorem gellMannCartan_flow_map_mul
    (K1 K2 t : ℝ) (X Y : InfoGeometry.Canonical.ZornMatrix ℝ) :
    axialCartanFlow (gellMannCartan K1 K2).1 t (X * Y) =
      axialCartanFlow (gellMannCartan K1 K2).1 t X *
        axialCartanFlow (gellMannCartan K1 K2).1 t Y := by
  exact axialCartanFlow_map_mul
    (gellMannCartan K1 K2).1 (gellMannCartan K1 K2).2 t X Y

end InfoGeometry.Lie.CanonicalZornG2GellMannRootComparison
