import InfoGeometry.GrandCanonical.ResponseMatrix
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.PhaseSpaceWeylCausalBridge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

namespace InfoGeometry.Canonical.ResponseWeylAnomalyBridge

open InfoGeometry.GrandCanonical
open InfoGeometry.Canonical
open InfoGeometry.Canonical.WeylTransportBridge
open InfoGeometry.Canonical.PhaseSpaceWeylCausalBridge
open InfoGeometry.Canonical.ConformalUnification

section Finite

variable {α I X A E : Type*}
variable [Fintype α]
variable [AddCommGroup A] [Module ℝ A]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Thermodynamic response determinant as a Weyl-anomaly readout:
if the response determinant is identified with flat Weyl holonomy, then it is
exactly the projector-obstruction norm on the same conformal source lane.
-/
@[rep_depth thermo, capstone] theorem
    responseDet_eq_projectorObstruction_nnnorm_of_flat_from_conformal
    (params : GrandCanonicalTwoParam α) (β μ : ℝ)
    (CCI : CertifiedConformalInference E)
    (Δ : WeylDifferentialOperator ℝ X A)
    (γ : WeylTrajectory I X)
    (bridge :
      FlatCurvatureProjectorObstructionBridge
        CCI.toConformalInference Δ γ)
    (B : WeylGaugeField X A)
    (hFlat : WeylGaugeField.IsFlat (Δ := Δ) B)
    (hReadout :
      (responseMatrix params β μ).det
        = bridge.lineIntegrator.holonomy bridge.holonomyMap B γ) :
    (responseMatrix params β μ).det
      = ‖CCI.toConformalInference.projectorObstruction‖₊ := by
  calc
    (responseMatrix params β μ).det
        = bridge.lineIntegrator.holonomy bridge.holonomyMap B γ := hReadout
    _ = ‖CCI.toConformalInference.projectorObstruction‖₊ := by
      exact holonomy_eq_projectorObstruction_nnnorm_of_flat_from_conformal
        (CCI := CCI) (Δ := Δ) (γ := γ) (bridge := bridge) (B := B) hFlat

/--
Compatibility corollary:
under the same readout identification, the response determinant equals the
conformal chiral scale.
-/
@[rep_depth thermo, capstone] theorem
    responseDet_eq_chiralScale_of_flat_from_conformal_compat
    (params : GrandCanonicalTwoParam α) (β μ : ℝ)
    (CCI : CertifiedConformalInference E)
    (Δ : WeylDifferentialOperator ℝ X A)
    (γ : WeylTrajectory I X)
    (bridge :
      FlatCurvatureProjectorObstructionBridge
        CCI.toConformalInference Δ γ)
    (B : WeylGaugeField X A)
    (hFlat : WeylGaugeField.IsFlat (Δ := Δ) B)
    (hReadout :
      (responseMatrix params β μ).det
        = bridge.lineIntegrator.holonomy bridge.holonomyMap B γ) :
    (responseMatrix params β μ).det
      = CCI.toConformalInference.chiralScale := by
  calc
    (responseMatrix params β μ).det
        = bridge.lineIntegrator.holonomy bridge.holonomyMap B γ := hReadout
    _ = CCI.toConformalInference.chiralScale := by
      exact holonomy_eq_chiralScale_of_flat_from_conformal_compat
        (CCI := CCI) (Δ := Δ) (γ := γ) (bridge := bridge) (B := B) hFlat

/--
Noncommutative obstruction forces thermodynamic nondegeneracy:
if the response determinant is read from flat Weyl holonomy, then noncommuting
Drazin/Moore-Penrose projectors force a nonzero response determinant.
-/
@[rep_depth thermo, capstone] theorem
    responseDet_ne_zero_of_flat_from_conformal_of_noncommute
    (params : GrandCanonicalTwoParam α) (β μ : ℝ)
    (CCI : CertifiedConformalInference E)
    (Δ : WeylDifferentialOperator ℝ X A)
    (γ : WeylTrajectory I X)
    (bridge :
      FlatCurvatureProjectorObstructionBridge
        CCI.toConformalInference Δ γ)
    (B : WeylGaugeField X A)
    (hFlat : WeylGaugeField.IsFlat (Δ := Δ) B)
    (hReadout :
      (responseMatrix params β μ).det
        = bridge.lineIntegrator.holonomy bridge.holonomyMap B γ)
    (hNonComm :
      CCI.toConformalInference.P_D.comp CCI.toConformalInference.P_MP
        ≠ CCI.toConformalInference.P_MP.comp CCI.toConformalInference.P_D) :
    (responseMatrix params β μ).det ≠ 0 := by
  rw [hReadout]
  exact holonomy_ne_zero_of_flat_from_conformal_of_noncommute
    (CCI := CCI) (Δ := Δ) (γ := γ) (bridge := bridge) (B := B) hFlat hNonComm

/--
Spinodal exclusion from noncommutative anomaly sourcing:
with the same readout identification, noncommuting projectors imply the
two-parameter grand-canonical point is not on the spinodal locus.
-/
@[rep_depth thermo, capstone] theorem
    not_spinodal2D_of_flat_from_conformal_of_noncommute
    (params : GrandCanonicalTwoParam α) (β μ : ℝ)
    (CCI : CertifiedConformalInference E)
    (Δ : WeylDifferentialOperator ℝ X A)
    (γ : WeylTrajectory I X)
    (bridge :
      FlatCurvatureProjectorObstructionBridge
        CCI.toConformalInference Δ γ)
    (B : WeylGaugeField X A)
    (hFlat : WeylGaugeField.IsFlat (Δ := Δ) B)
    (hReadout :
      (responseMatrix params β μ).det
        = bridge.lineIntegrator.holonomy bridge.holonomyMap B γ)
    (hNonComm :
      CCI.toConformalInference.P_D.comp CCI.toConformalInference.P_MP
        ≠ CCI.toConformalInference.P_MP.comp CCI.toConformalInference.P_D) :
    ¬ Spinodal2D params β μ := by
  intro hSpin
  have hDetNe :
      (responseMatrix params β μ).det ≠ 0 :=
    responseDet_ne_zero_of_flat_from_conformal_of_noncommute
      (params := params) (β := β) (μ := μ)
      (CCI := CCI) (Δ := Δ) (γ := γ) (bridge := bridge)
      (B := B) hFlat hReadout hNonComm
  exact hDetNe hSpin

end Finite

end InfoGeometry.Canonical.ResponseWeylAnomalyBridge
