import InfoGeometry.Lie.CanonicalZornG2GellMannRootComparison
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Faithfulness and canonical-generator readout for the G₂ Cartan plane

The two scalar Gell--Mann parameters are recovered from the canonical
parameter coordinates, so the Cartan readout is faithful.  The generator
identifications are re-exported here at the canonical derivation level.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornG2CartanFaithfulness

open InfoGeometry.Lie.CanonicalZornG2GellMannRootComparison
open InfoGeometry.Lie.CanonicalZornDerivationDimension
open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
open InfoGeometry.Lie.SplitOctonionAxialCartanErlangen
open InfoGeometry.Lie.SplitOctonionGellMannCartan

theorem gellMannCartan_param_injective :
    Function.Injective (fun p : ℝ × ℝ => gellMannCartan_param p.1 p.2) := by
  intro p q h
  have h6 := congrFun h 6
  have h13 := congrFun h 13
  change gellMannCartan_param p.1 p.2 6 =
    gellMannCartan_param q.1 q.2 6 at h6
  change gellMannCartan_param p.1 p.2 13 =
    gellMannCartan_param q.1 q.2 13 at h13
  rw [gellMannCartan_param_eq, gellMannCartan_param_eq] at h6 h13
  simp [parameterUnit] at h6 h13
  apply Prod.ext
  · linarith
  · linarith

theorem gellMannH1_canonicalCartanGenerator :
    gellMannH1_param = parameterUnit 6 :=
  gellMannH1_eq_canonicalCartanCombination

theorem gellMannH2_canonicalCartanGenerator :
    gellMannH2_param = -parameterUnit 6 + 2 • parameterUnit 13 :=
  gellMannH2_eq_canonicalCartanCombination

theorem gellMannCartan_param_canonical_readout (K1 K2 : ℝ) :
    gellMannCartan_param K1 K2 =
      K1 • gellMannH1_param + K2 • gellMannH2_param :=
  by
  change canonicalParameterLinearEquiv.symm
      (axialCartanLieEquiv (gellMannCartan K1 K2)) = _
  rw [gellMannCartan_parameter_readout]
  rw [gellMannH1_eq_canonicalCartanCombination,
    gellMannH2_eq_canonicalCartanCombination]

end InfoGeometry.Lie.CanonicalZornG2CartanFaithfulness
