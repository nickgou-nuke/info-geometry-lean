import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Continuous real hyperbolic rotors

This is the topological operator layer for a split generator `D` with
`D² = 1`.  The coefficients are exact witnesses `c` and `s` satisfying
`c² - s² = 1`; no complex scalar or analytic exponential is assumed.
-/

noncomputable section

namespace InfoGeometry.Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def continuousHyperbolicRotor
    (D : V →L[ℝ] V) (c s : ℝ) : V →L[ℝ] V :=
  c • (ContinuousLinearMap.id ℝ V) + s • D

def continuousReverseHyperbolicRotor
    (D : V →L[ℝ] V) (c s : ℝ) : V →L[ℝ] V :=
  c • (ContinuousLinearMap.id ℝ V) - s • D

theorem continuousHyperbolicRotor_comp_reverse
    (D : V →L[ℝ] V) (c s : ℝ)
    (hD : D.comp D = ContinuousLinearMap.id ℝ V)
    (hcs : c * c - s * s = 1) :
    (continuousHyperbolicRotor D c s).comp
        (continuousReverseHyperbolicRotor D c s) =
      ContinuousLinearMap.id ℝ V := by
  apply ContinuousLinearMap.ext
  intro v
  have hDv : D (D v) = v := by
    simpa [ContinuousLinearMap.comp_apply] using
      congrArg (fun f : V →L[ℝ] V => f v) hD
  calc
    (continuousHyperbolicRotor D c s).comp
        (continuousReverseHyperbolicRotor D c s) v =
        (c * c - s * s) • v := by
      simp [continuousHyperbolicRotor,
        continuousReverseHyperbolicRotor,
        ContinuousLinearMap.comp_apply,
        sub_eq_add_neg, add_smul, smul_add, smul_smul, hDv]
      have hcomm : c * s = s * c := by ring
      rw [hcomm]
      abel_nf
    _ = v := by rw [hcs]; simp

theorem continuousReverseHyperbolicRotor_comp
    (D : V →L[ℝ] V) (c s : ℝ)
    (hD : D.comp D = ContinuousLinearMap.id ℝ V)
    (hcs : c * c - s * s = 1) :
    (continuousReverseHyperbolicRotor D c s).comp
        (continuousHyperbolicRotor D c s) =
      ContinuousLinearMap.id ℝ V := by
  apply ContinuousLinearMap.ext
  intro v
  have hDv : D (D v) = v := by
    simpa [ContinuousLinearMap.comp_apply] using
      congrArg (fun f : V →L[ℝ] V => f v) hD
  calc
    (continuousReverseHyperbolicRotor D c s).comp
        (continuousHyperbolicRotor D c s) v =
        (c * c - s * s) • v := by
      simp [continuousHyperbolicRotor,
        continuousReverseHyperbolicRotor,
        ContinuousLinearMap.comp_apply,
        sub_eq_add_neg, add_smul, smul_add, smul_smul, hDv]
      have hcomm : c * s = s * c := by ring
      rw [hcomm]
      abel_nf
    _ = v := by rw [hcs]; simp


end InfoGeometry.Topology
