import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Arithmetic.RiemannApolloniusRiccatiBridge
import InfoGeometry.Arithmetic.RiemannApolloniusVectorFields

/-!
# Apollonius master potential and corrected Helmholtz/Cauchy--Riemann bridge

This owner formalizes the theorem-safe potential-theory layer associated with

  w(s) = s / (s - 1),
  z = s - 1/2,
  h(z) = 1/4 - z^2,
  Omega = -log w.

The logarithm itself is branch-sensitive, so the global algebraic owner is the
logarithmic derivative

  dOmega/dz = -1/h(z),

away from the two rational poles.  In real coordinates the Cauchy--Riemann
components determine the scalar-potential and stream-function gradients.  With
the repository orientation `J(x,y) = (y,-x)` and conformal metric
`g = |h|^{-2} I`, the exact relations are

  grad_g Phi = X_dil,
  X_rot = J (grad_g Phi),
  grad_g Psi = -X_rot.

No distributional delta-source theorem is asserted here.  Such a statement
requires a separate distribution/current owner and branch/winding data.
-/

noncomputable section

namespace InfoGeometry.Canonical.ApolloniusMasterPotentialHelmholtz

open Complex
open InfoGeometry.Arithmetic.RiemannApolloniusRiccatiBridge
open InfoGeometry.Arithmetic.RiemannApolloniusVectorFields

/-- Centered rational ratio `w(z) = (2z+1)/(2z-1)`. -/
def centeredRatio (z : ℂ) : ℂ :=
  (2 * z + 1) / (2 * z - 1)

/-- The rational Riccati scale `h(z)=1/4-z^2`. -/
abbrev hScale : ℂ → ℂ := centeredScale

/-- Algebraic logarithmic derivative of the master potential `Omega=-log w`. -/
def masterPotentialDerivative (z : ℂ) : ℂ :=
  -(hScale z)⁻¹

/-- The centered ratio agrees with the affine Apollonius ratio after uncentering. -/
theorem centeredRatio_eq_apolloniusRatio (z : ℂ) :
    centeredRatio z = apolloniusRatio (uncentered z) := by
  unfold centeredRatio apolloniusRatio uncentered
  ring_nf

/-- Reflection parity becomes reciprocal ratio, away from the two foci. -/
theorem centeredRatio_neg
    (z : ℂ) (hzp : z ≠ (1 / 2 : ℂ)) (hzn : z ≠ (-1 / 2 : ℂ)) :
    centeredRatio (-z) = (centeredRatio z)⁻¹ := by
  unfold centeredRatio
  have h1 : 2 * z - 1 ≠ 0 := by
    intro h
    apply hzp
    linear_combination h / 2
  have h2 : 2 * z + 1 ≠ 0 := by
    intro h
    apply hzn
    linear_combination h / 2
  field_simp [h1, h2]
  ring

/-- The logarithmic master derivative is exactly `-1/(1/4-z^2)`. -/
theorem masterPotentialDerivative_eq (z : ℂ) :
    masterPotentialDerivative z = -((1 / 4 : ℂ) - z ^ 2)⁻¹ := by
  rfl

/-- Equivalent reciprocal identity away from the Riccati fixed points. -/
theorem masterPotentialDerivative_mul_h
    (z : ℂ) (hz : hScale z ≠ 0) :
    masterPotentialDerivative z * hScale z = -1 := by
  unfold masterPotentialDerivative
  rw [neg_mul, inv_mul_cancel₀ hz]

/-- The two excluded points are exactly the zeros of the conformal scale. -/
theorem hScale_ne_zero_iff (z : ℂ) :
    hScale z ≠ 0 ↔ z ≠ (1 / 2 : ℂ) ∧ z ≠ (-1 / 2 : ℂ) := by
  rw [not_congr centeredScale_eq_zero_iff]
  push_neg

/-! ## Real scalar potential -/

/-- Squared distance to the focus `s=1`. -/
def focusOneSq (sigma t : ℝ) : ℝ :=
  (sigma - 1) ^ 2 + t ^ 2

/-- Squared distance to the focus `s=0`. -/
def focusZeroSq (sigma t : ℝ) : ℝ :=
  sigma ^ 2 + t ^ 2

/-- Real scalar potential `Phi = 1/2 log(r_1^2/r_0^2)`. -/
def scalarPotential (sigma t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log (focusOneSq sigma t / focusZeroSq sigma t)

/-- The central leaf is the zero-equipotential locus. -/
theorem scalarPotential_centralLeaf (t : ℝ) :
    scalarPotential (1 / 2) t = 0 := by
  unfold scalarPotential focusOneSq focusZeroSq
  have heq : ((1 / 2 : ℝ) - 1) ^ 2 + t ^ 2 = (1 / 2 : ℝ) ^ 2 + t ^ 2 := by
    ring
  rw [heq]
  have hpos : 0 < (1 / 2 : ℝ) ^ 2 + t ^ 2 := by positivity
  rw [div_self (ne_of_gt hpos), Real.log_one]
  ring

/-- Reflection across `sigma=1/2` negates the scalar potential away from the foci. -/
theorem scalarPotential_reflection
    (sigma t : ℝ)
    (h0 : focusZeroSq sigma t ≠ 0)
    (h1 : focusOneSq sigma t ≠ 0) :
    scalarPotential (1 - sigma) t = - scalarPotential sigma t := by
  unfold scalarPotential focusOneSq focusZeroSq at *
  have hz_swap : (1 - sigma) ^ 2 + t ^ 2 = (sigma - 1) ^ 2 + t ^ 2 := by ring
  have ho_swap : ((1 - sigma) - 1) ^ 2 + t ^ 2 = sigma ^ 2 + t ^ 2 := by ring
  rw [hz_swap, ho_swap, Real.log_div h0 h1, Real.log_div h1 h0]
  ring

/-! ## Cauchy--Riemann gradient data -/

/-- Squared conformal scale `|h|^2 = A^2+B^2` in real coordinates. -/
def conformalScaleSq (sigma t : ℝ) : ℝ :=
  scaleA sigma t ^ 2 + scaleB sigma t ^ 2

/-- Formal `sigma` derivative of `Phi`, read from `Omega'=-1/h`. -/
def phiSigma (sigma t : ℝ) : ℝ :=
  -scaleA sigma t / conformalScaleSq sigma t

/-- Formal `t` derivative of `Phi`, read from `Omega'=-1/h`. -/
def phiT (sigma t : ℝ) : ℝ :=
  -scaleB sigma t / conformalScaleSq sigma t

/-- Formal `sigma` derivative of the harmonic conjugate `Psi`. -/
def psiSigma (sigma t : ℝ) : ℝ :=
  scaleB sigma t / conformalScaleSq sigma t

/-- Formal `t` derivative of the harmonic conjugate `Psi`. -/
def psiT (sigma t : ℝ) : ℝ :=
  -scaleA sigma t / conformalScaleSq sigma t

/-- Clockwise quarter-turn complex structure on the real plane. -/
def J (v : ℝ × ℝ) : ℝ × ℝ :=
  (v.2, -v.1)

@[simp] theorem J_sq (v : ℝ × ℝ) : J (J v) = (-v.1, -v.2) := by
  rcases v with ⟨x,y⟩
  rfl

/-- Metric gradient of `Phi` for `g=|h|^{-2} I`. -/
def metricGradientPhi (sigma t : ℝ) : ℝ × ℝ :=
  (conformalScaleSq sigma t * phiSigma sigma t,
   conformalScaleSq sigma t * phiT sigma t)

/-- Metric gradient of `Psi` for the same conformal metric. -/
def metricGradientPsi (sigma t : ℝ) : ℝ × ℝ :=
  (conformalScaleSq sigma t * psiSigma sigma t,
   conformalScaleSq sigma t * psiT sigma t)

/-- The scalar-potential metric gradient is exactly the dilation-coordinate field. -/
theorem metricGradientPhi_eq_dilation
    (sigma t : ℝ) (hscale : conformalScaleSq sigma t ≠ 0) :
    metricGradientPhi sigma t = dilationCoordinateField sigma t := by
  apply Prod.ext <;>
    simp [metricGradientPhi, phiSigma, phiT, conformalScaleSq,
      dilationCoordinateField, hscale]

/-- The stream-function metric gradient is minus the rotational field. -/
theorem metricGradientPsi_eq_neg_rotational
    (sigma t : ℝ) (hscale : conformalScaleSq sigma t ≠ 0) :
    metricGradientPsi sigma t =
      (-(rotationalField sigma t).1, -(rotationalField sigma t).2) := by
  apply Prod.ext <;>
    simp [metricGradientPsi, psiSigma, psiT, conformalScaleSq,
      rotationalField, hscale]

/-- The rotational/unitary field is the quarter-turn of the scalar-potential gradient. -/
theorem rotational_eq_J_metricGradientPhi
    (sigma t : ℝ) (hscale : conformalScaleSq sigma t ≠ 0) :
    rotationalField sigma t = J (metricGradientPhi sigma t) := by
  rw [metricGradientPhi_eq_dilation sigma t hscale]
  apply Prod.ext <;>
    simp [J, rotationalField, dilationCoordinateField]

/-- Potential and unitary directions are orthogonal. -/
theorem potential_unitary_orthogonal
    (sigma t : ℝ) (hscale : conformalScaleSq sigma t ≠ 0) :
    (metricGradientPhi sigma t).1 * (rotationalField sigma t).1 +
      (metricGradientPhi sigma t).2 * (rotationalField sigma t).2 = 0 := by
  rw [metricGradientPhi_eq_dilation sigma t hscale]
  exact rotational_dilation_orthogonal sigma t |>.symm

/-! ## Unified complex Riccati field -/

/-- Unified complex metriplectic field in centered coordinates. -/
def unifiedField (gamma : ℝ) (z : ℂ) : ℂ :=
  ((gamma : ℂ) + Complex.I) * hScale z

/-- Exact master-potential reciprocal form, away from the scale zeros. -/
theorem unifiedField_eq_master_reciprocal
    (gamma : ℝ) (z : ℂ) (hz : hScale z ≠ 0) :
    unifiedField gamma z =
      -(((gamma : ℂ) + Complex.I) / masterPotentialDerivative z) := by
  unfold unifiedField masterPotentialDerivative
  field_simp [hz]
  ring

/-- Compact theorem packet for the corrected potential-theory layer. -/
theorem masterPotential_helmholtz_packet
    (sigma t gamma : ℝ)
    (hscale : conformalScaleSq sigma t ≠ 0) :
    metricGradientPhi sigma t = dilationCoordinateField sigma t ∧
    rotationalField sigma t = J (metricGradientPhi sigma t) ∧
    (metricGradientPhi sigma t).1 * (rotationalField sigma t).1 +
      (metricGradientPhi sigma t).2 * (rotationalField sigma t).2 = 0 :=
  ⟨metricGradientPhi_eq_dilation sigma t hscale,
    rotational_eq_J_metricGradientPhi sigma t hscale,
    potential_unitary_orthogonal sigma t hscale⟩

end InfoGeometry.Canonical.ApolloniusMasterPotentialHelmholtz

end noncomputable section
