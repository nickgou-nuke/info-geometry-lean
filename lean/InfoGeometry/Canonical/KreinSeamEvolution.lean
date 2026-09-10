import Mathlib
import InfoGeometry.Canonical.AharonovKreinWeakValueBridge
import InfoGeometry.Krein.DoubledSpace

/-!
# Krein seam identification and operatorial free-energy descent

The post-selection post = eta pre identifies transition cancellation with
Krein nullity. It is a choice of post-selection, not a consequence for arbitrary
independent boundary states.

The evolution below is an open-system Hamiltonian-plus-gradient free-energy
flow on the canonical doubled carrier. It is not a GENERIC energy-conserving
closed-system theorem. Actual trajectory and Frechet derivative hypotheses are
used to derive the free-energy derivative.
-/

noncomputable section
namespace InfoGeometry.Canonical.KreinSeamEvolution

open InfoGeometry.Krein
open AharonovKreinWeakValueBridge

section Nullity
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

theorem eta_postselection_overlap
    (K : InfoGeometry.OperatorAlgebra.KreinMetricDatum H) (psi : H) :
    transitionAmplitude (K.eta psi) psi = kreinQuadratic K psi := by
  exact real_inner_comm _ _

/-- The missing identification is derived under the explicit eta post-selection. -/
theorem nullMode_iff_eta_postselection
    (K : InfoGeometry.OperatorAlgebra.KreinMetricDatum H) (psi : H) :
    KreinNullMode K psi ↔
      psi ≠ 0 ∧ CrossSheetTransitionZero (K.eta psi) psi := by
  simp only [KreinNullMode, CrossSheetTransitionZero, eta_postselection_overlap]

/-- A quadratic-form-preserving map cannot turn a globally regular state null. -/
theorem preserving_map_keeps_regular
    (K : InfoGeometry.OperatorAlgebra.KreinMetricDatum H) (U : H → H)
    (hU : ∀ v, kreinQuadratic K (U v) = kreinQuadratic K v)
    (v : H) (hv : kreinQuadratic K v ≠ 0) :
    ¬ KreinNullMode K (U v) := by
  intro hn
  exact hv ((hU v).symm.trans hn.2)
end Nullity

section Evolution
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- The canonical Cl(1,1) complex axis does no Hilbert quadratic work. -/
theorem axis_inner_zero (v : DoubledSpace E) :
    inner (𝕜 := ℝ) v (complex_i v) = 0 := by
  simp [complex_i_apply, WithLp.prod_inner_apply, real_inner_comm]

theorem axis_inner_self (v : DoubledSpace E) :
    inner (𝕜 := ℝ) (complex_i v) (complex_i v) = inner (𝕜 := ℝ) v v := by
  simp [complex_i_apply, WithLp.prod_inner_apply, add_comm]

/-- Homogeneous double-angle coordinates. The only excluded point is (0,0). -/
def circleCos (n d : ℝ) : ℝ := (d ^ 2 - n ^ 2) / (d ^ 2 + n ^ 2)
def circleSin (n d : ℝ) : ℝ := 2 * d * n / (d ^ 2 + n ^ 2)

theorem circle_coordinates (n d : ℝ) (h : d ^ 2 + n ^ 2 ≠ 0) :
    circleCos n d ^ 2 + circleSin n d ^ 2 = 1 := by
  dsimp [circleCos, circleSin]
  field_simp [h] <;> ring

/-- Lift the homogeneous pair to the existing doubled-space complex axis. -/
def seamRotor (n d : ℝ) : DoubledSpace E →L[ℝ] DoubledSpace E :=
  circleCos n d • ContinuousLinearMap.id ℝ (DoubledSpace E) +
    circleSin n d • complex_i

/-- The spin readout has unit Hilbert quadratic norm even when d = 0, n ≠ 0. -/
theorem seamRotor_preserves_quadratic (n d : ℝ) (h : d ^ 2 + n ^ 2 ≠ 0)
    (v : DoubledSpace E) :
    inner (𝕜 := ℝ) (seamRotor n d v) (seamRotor n d v) = inner (𝕜 := ℝ) v v := by
  have hc := circle_coordinates n d h
  have he := congrArg (fun r : ℝ => r * inner (𝕜 := ℝ) v v) hc
  have hcross : inner (𝕜 := ℝ) (complex_i v) v = 0 := by
    rw [real_inner_comm]
    exact axis_inner_zero v
  simp only [seamRotor, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, axis_inner_zero, axis_inner_self,
    hcross, mul_zero, zero_add, add_zero]
  nlinarith [he]

theorem seamRotor_at_pole (n : ℝ) (hn : n ≠ 0) :
    seamRotor (E := E) n 0 = -ContinuousLinearMap.id ℝ (DoubledSpace E) := by
  have hc : circleCos n 0 = -1 := by
    simp [circleCos, pow_ne_zero 2 hn]
  have hs : circleSin n 0 = 0 := by simp [circleSin]
  simp [seamRotor, hc, hs]

/-- This is continuity of the alternative rotor readout, not continuity of n/d. -/
theorem seamRotor_continuousAt (n d : ℝ) (h : d ^ 2 + n ^ 2 ≠ 0) :
    ContinuousAt (fun p : ℝ × ℝ => seamRotor (E := E) p.1 p.2) (n, d) := by
  unfold seamRotor circleCos circleSin
  fun_prop (disch := assumption)

/-- Reversible rotation plus Onsager descent of a supplied free-energy gradient. -/
def descentVelocity (D : DoubledSpace E →L[ℝ] DoubledSpace E)
    (omega : ℝ) (gradient : DoubledSpace E) : DoubledSpace E :=
  omega • complex_i gradient - D gradient

theorem descent_pairing (D : DoubledSpace E →L[ℝ] DoubledSpace E)
    (omega : ℝ) (g : DoubledSpace E) :
    inner (𝕜 := ℝ) g (descentVelocity D omega g) =
      -inner (𝕜 := ℝ) g (D g) := by
  simp [descentVelocity, inner_sub_right, real_inner_smul_right, axis_inner_zero]

/-- Chain-rule closure: the dissipation rate is proved for an actual trajectory. -/
theorem hasDerivAt_freeEnergy
    (F : DoubledSpace E → ℝ) (trajectory : ℝ → DoubledSpace E)
    (D : DoubledSpace E →L[ℝ] DoubledSpace E) (omega t : ℝ)
    (g : DoubledSpace E)
    (hF : HasFDerivAt F (innerSL ℝ g) (trajectory t))
    (hx : HasDerivAt trajectory (descentVelocity D omega g) t) :
    HasDerivAt (fun s => F (trajectory s))
      (-inner (𝕜 := ℝ) g (D g)) t := by
  have h := hF.comp_hasDerivAt t hx
  simpa only [Function.comp_apply, innerSL_apply_apply, descent_pairing] using h

theorem freeEnergy_deriv_nonpos
    (F : DoubledSpace E → ℝ) (trajectory : ℝ → DoubledSpace E)
    (D : DoubledSpace E →L[ℝ] DoubledSpace E) (omega t : ℝ)
    (g : DoubledSpace E)
    (hF : HasFDerivAt F (innerSL ℝ g) (trajectory t))
    (hx : HasDerivAt trajectory (descentVelocity D omega g) t)
    (hD : ∀ v, 0 ≤ inner (𝕜 := ℝ) v (D v)) :
    deriv (fun s => F (trajectory s)) t ≤ 0 := by
  rw [(hasDerivAt_freeEnergy F trajectory D omega t g hF hx).deriv]
  exact neg_nonpos.mpr (hD g)

/-- An actual equilibrium trajectory retains the canonical rotational derivative. -/
theorem equilibrium_is_rotational
    (trajectory : ℝ → DoubledSpace E)
    (D : DoubledSpace E →L[ℝ] DoubledSpace E) (omega t : ℝ)
    (g : DoubledSpace E)
    (hx : HasDerivAt trajectory (descentVelocity D omega g) t)
    (hEq : D g = 0) :
    HasDerivAt trajectory (omega • complex_i g) t := by
  simpa [descentVelocity, hEq] using hx

/-- An implicit-midpoint rotational step preserves the squared Hilbert norm. -/
theorem rotational_midpoint_preserves_quadratic
    (v w : DoubledSpace E) (step : ℝ)
    (hstep : w - v = step • complex_i ((1 / 2 : ℝ) • (w + v))) :
    inner (𝕜 := ℝ) w w = inner (𝕜 := ℝ) v v := by
  have hzero := axis_inner_zero ((1 / 2 : ℝ) • (w + v))
  have hpair := congrArg
    (fun z => inner (𝕜 := ℝ) ((1 / 2 : ℝ) • (w + v)) z) hstep
  simp only [real_inner_smul_right, hzero, mul_zero] at hpair
  simp [inner_add_left, inner_sub_right,
    real_inner_smul_left, real_inner_comm] at hpair
  linarith
end Evolution

/-- Cancellation is local only when both principal parts use the same denominator. -/
theorem paired_pole_cancellation (a d regularPlus regularMinus : ℝ) :
    (a / d + regularPlus) + (-a / d + regularMinus) =
      regularPlus + regularMinus := by
  ring

/-- Exact cancellation gives a continuous reconstructed sum across the seam. -/
theorem continuous_paired_readout
    (a d regularPlus regularMinus : ℝ → ℝ) (T : ℝ)
    (hp : ContinuousAt regularPlus T) (hm : ContinuousAt regularMinus T) :
    ContinuousAt (fun t =>
      (a t / d t + regularPlus t) + (-a t / d t + regularMinus t)) T := by
  have he : (fun t => (a t / d t + regularPlus t) +
      (-a t / d t + regularMinus t)) = fun t => regularPlus t + regularMinus t := by
    funext t
    exact paired_pole_cancellation _ _ _ _
  rw [he]
  exact hp.add hm

end InfoGeometry.Canonical.KreinSeamEvolution
