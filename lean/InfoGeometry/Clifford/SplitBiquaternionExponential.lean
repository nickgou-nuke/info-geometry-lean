import InfoGeometry.Clifford.SplitBiquaternion
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# Explicit exponential packets for distinguished split-biquaternion generators

This file records theorem-honest closed forms for one-parameter packets attached
to concrete generators whose square class is already verified in the maintained
`SplitBiquaternion` owner:

* `I^2 = -1` gives a trigonometric packet;
* `J^2 = 1` and `K^2 = 1` give hyperbolic packets;
* `(iK)^2 = -1` gives a second trigonometric packet inside the complexified lane.

These are explicit finite closed forms. They are not yet a proof that the full
power-series exponential in a topological algebra has been constructed.
-/

namespace InfoGeometry.Clifford
namespace SplitBiquaternion

/-- Complex scalar times the square-plus generator `K`, producing a square-minus generator. -/
def iK : SplitBiquaternion :=
  scalar Complex.I * K

/-- Trigonometric packet attached to the square-minus generator `I`. -/
noncomputable def ellipticFlowI (θ : ℂ) : SplitBiquaternion :=
  scalar (Complex.cos θ) + scalar (Complex.sin θ) * I

/-- Hyperbolic packet attached to the square-plus generator `J`. -/
noncomputable def hyperbolicFlowJ (η : ℂ) : SplitBiquaternion :=
  scalar (Complex.cosh η) + scalar (Complex.sinh η) * J

/-- Hyperbolic packet attached to the square-plus generator `K`. -/
noncomputable def hyperbolicFlowK (η : ℂ) : SplitBiquaternion :=
  scalar (Complex.cosh η) + scalar (Complex.sinh η) * K

/-- Trigonometric packet attached to the square-minus generator `iK`. -/
noncomputable def ellipticFlowIK (θ : ℂ) : SplitBiquaternion :=
  scalar (Complex.cos θ) + scalar (Complex.sin θ) * iK

theorem iK_coords : iK = ⟨0, 0, 0, Complex.I⟩ := by
  change mul (scalar Complex.I) K = ⟨0, 0, 0, Complex.I⟩
  ext <;> simp [scalar, K, mul]

theorem iK_sq : iK * iK = scalar (-1 : ℂ) := by
  rw [iK_coords]
  change mul ⟨0, 0, 0, Complex.I⟩ ⟨0, 0, 0, Complex.I⟩ = scalar (-1 : ℂ)
  ext <;> simp [scalar, mul]

theorem ellipticFlowI_coords (θ : ℂ) :
    ellipticFlowI θ = ⟨Complex.cos θ, Complex.sin θ, 0, 0⟩ := by
  change add (scalar (Complex.cos θ)) (mul (scalar (Complex.sin θ)) I) = _
  ext <;> simp [scalar, I, add, mul]

theorem hyperbolicFlowJ_coords (η : ℂ) :
    hyperbolicFlowJ η = ⟨Complex.cosh η, 0, Complex.sinh η, 0⟩ := by
  change add (scalar (Complex.cosh η)) (mul (scalar (Complex.sinh η)) J) = _
  ext <;> simp [scalar, J, add, mul]

theorem hyperbolicFlowK_coords (η : ℂ) :
    hyperbolicFlowK η = ⟨Complex.cosh η, 0, 0, Complex.sinh η⟩ := by
  change add (scalar (Complex.cosh η)) (mul (scalar (Complex.sinh η)) K) = _
  ext <;> simp [scalar, K, add, mul]

theorem ellipticFlowIK_coords (θ : ℂ) :
    ellipticFlowIK θ = ⟨Complex.cos θ, 0, 0, Complex.I * Complex.sin θ⟩ := by
  change add (scalar (Complex.cos θ)) (mul (scalar (Complex.sin θ)) iK) = _
  rw [iK_coords]
  ext <;> simp [scalar, add, mul]
  ring

theorem norm_ellipticFlowI (θ : ℂ) :
    norm (ellipticFlowI θ) = 1 := by
  rw [ellipticFlowI_coords]
  simpa [norm, pow_two] using Complex.cos_sq_add_sin_sq θ

theorem norm_hyperbolicFlowJ (η : ℂ) :
    norm (hyperbolicFlowJ η) = 1 := by
  rw [hyperbolicFlowJ_coords]
  simpa [norm, pow_two] using Complex.cosh_sq_sub_sinh_sq η

theorem norm_hyperbolicFlowK (η : ℂ) :
    norm (hyperbolicFlowK η) = 1 := by
  rw [hyperbolicFlowK_coords]
  simpa [norm, pow_two] using Complex.cosh_sq_sub_sinh_sq η

theorem norm_ellipticFlowIK (θ : ℂ) :
    norm (ellipticFlowIK θ) = 1 := by
  rw [ellipticFlowIK_coords]
  calc
    Complex.cos θ * Complex.cos θ + 0 * 0 - 0 * 0 - (Complex.I * Complex.sin θ) * (Complex.I * Complex.sin θ)
        = Complex.cos θ ^ 2 + Complex.sin θ ^ 2 := by
          calc
            Complex.cos θ * Complex.cos θ + 0 * 0 - 0 * 0 - (Complex.I * Complex.sin θ) * (Complex.I * Complex.sin θ)
                = Complex.cos θ ^ 2 - Complex.I ^ 2 * Complex.sin θ ^ 2 := by ring
            _ = Complex.cos θ ^ 2 + Complex.sin θ ^ 2 := by simp [Complex.I_sq]
    _ = 1 := Complex.cos_sq_add_sin_sq θ

/-- The square-minus generator `iK` carries the same norm-one trigonometric packet as `I`. -/
theorem norm_iK_packet (θ : ℂ) :
    norm (scalar (Complex.cos θ) + scalar (Complex.sin θ) * iK) = 1 := by
  simpa [ellipticFlowIK] using norm_ellipticFlowIK θ

end SplitBiquaternion
end InfoGeometry.Clifford
