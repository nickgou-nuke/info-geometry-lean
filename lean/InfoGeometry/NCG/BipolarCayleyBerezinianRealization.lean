import InfoGeometry.Analysis.BipolarCrossRatioLog
import InfoGeometry.NCG.BerezinianSuperdeterminant
import Mathlib
import Mathlib.Tactic

/-!
# Explicit finite Berezinian realization of the bipolar Cayley readout

The informal formula `-coth(W/2) = Ber(D)` is not a theorem until the
supermatrix `D` is specified. This file supplies one exact finite `1|1`
realization:

`D(q) = diag(1+q, 1-q)`.

Its block-diagonal Berezinian is

`Ber(D(q)) = (1+q)/(1-q)`.

For `q = exp W`, this is the exponential formula for `-coth(W/2)`, and for
`q(s)=s/(1-s)` it reduces to `1/(1-2s)` away from the odd-block singularity.

This is a finite supermatrix identity. It does not construct a
super-Riemann surface, a superconformal field theory, or a canonical operator
called `D` beyond the explicit block chosen here.
-/

noncomputable section

namespace InfoGeometry.NCG.BipolarCayleyBerezinianRealization

open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
open InfoGeometry.NCG

abbrev ScalarBlock := Matrix (Fin 1) (Fin 1) ℂ

/-- One-dimensional scalar matrix. -/
def scalarBlock (z : ℂ) : ScalarBlock := !![z]

@[simp] theorem det_scalarBlock (z : ℂ) :
    Matrix.det (scalarBlock z) = z := by
  rw [Matrix.det_fin_one]
  simp [scalarBlock]

/-- Even block of the explicit `1|1` Cayley supermatrix. -/
def superCayleyEven (q : ℂ) : ScalarBlock := scalarBlock (1 + q)

/-- Odd block of the explicit `1|1` Cayley supermatrix. -/
def superCayleyOdd (q : ℂ) : ScalarBlock := scalarBlock (1 - q)

/-- Berezinian readout of the explicit diagonal supermatrix. The inverse
parameter is displayed explicitly, as required by the repository owner. -/
def superCayleyBerezinian (q : ℂ) : ℂ :=
  berezinianBlockDiag (superCayleyEven q) (superCayleyOdd q) (1 - q)⁻¹

/-- Closed form of the finite Berezinian. -/
theorem superCayleyBerezinian_eq (q : ℂ) :
    superCayleyBerezinian q = (1 + q) / (1 - q) := by
  simp [superCayleyBerezinian, superCayleyEven, superCayleyOdd, scalarBlock,
    berezinianBlockDiag, div_eq_mul_inv]

/-- Certificate that the supplied odd-block determinant inverse is genuine. -/
theorem superCayleyOdd_inverse_certificate
    {q : ℂ} (hq : 1 - q ≠ 0) :
    Matrix.det (superCayleyOdd q) * (1 - q)⁻¹ = 1 := by
  rw [superCayleyOdd, det_scalarBlock]
  exact mul_inv_cancel₀ hq

/-- Exponential definition of the readout traditionally denoted
`-coth(W/2)`. It is used instead of introducing a second hyperbolic-function
API. -/
def negCothHalfExp (W : ℂ) : ℂ :=
  (1 + Complex.exp W) / (1 - Complex.exp W)

/-- The exponential half-coth readout is exactly the chosen finite
Berezinian. -/
theorem negCothHalfExp_eq_superCayleyBerezinian (W : ℂ) :
    negCothHalfExp W = superCayleyBerezinian (Complex.exp W) := by
  rw [superCayleyBerezinian_eq]
  rfl

/-- On the punctured bipolar domain, the principal logarithm exponentiates to
`q`, so the finite Berezinian realizes the same readout. -/
theorem negCothHalfExp_bipolarLog
    {s : ℂ} (hs : s ∈ punctured01) :
    negCothHalfExp (bipolarLog s) =
      superCayleyBerezinian (crossRatio01 s) := by
  rw [negCothHalfExp_eq_superCayleyBerezinian,
    exp_bipolarLog hs]

/-- Algebraic reduction of the finite Berezinian to the critical-line pole.
The hypothesis is exactly invertibility of the odd block. -/
theorem superCayleyBerezinian_crossRatio01
    {s : ℂ} (hs : s ∈ punctured01)
    (hcrit : 1 - 2 * s ≠ 0) :
    superCayleyBerezinian (crossRatio01 s) =
      (1 - 2 * s)⁻¹ := by
  rw [superCayleyBerezinian_eq]
  have hden : 1 - s ≠ 0 := one_sub_ne_zero_of_mem hs
  have hodd :
      1 - s / (1 - s) = (1 - 2 * s) / (1 - s) := by
    field_simp [hden]
    ring
  have hodd_ne : 1 - s / (1 - s) ≠ 0 := by
    rw [hodd]
    exact div_ne_zero hcrit hden
  unfold crossRatio01 cayleyToFugacity
  field_simp [hden, hodd_ne, hcrit]
  ring

/-- The odd block is singular exactly when the Cayley coordinate equals one. -/
theorem det_superCayleyOdd_eq_zero_iff (q : ℂ) :
    Matrix.det (superCayleyOdd q) = 0 ↔ q = 1 := by
  rw [superCayleyOdd, det_scalarBlock]
  constructor
  · intro h
    exact (sub_eq_zero.mp h).symm
  · intro h
    rw [h, sub_self]

/-- On the bipolar chart, the odd-block singularity is exactly the affine
critical point `s = 1/2`. -/
theorem det_superCayleyOdd_crossRatio01_eq_zero_iff
    {s : ℂ} (hs : s ∈ punctured01) :
    Matrix.det (superCayleyOdd (crossRatio01 s)) = 0 ↔
      s = (1 / 2 : ℂ) := by
  rw [det_superCayleyOdd_eq_zero_iff]
  have hden : 1 - s ≠ 0 := one_sub_ne_zero_of_mem hs
  constructor
  · intro hq
    have hmul : s = 1 * (1 - s) := by
      apply (div_eq_iff hden).mp
      simpa [crossRatio01, cayleyToFugacity] using hq
    have htwo : s * 2 = 1 := by
      calc
        s * 2 = s + s := by ring
        _ = (1 - s) + s := by
          nth_rewrite 1 [hmul]
          simp
        _ = 1 := by ring
    exact (eq_div_iff (by norm_num : (2 : ℂ) ≠ 0)).2 htwo
  · intro hsHalf
    rw [hsHalf]
    norm_num [crossRatio01, cayleyToFugacity]

/-- Compact finite-supermatrix packet. -/
theorem bipolar_cayley_berezinian_packet
    {s : ℂ} (hs : s ∈ punctured01)
    (hcrit : 1 - 2 * s ≠ 0) :
    negCothHalfExp (bipolarLog s) =
        superCayleyBerezinian (crossRatio01 s) ∧
      superCayleyBerezinian (crossRatio01 s) =
        (1 - 2 * s)⁻¹ := by
  exact ⟨negCothHalfExp_bipolarLog hs,
    superCayleyBerezinian_crossRatio01 hs hcrit⟩

end InfoGeometry.NCG.BipolarCayleyBerezinianRealization
