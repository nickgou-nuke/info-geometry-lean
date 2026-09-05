import InfoGeometry.Twistor.PenrosePolynomialCCR
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The signed real bi-twistor carrier behind the CCR triple

The real form of the twistor Hermitian space has signature (4,4).
We reuse the repository's signature-(2,2) `twistorHermitian`, not the
unrelated positive-definite `Physics.PenroseTwistor.twistorDot`.

In this diagonal spin frame, twistor conjugation into the dual includes the
sign matrix diag(1,1,-1,-1). The map into the eight-complex-dimensional
coefficient space therefore has lower coefficients `epsilon_i conj(z_i)`.
The phase operation is real-linear and preserves this signed reality.
-/

noncomputable section

namespace InfoGeometry.Twistor.PenroseSignedCCRGeometry

open InfoGeometry.Twistor.PenroseTwistor
open InfoGeometry.Twistor.PenrosePolynomialCCR

/-- Real-linear scalar complex structure on the existing twistor carrier. -/
def phaseJ : TwistorCarrier →ₗ[ℝ] TwistorCarrier where
  toFun z := fun i => Complex.I * z i
  map_add' z w := by funext i; simp [mul_add]
  map_smul' r z := by funext i; apply Complex.ext <;> simp

/-- Twice the real part of the existing Hermitian form: the chapter's unit has norm 2. -/
def metric : LinearMap.BilinForm ℝ TwistorCarrier := 2 • twistorRealBilinear

@[simp] theorem metric_apply (z w : TwistorCarrier) :
    metric z w = 2 * (twistorHermitian z w).re := rfl

/-- Symplectic form determined by the real metric and the complex structure. -/
def symplectic (z w : TwistorCarrier) : ℝ := -metric z (phaseJ w)

theorem symplectic_eq_im (z w : TwistorCarrier) :
    symplectic z w = 2 * (twistorHermitian z w).im := by
  simp [symplectic, phaseJ, twistorHermitian_apply, Fin.sum_univ_four,
    Complex.mul_re, Complex.mul_im] <;> ring

@[simp] theorem phaseJ_sq (z : TwistorCarrier) : phaseJ (phaseJ z) = -z := by
  funext i
  simp [phaseJ, ← mul_assoc, Complex.I_sq]

theorem metric_symm (z w : TwistorCarrier) : metric z w = metric w z := by
  simp [twistorHermitian_apply, Fin.sum_univ_four, Complex.mul_re] <;> ring

theorem metric_phaseJ (z w : TwistorCarrier) : metric (phaseJ z) (phaseJ w) = metric z w := by
  simp [phaseJ, twistorHermitian_apply, Fin.sum_univ_four,
    Complex.mul_re, Complex.mul_im] <;> ring

theorem symplectic_skew (z w : TwistorCarrier) : symplectic z w = -symplectic w z := by
  simp [symplectic_eq_im, twistorHermitian_apply, Fin.sum_univ_four,
    Complex.mul_im] <;> ring

@[simp] theorem symplectic_self (z : TwistorCarrier) : symplectic z z = 0 := by
  have h := symplectic_skew z z
  linarith

theorem symplectic_phaseJ (z w : TwistorCarrier) :
    symplectic (phaseJ z) (phaseJ w) = symplectic z w := by
  unfold symplectic
  rw [metric_phaseJ]

/-- Native real quadratic form, with the explicit (4,4) coordinate signs. -/
theorem quadratic_signature (z : TwistorCarrier) :
    twistorRealQuadraticForm z =
      (z 0).re ^ 2 + (z 0).im ^ 2 + (z 1).re ^ 2 + (z 1).im ^ 2 -
      ((z 2).re ^ 2 + (z 2).im ^ 2 + (z 3).re ^ 2 + (z 3).im ^ 2) := by
  simp [twistorRealQuadraticForm_apply, helicity, twistorHermitian_apply,
    Fin.sum_univ_four, Complex.mul_re] <;> ring

theorem real_carrier_finrank : Module.finrank ℝ TwistorCarrier = 8 := by
  simp [TwistorCarrier, Module.finrank_pi_fintype]

theorem metric_self (z : TwistorCarrier) :
    metric z z = 2 * twistorRealQuadraticForm z := by
  rw [metric_apply, twistorRealQuadraticForm_apply]
  rfl

/-- Dual-conjugation sign in the chosen diagonal Hermitian frame. -/
def dualSign (i : Fin 4) : ℂ := if i.val < 2 then 1 else -1

/-- Signed real bi-twistors inside the complex coefficient pair. -/
def signedPair : TwistorCarrier →ₗ[ℝ] Coeff where
  toFun z := (z, fun i => dualSign i * star (z i))
  map_add' z w := by
    apply Prod.ext
    · rfl
    · funext i; simp [mul_add]
  map_smul' r z := by
    apply Prod.ext
    · rfl
    · funext i; apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

/-- The coefficient-frame form of the chapter's complex-structure operation. -/
def coefficientJ (A : Coeff) : Coeff :=
  (fun i => Complex.I * A.1 i, fun i => -Complex.I * A.2 i)

theorem signedPair_phaseJ (z : TwistorCarrier) :
    signedPair (phaseJ z) = coefficientJ (signedPair z) := by
  apply Prod.ext
  · rfl
  · funext i; apply Complex.ext <;>
      simp [signedPair, phaseJ, coefficientJ, Complex.mul_re, Complex.mul_im] <;> ring

/-- The coefficient-frame embedding is injective. -/
theorem signedPair_injective : Function.Injective signedPair := by
  intro z w h
  exact congrArg Prod.fst h

/-- The CCR pairing, multiplied by `i`, is the real symplectic form. -/
theorem imaginary_omega_signed (z w : TwistorCarrier) :
    Complex.I * omega (signedPair z) (signedPair w) = (symplectic z w : ℂ) := by
  apply Complex.ext <;>
    simp [omega, contraction, signedPair, dualSign, symplectic_eq_im,
      twistorHermitian_apply, Fin.sum_univ_four, Complex.mul_re, Complex.mul_im] <;> ring

/-- The intended scalar product in (7.97) is obtained by the CCR commutator with `J`. -/
theorem imaginary_omega_phaseJ (z w : TwistorCarrier) :
    Complex.I * omega (signedPair z) (signedPair (phaseJ w)) = (metric z w : ℂ) := by
  rw [imaginary_omega_signed]
  unfold symplectic
  rw [phaseJ_sq]
  simp

/-- The reduced real triple that follows from the literal six-term CCR alternation. -/
def realTriple (x y z : TwistorCarrier) : TwistorCarrier :=
  symplectic y z • x + symplectic z x • y + symplectic x y • z

private theorem ofReal_smul_coeff (r : ℝ) (A : Coeff) : (r : ℂ) • A = r • A := by
  apply Prod.ext <;> funext i <;> apply Complex.ext <;> simp

/-- Reality of the reduced coefficient triple, proved with the signed embedding. -/
theorem signedPair_triple (x y z : TwistorCarrier) :
    coefficientTriple 1 (signedPair x) (signedPair y) (signedPair z) =
      signedPair (realTriple x y z) := by
  simp only [coefficientTriple, mul_one, smul_add, smul_smul,
    imaginary_omega_signed, ofReal_smul_coeff]
  simp [realTriple]

/-- Closure as an equality in the concrete polynomial operator algebra. -/
theorem realTriple_operator_closure (x y z : TwistorCarrier) :
    operatorTriple (quantize 1 (signedPair x)) (quantize 1 (signedPair y))
        (quantize 1 (signedPair z)) = quantize 1 (signedPair (realTriple x y z)) := by
  rw [quantize_triple, signedPair_triple]

/-- Central CCR alone supply this contraction triple, not a 7D vector cross product. -/
theorem realTriple_repeated (x y : TwistorCarrier) : realTriple x x y = 0 := by
  rw [realTriple, symplectic_skew y x, symplectic_self]
  simp

end InfoGeometry.Twistor.PenroseSignedCCRGeometry
