import InfoGeometry.Twistor.PenroseTwistor
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.Tactic

/-!
# A concrete polynomial realization of the bi-twistor CCR

Source: Penrose, Chapter 7, equations (7.59), (7.82)--(7.90).
The coefficient carrier reuses the repository's complex twistor four-space.
The operators act on the full polynomial algebra, not on a finite-dimensional
matrix space. No commutator relation is postulated. This algebraic model is
not the analytic Hilbert space or Cech cohomology of massless fields.
-/

noncomputable section

namespace InfoGeometry.Twistor.PenrosePolynomialCCR

open InfoGeometry.Twistor.PenroseTwistor
open scoped BigOperators

abbrev Coeff := TwistorCarrier × TwistorCarrier
abbrev WavePolynomial := MvPolynomial (Fin 4) ℂ
abbrev Operator := Module.End ℂ WavePolynomial

/-- Ordinary contraction of a coordinate coefficient and a dual coefficient. -/
def contraction (a b : TwistorCarrier) : ℂ := ∑ i, a i * b i

/-- The linear polynomial with prescribed multiplication coefficients. -/
def linearForm (a : TwistorCarrier) : WavePolynomial :=
  ∑ i, a i • MvPolynomial.X i

/-- Native polynomial derivation specified on the four generators. -/
def directional (b : TwistorCarrier) : Derivation ℂ WavePolynomial WavePolynomial :=
  MvPolynomial.mkDerivation ℂ (fun i => b i • (1 : WavePolynomial))

@[simp] theorem directional_X (b : TwistorCarrier) (j : Fin 4) :
    directional b (MvPolynomial.X j) = b j • (1 : WavePolynomial) := by
  simp [directional]

/-- The displayed derivation is exactly the linear combination of native partials. -/
theorem directional_eq_pderiv_sum (b : TwistorCarrier) :
    directional b = ∑ i : Fin 4, b i • MvPolynomial.pderiv i := by
  apply MvPolynomial.derivation_ext
  intro j
  fin_cases j <;>
    simp [directional, Fin.sum_univ_four, MvPolynomial.pderiv_X, Pi.single_apply]

@[simp] theorem linearForm_add (a b : TwistorCarrier) :
    linearForm (a + b) = linearForm a + linearForm b := by
  simp [linearForm, add_smul, Finset.sum_add_distrib]

@[simp] theorem linearForm_smul (c : ℂ) (a : TwistorCarrier) :
    linearForm (c • a) = c • linearForm a := by
  simp [linearForm, Finset.smul_sum, smul_smul]

@[simp] theorem linearForm_zero : linearForm 0 = 0 := by simp [linearForm]

@[simp] theorem directional_add (a b : TwistorCarrier) :
    directional (a + b) = directional a + directional b := by
  apply MvPolynomial.derivation_ext
  intro j
  simp [add_smul]

@[simp] theorem directional_smul (c : ℂ) (a : TwistorCarrier) :
    directional (c • a) = c • directional a := by
  apply MvPolynomial.derivation_ext
  intro j
  simp [smul_smul]

@[simp] theorem directional_zero : directional 0 = 0 := by
  apply MvPolynomial.derivation_ext
  intro j
  simp

theorem contraction_comm (a b : TwistorCarrier) : contraction a b = contraction b a := by
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem directional_linearForm (a b : TwistorCarrier) :
    directional b (linearForm a) = contraction a b • (1 : WavePolynomial) := by
  simp [linearForm, contraction, map_sum, directional_X, smul_smul, Finset.sum_smul]

theorem directional_mul (b : TwistorCarrier) (p q : WavePolynomial) :
    directional b (p * q) = directional b p * q + p * directional b q := by
  rw [Derivation.leibniz]
  simp only [smul_eq_mul]
  ring

/-- Constant-coefficient partial derivations commute; proved on generators. -/
theorem directional_commute (a b : TwistorCarrier) (p : WavePolynomial) :
    directional a (directional b p) = directional b (directional a p) := by
  have h : ⁅directional a, directional b⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro j
    simp [Derivation.commutator_apply]
  have hp := Derivation.congr_fun h p
  exact sub_eq_zero.mp (by simpa [Derivation.commutator_apply] using hp)

/-- `a_i Z_i + b_i W_i`, with `Z_i = X_i` and `W_i = -h partial_i`. -/
def quantize (h : ℂ) (A : Coeff) : Operator where
  toFun p := linearForm A.1 * p - h • directional A.2 p
  map_add' p q := by simp [mul_add, smul_add] <;> abel
  map_smul' c p := by
    simp [Algebra.mul_smul_comm, smul_sub, smul_smul, mul_comm]

@[simp] theorem quantize_apply (h : ℂ) (A : Coeff) (p : WavePolynomial) :
    quantize h A p = linearForm A.1 * p - h • directional A.2 p := rfl

@[simp] theorem quantize_zero (h : ℂ) : quantize h 0 = 0 := by
  apply LinearMap.ext
  intro p
  simp

@[simp] theorem quantize_add (h : ℂ) (A B : Coeff) :
    quantize h (A + B) = quantize h A + quantize h B := by
  apply LinearMap.ext
  intro p
  simp [add_mul, smul_add] <;> abel

@[simp] theorem quantize_smul (h c : ℂ) (A : Coeff) :
    quantize h (c • A) = c • quantize h A := by
  apply LinearMap.ext
  intro p
  simp [Algebra.smul_mul_assoc, smul_sub, smul_smul, mul_comm]

/-- Canonical alternating pairing of the multiplication/differentiation coefficients. -/
def omega (A B : Coeff) : ℂ := contraction A.1 B.2 - contraction A.2 B.1

theorem omega_skew (A B : Coeff) : omega A B = -omega B A := by
  unfold omega
  rw [contraction_comm B.1 A.2, contraction_comm B.2 A.1]
  ring

/-- Full CCR on arbitrary linear bi-twistors, derived in the polynomial representation. -/
theorem quantize_commutator (h : ℂ) (A B : Coeff) :
    quantize h A * quantize h B - quantize h B * quantize h A =
      (h * omega A B) • (1 : Operator) := by
  apply LinearMap.ext
  intro p
  change quantize h A (quantize h B p) - quantize h B (quantize h A p) =
    (h * omega A B) • p
  simp only [quantize_apply, map_sub, map_smul, directional_mul, directional_linearForm]
  rw [directional_commute B.2 A.2 p, contraction_comm B.1 A.2]
  simp [omega, Algebra.smul_def] <;> ring

/-- Coordinate multiplication operator. -/
def Z (i : Fin 4) : Operator := quantize 1 (Pi.single i 1, 0)

/-- Conjugate polynomial differentiation operator. -/
def W (h : ℂ) (i : Fin 4) : Operator := quantize h (0, Pi.single i 1)

theorem Z_apply (i : Fin 4) (p : WavePolynomial) : Z i p = MvPolynomial.X i * p := by
  simp [Z, linearForm]

theorem W_apply (h : ℂ) (i : Fin 4) (p : WavePolynomial) :
    W h i p = -h • MvPolynomial.pderiv i p := by
  rw [W, quantize_apply, linearForm_zero, directional_eq_pderiv_sum]
  simp

/-- The coordinate CCR are genuine operator equalities, not structure fields. -/
theorem coordinate_CCR (h : ℂ) (i j : Fin 4) :
    Z i * W h j - W h j * Z i = (if i = j then h else 0) • (1 : Operator) := by
  apply LinearMap.ext
  intro p
  simp only [Module.End.mul_apply, LinearMap.sub_apply, Z_apply, W_apply,
    MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X]
  by_cases hij : i = j
  · subst j
    simp [Algebra.smul_def, Pi.single_apply] <;> ring
  · simp [hij, Ne.symm hij, Algebra.smul_def, Pi.single_apply] <;> ring

/-- Multiplication coordinates commute in the actual polynomial model. -/
theorem coordinate_ZZ (i j : Fin 4) : Z i * Z j = Z j * Z i := by
  apply LinearMap.ext
  intro p
  simp only [Module.End.mul_apply, Z_apply]
  ring

/-- Differentiation coordinates also commute; no second CCR is assumed. -/
theorem coordinate_WW (h : ℂ) (i j : Fin 4) : W h i * W h j = W h j * W h i := by
  have hh := quantize_commutator h (0, Pi.single i 1) (0, Pi.single j 1)
  have ho : omega (0, Pi.single i 1) (0, Pi.single j 1) = 0 := by
    simp [omega, contraction]
  rw [ho, mul_zero, zero_smul] at hh
  exact sub_eq_zero.mp hh

/-- The six-term alternating operator product from equation (7.89). -/
def operatorTriple (A B C : Operator) : Operator :=
  Complex.I • (A * B * C + B * C * A + C * A * B -
    A * C * B - B * A * C - C * B * A)

/-- Rewriting the six products uses only associativity of operator composition. -/
theorem operatorTriple_commutators (A B C : Operator) :
    operatorTriple A B C = Complex.I •
      (A * (B * C) - A * (C * B) + B * (C * A) - B * (A * C) +
        C * (A * B) - C * (B * A)) := by
  unfold operatorTriple
  congr 1
  simp only [mul_assoc]
  abel

private theorem alternating_factor (A B C : Operator) :
    A * (B * C) - A * (C * B) + B * (C * A) - B * (A * C) +
        C * (A * B) - C * (B * A) =
      A * (B * C - C * B) + B * (C * A - A * C) +
        C * (A * B - B * A) := by
  simp only [mul_sub]
  abel

/-- Coefficient readout of the CCR-reduced triple; not an octonion associator. -/
def coefficientTriple (h : ℂ) (A B C : Coeff) : Coeff :=
  (Complex.I * h) • (omega B C • A + omega C A • B + omega A B • C)

/-- Every cubic operator term cancels, yielding an actual linear bi-twistor. -/
theorem quantize_triple (h : ℂ) (A B C : Coeff) :
    operatorTriple (quantize h A) (quantize h B) (quantize h C) =
      quantize h (coefficientTriple h A B C) := by
  rw [operatorTriple_commutators]
  rw [alternating_factor]
  rw [quantize_commutator, quantize_commutator, quantize_commutator]
  simp [coefficientTriple, Algebra.mul_smul_comm, smul_add,
    smul_smul, mul_assoc]

/-- On coefficient triples the displayed deformation vanishes at `h = 0`. -/
theorem coefficientTriple_zero (A B C : Coeff) : coefficientTriple 0 A B C = 0 := by
  simp [coefficientTriple]

end InfoGeometry.Twistor.PenrosePolynomialCCR
