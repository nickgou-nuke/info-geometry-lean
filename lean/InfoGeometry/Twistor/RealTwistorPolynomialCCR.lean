/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FiniteDimensionalCCRNoGo
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Intrinsically real polynomial twistor quantization

The algebraic wavefunctions are `MvPolynomial ι ℝ`.  In particular, `ι = Fin 4`
gives a real four-coordinate twistor realization.  The coefficient field and
operator algebra are real throughout; no restriction of scalars is used.

The construction is the real, arbitrary-finite-coordinate counterpart of
`PenrosePolynomialCCR`.  It derives the canonical commutation relations from
native polynomial multiplication and differentiation.  For a nonempty
coordinate set, the representation is infinite dimensional.  The number
operator identities below are algebraic degree identities, not a claim about
physical helicity, a Hilbert completion, or a Penrose transform.
-/

noncomputable section

namespace InfoGeometry.Twistor.RealPolynomialCCR

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev Coordinates (ι : Type*) := ι → ℝ
abbrev Coeff (ι : Type*) := Coordinates ι × Coordinates ι
abbrev WavePolynomial (ι : Type*) := MvPolynomial ι ℝ
abbrev Operator (ι : Type*) := Module.End ℝ (WavePolynomial ι)

/-- Evaluation of coordinate coefficients against dual coordinate coefficients. -/
def contraction (a b : Coordinates ι) : ℝ := ∑ i, a i * b i

/-- Multiplication by a linear polynomial. -/
def linearForm (a : Coordinates ι) : WavePolynomial ι :=
  ∑ i, a i • MvPolynomial.X i

/-- Constant-coefficient derivation, constructed by the universal property. -/
def directional (b : Coordinates ι) :
    Derivation ℝ (WavePolynomial ι) (WavePolynomial ι) :=
  MvPolynomial.mkDerivation ℝ (fun i => b i • (1 : WavePolynomial ι))

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem directional_X (b : Coordinates ι) (j : ι) :
    directional b (MvPolynomial.X j) = b j • (1 : WavePolynomial ι) := by
  simp [directional]

theorem directional_eq_pderiv_sum (b : Coordinates ι) :
    directional b = ∑ i, b i • MvPolynomial.pderiv i := by
  apply MvPolynomial.derivation_ext
  intro j
  simp [directional, MvPolynomial.pderiv_X, Pi.single_apply]

omit [DecidableEq ι] in
@[simp] theorem linearForm_add (a b : Coordinates ι) :
    linearForm (a + b) = linearForm a + linearForm b := by
  simp [linearForm, add_smul, Finset.sum_add_distrib]

omit [DecidableEq ι] in
@[simp] theorem linearForm_smul (c : ℝ) (a : Coordinates ι) :
    linearForm (c • a) = c • linearForm a := by
  simp [linearForm, Finset.smul_sum, smul_smul]

omit [DecidableEq ι] in
@[simp] theorem linearForm_zero : linearForm (0 : Coordinates ι) = 0 := by
  simp [linearForm]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem directional_add (a b : Coordinates ι) :
    directional (a + b) = directional a + directional b := by
  apply MvPolynomial.derivation_ext
  intro j
  simp [add_smul]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem directional_smul (c : ℝ) (a : Coordinates ι) :
    directional (c • a) = c • directional a := by
  apply MvPolynomial.derivation_ext
  intro j
  simp [smul_smul]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem directional_zero : directional (0 : Coordinates ι) = 0 := by
  apply MvPolynomial.derivation_ext
  intro j
  simp

omit [DecidableEq ι] in
theorem contraction_comm (a b : Coordinates ι) : contraction a b = contraction b a := by
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

omit [DecidableEq ι] in
theorem directional_linearForm (a b : Coordinates ι) :
    directional b (linearForm a) = contraction a b • (1 : WavePolynomial ι) := by
  simp [linearForm, contraction, map_sum, smul_smul, Finset.sum_smul]

omit [Fintype ι] [DecidableEq ι] in
theorem directional_mul (b : Coordinates ι) (p q : WavePolynomial ι) :
    directional b (p * q) = directional b p * q + p * directional b q := by
  rw [Derivation.leibniz]
  simp only [smul_eq_mul]
  ring

omit [Fintype ι] [DecidableEq ι] in
theorem directional_commute (a b : Coordinates ι) (p : WavePolynomial ι) :
    directional a (directional b p) = directional b (directional a p) := by
  have h : ⁅directional a, directional b⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro j
    simp [Derivation.commutator_apply]
  have hp := Derivation.congr_fun h p
  exact sub_eq_zero.mp (by simpa [Derivation.commutator_apply] using hp)

/-- The real Weyl operator `a · X - h b · ∂`. -/
def quantize (h : ℝ) (A : Coeff ι) : Operator ι where
  toFun p := linearForm A.1 * p - h • directional A.2 p
  map_add' p q := by simp [mul_add, smul_add]; abel
  map_smul' c p := by
    simp [smul_sub, smul_smul, mul_comm]

omit [DecidableEq ι] in
@[simp] theorem quantize_apply (h : ℝ) (A : Coeff ι) (p : WavePolynomial ι) :
    quantize h A p = linearForm A.1 * p - h • directional A.2 p := rfl

omit [DecidableEq ι] in
@[simp] theorem quantize_zero (h : ℝ) : quantize h (0 : Coeff ι) = 0 := by
  apply LinearMap.ext
  intro p
  simp

omit [DecidableEq ι] in
@[simp] theorem quantize_add (h : ℝ) (A B : Coeff ι) :
    quantize h (A + B) = quantize h A + quantize h B := by
  apply LinearMap.ext
  intro p
  simp [add_mul, smul_add]; abel

omit [DecidableEq ι] in
@[simp] theorem quantize_smul (h c : ℝ) (A : Coeff ι) :
    quantize h (c • A) = c • quantize h A := by
  apply LinearMap.ext
  intro p
  simp [smul_sub, smul_smul, mul_comm]

/-- Alternating pairing; this is distinct from a symmetric Krein form. -/
def omega (A B : Coeff ι) : ℝ := contraction A.1 B.2 - contraction A.2 B.1

omit [DecidableEq ι] in
theorem omega_skew (A B : Coeff ι) : omega A B = -omega B A := by
  unfold omega
  rw [contraction_comm B.1 A.2, contraction_comm B.2 A.1]
  ring

omit [DecidableEq ι] in
@[simp] theorem omega_self (A : Coeff ι) : omega A A = 0 := by
  simp [omega, contraction_comm A.2 A.1]

omit [DecidableEq ι] in
/-- Exact CCR on the full real polynomial module. -/
theorem quantize_commutator (h : ℝ) (A B : Coeff ι) :
    quantize h A * quantize h B - quantize h B * quantize h A =
      (h * omega A B) • (1 : Operator ι) := by
  apply LinearMap.ext
  intro p
  change quantize h A (quantize h B p) - quantize h B (quantize h A p) =
    (h * omega A B) • p
  simp only [quantize_apply, map_sub, map_smul, directional_mul, directional_linearForm]
  rw [directional_commute B.2 A.2 p, contraction_comm B.1 A.2]
  simp [omega, Algebra.smul_def]; ring

def create (i : ι) : Operator ι := quantize 1 (Pi.single i 1, 0)

def annihilate (i : ι) : Operator ι := (MvPolynomial.pderiv i).toLinearMap

@[simp] theorem create_apply (i : ι) (p : WavePolynomial ι) :
    create i p = MvPolynomial.X i * p := by
  simp [create, linearForm]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem annihilate_apply (i : ι) (p : WavePolynomial ι) :
    annihilate i p = MvPolynomial.pderiv i p := rfl

/-- The usual positive-sign creation/annihilation convention. -/
theorem annihilate_create_commutator (i j : ι) :
    annihilate i * create j - create j * annihilate i =
      (if i = j then 1 else 0 : ℝ) • (1 : Operator ι) := by
  apply LinearMap.ext
  intro p
  simp only [Module.End.mul_apply, LinearMap.sub_apply, create_apply, annihilate_apply,
    MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X]
  by_cases h : i = j
  · subst j
    simp
  · simp [h, Ne.symm h]

theorem create_commute (i j : ι) : create i * create j = create j * create i := by
  apply LinearMap.ext
  intro p
  simp only [Module.End.mul_apply, create_apply]
  ring

omit [Fintype ι] [DecidableEq ι] in
theorem annihilate_commute (i j : ι) :
    annihilate i * annihilate j = annihilate j * annihilate i := by
  classical
  have hij : ⁅MvPolynomial.pderiv (R := ℝ) i, MvPolynomial.pderiv (R := ℝ) j⁆ =
      (0 : Derivation ℝ (WavePolynomial ι) (WavePolynomial ι)) := by
    apply MvPolynomial.derivation_ext
    intro k
    simp only [Derivation.commutator_apply, MvPolynomial.pderiv_X, Pi.single_apply]
    split_ifs <;> simp
  apply LinearMap.ext
  intro p
  have hp := Derivation.congr_fun hij p
  exact sub_eq_zero.mp (by simpa [Derivation.commutator_apply] using hp)

/-- Each occupation operator is an actual composition of the polynomial operators. -/
def number (i : ι) : Operator ι := create i * annihilate i

theorem number_monomial (i : ι) (m : ι →₀ ℕ) (a : ℝ) :
    number i (MvPolynomial.monomial m a) =
      m i • MvPolynomial.monomial m a := by
  change create i (annihilate i (MvPolynomial.monomial m a)) = _
  rw [create_apply, annihilate_apply]
  exact MvPolynomial.X_mul_pderiv_monomial (R := ℝ)

/-- Euler operator, defined from the finite coordinate sum. -/
def euler : Operator ι := ∑ i, number i

theorem euler_monomial (m : ι →₀ ℕ) (a : ℝ) :
    euler (MvPolynomial.monomial m a) =
      (∑ i, m i) • MvPolynomial.monomial m a := by
  simp only [euler, LinearMap.sum_apply, number_monomial, Finset.sum_smul]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem annihilate_vacuum (i : ι) :
    annihilate i (1 : WavePolynomial ι) = 0 := by
  simp

omit [Fintype ι] [DecidableEq ι] in
/-- The representation is nonzero: the vacuum is a genuine nonzero polynomial. -/
theorem vacuum_ne_zero : (1 : WavePolynomial ι) ≠ 0 := one_ne_zero

/-- A coordinate commutator acts as identity on a nonzero vacuum. -/
theorem vacuum_CCR (i : ι) :
    (annihilate i * create i - create i * annihilate i) (1 : WavePolynomial ι) = 1 := by
  rw [annihilate_create_commutator]
  simp

/-- Exact CCR preclude a finite-dimensional carrier as soon as there is a mode. -/
theorem wavePolynomial_not_finiteDimensional [Nonempty ι] :
    ¬ FiniteDimensional ℝ (WavePolynomial ι) := by
  intro h
  let _ := h
  let i : ι := Classical.choice ‹Nonempty ι›
  apply InfoGeometry.Canonical.FiniteDimensionalCCRNoGo.commutator_ne_scalar_smul_one
    (annihilate i) (create i) (1 : ℝ) one_ne_zero
  simpa using annihilate_create_commutator i i

end InfoGeometry.Twistor.RealPolynomialCCR
