import InfoGeometry.Twistor.PenrosePolynomialCCR

/-!
# Polynomial CCR for arbitrarily many twistor constituents

The carrier is the full native polynomial algebra. Multiplication and
partial differentiation are actual endomorphisms, not assumed CCR data.
The generic operators recover the existing single-twistor owner exactly.
No Hilbert completion or analytic-adjoint claim is made.
-/

noncomputable section
namespace InfoGeometry.Twistor.TwistorConstituentCCR

open scoped BigOperators Classical
variable {ι : Type*}

abbrev PolynomialSpace (ι : Type*) := MvPolynomial ι ℂ
abbrev PolynomialOperator (ι : Type*) := Module.End ℂ (PolynomialSpace ι)

def creation (i : ι) : PolynomialOperator ι where
  toFun p := MvPolynomial.X i * p
  map_add' p q := mul_add _ _ _
  map_smul' c p := by simp [Algebra.mul_smul_comm]

def derivative (i : ι) : PolynomialOperator ι := (MvPolynomial.pderiv i).toLinearMap

@[simp] theorem creation_apply (i : ι) (p : PolynomialSpace ι) :
    creation i p = MvPolynomial.X i * p := rfl

@[simp] theorem derivative_apply (i : ι) (p : PolynomialSpace ι) :
    derivative i p = MvPolynomial.pderiv i p := rfl

def conjugateCoordinate (h : ℂ) (i : ι) : PolynomialOperator ι := -(h • derivative i)

@[simp] theorem conjugateCoordinate_apply (h : ℂ) (i : ι) (p : PolynomialSpace ι) :
    conjugateCoordinate h i p = -h • MvPolynomial.pderiv i p := by
  simp [conjugateCoordinate]

theorem partials_commute (i j : ι) (p : PolynomialSpace ι) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j p) =
      MvPolynomial.pderiv j (MvPolynomial.pderiv i p) := by
  have hd : ⁅(MvPolynomial.pderiv i : Derivation ℂ (PolynomialSpace ι) (PolynomialSpace ι)),
      MvPolynomial.pderiv j⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro k
    simp [Derivation.commutator_apply, MvPolynomial.pderiv_X]
  have hp := Derivation.congr_fun hd p
  exact sub_eq_zero.mp (by simpa [Derivation.commutator_apply] using hp)

theorem creation_commute (i j : ι) : creation i * creation j = creation j * creation i := by
  apply LinearMap.ext
  intro p
  simp only [Module.End.mul_apply, creation_apply]
  ring

theorem derivative_commute (i j : ι) : derivative i * derivative j = derivative j * derivative i := by
  apply LinearMap.ext
  intro p
  exact partials_commute i j p

/-- Derived from Leibniz and the values on polynomial generators. -/
theorem coordinate_CCR (h : ℂ) (i j : ι) :
    creation i * conjugateCoordinate h j - conjugateCoordinate h j * creation i =
      (if i = j then h else 0) • (1 : PolynomialOperator ι) := by
  apply LinearMap.ext
  intro p
  simp only [Module.End.mul_apply, LinearMap.sub_apply, creation_apply,
    conjugateCoordinate_apply, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X]
  by_cases hij : i = j
  · subst j
    simp [Algebra.smul_def]; ring
  · simp [hij, Algebra.smul_def]; ring

def quadratic (i j : ι) : PolynomialOperator ι := creation i * derivative j

@[simp] theorem quadratic_apply (i j : ι) (p : PolynomialSpace ι) :
    quadratic i j p = MvPolynomial.X i * MvPolynomial.pderiv j p := rfl

/-- Full matrix-unit Lie relation in the polynomial endomorphism algebra. -/
theorem quadratic_commutator (i j k l : ι) :
    quadratic i j * quadratic k l - quadratic k l * quadratic i j =
      (if j = k then quadratic i l else 0) -
        (if l = i then quadratic k j else 0) := by
  apply LinearMap.ext
  intro p
  simp only [Module.End.mul_apply, LinearMap.sub_apply, quadratic_apply,
    MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X]
  rw [partials_commute j l p]
  by_cases hjk : j = k <;> by_cases hli : l = i <;>
    simp [hjk, hli, Eq.comm, quadratic_apply] <;> ring

theorem creation_eq_existing (i : Fin 4) : creation i = PenrosePolynomialCCR.Z i := by
  apply LinearMap.ext
  intro p
  exact (PenrosePolynomialCCR.Z_apply i p).symm

theorem conjugateCoordinate_eq_existing (h : ℂ) (i : Fin 4) :
    conjugateCoordinate h i = PenrosePolynomialCCR.W h i := by
  apply LinearMap.ext
  intro p
  simp only [conjugateCoordinate_apply, PenrosePolynomialCCR.W_apply]

abbrev ConstituentPolynomial (n : ℕ) := PolynomialSpace (Fin n × Fin 4)
abbrev ConstituentOperator (n : ℕ) := PolynomialOperator (Fin n × Fin 4)

/-- Perjes (6.13), including the constituent Kronecker delta. -/
theorem constituent_CCR (n : ℕ) (h : ℂ) (i j : Fin n) (a b : Fin 4) :
    creation (i, a) * conjugateCoordinate h (j, b) -
      conjugateCoordinate h (j, b) * creation (i, a) =
        (if i = j ∧ a = b then h else 0) • (1 : ConstituentOperator n) := by
  simpa only [Prod.mk.injEq] using coordinate_CCR h (i, a) (j, b)

theorem distinct_constituents_commute (n : ℕ) (h : ℂ) (i j : Fin n)
    (hij : i ≠ j) (a b : Fin 4) :
    creation (i, a) * conjugateCoordinate h (j, b) =
      conjugateCoordinate h (j, b) * creation (i, a) := by
  have hh := constituent_CCR n h i j a b
  simp only [hij, false_and, ite_false, zero_smul] at hh
  exact sub_eq_zero.mp hh

/-- A nonzero central CCR cannot be a commuting representation. -/
theorem coordinate_noncommuting (h : ℂ) (hh : h ≠ 0) (i : ι) :
    creation i * conjugateCoordinate h i ≠ conjugateCoordinate h i * creation i := by
  intro hc
  have he := coordinate_CCR h i i
  rw [hc, sub_self, ite_eq_left rfl] at he
  have hp := congrArg (fun T : PolynomialOperator ι => T 1) he
  have hz : (MvPolynomial.C h : PolynomialSpace ι) = 0 := by
    simpa [Algebra.smul_def] using hp.symm
  exact hh (by simpa using congrArg (MvPolynomial.eval (fun _ : ι => (0 : ℂ))) hz)

end InfoGeometry.Twistor.TwistorConstituentCCR
