import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic

/-!
# Finite logarithmic translation operators

This is the finite algebraic shadow of the logarithmic-scale translation
operator used in spectral-operator constructions.  It proves only the shift
semigroup law and the readout on exponential test functions; no unbounded
operator, functional calculus, spectrum, or zeta statement is made.
-/

noncomputable section

namespace InfoGeometry.Analysis.FiniteDirichletShiftOperatorBridge

open scoped BigOperators

abbrev ScaleFunctions := ℝ → ℂ
abbrev ScaleEnd := ScaleFunctions →ₗ[ℂ] ScaleFunctions

/-- Translation by a logarithmic scale increment. -/
def translationShift (u : ℝ) : ScaleEnd where
  toFun f t := f (t - u)
  map_add' f g := by
    ext t
    simp
  map_smul' c f := by
    ext t
    simp

@[simp] theorem translationShift_apply (u : ℝ) (f : ScaleFunctions) (t : ℝ) :
    translationShift u f t = f (t - u) := rfl

theorem translationShift_zero : translationShift 0 = 1 := by
  ext f t
  simp [translationShift]

theorem translationShift_add (u v : ℝ) :
    translationShift u * translationShift v = translationShift (u + v) := by
  ext f t
  simp [translationShift, sub_eq_add_neg, add_assoc, add_comm]

theorem translationShift_neg_mul (u : ℝ) :
    translationShift (-u) * translationShift u = 1 := by
  rw [translationShift_add]
  simpa using translationShift_zero

theorem translationShift_mul_neg (u : ℝ) :
    translationShift u * translationShift (-u) = 1 := by
  rw [translationShift_add]
  simpa using translationShift_zero

noncomputable def translationShiftEquiv (u : ℝ) :
    ScaleFunctions ≃ₗ[ℂ] ScaleFunctions where
  toFun := translationShift u
  invFun := translationShift (-u)
  left_inv := by
    intro f
    funext t
    simp [translationShift]
  right_inv := by
    intro f
    funext t
    simp [translationShift]
  map_add' := (translationShift u).map_add
  map_smul' := (translationShift u).map_smul

@[simp] theorem translationShiftEquiv_apply
    (u : ℝ) (f : ScaleFunctions) (t : ℝ) :
    translationShiftEquiv u f t = f (t - u) := rfl

theorem translationShiftEquiv_neg (u : ℝ) :
    translationShiftEquiv (-u) = (translationShiftEquiv u).symm := by
  ext f t
  simp [translationShiftEquiv, translationShift]

theorem translationShiftEquiv_add (u v : ℝ) :
    (translationShiftEquiv v).trans (translationShiftEquiv u) =
      translationShiftEquiv (u + v) := by
  ext f t
  simp [translationShiftEquiv, translationShift, sub_eq_add_neg,
    add_assoc, add_comm]

noncomputable def translationShiftUnit (u : ℝ) : ScaleEndˣ where
  val := translationShift u
  inv := translationShift (-u)
  val_inv := translationShift_mul_neg u
  inv_val := translationShift_neg_mul u

@[simp] theorem translationShiftUnit_val (u : ℝ) :
    (translationShiftUnit u : ScaleEnd) = translationShift u := rfl

noncomputable def translationShiftUnitHom :
    Multiplicative ℝ →* ScaleEndˣ where
  toFun u := translationShiftUnit u
  map_one' := by
    apply Units.ext
    simpa using translationShift_zero
  map_mul' u v := by
    apply Units.ext
    change translationShift (u.toAdd + v.toAdd) =
      translationShift u.toAdd * translationShift v.toAdd
    exact (translationShift_add u.toAdd v.toAdd).symm

@[simp] theorem translationShiftUnitHom_apply (u : ℝ) :
    translationShiftUnitHom (Multiplicative.ofAdd u) =
      translationShiftUnit u := rfl

theorem translationShift_log_mul
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    translationShift (Real.log ((m * n : ℕ) : ℝ)) =
      translationShift (Real.log (m : ℝ)) *
        translationShift (Real.log (n : ℝ)) := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hlog : Real.log ((m * n : ℕ) : ℝ) =
      Real.log (m : ℝ) + Real.log (n : ℝ) := by
    push_cast
    exact Real.log_mul (ne_of_gt hm_pos) (ne_of_gt hn_pos)
  rw [hlog]
  exact (translationShift_add _ _).symm

theorem translationShiftUnitHom_log_mul
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    translationShiftUnitHom
        (Multiplicative.ofAdd (Real.log ((m * n : ℕ) : ℝ))) =
      translationShiftUnitHom (Multiplicative.ofAdd (Real.log (m : ℝ))) *
        translationShiftUnitHom (Multiplicative.ofAdd (Real.log (n : ℝ))) := by
  apply Units.ext
  change translationShift (Real.log ((m * n : ℕ) : ℝ)) =
    translationShift (Real.log (m : ℝ)) * translationShift (Real.log (n : ℝ))
  exact translationShift_log_mul m n hm hn

/-! ## Positive-natural multiplicative packaging -/

/- The logarithmic shifts form a genuine multiplicative representation of the
positive natural numbers.  The positivity subtype is essential: `log 0` is
defined in Mathlib, but it is not the arithmetic logarithmic shift intended
here. -/
noncomputable def positiveNatTranslationShiftUnitHom : ℕ+ →* ScaleEndˣ where
  toFun n := translationShiftUnit (Real.log (n.1 : ℝ))
  map_one' := by
    apply Units.ext
    simpa [translationShiftUnit] using translationShift_zero
  map_mul' := by
    intro m n
    apply Units.ext
    change translationShift (Real.log ((m.1 * n.1 : ℕ) : ℝ)) =
      translationShift (Real.log (m.1 : ℝ)) *
        translationShift (Real.log (n.1 : ℝ))
    exact translationShift_log_mul m.1 n.1 m.2 n.2

@[simp] theorem positiveNatTranslationShiftUnitHom_apply (n : ℕ+) :
    positiveNatTranslationShiftUnitHom n =
      translationShiftUnit (Real.log (n.1 : ℝ)) := rfl

/-- Exponential test family in logarithmic coordinates. -/
def exponentialTest (s : ℂ) : ScaleFunctions :=
  fun t => Complex.exp (s * (t : ℂ))

theorem translationShift_exponentialTest (s : ℂ) (u t : ℝ) :
    translationShift u (exponentialTest s) t =
      Complex.exp (-s * (u : ℂ)) * exponentialTest s t := by
  rw [translationShift_apply]
  unfold exponentialTest
  rw [show s * ((t - u : ℝ) : ℂ) = (-s * (u : ℂ)) + s * (t : ℂ) by
    push_cast
    ring]
  rw [Complex.exp_add]

theorem positiveNatTranslationShiftUnitHom_exponentialTest
    (n : ℕ+) (s : ℂ) :
    (positiveNatTranslationShiftUnitHom n : ScaleEnd)
        (exponentialTest s) =
      Complex.exp (-(s * (Real.log (n.1 : ℝ) : ℂ))) •
        exponentialTest s := by
  change translationShift (Real.log (n.1 : ℝ)) (exponentialTest s) =
    Complex.exp (-(s * (Real.log (n.1 : ℝ) : ℂ))) •
      exponentialTest s
  ext t
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [translationShift_exponentialTest]
  rw [show -s * (Real.log (n.1 : ℝ) : ℂ) =
    -(s * (Real.log (n.1 : ℝ) : ℂ)) by ring]

theorem translationShift_exponentialTest_amplitude_phase
    (σ E u t : ℝ) :
    translationShift u
        (exponentialTest ((σ : ℂ) + Complex.I * (E : ℂ))) t =
      (Real.exp (-σ * u) : ℂ) *
          Complex.exp (-Complex.I * (E : ℂ) * (u : ℂ)) *
        exponentialTest ((σ : ℂ) + Complex.I * (E : ℂ)) t := by
  rw [translationShift_exponentialTest]
  have hsplit :
      -((σ : ℂ) + Complex.I * (E : ℂ)) * (u : ℂ) =
        ((-σ * u : ℝ) : ℂ) +
          (-Complex.I * (E : ℂ) * (u : ℂ)) := by
    push_cast
    ring
  rw [hsplit, Complex.exp_add, ← Complex.ofReal_exp]

/-- The finite Dirichlet shift operator, indexed by `1 ≤ n ≤ N + 1`. -/
def finiteDirichletShift (N : ℕ) : ScaleEnd :=
  Finset.sum (Finset.range (N + 1))
    (fun n => translationShift (Real.log (Nat.succ n : ℕ)))

theorem finiteDirichletShift_apply (N : ℕ) (f : ScaleFunctions) (t : ℝ) :
    finiteDirichletShift N f t =
      Finset.sum (Finset.range (N + 1))
        (fun n => translationShift (Real.log (Nat.succ n : ℕ)) f t) := by
  simp [finiteDirichletShift]

theorem finiteDirichletShift_exponentialTest (N : ℕ) (s : ℂ) (t : ℝ) :
    finiteDirichletShift N (exponentialTest s) t =
      Finset.sum (Finset.range (N + 1))
        (fun n => Complex.exp (-s * (Real.log (Nat.succ n : ℕ) : ℂ))) *
        exponentialTest s t := by
  rw [finiteDirichletShift_apply]
  simp_rw [translationShift_exponentialTest]
  rw [Finset.sum_mul]

/-- The finite Möbius-weighted logarithmic shift operator. -/
def finiteMobiusShift (N : ℕ) : ScaleEnd :=
  Finset.sum (Finset.range (N + 1))
    (fun n =>
      ((ArithmeticFunction.moebius (Nat.succ n) : ℤ) : ℂ) •
        translationShift (Real.log (Nat.succ n : ℕ)))

theorem finiteMobiusShift_exponentialTest (N : ℕ) (s : ℂ) (t : ℝ) :
    finiteMobiusShift N (exponentialTest s) t =
      Finset.sum (Finset.range (N + 1))
        (fun n =>
          ((ArithmeticFunction.moebius (Nat.succ n) : ℤ) : ℂ) *
            Complex.exp (-s * (Real.log (Nat.succ n : ℕ) : ℂ))) *
        exponentialTest s t := by
  unfold finiteMobiusShift
  change
    (Finset.sum (Finset.range (N + 1))
      (fun n =>
        ((ArithmeticFunction.moebius (Nat.succ n) : ℤ) : ℂ) •
          translationShift (Real.log (Nat.succ n : ℕ))))
      (exponentialTest s) t = _
  rw [LinearMap.sum_apply, Finset.sum_apply]
  simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  change
    ((ArithmeticFunction.moebius (Nat.succ n) : ℤ) : ℂ) *
        translationShift (Real.log (Nat.succ n : ℕ)) (exponentialTest s) t =
      (((ArithmeticFunction.moebius (Nat.succ n) : ℤ) : ℂ) *
          Complex.exp (-s * (Real.log (Nat.succ n : ℕ) : ℂ))) *
        exponentialTest s t
  rw [translationShift_exponentialTest]
  ring

/-- A finite Dirichlet operator with arbitrary complex coefficients. -/
def dirichletOperator (N : ℕ) (a : ℕ → ℂ) : ScaleEnd :=
  Finset.sum (Finset.range (N + 1))
    (fun n => a (Nat.succ n) • translationShift (Real.log (Nat.succ n : ℕ)))

theorem dirichletOperator_exponentialTest
    (N : ℕ) (a : ℕ → ℂ) (s : ℂ) (t : ℝ) :
    dirichletOperator N a (exponentialTest s) t =
      Finset.sum (Finset.range (N + 1))
        (fun n => a (Nat.succ n) *
          Complex.exp (-s * (Real.log (Nat.succ n : ℕ) : ℂ))) *
        exponentialTest s t := by
  unfold dirichletOperator
  rw [LinearMap.sum_apply, Finset.sum_apply]
  simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  rw [translationShift_exponentialTest]
  ring

def dirichletEigenvalue (N : ℕ) (a : ℕ → ℂ) (s : ℂ) : ℂ :=
  Finset.sum (Finset.range (N + 1))
    (fun n => a (Nat.succ n) *
      Complex.exp (-s * (Real.log (Nat.succ n : ℕ) : ℂ)))

theorem dirichletOperator_exponentialTest_eigenvector
    (N : ℕ) (a : ℕ → ℂ) (s : ℂ) :
    dirichletOperator N a (exponentialTest s) =
      dirichletEigenvalue N a s • exponentialTest s := by
  ext t
  change dirichletOperator N a (exponentialTest s) t = _
  rw [dirichletOperator_exponentialTest]
  simp [dirichletEigenvalue, Pi.smul_apply]

def dirichletEigenvalueCpow (N : ℕ) (a : ℕ → ℂ) (s : ℂ) : ℂ :=
  Finset.sum (Finset.range (N + 1))
    (fun n => a (Nat.succ n) * (Nat.succ n : ℂ) ^ (-s))

theorem dirichletEigenvalue_eq_cpow
    (N : ℕ) (a : ℕ → ℂ) (s : ℂ) :
    dirichletEigenvalue N a s = dirichletEigenvalueCpow N a s := by
  unfold dirichletEigenvalue dirichletEigenvalueCpow
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : (Nat.succ n : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero n)
  have hlog : Complex.log (Nat.succ n : ℂ) =
      (Real.log (Nat.succ n : ℝ) : ℂ) := by
    exact (Complex.ofReal_log (by positivity)).symm
  rw [Complex.cpow_def_of_ne_zero hn0, hlog]
  ring_nf

theorem dirichletOperator_exponentialTest_eigenvector_cpow
    (N : ℕ) (a : ℕ → ℂ) (s : ℂ) :
    dirichletOperator N a (exponentialTest s) =
      dirichletEigenvalueCpow N a s • exponentialTest s := by
  rw [dirichletOperator_exponentialTest_eigenvector]
  exact congrArg (fun z : ℂ => z • exponentialTest s)
    (dirichletEigenvalue_eq_cpow N a s)

def zetaCoefficients : ℕ → ℂ := fun _ => 1

def mobiusCoefficients : ℕ → ℂ :=
  fun n => (ArithmeticFunction.moebius n : ℤ)

theorem finiteDirichletShift_eq_zetaCoefficients (N : ℕ) :
    finiteDirichletShift N = dirichletOperator N zetaCoefficients := by
  ext f t
  simp [finiteDirichletShift, dirichletOperator, zetaCoefficients]

theorem finiteMobiusShift_eq_mobiusCoefficients (N : ℕ) :
    finiteMobiusShift N = dirichletOperator N mobiusCoefficients := by
  ext f t
  simp [finiteMobiusShift, dirichletOperator, mobiusCoefficients]


end InfoGeometry.Analysis.FiniteDirichletShiftOperatorBridge

end noncomputable section
