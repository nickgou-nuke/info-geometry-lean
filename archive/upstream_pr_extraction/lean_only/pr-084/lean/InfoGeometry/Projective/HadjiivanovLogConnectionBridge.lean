import InfoGeometry.Projective.PuncturedAffineLogDeRhamBridge
import InfoGeometry.Clifford.LogCftMonodromy
import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Algebraic logarithmic connection with a Hadjiivanov residue

This owner places a finite-dimensional endomorphism-valued residue over the
Laurent logarithmic coefficient operator.  Its section carrier is
`ℂ[T,T⁻¹] ⊗ V`, and its connection operator is the finite algebraic sum

`T∂_T ⊗ 1 + 1 ⊗ (h · 1 + N)`.

Only algebraic connection identities and an explicit bridge to the existing
Hadjiivanov matrix readout are asserted.  No analytic horizontal sections,
parallel transport, holonomy, or fundamental-group realization is claimed.
-/

namespace InfoGeometry.Projective.HadjiivanovLogConnectionBridge

open scoped TensorProduct
open InfoGeometry.Projective.PuncturedAffineLogDifferential
open InfoGeometry.Clifford.LogCftMonodromy

noncomputable section

abbrev LaurentRing := LaurentPolynomial ℂ

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Finite algebraic sections over the punctured-affine Laurent base. -/
abbrev LogSection (V : Type*) [AddCommGroup V] [Module ℂ V] :=
  LaurentRing ⊗[ℂ] V

/-- A scalar plus square-zero nilpotent logarithmic residue. -/
structure LogResidue (V : Type*) [AddCommGroup V] [Module ℂ V] where
  weight : ℂ
  nilpotent : V →ₗ[ℂ] V
  nilpotent_sq : nilpotent.comp nilpotent = 0

/-- The residue endomorphism `h I + N`. -/
def residueOperator (R : LogResidue V) : V →ₗ[ℂ] V :=
  R.weight • LinearMap.id + R.nilpotent

@[simp] theorem residueOperator_apply (R : LogResidue V) (v : V) :
    residueOperator R v = R.weight • v + R.nilpotent v := by
  simp [residueOperator]

theorem nilpotent_apply_twice (R : LogResidue V) (v : V) :
    R.nilpotent (R.nilpotent v) = 0 := by
  have h := LinearMap.congr_fun R.nilpotent_sq v
  simpa using h

/-- The base part `T∂_T ⊗ 1` of the logarithmic connection. -/
def baseLogOperator : LogSection V →ₗ[ℂ] LogSection V :=
  TensorProduct.map logarithmicDifferential LinearMap.id

/-- The fiber part `1 ⊗ (h I + N)` of the logarithmic connection. -/
def residueSectionOperator (R : LogResidue V) :
    LogSection V →ₗ[ℂ] LogSection V :=
  TensorProduct.map LinearMap.id (residueOperator R)

/-- The finite algebraic logarithmic connection coefficient operator. -/
def logarithmicConnection (R : LogResidue V) :
    LogSection V →ₗ[ℂ] LogSection V :=
  baseLogOperator + residueSectionOperator R

@[simp] theorem baseLogOperator_tmul (f : LaurentRing) (v : V) :
    baseLogOperator (f ⊗ₜ[ℂ] v) = logarithmicDifferential f ⊗ₜ[ℂ] v := by
  simp [baseLogOperator]

@[simp] theorem residueSectionOperator_tmul
    (R : LogResidue V) (f : LaurentRing) (v : V) :
    residueSectionOperator R (f ⊗ₜ[ℂ] v) =
      f ⊗ₜ[ℂ] residueOperator R v := by
  simp [residueSectionOperator]

/-- Explicit separation of base logarithmic derivative and fiber residue. -/
theorem logarithmicConnection_tmul
    (R : LogResidue V) (f : LaurentRing) (v : V) :
    logarithmicConnection R (f ⊗ₜ[ℂ] v) =
      logarithmicDifferential f ⊗ₜ[ℂ] v +
        f ⊗ₜ[ℂ] (R.weight • v + R.nilpotent v) := by
  simp [logarithmicConnection]

theorem logarithmicConnection_T_tmul
    (R : LogResidue V) (n : ℤ) (v : V) :
    logarithmicConnection R (LaurentPolynomial.T n ⊗ₜ[ℂ] v) =
      (n : ℂ) • (LaurentPolynomial.T n ⊗ₜ[ℂ] v) +
        LaurentPolynomial.T n ⊗ₜ[ℂ]
          (R.weight • v + R.nilpotent v) := by
  rw [logarithmicConnection_tmul,
    logarithmicDifferential_T]
  congr 1

theorem logarithmicConnection_C_tmul
    (R : LogResidue V) (c : ℂ) (v : V) :
    logarithmicConnection R (LaurentPolynomial.C c ⊗ₜ[ℂ] v) =
      LaurentPolynomial.C c ⊗ₜ[ℂ]
        (R.weight • v + R.nilpotent v) := by
  rw [logarithmicConnection_tmul,
    logarithmicDifferential_C]
  simp

theorem logarithmicConnection_C_mul_T_tmul
    (R : LogResidue V) (c : ℂ) (n : ℤ) (v : V) :
    logarithmicConnection R
        ((LaurentPolynomial.C c * LaurentPolynomial.T n) ⊗ₜ[ℂ] v) =
      (n : ℂ) •
          ((LaurentPolynomial.C c * LaurentPolynomial.T n) ⊗ₜ[ℂ] v) +
        (LaurentPolynomial.C c * LaurentPolynomial.T n) ⊗ₜ[ℂ]
          (R.weight • v + R.nilpotent v) := by
  rw [logarithmicConnection_tmul,
    logarithmicDifferential_C_mul_T]
  congr 1

/-- Leibniz expansion on a pure section, with the fiber residue held fixed. -/
theorem logarithmicConnection_mul_tmul
    (R : LogResidue V) (f g : LaurentRing) (v : V) :
    logarithmicConnection R ((f * g) ⊗ₜ[ℂ] v) =
      (logarithmicDifferential f * g + f * logarithmicDifferential g) ⊗ₜ[ℂ] v +
        (f * g) ⊗ₜ[ℂ] (R.weight • v + R.nilpotent v) := by
  rw [logarithmicConnection_tmul, logarithmicDifferential_mul]

/-- The concrete rank-two residue `h I + N` used by the native LCFT owner. -/
def nativeHadjiivanovResidue (h : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  h • (1 : Matrix (Fin 2) (Fin 2) ℂ) + jordanNilpotent

theorem nativeHadjiivanovResidue_eq_l0Cell (h : ℂ) :
    nativeHadjiivanovResidue h = virasoroL0Cell h := by
  rw [nativeHadjiivanovResidue, l0_cell_decomposition]

/-- Explicit algebraic residue-to-monodromy readout; this is not a holonomy theorem. -/
def residueMonodromyReadout (h : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  lcftPhase h •
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) + logShearBase • jordanNilpotent)

theorem residueMonodromyReadout_eq_hadjiivanov (h : ℂ) :
    residueMonodromyReadout h = hadjiivanovMonodromy h := by
  rw [residueMonodromyReadout, hadjiivanovMonodromy_phase_nilpotent]

theorem nativeHadjiivanovNilpotent_sq :
    (jordanNilpotent : Matrix (Fin 2) (Fin 2) ℂ) * jordanNilpotent = 0 :=
  jordanNilpotent_sq

end

end InfoGeometry.Projective.HadjiivanovLogConnectionBridge
