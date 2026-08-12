import proofs.CantorBoundaryCuntzFamily
import proofs.GellMannParafermionSolder
import InfoGeometry.Canonical.ProjectiveAffineConformalClosure55

/-!
# Finite twistor matrix identities

Finite algebraic core:
* four complex coordinates form a `2×2` Pauli-type matrix;
* its determinant is the corresponding quadratic polynomial;
* zero determinant is recorded as `NullParavector`;
* rank-one spinor dyads have zero determinant;
* twistor incidence is encoded as a finite matrix equation
  `ω = i X π`;
* projective twistor equality is scalar multiplication by a nonzero complex
  number.
-/

noncomputable section

namespace TwistorParafermionBoundary

open scoped BigOperators
open CantorBoundaryCuntzFamily
open GellMannParafermionSolder

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-- A `2×2` complex matrix built from four complex coordinates. -/
def pauliParavector (t x y z : ℂ) : M2C :=
  !![t + z, x - Complex.I * y;
     x + Complex.I * y, t - z]

/-- The determinant is the associated quadratic polynomial. -/
theorem det_pauliParavector (t x y z : ℂ) :
    Matrix.det (pauliParavector t x y z) = t^2 - x^2 - y^2 - z^2 := by
  simp [pauliParavector, Matrix.det_fin_two]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The zero-determinant predicate for `2×2` complex matrices. -/
def NullParavector (X : M2C) : Prop :=
  Matrix.det X = 0

/-- The matrix is zero-determinant exactly when its quadratic polynomial vanishes. -/
theorem pauliParavector_null_iff (t x y z : ℂ) :
    NullParavector (pauliParavector t x y z) ↔ t^2 - x^2 - y^2 - z^2 = 0 := by
  unfold NullParavector
  rw [det_pauliParavector]

/-- Rank-one matrix built from two complex two-vectors. -/
def spinorDyad (a b c d : ℂ) : M2C :=
  !![a * c, a * d; b * c, b * d]

/-- These rank-one matrices have zero determinant. -/
theorem spinorDyad_null (a b c d : ℂ) :
    NullParavector (spinorDyad a b c d) := by
  unfold NullParavector spinorDyad
  simp [Matrix.det_fin_two]
  ring

/-- A two-component complex vector denoted by `π`. -/
structure PrimedSpinor where
  pi0 : ℂ
  pi1 : ℂ

/-- A two-component complex vector denoted by `ω`. -/
structure UnprimedSpinor where
  omega0 : ℂ
  omega1 : ℂ

/-- Four complex components grouped as `(ω₀,ω₁,π₀,π₁)`. -/
structure Twistor4 where
  omega0 : ℂ
  omega1 : ℂ
  pi0 : ℂ
  pi1 : ℂ

/-- Incidence relation `ω = i X π` for a `2×2` complex matrix. -/
def incidentTwistor (X : M2C) (π : PrimedSpinor) : Twistor4 where
  omega0 := Complex.I * (X 0 0 * π.pi0 + X 0 1 * π.pi1)
  omega1 := Complex.I * (X 1 0 * π.pi0 + X 1 1 * π.pi1)
  pi0 := π.pi0
  pi1 := π.pi1

/-- Incidence recovers the first twistor component by definition. -/
theorem incidentTwistor_omega0 (X : M2C) (π : PrimedSpinor) :
    (incidentTwistor X π).omega0 =
      Complex.I * (X 0 0 * π.pi0 + X 0 1 * π.pi1) := rfl

/-- Incidence recovers the second twistor component by definition. -/
theorem incidentTwistor_omega1 (X : M2C) (π : PrimedSpinor) :
    (incidentTwistor X π).omega1 =
      Complex.I * (X 1 0 * π.pi0 + X 1 1 * π.pi1) := rfl

/-- Incidence for `pauliParavector`, first component expanded. -/
theorem incidentTwistor_pauli_omega0 (t x y z : ℂ) (π : PrimedSpinor) :
    (incidentTwistor (pauliParavector t x y z) π).omega0 =
      Complex.I * ((t + z) * π.pi0 + (x - Complex.I * y) * π.pi1) := rfl

/-- Incidence for `pauliParavector`, second component expanded. -/
theorem incidentTwistor_pauli_omega1 (t x y z : ℂ) (π : PrimedSpinor) :
    (incidentTwistor (pauliParavector t x y z) π).omega1 =
      Complex.I * ((x + Complex.I * y) * π.pi0 + (t - z) * π.pi1) := rfl

/-- Projective twistor equivalence: nonzero scalar multiple. -/
def projectiveTwistorEq (Z W : Twistor4) : Prop :=
  ∃ lam : ℂ, lam ≠ 0 ∧
    W.omega0 = lam * Z.omega0 ∧ W.omega1 = lam * Z.omega1 ∧
    W.pi0 = lam * Z.pi0 ∧ W.pi1 = lam * Z.pi1

/-- Projective twistor equivalence is reflexive. -/
theorem projectiveTwistorEq_refl (Z : Twistor4) : projectiveTwistorEq Z Z := by
  refine ⟨1, by norm_num, ?_, ?_, ?_, ?_⟩ <;> simp

/-- Combined finite matrix identities from the preceding declarations. -/
theorem twistor_parafermion_boundary_synthesis
    (t x y z : ℂ) (π : PrimedSpinor)
    (a b c d : ℂ) :
    Matrix.det (pauliParavector t x y z) = t^2 - x^2 - y^2 - z^2 ∧
    (NullParavector (pauliParavector t x y z) ↔ t^2 - x^2 - y^2 - z^2 = 0) ∧
    NullParavector (spinorDyad a b c d) ∧
    (incidentTwistor (pauliParavector t x y z) π).omega0 =
      Complex.I * ((t + z) * π.pi0 + (x - Complex.I * y) * π.pi1) ∧
    (incidentTwistor (pauliParavector t x y z) π).omega1 =
      Complex.I * ((x + Complex.I * y) * π.pi0 + (t - z) * π.pi1) := by
  exact ⟨det_pauliParavector t x y z,
    pauliParavector_null_iff t x y z,
    spinorDyad_null a b c d,
    incidentTwistor_pauli_omega0 t x y z π,
    incidentTwistor_pauli_omega1 t x y z π⟩

end TwistorParafermionBoundary

end noncomputable section
