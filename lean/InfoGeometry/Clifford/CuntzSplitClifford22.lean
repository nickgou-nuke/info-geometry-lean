import InfoGeometry.Algebra.CuntzMatrixUnitRepresentation
import InfoGeometry.Clifford.Cl11Matrix

/-!
# The real split Clifford representation induced by Cuntz matrix units

The existing real `Cl(1,1)` atom supplies `u`, `v`, and `w`. Four explicit
blocks satisfy signature `(2,2)` and induce a native `CliffordAlgebra.lift`.
The matrix-unit algebra map transports this representation to every real
algebra with the existing two-generator algebraic Cuntz presentation.

The fundamental symmetry below is a real linear matrix. It is not a
Tomita--Takesaki antiunitary. No topology or evolution law follows from this
finite algebraic representation alone.
-/

noncomputable section

namespace InfoGeometry.Clifford.CuntzSplitClifford22

open Matrix
open InfoGeometry.Algebra.Cuntz

abbrev Atom := Matrix (Fin 2) (Fin 2) ℝ
abbrev Block := Matrix (Fin 2) (Fin 2) Atom
abbrev Vector22 := ℝ × ℝ × ℝ × ℝ

abbrev u : Atom := Cl11Matrix.J1
abbrev v : Atom := Cl11Matrix.Eplus
abbrev w : Atom := Cl11Matrix.Eminus

def gamma0 : Block := !![0, 1; 1, 0]
def gamma1 : Block := !![0, w; -w, 0]
def gamma2 : Block := !![0, u; -u, 0]
def gamma3 : Block := !![0, v; -v, 0]
def gamma : Fin 4 → Block := ![gamma0, gamma1, gamma2, gamma3]
def signature : Fin 4 → ℝ := ![1, 1, -1, -1]

/-- All sixteen Clifford relations, including their diagonal signs. -/
theorem gamma_anticommutator (a b : Fin 4) :
    gamma a * gamma b + gamma b * gamma a =
      if a = b then (2 * signature a) • (1 : Block) else 0 := by
  fin_cases a <;> fin_cases b <;> ext i j k l <;>
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [gamma, gamma0, gamma1, gamma2, gamma3, signature,
      u, v, w, Cl11Matrix.J1, Cl11Matrix.Eplus, Cl11Matrix.Eminus,
      Matrix.mul_apply, Fin.sum_univ_two]

def q22 : QuadraticForm ℝ Vector22 :=
  QuadraticMap.sq.prod
    (QuadraticMap.sq.prod ((-QuadraticMap.sq).prod (-QuadraticMap.sq)))

@[simp] theorem q22_apply (t x y z : ℝ) :
    q22 (t, x, y, z) = t ^ 2 + x ^ 2 - y ^ 2 - z ^ 2 := by
  simp [q22]
  ring

def generator : Vector22 →ₗ[ℝ] Block where
  toFun x := x.1 • gamma0 + x.2.1 • gamma1 +
    x.2.2.1 • gamma2 + x.2.2.2 • gamma3
  map_add' x y := by simp [add_smul]; abel
  map_smul' r x := by simp [smul_add, smul_smul]

theorem generator_sq (x : Vector22) :
    generator x * generator x = q22 x • (1 : Block) := by
  rcases x with ⟨t, x, y, z⟩
  ext i j k l
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [generator, q22_apply, gamma0, gamma1, gamma2, gamma3,
      u, v, w, Cl11Matrix.J1, Cl11Matrix.Eplus, Cl11Matrix.Eminus,
      Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- A genuine universal Clifford algebra representation over the real numbers. -/
def matrixRepresentation : CliffordAlgebra q22 →ₐ[ℝ] Block :=
  CliffordAlgebra.lift q22 ⟨generator, fun x => by
    simpa [Algebra.algebraMap_eq_smul_one] using generator_sq x⟩

@[simp] theorem matrixRepresentation_iota (x : Vector22) :
    matrixRepresentation (CliffordAlgebra.ι q22 x) = generator x := by
  exact CliffordAlgebra.lift_ι_apply _ _ x

section Transport

variable {A : Type*} [Ring A] [Algebra ℝ A]
variable (P : AlgebraicCuntzNPresentation ℝ 2 A)

/-- Apply the derived matrix-unit algebra homomorphism to each outer block. -/
def blockHom : Block →ₐ[ℝ] Matrix (Fin 2) (Fin 2) A where
  toFun M i j := P.matrixTwoHom (M i j)
  map_zero' := by ext i j; simp
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_add' M K := by ext i j; simp
  map_mul' M K := by
    ext i j
    change P.matrixTwoHom (∑ k, M i k * K k j) =
      ∑ k, P.matrixTwoHom (M i k) * P.matrixTwoHom (K k j)
    simp only [map_sum, map_mul]
  commutes' r := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Algebra.algebraMap_eq_smul_one]

def cuntzGamma (a : Fin 4) : Matrix (Fin 2) (Fin 2) A :=
  blockHom P (gamma a)

def cuntzRepresentation :
    CliffordAlgebra q22 →ₐ[ℝ] Matrix (Fin 2) (Fin 2) A :=
  (blockHom P).comp matrixRepresentation

@[simp] theorem cuntzRepresentation_iota (x : Vector22) :
    cuntzRepresentation P (CliffordAlgebra.ι q22 x) = blockHom P (generator x) := by
  simp [cuntzRepresentation]

theorem cuntzGamma_anticommutator (a b : Fin 4) :
    cuntzGamma P a * cuntzGamma P b + cuntzGamma P b * cuntzGamma P a =
      if a = b then (2 * signature a) • (1 : Matrix (Fin 2) (Fin 2) A) else 0 := by
  have h := congrArg (blockHom P) (gamma_anticommutator a b)
  simpa [cuntzGamma, apply_ite] using h

/-- Readback of the off-diagonal involution as the sum of Cuntz matrix units. -/
theorem matrixTwoHom_u :
    P.matrixTwoHom u = P.matrixUnit 0 1 + P.matrixUnit 1 0 := by
  simp [u, Cl11Matrix.J1]

theorem matrixTwoHom_v :
    P.matrixTwoHom v = P.matrixUnit 0 0 - P.matrixUnit 1 1 := by
  simp [v, Cl11Matrix.Eplus, sub_eq_add_neg]

theorem matrixTwoHom_w :
    P.matrixTwoHom w = P.matrixUnit 0 1 - P.matrixUnit 1 0 := by
  simp [w, Cl11Matrix.Eminus, sub_eq_add_neg]

end Transport

/-- The algebraic real Cuntz quotient supplies a concrete instantiation. -/
def quotientRepresentation : CliffordAlgebra q22 →ₐ[ℝ]
    Matrix (Fin 2) (Fin 2) (CuntzTensorQuotient ℝ 2) :=
  cuntzRepresentation (cuntzTensorQuotientPresentation ℝ 2)

@[simp] theorem gamma0_sq : gamma0 * gamma0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma0, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem gamma0_star : star gamma0 = gamma0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gamma0, Matrix.star_apply]

/-- The adjoint defined by the additional fundamental symmetry. -/
def kreinAdjoint (T : Block) : Block := gamma0 * star T * gamma0

theorem kreinAdjoint_involutive (T : Block) :
    kreinAdjoint (kreinAdjoint T) = T := by
  simp only [kreinAdjoint, star_mul, gamma0_star, star_star]
  calc
    _ = (gamma0 * gamma0) * T * (gamma0 * gamma0) := by noncomm_ring
    _ = T := by simp

theorem kreinAdjoint_mul (T U : Block) :
    kreinAdjoint (T * U) = kreinAdjoint U * kreinAdjoint T := by
  simp only [kreinAdjoint, star_mul]
  symm
  calc
    (gamma0 * star U * gamma0) * (gamma0 * star T * gamma0) =
        gamma0 * star U * (gamma0 * gamma0) * star T * gamma0 := by noncomm_ring
    _ = gamma0 * (star U * star T) * gamma0 := by simp [mul_assoc]

end InfoGeometry.Clifford.CuntzSplitClifford22
