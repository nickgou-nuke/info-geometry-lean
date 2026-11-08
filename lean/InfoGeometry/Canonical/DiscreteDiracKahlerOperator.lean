import InfoGeometry.Canonical.StandardIntegralSplitOctonionMultiplication
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical

/-- 1. Дискретен Външен Диференциал d_θ(ω) = θ * ω -/
def discreteExteriorDerivative (theta omega : StandardIntegralSplitOctonion) : StandardIntegralSplitOctonion :=
  splitOctonionMul theta omega

/-- Лемма за лява абсорбция на нулата при октонионно умножение -/
theorem splitOctonionMul_zero_left (x : StandardIntegralSplitOctonion) :
    splitOctonionMul (fun _ => 0) x = (fun _ => 0) := by
  ext r
  fin_cases r <;>
    dsimp [splitOctonionMul, splitQuaternionOf, splitQuaternionLPart,
      splitQuaternionAdd, splitQuaternionMul, splitQuaternionConj,
      splitOctonionOfQuaternionPair] <;>
    ring

/-- 2. Нилпотентност на Диференциала d²(ω) = 0 за θ² = 0 в Асоциативните Сектори -/
theorem discrete_d_sq_zero_of_associative
    (theta omega : StandardIntegralSplitOctonion)
    (h_theta_sq : splitOctonionMul theta theta = (fun _ => 0))
    (h_assoc : splitOctonionMul theta (splitOctonionMul theta omega) =
               splitOctonionMul (splitOctonionMul theta theta) omega) :
    discreteExteriorDerivative theta (discreteExteriorDerivative theta omega) = (fun _ => 0) := by
  dsimp [discreteExteriorDerivative]
  rw [h_assoc]
  rw [h_theta_sq]
  exact splitOctonionMul_zero_left omega

/-- **Master Synthesis**: Дискретен Дирак-Келеров Диференциален Двигател -/
theorem master_discrete_dirac_kahler_synthesis
    (theta omega : StandardIntegralSplitOctonion)
    (h_theta_sq : splitOctonionMul theta theta = (fun _ => 0))
    (h_assoc : splitOctonionMul theta (splitOctonionMul theta omega) =
               splitOctonionMul (splitOctonionMul theta theta) omega) :
    discreteExteriorDerivative theta (discreteExteriorDerivative theta omega) = (fun _ => 0) :=
  discrete_d_sq_zero_of_associative theta omega h_theta_sq h_assoc

/-! Generic multiplication formulation. The associator condition is explicit. -/

def leftMultiplicationDifferential
    {A : Type*} (mul : A → A → A) (theta omega : A) : A :=
  mul theta omega

def multiplicationAssociator
    {A : Type*} [AddCommGroup A]
    (mul : A → A → A) (x y z : A) : A :=
  mul (mul x y) z - mul x (mul y z)

theorem leftMultiplicationDifferential_sq_eq_sub_associator
    {A : Type*} [AddCommGroup A]
    (mul : A → A → A) (theta omega : A) :
    leftMultiplicationDifferential mul theta
        (leftMultiplicationDifferential mul theta omega) =
      mul (mul theta theta) omega -
        multiplicationAssociator mul theta theta omega := by
  exact (sub_sub_cancel (mul (mul theta theta) omega)
    (mul theta (mul theta omega))).symm

theorem leftMultiplicationDifferential_sq_zero_of_square_zero_and_associative
    {A : Type*} [AddCommGroup A]
    (mul : A → A → A) (theta omega : A)
    (h_theta_sq : mul theta theta = 0)
    (h_assoc : multiplicationAssociator mul theta theta omega = 0)
    (h_zero : mul 0 omega = 0) :
    leftMultiplicationDifferential mul theta
        (leftMultiplicationDifferential mul theta omega) = 0 := by
  rw [leftMultiplicationDifferential_sq_eq_sub_associator, h_theta_sq]
  simp [h_zero, h_assoc]

end InfoGeometry.Canonical
