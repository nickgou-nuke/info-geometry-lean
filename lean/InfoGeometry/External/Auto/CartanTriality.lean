import Init
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-- Formalization of the Triality automorphism on Spin(8) representations.
    We abstract the three 8-dimensional representations as a type with 3 elements,
    and define the S3 permutations representing Cartan's triality. --/

inductive Spin8Rep where
  | vector : Spin8Rep
  | spinorPlus : Spin8Rep
  | spinorMinus : Spin8Rep
  deriving Repr, DecidableEq

namespace CartanTriality

/-- Triality order-3 automorphism -/
def rho : Spin8Rep → Spin8Rep
  | Spin8Rep.vector => Spin8Rep.spinorPlus
  | Spin8Rep.spinorPlus => Spin8Rep.spinorMinus
  | Spin8Rep.spinorMinus => Spin8Rep.vector

/-- Triality order-2 automorphism (vector / spinorPlus swap) -/
def sigma : Spin8Rep → Spin8Rep
  | Spin8Rep.vector => Spin8Rep.spinorPlus
  | Spin8Rep.spinorPlus => Spin8Rep.vector
  | Spin8Rep.spinorMinus => Spin8Rep.spinorMinus

theorem rho_cubed_is_identity (x : Spin8Rep) : rho (rho (rho x)) = x := by
  cases x <;> rfl

theorem sigma_squared_is_identity (x : Spin8Rep) : sigma (sigma x) = x := by
  cases x <;> rfl

theorem rho_sigma_relation (x : Spin8Rep) : sigma (rho (sigma x)) = rho (rho x) := by
  cases x <;> rfl

end CartanTriality