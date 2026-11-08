import InfoGeometry.Canonical.TensorTowerColimit
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.BottPeriodicity

/-!
# Chiral operator tower and split Bott bridge

This file keeps three levels separate:

* `TensorTowerColimit` supplies the algebraic stage-to-stage transport;
* a finite readout is an explicit map out of the ambient operator carrier;
* `BottPeriodicity` supplies the native split-Clifford stabilization step.

No finite readout is identified with the operator colimit, and no periodicity
claim is made about individual operator words.
-/

namespace InfoGeometry.OperatorAlgebra

open scoped TensorProduct
open InfoGeometry.Clifford.BottPeriodicity
open InfoGeometry.Clifford.ClNN

variable {R : Type*} [CommRing R]
variable (A : ℕ → Type*)
variable [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
variable (iota : ∀ n, A n →ₗ[R] A (n + 1))
variable (A_inf : Type*) [AddCommGroup A_inf] [Module R A_inf]
variable (psi : ∀ n, A n →ₗ[R] A_inf)
variable (psi_comm : ∀ n, (psi (n + 1)).comp (iota n) = psi n)

include psi_comm

/-- The image of a stage after a finite number of operator-envelope steps. -/
def stageTransport (n m : ℕ) : A n →ₗ[R] A_inf :=
  (psi (n + m)).comp (iota_seq A iota n m)

/-- Compatible tower maps agree after every finite number of steps. -/
theorem stageTransport_eq (n m : ℕ) :
    stageTransport A iota A_inf psi n m = psi n := by
  exact psi_comp_iota_seq A iota A_inf psi psi_comm n m

/-- A finite readout is an explicit projection from the ambient operator carrier.

The readout is deliberately not called a colimit map: it is additional data
used to form a finite window or cyclotomic shadow. -/
def finiteReadout {W : Type*} [AddCommGroup W] [Module R W]
    (readout : A_inf →ₗ[R] W) (n : ℕ) : A n →ₗ[R] W :=
  readout.comp (psi n)

theorem finiteReadout_stageTransport {W : Type*} [AddCommGroup W] [Module R W]
    (readout : A_inf →ₗ[R] W) (n m : ℕ) :
    (readout.comp (stageTransport A iota A_inf psi n m)) =
      finiteReadout A A_inf psi readout n := by
  rw [stageTransport_eq A iota A_inf psi psi_comm n m]
  rfl

end InfoGeometry.OperatorAlgebra
