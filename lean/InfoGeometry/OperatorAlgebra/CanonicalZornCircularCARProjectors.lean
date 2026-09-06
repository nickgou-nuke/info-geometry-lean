import Mathlib.Tactic
import InfoGeometry.Arithmetic.PrimeMajoranaCAR
import InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge

/-!
# Circular split-octonion CAR projectors and operator roots

The native circular Zorn rails become square-zero operators under the
right-regular lift.  Their CAR relation canonically generates complementary
projectors, Majorana roots of `+1` and `-1`, and a parity involution.

This is an algebraic operator theorem.  It does not identify these operators
with quantized electromagnetic flux tubes or with Riemann-zero ordinates.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.CanonicalZornCircularCARProjectors

open InfoGeometry.Arithmetic.PrimeMajoranaCAR
open InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge

abbrev CZ := InfoGeometry.Canonical.ZornMatrix ℝ
abbrev EndCZ := Module.End ℝ CZ

def circularExteriorCARPair (i : Fin 3) : ExteriorCARPair EndCZ where
  eps := (rightRegularCARPair i).cre
  iota := (rightRegularCARPair i).ann
  eps_sq_zero := (rightRegularCARPair i).cre_sq
  iota_sq_zero := (rightRegularCARPair i).ann_sq
  iota_eps_add_eps_iota := (rightRegularCARPair i).anti

def creation (i : Fin 3) : EndCZ :=
  (circularExteriorCARPair i).eps

def annihilation (i : Fin 3) : EndCZ :=
  (circularExteriorCARPair i).iota

def occupationProjector (i : Fin 3) : EndCZ :=
  (circularExteriorCARPair i).numberOp

def vacancyProjector (i : Fin 3) : EndCZ :=
  (circularExteriorCARPair i).iota *
    (circularExteriorCARPair i).eps

def majoranaPlus (i : Fin 3) : EndCZ :=
  (circularExteriorCARPair i).cMajorana

def majoranaMinus (i : Fin 3) : EndCZ :=
  (circularExteriorCARPair i).dMajorana

def parityOperator (i : Fin 3) : EndCZ :=
  (circularExteriorCARPair i).parityOp

@[simp] theorem creation_sq_zero (i : Fin 3) :
    creation i * creation i = 0 :=
  (circularExteriorCARPair i).eps_sq_zero

@[simp] theorem annihilation_sq_zero (i : Fin 3) :
    annihilation i * annihilation i = 0 :=
  (circularExteriorCARPair i).iota_sq_zero

theorem annihilation_creation_CAR (i : Fin 3) :
    annihilation i * creation i + creation i * annihilation i = 1 :=
  (circularExteriorCARPair i).iota_eps_add_eps_iota

theorem occupationProjector_idempotent (i : Fin 3) :
    occupationProjector i * occupationProjector i = occupationProjector i := by
  simpa [occupationProjector] using
    (ExteriorCARPair.numberOp_idem (circularExteriorCARPair i))

theorem vacancyProjector_idempotent (i : Fin 3) :
    vacancyProjector i * vacancyProjector i = vacancyProjector i := by
  rw [vacancyProjector,
    ExteriorCARPair.iota_mul_eps_eq_one_sub_eps_mul_iota]
  have hN := ExteriorCARPair.numberOp_idem (circularExteriorCARPair i)
  dsimp [ExteriorCARPair.numberOp] at hN
  rw [sub_mul, mul_sub, one_mul]
  have hNN :
      ((circularExteriorCARPair i).eps * (circularExteriorCARPair i).iota) *
          ((circularExteriorCARPair i).eps * (circularExteriorCARPair i).iota) =
        (circularExteriorCARPair i).eps * (circularExteriorCARPair i).iota := by
    exact hN
  simp [one_mul, mul_one, mul_sub, hNN]

theorem occupationProjector_add_vacancyProjector (i : Fin 3) :
    occupationProjector i + vacancyProjector i = 1 := by
  simpa [occupationProjector, vacancyProjector] using
    (ExteriorCARPair.eps_iota_add_iota_eps (circularExteriorCARPair i))

theorem majoranaPlus_sq (i : Fin 3) :
    majoranaPlus i * majoranaPlus i = 1 := by
  simpa [majoranaPlus] using
    (ExteriorCARPair.cMajorana_sq (circularExteriorCARPair i))

theorem majoranaMinus_sq (i : Fin 3) :
    majoranaMinus i * majoranaMinus i = -1 := by
  simpa [majoranaMinus] using
    (ExteriorCARPair.dMajorana_sq (circularExteriorCARPair i))

theorem majoranaPlus_majoranaMinus_anticomm (i : Fin 3) :
    majoranaPlus i * majoranaMinus i +
      majoranaMinus i * majoranaPlus i = 0 := by
  simpa [majoranaPlus, majoranaMinus] using
    (ExteriorCARPair.cMajorana_dMajorana_anticomm_zero
      (circularExteriorCARPair i))

theorem parityOperator_sq (i : Fin 3) :
    parityOperator i * parityOperator i = 1 := by
  simpa [parityOperator] using
    (ExteriorCARPair.parityOp_sq (circularExteriorCARPair i))

theorem circularOperatorRootPacket (i : Fin 3) :
    creation i * creation i = 0 ∧
      annihilation i * annihilation i = 0 ∧
      occupationProjector i * occupationProjector i = occupationProjector i ∧
      vacancyProjector i * vacancyProjector i = vacancyProjector i ∧
      occupationProjector i + vacancyProjector i = 1 ∧
      majoranaPlus i * majoranaPlus i = 1 ∧
      majoranaMinus i * majoranaMinus i = -1 ∧
      parityOperator i * parityOperator i = 1 := by
  exact ⟨creation_sq_zero i,
    annihilation_sq_zero i,
    occupationProjector_idempotent i,
    vacancyProjector_idempotent i,
    occupationProjector_add_vacancyProjector i,
    majoranaPlus_sq i,
    majoranaMinus_sq i,
    parityOperator_sq i⟩

end InfoGeometry.OperatorAlgebra.CanonicalZornCircularCARProjectors
