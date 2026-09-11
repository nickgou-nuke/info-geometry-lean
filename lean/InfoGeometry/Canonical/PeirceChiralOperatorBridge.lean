import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical

/-!
# Associative operator carrier for a chiral Peirce packet

This owner isolates the operator-level pattern already occurring in the Cuntz,
Clifford, and parity owners.  It is deliberately formulated over an
associative ring.  It does not install an associative multiplication on the
split-octonion carrier and does not assert a faithful representation of the
whole nonassociative Zorn algebra.
-/

structure PeirceChiralOperatorPacket (A : Type*) [Ring A] where
  pPlus : A
  pMinus : A
  sigmaPlus : A
  sigmaMinus : A
  p_sum : pPlus + pMinus = 1
  p_plus_sq : pPlus * pPlus = pPlus
  p_minus_sq : pMinus * pMinus = pMinus
  p_plus_mul_minus : pPlus * pMinus = 0
  p_minus_mul_plus : pMinus * pPlus = 0
  sigmaPlus_mul_sigmaMinus : sigmaPlus * sigmaMinus = pPlus
  sigmaMinus_mul_sigmaPlus : sigmaMinus * sigmaPlus = pMinus
  sigmaPlus_sq : sigmaPlus * sigmaPlus = 0
  sigmaMinus_sq : sigmaMinus * sigmaMinus = 0
  pPlus_mul_sigmaPlus : pPlus * sigmaPlus = sigmaPlus
  sigmaPlus_mul_pMinus : sigmaPlus * pMinus = sigmaPlus
  pMinus_mul_sigmaMinus : pMinus * sigmaMinus = sigmaMinus
  sigmaMinus_mul_pPlus : sigmaMinus * pPlus = sigmaMinus
  pMinus_mul_sigmaPlus : pMinus * sigmaPlus = 0
  sigmaPlus_mul_pPlus : sigmaPlus * pPlus = 0
  pPlus_mul_sigmaMinus : pPlus * sigmaMinus = 0
  sigmaMinus_mul_pMinus : sigmaMinus * pMinus = 0

namespace PeirceChiralOperatorPacket

variable {A : Type*} [Ring A]
variable (P : PeirceChiralOperatorPacket A)

def peirce11 (x : A) : A := P.pPlus * x * P.pPlus
def peirce12 (x : A) : A := P.pPlus * x * P.pMinus
def peirce21 (x : A) : A := P.pMinus * x * P.pPlus
def peirce22 (x : A) : A := P.pMinus * x * P.pMinus

def parity : A := P.pPlus - P.pMinus

theorem global_decomposition (x : A) :
    x = P.peirce11 x + P.peirce12 x + P.peirce21 x + P.peirce22 x := by
  calc
    x = 1 * x * 1 := by simp
    _ = (P.pPlus + P.pMinus) * x * (P.pPlus + P.pMinus) := by rw [P.p_sum]
    _ = P.peirce11 x + P.peirce12 x + P.peirce21 x + P.peirce22 x := by
      dsimp [peirce11, peirce12, peirce21, peirce22]
      noncomm_ring

@[simp] theorem peirce12_sigmaPlus :
    P.peirce12 P.sigmaPlus = P.sigmaPlus := by
  dsimp [peirce12]
  calc
    P.pPlus * P.sigmaPlus * P.pMinus = P.pPlus * (P.sigmaPlus * P.pMinus) := by rw [mul_assoc]
    _ = P.pPlus * P.sigmaPlus := by rw [P.sigmaPlus_mul_pMinus]
    _ = P.sigmaPlus := P.pPlus_mul_sigmaPlus

@[simp] theorem peirce21_sigmaMinus :
    P.peirce21 P.sigmaMinus = P.sigmaMinus := by
  dsimp [peirce21]
  calc
    P.pMinus * P.sigmaMinus * P.pPlus = P.pMinus * (P.sigmaMinus * P.pPlus) := by rw [mul_assoc]
    _ = P.pMinus * P.sigmaMinus := by rw [P.sigmaMinus_mul_pPlus]
    _ = P.sigmaMinus := P.pMinus_mul_sigmaMinus

@[simp] theorem peirce11_sigmaPlus :
    P.peirce11 P.sigmaPlus = 0 := by
  dsimp [peirce11]
  calc
    P.pPlus * P.sigmaPlus * P.pPlus = P.pPlus * (P.sigmaPlus * P.pPlus) := by rw [mul_assoc]
    _ = 0 := by rw [P.sigmaPlus_mul_pPlus, mul_zero]

@[simp] theorem peirce22_sigmaPlus :
    P.peirce22 P.sigmaPlus = 0 := by
  dsimp [peirce22]
  calc
    P.pMinus * P.sigmaPlus * P.pMinus = P.pMinus * (P.sigmaPlus * P.pMinus) := by rw [mul_assoc]
    _ = 0 := by rw [P.sigmaPlus_mul_pMinus, P.pMinus_mul_sigmaPlus]

@[simp] theorem peirce11_sigmaMinus :
    P.peirce11 P.sigmaMinus = 0 := by
  dsimp [peirce11]
  calc
    P.pPlus * P.sigmaMinus * P.pPlus = P.pPlus * (P.sigmaMinus * P.pPlus) := by rw [mul_assoc]
    _ = 0 := by rw [P.sigmaMinus_mul_pPlus, P.pPlus_mul_sigmaMinus]

@[simp] theorem peirce22_sigmaMinus :
    P.peirce22 P.sigmaMinus = 0 := by
  dsimp [peirce22]
  calc
    P.pMinus * P.sigmaMinus * P.pMinus = P.pMinus * (P.sigmaMinus * P.pMinus) := by rw [mul_assoc]
    _ = 0 := by rw [P.sigmaMinus_mul_pMinus, mul_zero]

theorem parity_sq : P.parity * P.parity = 1 := by
  dsimp [parity]
  calc
    (P.pPlus - P.pMinus) * (P.pPlus - P.pMinus) =
        P.pPlus * P.pPlus - P.pPlus * P.pMinus -
          P.pMinus * P.pPlus + P.pMinus * P.pMinus := by noncomm_ring
    _ = 1 := by
      rw [P.p_plus_sq, P.p_plus_mul_minus, P.p_minus_mul_plus, P.p_minus_sq]
      noncomm_ring
      exact P.p_sum

theorem parity_mul_sigmaPlus : P.parity * P.sigmaPlus = P.sigmaPlus := by
  dsimp [parity]
  rw [sub_mul, P.pPlus_mul_sigmaPlus, P.pMinus_mul_sigmaPlus, sub_zero]

theorem sigmaPlus_mul_parity : P.sigmaPlus * P.parity = -P.sigmaPlus := by
  dsimp [parity]
  rw [mul_sub, P.sigmaPlus_mul_pPlus, P.sigmaPlus_mul_pMinus, zero_sub]

theorem parity_sigmaPlus_anticommute :
    P.parity * P.sigmaPlus + P.sigmaPlus * P.parity = 0 := by
  rw [P.parity_mul_sigmaPlus, P.sigmaPlus_mul_parity, add_neg_cancel]

theorem parity_mul_sigmaMinus : P.parity * P.sigmaMinus = -P.sigmaMinus := by
  dsimp [parity]
  rw [sub_mul, P.pPlus_mul_sigmaMinus, P.pMinus_mul_sigmaMinus, zero_sub]

theorem sigmaMinus_mul_parity : P.sigmaMinus * P.parity = P.sigmaMinus := by
  dsimp [parity]
  rw [mul_sub, P.sigmaMinus_mul_pPlus, P.sigmaMinus_mul_pMinus, sub_zero]

theorem parity_sigmaMinus_anticommute :
    P.parity * P.sigmaMinus + P.sigmaMinus * P.parity = 0 := by
  rw [P.parity_mul_sigmaMinus, P.sigmaMinus_mul_parity, neg_add_cancel]

end PeirceChiralOperatorPacket
end InfoGeometry.Canonical
