import InfoGeometry.Canonical.Cl55OperatorProjectiveBoundary
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.OperatorCl11WittBasis

/-!
# The boundary `Cl(5,5)` packet as an abstract `Cl(1,1)` operator packet

The fifth positive/negative Clifford pair is not identified directly with the
two involutions of `Cl(1,1)`.  The second involution is the negative bivector
`-(e₄ f₄)`.  With this choice, the generic Witt operators are exactly the
existing projective annihilator and creator operators.
-/

variable {A : Type*} [Ring A] [Algebra ℚ A]

namespace InfoGeometry.Canonical.Cl55OperatorCl11Boundary

open InfoGeometry.Canonical.Cl55OperatorProjectiveBoundary
open InfoGeometry.Canonical.OperatorCl11WittBasis

variable {e f : Fin 5 → A} [hCl : OperatorCl55 e f]

def boundaryExchange (e f : Fin 5 → A) : A := -(e 4 * f 4)

omit [Algebra ℚ A] in
lemma boundary_exchange_sq : boundaryExchange e f * boundaryExchange e f = 1 := by
  unfold boundaryExchange
  have he := hCl.e_sq 4
  have hf := hCl.f_sq 4
  have hef := hCl.ef_anti 4 4
  have hfe : f 4 * e 4 = -(e 4 * f 4) := by
    calc
      f 4 * e 4 = (e 4 * f 4 + f 4 * e 4) - e 4 * f 4 := by
        rw [add_sub_cancel_left]
      _ = 0 - e 4 * f 4 := by rw [hef]
      _ = -(e 4 * f 4) := by rw [zero_sub]
  calc
    (-(e 4 * f 4)) * (-(e 4 * f 4)) = (e 4 * f 4) * (e 4 * f 4) := by simp
    _ = e 4 * (f 4 * e 4) * f 4 := by simp only [mul_assoc]
    _ = e 4 * (-(e 4 * f 4)) * f 4 := by rw [hfe]
    _ = -((e 4 * e 4) * (f 4 * f 4)) := by noncomm_ring
    _ = 1 := by rw [he, hf]; simp

omit [Algebra ℚ A] in
lemma boundary_exchange_gamma_anticomm :
    boundaryExchange e f * e 4 = -(e 4 * boundaryExchange e f) := by
  unfold boundaryExchange
  have he := hCl.e_sq 4
  have hef := hCl.ef_anti 4 4
  have hfe : f 4 * e 4 = -(e 4 * f 4) := by
    calc
      f 4 * e 4 = (e 4 * f 4 + f 4 * e 4) - e 4 * f 4 := by
        rw [add_sub_cancel_left]
      _ = 0 - e 4 * f 4 := by rw [hef]
      _ = -(e 4 * f 4) := by rw [zero_sub]
  calc
    (-(e 4 * f 4)) * e 4 = -(e 4 * (f 4 * e 4)) := by
      simp only [mul_assoc, neg_mul]
    _ = -(e 4 * (-(e 4 * f 4))) := by rw [hfe]
    _ = e 4 * (e 4 * f 4) := by simp
    _ = -(e 4 * (-(e 4 * f 4))) := by simp

instance boundary_operatorCl11 :
    OperatorCl11 (e 4) (boundaryExchange e f) where
  gamma_sq := hCl.e_sq 4
  exchange_sq := boundary_exchange_sq (e := e) (f := f)
  exchange_gamma_anticomm := boundary_exchange_gamma_anticomm (e := e) (f := f)

omit [Algebra ℚ A] in
lemma phase_boundary_eq :
    phase (e 4) (boundaryExchange e f) = f 4 := by
  unfold phase boundaryExchange
  have he := hCl.e_sq 4
  have hef := hCl.ef_anti 4 4
  have hfe : f 4 * e 4 = -(e 4 * f 4) := by
    calc
      f 4 * e 4 = (e 4 * f 4 + f 4 * e 4) - e 4 * f 4 := by
        rw [add_sub_cancel_left]
      _ = 0 - e 4 * f 4 := by rw [hef]
      _ = -(e 4 * f 4) := by rw [zero_sub]
  calc
    (-(e 4 * f 4)) * e 4 = -(e 4 * (f 4 * e 4)) := by
      simp only [mul_assoc, neg_mul]
    _ = -(e 4 * (-(e 4 * f 4))) := by rw [hfe]
    _ = e 4 * (e 4 * f 4) := by simp
    _ = f 4 := by rw [← mul_assoc, he, one_mul]

theorem wittPlus_boundary_eq :
    wittPlus (e 4) (boundaryExchange e f) = boundaryAnnihilator e f := by
  unfold wittPlus boundaryAnnihilator annihilator
  rw [phase_boundary_eq (e := e) (f := f)]
  rfl

theorem wittMinus_boundary_eq :
    wittMinus (e 4) (boundaryExchange e f) = boundaryCreator e f := by
  unfold wittMinus boundaryCreator creator
  rw [phase_boundary_eq (e := e) (f := f)]
  rfl

end InfoGeometry.Canonical.Cl55OperatorCl11Boundary
