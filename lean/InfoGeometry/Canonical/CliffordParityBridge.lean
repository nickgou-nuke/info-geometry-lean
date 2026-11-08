import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic

noncomputable section

namespace InfoGeometry.Canonical.CliffordParity

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable {Q : QuadraticForm R M}

class HasVolumeElement (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] 
    (Q : QuadraticForm R M) where
  Omega : CliffordAlgebra Q
  omega_sq : Omega * Omega = -1
  omega_odd : ∀ v : M, Omega * (CliffordAlgebra.ι Q v) = - ((CliffordAlgebra.ι Q v) * Omega)

open HasVolumeElement

/-- Spinorial Chirality Operator \Gamma_5 -/
def Gamma5 [HasVolumeElement R M Q] : CliffordAlgebra Q := Omega

/-- Weyl Projectors -/
def P_plus [Invertible (2 : R)] [HasVolumeElement R M Q] : CliffordAlgebra Q :=
  (⅟(2 : R) • 1) + (⅟(2 : R) • Gamma5)

def P_minus [Invertible (2 : R)] [HasVolumeElement R M Q] : CliffordAlgebra Q :=
  (⅟(2 : R) • 1) - (⅟(2 : R) • Gamma5)

/-- Odd Clifford multiplication by vector v performs chiral flip -/
theorem chiral_intertwining_plus [Invertible (2 : R)] [HasVolumeElement R M Q] (v : M) :
    P_plus * (CliffordAlgebra.ι Q v) = (CliffordAlgebra.ι Q v) * P_minus := by
  dsimp [P_plus, P_minus, Gamma5]
  rw [add_mul, mul_sub]
  have h1 : (⅟(2 : R) • (1 : CliffordAlgebra Q)) * (CliffordAlgebra.ι Q v) = (CliffordAlgebra.ι Q v) * (⅟(2 : R) • (1 : CliffordAlgebra Q)) := by
    rw [Algebra.smul_mul_assoc, one_mul, Algebra.mul_smul_comm, mul_one]
  have h2 : (⅟(2 : R) • Omega) * (CliffordAlgebra.ι Q v) = - ((CliffordAlgebra.ι Q v) * (⅟(2 : R) • Omega)) := by
    calc (⅟(2 : R) • Omega) * (CliffordAlgebra.ι Q v)
      _ = ⅟(2 : R) • (Omega * (CliffordAlgebra.ι Q v)) := by rw [Algebra.smul_mul_assoc]
      _ = ⅟(2 : R) • (- ((CliffordAlgebra.ι Q v) * Omega)) := by rw [omega_odd]
      _ = - (⅟(2 : R) • ((CliffordAlgebra.ι Q v) * Omega)) := by rw [smul_neg]
      _ = - ((CliffordAlgebra.ι Q v) * (⅟(2 : R) • Omega)) := by rw [Algebra.mul_smul_comm]
  rw [h1, h2]
  exact sub_eq_add_neg _ _ |>.symm

theorem chiral_intertwining_minus [Invertible (2 : R)] [HasVolumeElement R M Q] (v : M) :
    P_minus * (CliffordAlgebra.ι Q v) = (CliffordAlgebra.ι Q v) * P_plus := by
  dsimp [P_plus, P_minus, Gamma5]
  rw [sub_mul, mul_add]
  have h1 : (⅟(2 : R) • (1 : CliffordAlgebra Q)) * (CliffordAlgebra.ι Q v) = (CliffordAlgebra.ι Q v) * (⅟(2 : R) • (1 : CliffordAlgebra Q)) := by
    rw [Algebra.smul_mul_assoc, one_mul, Algebra.mul_smul_comm, mul_one]
  have h2 : (⅟(2 : R) • Omega) * (CliffordAlgebra.ι Q v) = - ((CliffordAlgebra.ι Q v) * (⅟(2 : R) • Omega)) := by
    calc (⅟(2 : R) • Omega) * (CliffordAlgebra.ι Q v)
      _ = ⅟(2 : R) • (Omega * (CliffordAlgebra.ι Q v)) := by rw [Algebra.smul_mul_assoc]
      _ = ⅟(2 : R) • (- ((CliffordAlgebra.ι Q v) * Omega)) := by rw [omega_odd]
      _ = - (⅟(2 : R) • ((CliffordAlgebra.ι Q v) * Omega)) := by rw [smul_neg]
      _ = - ((CliffordAlgebra.ι Q v) * (⅟(2 : R) • Omega)) := by rw [Algebra.mul_smul_comm]
  rw [h1, h2]
  exact sub_neg_eq_add _ _

/-- Odd-even conversion via \gamma_0 -/
def rho_R (x gamma_0 : CliffordAlgebra Q) : CliffordAlgebra Q :=
  x * gamma_0

/-- Hestenes Hermitian adjoint -/
def hestenes_adjoint (rev : CliffordAlgebra Q → CliffordAlgebra Q) (a gamma_0 : CliffordAlgebra Q) : CliffordAlgebra Q :=
  gamma_0 * (rev a) * gamma_0

/-- Hodge duality on paravectors -/
theorem hodge_paravector_duality [HasVolumeElement R M Q] 
    (rev : CliffordAlgebra Q → CliffordAlgebra Q)
    (x gamma_0 : CliffordAlgebra Q) (star_x : CliffordAlgebra Q)
    (h_star : star_x = rev x * Omega) 
    (h_gamma0_sq : gamma_0 * gamma_0 = 1)
    (h_omega_gamma0 : Omega * gamma_0 = - (gamma_0 * Omega))
    (h_rev_mul : ∀ a b, rev (a * b) = rev b * rev a)
    (h_rev_gamma0 : rev gamma_0 = gamma_0) :
    rho_R star_x gamma_0 = - hestenes_adjoint rev (rho_R x gamma_0) gamma_0 * Omega := by
  dsimp [rho_R, hestenes_adjoint]
  rw [h_star]
  -- LHS: rev x * (Omega * gamma_0) = rev x * (- (gamma_0 * Omega)) = - (rev x * gamma_0 * Omega)
  have lhs_eq : (rev x * Omega) * gamma_0 = - (rev x * gamma_0 * Omega) := by
    calc (rev x * Omega) * gamma_0
      _ = rev x * (Omega * gamma_0) := by rw [mul_assoc]
      _ = rev x * (- (gamma_0 * Omega)) := by rw [h_omega_gamma0]
      _ = - (rev x * (gamma_0 * Omega)) := by rw [mul_neg]
      _ = - (rev x * gamma_0 * Omega) := by rw [mul_assoc]
  
  -- RHS: - (gamma_0 * (rev gamma_0 * rev x) * gamma_0 * Omega)
  have rhs_eq : - (gamma_0 * (rev (x * gamma_0)) * gamma_0) * Omega = - (rev x * gamma_0 * Omega) := by
    calc - (gamma_0 * (rev (x * gamma_0)) * gamma_0) * Omega
      _ = - (gamma_0 * (rev gamma_0 * rev x) * gamma_0) * Omega := by rw [h_rev_mul]
      _ = - (gamma_0 * (gamma_0 * rev x) * gamma_0) * Omega := by rw [h_rev_gamma0]
      _ = - ((gamma_0 * gamma_0) * rev x * gamma_0) * Omega := by rw [←mul_assoc gamma_0 gamma_0 (rev x)]
      _ = - (1 * rev x * gamma_0) * Omega := by rw [h_gamma0_sq]
      _ = - (rev x * gamma_0) * Omega := by rw [one_mul]
      _ = - (rev x * gamma_0 * Omega) := by rw [neg_mul]

  rw [lhs_eq, rhs_eq]

end InfoGeometry.Canonical.CliffordParity
