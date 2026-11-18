/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Star.Unitary
import InfoGeometry.OperatorAlgebra.ChiralProjectorFromInvolution
import InfoGeometry.Krein.TomitaMatrixAtom

/-!
# The overlap operator from two involutions

The ordered product of two self-adjoint involutions is unitary, and
`D = 1 + gamma * epsilon` satisfies the Ginsparg–Wilson identity with coefficient
one. Neither commutation nor anticommutation is assumed. The chiral intertwiners
use the half-projectors already owned by `ChiralInvolution`.

The algebraic identity only needs a ring and the two square laws. The star
conclusions additionally need self-adjointness; the projector conclusions use
an algebra over `ℝ`. A concrete pair in the full real matrix algebra `M₂(ℝ)`
shows that the construction retains noncommuting operators and that its normal
Dirac operator need not be self-adjoint.

This file starts with supplied involutions. Constructing a spectral sign from a
gapped Hamiltonian, proving lattice locality, and choosing a determinant-line
phase are separate analytic and geometric problems.

The normalization agrees with Neuberger's polynomial identity for `D = 1 + V`:
<https://arxiv.org/abs/hep-lat/9801031>.
-/

namespace InfoGeometry.Algebra.OverlapInvolutionPair

variable {A : Type*} [Ring A]

/-- The ordered overlap phase. -/
def phase (gamma epsilon : A) : A := gamma * epsilon

/-- The overlap operator in the normalization with Ginsparg–Wilson coefficient one. -/
def dirac (gamma epsilon : A) : A := 1 + phase gamma epsilon

/-- Left multiplication by the first involution removes its square. -/
theorem gamma_mul_dirac (gamma epsilon : A) (hgamma : gamma * gamma = 1) :
    gamma * dirac gamma epsilon = gamma + epsilon := by
  unfold dirac phase
  rw [mul_add, mul_one, ← mul_assoc, hgamma, one_mul]

/-- Right multiplication by the second involution removes its square. -/
theorem dirac_mul_epsilon (gamma epsilon : A) (hepsilon : epsilon * epsilon = 1) :
    dirac gamma epsilon * epsilon = epsilon + gamma := by
  unfold dirac phase
  rw [add_mul, one_mul, mul_assoc, hepsilon, mul_one]

/-- The overlap operator intertwines the two involutions without commuting them. -/
theorem gamma_mul_dirac_eq_dirac_mul_epsilon (gamma epsilon : A)
    (hgamma : gamma * gamma = 1) (hepsilon : epsilon * epsilon = 1) :
    gamma * dirac gamma epsilon = dirac gamma epsilon * epsilon := by
  rw [gamma_mul_dirac gamma epsilon hgamma, dirac_mul_epsilon gamma epsilon hepsilon]
  exact add_comm gamma epsilon

/-- The exact defect in Ginsparg–Wilson is the defect in the second square law. -/
theorem ginspargWilson_residual (gamma epsilon : A) (hgamma : gamma * gamma = 1) :
    dirac gamma epsilon * gamma * dirac gamma epsilon -
        (gamma * dirac gamma epsilon + dirac gamma epsilon * gamma) =
      gamma * (epsilon * epsilon - 1) := by
  calc
    dirac gamma epsilon * gamma * dirac gamma epsilon -
        (gamma * dirac gamma epsilon + dirac gamma epsilon * gamma) =
        dirac gamma epsilon * (gamma + epsilon) -
          ((gamma + epsilon) + dirac gamma epsilon * gamma) := by
      simp only [mul_assoc, gamma_mul_dirac gamma epsilon hgamma]
    _ = dirac gamma epsilon * epsilon - (gamma + epsilon) := by
      rw [mul_add]
      abel
    _ = gamma * (epsilon * epsilon - 1) := by
      unfold dirac phase
      noncomm_ring

/-- The polynomial Ginsparg–Wilson identity also covers zero modes of `D`. -/
theorem ginspargWilson (gamma epsilon : A)
    (hgamma : gamma * gamma = 1) (hepsilon : epsilon * epsilon = 1) :
    gamma * dirac gamma epsilon + dirac gamma epsilon * gamma =
      dirac gamma epsilon * gamma * dirac gamma epsilon := by
  have h := ginspargWilson_residual gamma epsilon hgamma
  rw [hepsilon, sub_self, mul_zero] at h
  exact (sub_eq_zero.mp h).symm

/-- With the first square law fixed, Ginsparg–Wilson is equivalent to the second. -/
theorem ginspargWilson_iff (gamma epsilon : A) (hgamma : gamma * gamma = 1) :
    (gamma * dirac gamma epsilon + dirac gamma epsilon * gamma =
      dirac gamma epsilon * gamma * dirac gamma epsilon) ↔
      epsilon * epsilon = 1 := by
  constructor
  · intro h
    have hz : gamma * (epsilon * epsilon - 1) = 0 := by
      rw [← ginspargWilson_residual gamma epsilon hgamma, h, sub_self]
    have hzero : epsilon * epsilon - 1 = 0 := by
      calc
        epsilon * epsilon - 1 = gamma * (gamma * (epsilon * epsilon - 1)) := by
          rw [← mul_assoc, hgamma, one_mul]
        _ = 0 := by rw [hz, mul_zero]
    exact sub_eq_zero.mp hzero
  · exact ginspargWilson gamma epsilon hgamma

/-- In this normalization the modified chirality is the negative second involution. -/
theorem modified_chirality (gamma epsilon : A) (hgamma : gamma * gamma = 1) :
    gamma * (1 - dirac gamma epsilon) = -epsilon := by
  rw [mul_sub, mul_one, gamma_mul_dirac gamma epsilon hgamma]
  abel

section Star

variable [StarRing A]

/-- Reversal of the ordered phase is its adjoint. -/
theorem star_phase (gamma epsilon : A)
    (hgamma : IsSelfAdjoint gamma) (hepsilon : IsSelfAdjoint epsilon) :
    star (phase gamma epsilon) = phase epsilon gamma := by
  simp only [phase, star_mul, hgamma.star_eq, hepsilon.star_eq]

/-- Two self-adjoint involutions have a unitary ordered product. -/
theorem phase_mem_unitary (gamma epsilon : A)
    (hgamma_sq : gamma * gamma = 1) (hepsilon_sq : epsilon * epsilon = 1)
    (hgamma : IsSelfAdjoint gamma) (hepsilon : IsSelfAdjoint epsilon) :
    phase gamma epsilon ∈ unitary A := by
  change gamma * epsilon ∈ unitary A
  apply (unitary A).mul_mem
  · exact ⟨by rw [hgamma.star_eq, hgamma_sq], by rw [hgamma.star_eq, hgamma_sq]⟩
  · exact ⟨by rw [hepsilon.star_eq, hepsilon_sq], by rw [hepsilon.star_eq, hepsilon_sq]⟩

/-- The overlap phase as an element of Mathlib's native unitary group. -/
def unitaryPhase (gamma epsilon : A)
    (hgamma_sq : gamma * gamma = 1) (hepsilon_sq : epsilon * epsilon = 1)
    (hgamma : IsSelfAdjoint gamma) (hepsilon : IsSelfAdjoint epsilon) : unitary A :=
  ⟨phase gamma epsilon,
    phase_mem_unitary gamma epsilon hgamma_sq hepsilon_sq hgamma hepsilon⟩

/-- Gamma Hermiticity follows from the first square law and both adjoint laws. -/
theorem star_dirac (gamma epsilon : A) (hgamma_sq : gamma * gamma = 1)
    (hgamma : IsSelfAdjoint gamma) (hepsilon : IsSelfAdjoint epsilon) :
    star (dirac gamma epsilon) = gamma * dirac gamma epsilon * gamma := by
  rw [gamma_mul_dirac gamma epsilon hgamma_sq]
  simp only [dirac, phase, star_add, star_one, star_mul,
    hgamma.star_eq, hepsilon.star_eq, add_mul, hgamma_sq]

/-- The adjoint square has the same exact value on either side of the overlap operator. -/
theorem dirac_star_mul (gamma epsilon : A)
    (hgamma_sq : gamma * gamma = 1) (hepsilon_sq : epsilon * epsilon = 1)
    (hgamma : IsSelfAdjoint gamma) (hepsilon : IsSelfAdjoint epsilon) :
    star (dirac gamma epsilon) * dirac gamma epsilon =
      dirac gamma epsilon + star (dirac gamma epsilon) := by
  have hunit := phase_mem_unitary gamma epsilon hgamma_sq hepsilon_sq hgamma hepsilon
  change star (1 + phase gamma epsilon) * (1 + phase gamma epsilon) =
    (1 + phase gamma epsilon) + star (1 + phase gamma epsilon)
  simp only [star_add, star_one]
  calc
    (1 + star (phase gamma epsilon)) * (1 + phase gamma epsilon) =
        1 + phase gamma epsilon + star (phase gamma epsilon) +
          star (phase gamma epsilon) * phase gamma epsilon := by noncomm_ring
    _ = (1 + phase gamma epsilon) + (1 + star (phase gamma epsilon)) := by
      rw [Unitary.star_mul_self_of_mem hunit]
      abel

/-- The other ordered adjoint square has the same value. -/
theorem dirac_mul_star (gamma epsilon : A)
    (hgamma_sq : gamma * gamma = 1) (hepsilon_sq : epsilon * epsilon = 1)
    (hgamma : IsSelfAdjoint gamma) (hepsilon : IsSelfAdjoint epsilon) :
    dirac gamma epsilon * star (dirac gamma epsilon) =
      dirac gamma epsilon + star (dirac gamma epsilon) := by
  have hunit := phase_mem_unitary gamma epsilon hgamma_sq hepsilon_sq hgamma hepsilon
  change (1 + phase gamma epsilon) * star (1 + phase gamma epsilon) =
    (1 + phase gamma epsilon) + star (1 + phase gamma epsilon)
  simp only [star_add, star_one]
  calc
    (1 + phase gamma epsilon) * (1 + star (phase gamma epsilon)) =
        1 + star (phase gamma epsilon) + phase gamma epsilon +
          phase gamma epsilon * star (phase gamma epsilon) := by noncomm_ring
    _ = (1 + phase gamma epsilon) + (1 + star (phase gamma epsilon)) := by
      rw [Unitary.mul_star_self_of_mem hunit]
      abel

/-- The overlap operator is normal in the native star-algebra sense. -/
theorem dirac_isStarNormal (gamma epsilon : A)
    (hgamma_sq : gamma * gamma = 1) (hepsilon_sq : epsilon * epsilon = 1)
    (hgamma : IsSelfAdjoint gamma) (hepsilon : IsSelfAdjoint epsilon) :
    IsStarNormal (dirac gamma epsilon) where
  star_comm_self :=
    (dirac_star_mul gamma epsilon hgamma_sq hepsilon_sq hgamma hepsilon).trans
      (dirac_mul_star gamma epsilon hgamma_sq hepsilon_sq hgamma hepsilon).symm

/-- Self-adjointness, unlike normality, requires the two supplied signs to commute. -/
theorem dirac_isSelfAdjoint_iff_commute (gamma epsilon : A)
    (hgamma : IsSelfAdjoint gamma) (hepsilon : IsSelfAdjoint epsilon) :
    IsSelfAdjoint (dirac gamma epsilon) ↔ Commute gamma epsilon := by
  constructor
  · intro h
    have heq : (1 : A) + epsilon * gamma = 1 + gamma * epsilon := by
      simpa only [IsSelfAdjoint, dirac, phase, star_add, star_one, star_mul,
        hgamma.star_eq, hepsilon.star_eq] using h
    exact (add_left_cancel heq).symm
  · intro h
    change star (1 + gamma * epsilon) = 1 + gamma * epsilon
    rw [star_add, star_one, star_mul, hgamma.star_eq, hepsilon.star_eq, h.eq]

end Star

section Projectors

variable [Algebra ℝ A]

open InfoGeometry.OperatorAlgebra

/-- The overlap operator transports the existing positive sign idempotents.
Since the modified chirality is `-epsilon`, its negative projector is the
positive projector of `epsilon` occurring here. -/
theorem Pleft_mul_dirac (gamma epsilon : ChiralInvolution A) :
    gamma.Pleft * dirac gamma.chi epsilon.chi =
      dirac gamma.chi epsilon.chi * epsilon.Pleft := by
  unfold ChiralInvolution.Pleft
  rw [smul_mul_assoc, mul_smul_comm]
  apply congrArg (fun x : A => (1 / 2 : ℝ) • x)
  rw [add_mul, one_mul, mul_add, mul_one,
    gamma_mul_dirac_eq_dirac_mul_epsilon gamma.chi epsilon.chi gamma.chi_sq epsilon.chi_sq]

/-- The same ordered intertwiner transports the existing negative sign idempotents. -/
theorem Pright_mul_dirac (gamma epsilon : ChiralInvolution A) :
    gamma.Pright * dirac gamma.chi epsilon.chi =
      dirac gamma.chi epsilon.chi * epsilon.Pright := by
  unfold ChiralInvolution.Pright
  rw [smul_mul_assoc, mul_smul_comm]
  apply congrArg (fun x : A => (1 / 2 : ℝ) • x)
  rw [sub_mul, one_mul, mul_sub, mul_one,
    gamma_mul_dirac_eq_dirac_mul_epsilon gamma.chi epsilon.chi gamma.chi_sq epsilon.chi_sq]

end Projectors

section RealMatrixWitness

open InfoGeometry.Krein.TomitaMatrixAtom

/-- The existing real diagonal sign and swap are a concrete noncommuting pair. -/
theorem eps_J_noncommute : eps * J ≠ J * eps := by
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
  norm_num [eps, J, Matrix.mul_apply, Fin.sum_univ_two] at h01

/-- The full real matrix algebra contains a concrete pair of self-adjoint
involutions that do not commute. The entries are supplied by the existing atom. -/
theorem exists_noncommuting_real_involutions :
    ∃ gamma epsilon : Matrix (Fin 2) (Fin 2) ℝ,
      gamma * epsilon ≠ epsilon * gamma ∧
      gamma * gamma = 1 ∧ epsilon * epsilon = 1 ∧
      IsSelfAdjoint gamma ∧ IsSelfAdjoint epsilon := by
  have hgamma : IsSelfAdjoint eps := by
    change star eps = eps
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [eps, Matrix.star_apply]
  have hepsilon : IsSelfAdjoint J := by
    change star J = J
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [J, Matrix.star_apply]
  exact ⟨eps, J, eps_J_noncommute, eps_sq, J_sq, hgamma, hepsilon⟩

/-- An actual noncommuting pair in the full real matrix algebra gives a normal,
non-self-adjoint overlap operator. The matrices are reused from the split atom. -/
theorem real_matrix_noncommuting_witness :
    ∃ gamma epsilon : Matrix (Fin 2) (Fin 2) ℝ,
      gamma * gamma = 1 ∧ epsilon * epsilon = 1 ∧
      IsSelfAdjoint gamma ∧ IsSelfAdjoint epsilon ∧
      gamma * epsilon ≠ epsilon * gamma ∧
      gamma * dirac gamma epsilon + dirac gamma epsilon * gamma =
        dirac gamma epsilon * gamma * dirac gamma epsilon ∧
      IsStarNormal (dirac gamma epsilon) ∧ ¬IsSelfAdjoint (dirac gamma epsilon) := by
  obtain ⟨gamma, epsilon, hnoncomm, hgamma_sq, hepsilon_sq, hgamma, hepsilon⟩ :=
    exists_noncommuting_real_involutions
  refine ⟨gamma, epsilon, hgamma_sq, hepsilon_sq, hgamma, hepsilon, hnoncomm,
    ginspargWilson gamma epsilon hgamma_sq hepsilon_sq,
    dirac_isStarNormal gamma epsilon hgamma_sq hepsilon_sq hgamma hepsilon, ?_⟩
  intro h
  exact hnoncomm ((dirac_isSelfAdjoint_iff_commute gamma epsilon hgamma hepsilon).mp h).eq

end RealMatrixWitness

end InfoGeometry.Algebra.OverlapInvolutionPair
