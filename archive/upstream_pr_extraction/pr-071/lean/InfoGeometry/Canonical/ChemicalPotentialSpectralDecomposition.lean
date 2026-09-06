import Mathlib

/-!
# Common-projector chemical-potential deformation

This owner isolates the finite commuting control case.  A supplied common
spectral resolution carries the projector algebra and the two diagonal
readouts (energy and charge).  The chemical potential changes only the
coefficient of each already fixed projector.

No differentiability, Berry connection, or spectral theorem for an analytic
operator family is claimed here; those require additional finite-dimensional
and regularity hypotheses.
-/

open scoped BigOperators

namespace InfoGeometry.Canonical

section

variable {d r : ℕ}

abbrev ComplexMatrix (d : ℕ) := Matrix (Fin d) (Fin d) ℂ

/-- A finite common spectral resolution for a Hamiltonian and a number
operator.  The projector laws are part of the supplied finite algebraic data.
-/
structure CommonSpectralResolution (d r : ℕ) where
  projector : Fin r → ComplexMatrix d
  energy : Fin r → ℝ
  charge : Fin r → ℝ
  hamiltonian : ComplexMatrix d
  number : ComplexMatrix d
  hamiltonian_expansion :
    hamiltonian = ∑ i, (energy i : ℂ) • projector i
  number_expansion :
    number = ∑ i, (charge i : ℂ) • projector i
  projector_mul :
    ∀ i j, projector i * projector j = if i = j then projector i else 0
  projector_sum : ∑ i, projector i = 1

namespace CommonSpectralResolution

variable (S : CommonSpectralResolution d r)

/-- The finite grand-canonical operator `H - μ N`. -/
def grandCanonicalOperator (μ : ℝ) : ComplexMatrix d :=
  S.hamiltonian - (μ : ℂ) • S.number

/-- Its expansion in the common spectral projectors. -/
theorem grandCanonicalOperator_spectral (μ : ℝ) :
    S.grandCanonicalOperator μ =
      ∑ i, ((S.energy i - μ * S.charge i : ℝ) : ℂ) • S.projector i := by
  rw [grandCanonicalOperator, S.hamiltonian_expansion, S.number_expansion]
  rw [Finset.smul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [smul_smul]
  norm_num
  rw [sub_smul]
  simp

/-- Each common projector is an eigenprojector of the deformed operator. -/
theorem grandCanonicalOperator_mul_projector (μ : ℝ) (i : Fin r) :
    S.grandCanonicalOperator μ * S.projector i =
      ((S.energy i - μ * S.charge i : ℝ) : ℂ) • S.projector i := by
  rw [grandCanonicalOperator_spectral]
  calc
    (∑ j, ((S.energy j - μ * S.charge j : ℝ) : ℂ) • S.projector j) *
        S.projector i =
        ∑ j, ((S.energy j - μ * S.charge j : ℝ) : ℂ) •
          (S.projector j * S.projector i) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro j hj
            rw [smul_mul_assoc]
    _ = ∑ j, if j = i then
          ((S.energy j - μ * S.charge j : ℝ) : ℂ) • S.projector i else 0 := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [S.projector_mul]
          split_ifs
          · subst j
            simp
          · simp
    _ = ((S.energy i - μ * S.charge i : ℝ) : ℂ) • S.projector i := by
          simp

/-- The common projectors commute, as required in the finite control case. -/
theorem projector_commute (i j : Fin r) :
    S.projector i * S.projector j = S.projector j * S.projector i := by
  rw [S.projector_mul, S.projector_mul]
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h]

/-- The spectral projectors are independent of the chemical potential. -/
def spectralProjector (_μ : ℝ) (i : Fin r) : ComplexMatrix d := S.projector i

@[simp] theorem spectralProjector_constant (μ ν : ℝ) (i : Fin r) :
    S.spectralProjector μ i = S.spectralProjector ν i := rfl

end CommonSpectralResolution

end

end InfoGeometry.Canonical
