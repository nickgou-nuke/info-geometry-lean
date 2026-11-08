/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.NuclearFiveGradeSolovievCommonCompression
import InfoGeometry.Physics.NuclearFeshbachReduction

/-!
# A complementary-resolvent obstruction on the algebraic common carrier

The existing common carrier contains every sequence, without a summability or
operator-domain restriction. At nonzero phonon coupling, an explicit recurrence
therefore supplies a nonzero full eigenvector at every real energy, entirely
in fermion coordinate zero. The current model projector reads coordinate two,
so all these vectors lie in its complementary kernel.

Consequently the shifted complementary block has no left inverse on that
complement, and hence no two-sided resolvent. This is an algebraic fact about
the actual existing carrier, not a claim about a Hilbert-space realization.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearAlgebraicResolventObstruction

open Matrix
open InfoGeometry.Algebra
open InfoGeometry.Physics.NuclearFiveGradeCommonCarrierRepresentation
open InfoGeometry.Physics.NuclearFiveGradeSolovievCommonCompression
open InfoGeometry.Physics.NuclearFeshbachReduction

/-- The unoccupied fermion coordinate, with the existing scalar Zorn coefficient. -/
def vacuumKet (a : ℝ) : FermionVector := ![scalarCoefficient a, 0, 0, 0]

@[simp] theorem vacuumKet_zero : vacuumKet 0 = 0 := by
  funext i
  fin_cases i <;> rfl

@[simp] theorem vacuumKet_add (a b : ℝ) :
    vacuumKet a + vacuumKet b = vacuumKet (a + b) := by
  funext i
  fin_cases i <;> ext j <;>
    simp [vacuumKet, scalarCoefficient, ZornVectorMatrix.add, ZornVectorMatrix.zero]

@[simp] theorem vacuumKet_smul (c a : ℝ) :
    c • vacuumKet a = vacuumKet (c * a) := by
  funext i
  fin_cases i <;> ext j <;>
    simp [vacuumKet, scalarCoefficient, ZornVectorMatrix.smul, ZornVectorMatrix.zero]

/-- Adjacent coefficients, constructed by ordinary recursion on `Nat`. -/
def coefficientPair (E omega g : ℝ) : ℕ → ℝ × ℝ
  | 0 => (1, E / g)
  | n + 1 =>
      let p := coefficientPair E omega g n
      (p.2, ((E - omega * ((n + 1 : ℕ) : ℝ)) * p.2 - g * p.1) /
        (g * ((n + 2 : ℕ) : ℝ)))

def coefficient (E omega g : ℝ) (n : ℕ) : ℝ :=
  (coefficientPair E omega g n).1

@[simp] theorem coefficient_zero (E omega g : ℝ) : coefficient E omega g 0 = 1 := rfl

@[simp] theorem coefficient_one (E omega g : ℝ) : coefficient E omega g 1 = E / g := rfl

theorem coefficient_step (E omega g : ℝ) (n : ℕ) :
    coefficient E omega g (n + 2) =
      ((E - omega * ((n + 1 : ℕ) : ℝ)) * coefficient E omega g (n + 1) -
        g * coefficient E omega g n) / (g * ((n + 2 : ℕ) : ℝ)) := rfl

theorem coefficient_zero_balance (E omega g : ℝ) (hg : g ≠ 0) :
    g * coefficient E omega g 1 = E * coefficient E omega g 0 := by
  simp only [coefficient_zero, coefficient_one, mul_one]
  field_simp [hg]

theorem coefficient_step_balance (E omega g : ℝ) (hg : g ≠ 0) (n : ℕ) :
    omega * ((n + 1 : ℕ) : ℝ) * coefficient E omega g (n + 1) +
        g * (coefficient E omega g n +
          ((n + 2 : ℕ) : ℝ) * coefficient E omega g (n + 2)) =
      E * coefficient E omega g (n + 1) := by
  have hn : ((n + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  have h := (eq_div_iff (mul_ne_zero hg hn)).mp (coefficient_step E omega g n)
  linear_combination h

/-- An actual vector in the unrestricted algebraic nuclear carrier. -/
def discardedEigenvector (E omega g : ℝ) : Carrier :=
  fun n => vacuumKet (coefficient E omega g n)

theorem discardedEigenvector_ne_zero (E omega g : ℝ) :
    discardedEigenvector E omega g ≠ 0 := by
  intro h
  have h0 := congrArg (fun ψ : Carrier => (ψ 0 0).a) h
  change (1 : ℝ) = 0 at h0
  exact one_ne_zero h0

theorem modelProjection_discardedEigenvector (E omega g : ℝ) :
    modelProjection (discardedEigenvector E omega g) = 0 := by
  have hr : modelReadout (discardedEigenvector E omega g) = 0 := by
    funext i
    fin_cases i <;> rfl
  change modelEmbed (modelReadout (discardedEigenvector E omega g)) = 0
  rw [hr, map_zero]

theorem quasiparticleNumber_vacuumStream (a : ℕ → ℝ) :
    quasiparticleNumber (fun n => vacuumKet (a n)) = 0 := by
  unfold quasiparticleNumber
  rw [number1_eq_diagonal]
  funext n i
  fin_cases i <;>
    simp [representation_apply, vacuumKet, Fin.sum_univ_four,
      ZornVectorMatrix.smul_zero, ZornVectorMatrix.zero_smul,
      ZornVectorMatrix.add_zero]

theorem fullHamiltonian_vacuumStream_zero (Eqp omega g : ℝ) (a : ℕ → ℝ) :
    fullHamiltonian Eqp omega g (fun n => vacuumKet (a n)) 0 =
      vacuumKet (g * a 1) := by
  simp [fullHamiltonian, quasiparticleNumber_vacuumStream, phononNumber,
    phononCreation, phononAnnihilation, Module.End.mul_apply]

theorem fullHamiltonian_vacuumStream_succ (Eqp omega g : ℝ) (a : ℕ → ℝ) (n : ℕ) :
    fullHamiltonian Eqp omega g (fun k => vacuumKet (a k)) (n + 1) =
      vacuumKet (omega * ((n + 1 : ℕ) : ℝ) * a (n + 1) +
        g * (a n + ((n + 2 : ℕ) : ℝ) * a (n + 2))) := by
  simp [fullHamiltonian, quasiparticleNumber_vacuumStream, phononNumber,
    phononCreation, phononAnnihilation, Module.End.mul_apply, mul_assoc, Nat.add_assoc]
  congr 1
  ring

/-- Every real energy has an algebraic eigenvector discarded by the model. -/
theorem fullHamiltonian_discardedEigenvector (Eqp omega g E : ℝ) (hg : g ≠ 0) :
    fullHamiltonian Eqp omega g (discardedEigenvector E omega g) =
      E • discardedEigenvector E omega g := by
  funext n
  cases n with
  | zero =>
      change fullHamiltonian Eqp omega g
          (fun k => vacuumKet (coefficient E omega g k)) 0 =
        E • vacuumKet (coefficient E omega g 0)
      rw [fullHamiltonian_vacuumStream_zero, vacuumKet_smul,
        coefficient_zero_balance E omega g hg]
  | succ n =>
      change fullHamiltonian Eqp omega g
          (fun k => vacuumKet (coefficient E omega g k)) (n + 1) =
        E • vacuumKet (coefficient E omega g (n + 1))
      rw [fullHamiltonian_vacuumStream_succ, vacuumKet_smul,
        coefficient_step_balance E omega g hg n]

theorem denominator_discardedEigenvector (Eqp omega g E : ℝ) (hg : g ≠ 0) :
    denominator modelProjection (fullHamiltonian Eqp omega g) E
      (discardedEigenvector E omega g) = 0 := by
  have hQ : (1 - modelProjection) (discardedEigenvector E omega g) =
      discardedEigenvector E omega g := by
    simp only [LinearMap.sub_apply, Module.End.one_apply,
      modelProjection_discardedEigenvector, sub_zero]
  change E • ((1 - modelProjection) (discardedEigenvector E omega g)) -
    (1 - modelProjection) (fullHamiltonian Eqp omega g
      ((1 - modelProjection) (discardedEigenvector E omega g))) = 0
  rw [hQ, fullHamiltonian_discardedEigenvector Eqp omega g E hg,
    map_smul, hQ, sub_self]

/-- On the current unrestricted carrier, a nonzero coupling excludes even
a left complementary inverse, hence excludes a two-sided Feshbach resolvent. -/
theorem no_left_complementary_resolvent (Eqp omega g E : ℝ) (hg : g ≠ 0)
    (R : Operator) :
    R * denominator modelProjection (fullHamiltonian Eqp omega g) E ≠
      1 - modelProjection := by
  intro h
  have hv := LinearMap.congr_fun h (discardedEigenvector E omega g)
  simp only [Module.End.mul_apply,
    denominator_discardedEigenvector Eqp omega g E hg, map_zero,
    LinearMap.sub_apply, Module.End.one_apply,
    modelProjection_discardedEigenvector, sub_zero] at hv
  exact discardedEigenvector_ne_zero E omega g hv.symm

end InfoGeometry.Physics.NuclearAlgebraicResolventObstruction
