import Mathlib
import InfoGeometry.Geometry.RealRotorCore
import InfoGeometry.Krein.FiniteMadelungPhaseRotation
import InfoGeometry.Canonical.ArakiItakuraSaitoEquivalence
import InfoGeometry.Canonical.OperatorialItakuraSaitoFramework
import InfoGeometry.Canonical.MatrixExponentialTraceDet
import InfoGeometry.Canonical.RelativeModularHamiltonian
import InfoGeometry.Canonical.CuntzMatrixCompatibleStateNet
import InfoGeometry.Canonical.MatrixExponentialTraceDet
import InfoGeometry.Arithmetic.RiemannPoleZeroMonodromy
import InfoGeometry.Arithmetic.IndexTheorem
import InfoGeometry.Thermal.FiniteMatrix
import InfoGeometry.Canonical.MadelungScaleQuantum

/-!
# Finite Madelung--Tomita quantization

This file is the finite-dimensional algebraic owner for the real part of the
Madelung/Tomita chain.  It deliberately uses the existing real chiral carrier,
the finite phase rotation, the relative-modular Itakura--Saito owner, and the
finite divisor/kernel index owner.

The exact canonical commutation relation is not asserted on a finite matrix
carrier: its trace obstruction is proved explicitly below.  A finite matrix
discretization therefore carries a boundary defect rather than pretending to
be the unbounded logarithmic derivative.
-/

noncomputable section

namespace InfoGeometry.Canonical.FiniteMadelungTomitaQuantization

open Matrix
open InfoGeometry.Geometry
open InfoGeometry.Geometry.RealChiralPhase
open InfoGeometry.Krein.FiniteMadelungPhaseRotation
open InfoGeometry.Canonical.ArakiItakuraSaitoEquivalence
open InfoGeometry.Arithmetic.RiemannPoleZeroMonodromy
open InfoGeometry.Arithmetic.IndexTheorem
open InfoGeometry.Algebra.EulerLaurentDerivation
open InfoGeometry.Canonical.RelativeModularHamiltonian
open InfoGeometry.Canonical.RelativePotentialCore
open InfoGeometry.Canonical.CuntzMatrixCompatibleStateNet
open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.Canonical.PositiveRayCore
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.OperatorAlgebra.FiniteRelativeModularOperator
open InfoGeometry.Algebra.EulerLaurentDerivation

/-! ## Finite polar/Madelung carrier -/

abbrev FiniteCarrier := Matrix (Fin 2) (Fin 2) ℝ

def polarPhase (φ : ℝ) : FiniteCarrier := phaseRotation φ

def polarPositive : FiniteCarrier := 1

def polarState (φ : ℝ) : FiniteCarrier := polarPhase φ * polarPositive

theorem polarState_eq_phase (φ : ℝ) :
    polarState φ = polarPhase φ := by
  simp [polarState, polarPositive]

theorem polarState_factorization (φ : ℝ) :
    polarState φ = polarPhase φ * polarPositive := rfl

theorem polarPositive_sq : polarPositive * polarPositive = (1 : FiniteCarrier) := by
  simp [polarPositive]

theorem polarPositive_self_adjoint : polarPositive.transpose = polarPositive := by
  simp [polarPositive]

theorem polarPhase_orthogonal (φ : ℝ) :
    (polarPhase φ).transpose * polarPhase φ = 1 :=
  phaseRotation_transpose_mul φ

def positivePolarPart (r : Fin 2 → ℝ) : FiniteCarrier :=
  Matrix.diagonal r

def positivePolarSquare (r : Fin 2 → ℝ) : FiniteCarrier :=
  Matrix.diagonal (fun i => r i ^ 2)

theorem positivePolarPart_posSemidef
    (r : Fin 2 → ℝ) (hr : ∀ i, 0 ≤ r i) :
    (positivePolarPart r).PosSemidef := by
  exact Matrix.PosSemidef.diagonal hr

theorem positivePolarSquare_posSemidef (r : Fin 2 → ℝ) :
    (positivePolarSquare r).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro i
  exact sq_nonneg (r i)

def positivePolarState (φ : ℝ) (r : Fin 2 → ℝ) : FiniteCarrier :=
  polarPhase φ * positivePolarPart r

theorem positivePolarPart_sq (r : Fin 2 → ℝ) :
    positivePolarPart r * positivePolarPart r = positivePolarSquare r := by
  rw [positivePolarPart, positivePolarSquare, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  simp [pow_two]

theorem positivePolarState_factorization (φ : ℝ) (r : Fin 2 → ℝ) :
    positivePolarState φ r = polarPhase φ * positivePolarPart r := rfl

theorem positivePolarPart_self_adjoint (r : Fin 2 → ℝ) :
    (positivePolarPart r).transpose = positivePolarPart r := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [positivePolarPart]
  · simp [positivePolarPart, h, Ne.symm h]

theorem positivePolarState_transpose_mul_self
    (φ : ℝ) (r : Fin 2 → ℝ) :
    (positivePolarState φ r).transpose * positivePolarState φ r =
      positivePolarSquare r := by
  calc
    (positivePolarState φ r).transpose * positivePolarState φ r =
        (positivePolarPart r).transpose *
          ((polarPhase φ).transpose * polarPhase φ) *
            positivePolarPart r := by
      simp [positivePolarState, Matrix.transpose_mul, mul_assoc]
    _ = positivePolarPart r * positivePolarPart r := by
      rw [positivePolarPart_self_adjoint, polarPhase_orthogonal]
      simp
    _ = positivePolarSquare r := positivePolarPart_sq r

/-! ## Finite ancestor and chiral standing/travelling waves -/

def ancestor (Ξ Υ : ℝ → ℝ) (t : ℝ) : RealChiralPhase := (Ξ t, Υ t)

def hestenesConjugate (Ξ Υ : ℝ → ℝ) (t : ℝ) : RealChiralPhase :=
  (Ξ t, -Υ t)

theorem hestenesConjugate_involutive (Ξ Υ : ℝ → ℝ) (t : ℝ) :
    hestenesConjugate (fun u => (ancestor Ξ Υ u).1)
      (fun u => -(ancestor Ξ Υ u).2) t = ancestor Ξ Υ t := by
  simp [hestenesConjugate, ancestor]

theorem hestenesConjugate_normSq (Ξ Υ : ℝ → ℝ) (t : ℝ) :
    normSq (hestenesConjugate Ξ Υ t) = normSq (ancestor Ξ Υ t) := by
  simp [hestenesConjugate, ancestor, normSq]
  ring

def standingPlus (Ξ Υ : ℝ → ℝ) (t : ℝ) : ℝ := Ξ t + Υ t

def standingMinus (Ξ Υ : ℝ → ℝ) (t : ℝ) : ℝ := Ξ t - Υ t

theorem ancestor_reconstruct (Ξ Υ : ℝ → ℝ) (t : ℝ) :
    ((standingPlus Ξ Υ t + standingMinus Ξ Υ t) / 2,
      (standingPlus Ξ Υ t - standingMinus Ξ Υ t) / 2) = ancestor Ξ Υ t := by
  simp [standingPlus, standingMinus, ancestor]

theorem standing_reconstruct (Ξ Υ : ℝ → ℝ) (t : ℝ) :
    standingPlus Ξ Υ t = (ancestor Ξ Υ t).1 + (ancestor Ξ Υ t).2 ∧
    standingMinus Ξ Υ t = (ancestor Ξ Υ t).1 - (ancestor Ξ Υ t).2 := by
  constructor <;> rfl

theorem ancestor_normSq (Ξ Υ : ℝ → ℝ) (t : ℝ) :
    normSq (ancestor Ξ Υ t) = (Ξ t)^2 + (Υ t)^2 := by
  simp [ancestor, normSq]

theorem ancestor_normSq_nonneg (Ξ Υ : ℝ → ℝ) (t : ℝ) :
    0 ≤ normSq (ancestor Ξ Υ t) := by
  rw [ancestor_normSq]
  positivity

theorem ancestor_normSq_eq_zero_iff (Ξ Υ : ℝ → ℝ) (t : ℝ) :
    normSq (ancestor Ξ Υ t) = 0 ↔ Ξ t = 0 ∧ Υ t = 0 := by
  rw [ancestor_normSq]
  constructor
  · intro h
    have hΞ : Ξ t = 0 := by
      nlinarith [sq_nonneg (Ξ t), sq_nonneg (Υ t)]
    have hΥ : Υ t = 0 := by
      nlinarith [sq_nonneg (Ξ t), sq_nonneg (Υ t)]
    exact ⟨hΞ, hΥ⟩
  · rintro ⟨hΞ, hΥ⟩
    simp [hΞ, hΥ]

/--
The finite chiral carrier has the same nonzero-radius criterion as the native
complex Madelung polar decomposition.  The radius is read through the existing
`ancestor_normSq` theorem rather than introduced a second time.
-/
theorem finite_madelung_polar_iff_ancestor_normSq_pos
    (Ξ Υ : ℝ → ℝ) (t : ℝ) (K : ℂ) (hK : K * K = -1)
    (ℏ : ℝ) (hℏ : ℏ ≠ 0) :
    (∃ (ρ S : ℝ), 0 < ρ ∧ Ξ t = Real.sqrt ρ * Real.cos (S / ℏ) ∧
      Υ t = Real.sqrt ρ * Real.sin (S / ℏ)) ↔
        0 < normSq (ancestor Ξ Υ t) := by
  rw [ancestor_normSq]
  exact InfoGeometry.Canonical.MadelungScaleQuantum.hestenesKreinToMadelung
    Ξ Υ t K hK ℏ hℏ

/-! ## Logarithmic radial and phase rates -/

theorem ancestor_log_normSq_derivative
    (Ξ Υ dΞ dΥ : ℝ → ℝ) (t : ℝ)
    (hΞ : HasDerivAt Ξ (dΞ t) t)
    (hΥ : HasDerivAt Υ (dΥ t) t)
    (hρ : normSq (ancestor Ξ Υ t) ≠ 0) :
    HasDerivAt (fun u => Real.log (normSq (ancestor Ξ Υ u)))
      (2 * chiralRadialRate (ancestor Ξ Υ t) (dΞ t, dΥ t)) t := by
  simpa [ancestor] using
    hasDerivAt_log_normSq_of_components Ξ Υ (dΞ t) (dΥ t) t hΞ hΥ hρ

theorem phase_current_quadrature
    (Ξ Υ dΞ dΥ : ℝ → ℝ) (t : ℝ)
    (hρ : normSq (ancestor Ξ Υ t) ≠ 0) :
    normSq (ancestor Ξ Υ t) *
        chiralPhaseRate (ancestor Ξ Υ t) (dΞ t, dΥ t) =
      Ξ t * dΥ t - Υ t * dΞ t := by
  simpa [ancestor, phaseNumerator] using
    chiralPhaseRate_mul_normSq (ancestor Ξ Υ t) (dΞ t, dΥ t) hρ

/-! ## Finite current conservation -/

def madelungCurrent (ρ S : ℝ → ℝ) (m : ℝ) (t : ℝ) : ℝ :=
  (ρ t / m) * deriv S t

theorem current_derivative_zero_of_constant_density_and_velocity
    (ρ S : ℝ → ℝ) (m c v : ℝ)
    (hρ : ∀ t, ρ t = c)
    (hv : ∀ t, deriv S t = v) :
    ∀ t, deriv (fun u => madelungCurrent ρ S m u) t = 0 := by
  intro t
  have hfun : (fun u => madelungCurrent ρ S m u) =
      (fun _ => (c / m) * v) := by
    funext u
    simp [madelungCurrent, hρ u, hv u]
  rw [hfun]
  exact (hasDerivAt_const t ((c / m) * v)).deriv

theorem current_zero_of_stationary_phase
    (ρ S : ℝ → ℝ) (m : ℝ)
    (hρ : ∀ t, ρ t = ρ 0)
    (hS : ∀ t, deriv S t = deriv S 0) :
    ∀ t, deriv (fun u => madelungCurrent ρ S m u) t = 0 := by
  exact current_derivative_zero_of_constant_density_and_velocity ρ S m
    (ρ 0) (deriv S 0) hρ hS

/-! ## Finite logarithmic momentum and the CCR obstruction -/

def logCoordinate (q : Fin n → ℝ) : Fin n → ℝ := q

def finiteMomentum (K : ℝ) (d : Fin n → Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  K • d

theorem finiteMomentum_smul (K L : ℝ) (d : Fin n → Fin n → ℝ) :
    finiteMomentum (K + L) d = finiteMomentum K d + finiteMomentum L d := by
  simp [finiteMomentum, add_smul]

def matrixCommutator {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) := A * B - B * A

theorem trace_matrixCommutator_zero {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.trace (matrixCommutator A B) = 0 := by
  unfold matrixCommutator
  rw [Matrix.trace_sub, Matrix.trace_mul_comm A B]
  simp

theorem finite_CCR_identity_impossible {n : ℕ} (hn : 0 < n)
    (Q P : Matrix (Fin n) (Fin n) ℝ) (K : ℝ) (hK : K ≠ 0) :
    matrixCommutator Q P ≠ K • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  intro h
  have ht := congrArg Matrix.trace h
  rw [trace_matrixCommutator_zero] at ht
  have hcases : n = 0 ∨ K = 0 := by
    simpa [Matrix.trace, Matrix.smul_apply] using ht
  rcases hcases with hn0 | hK0
  · exact False.elim (Nat.ne_of_gt hn hn0)
  · exact hK hK0

/-! ## Relative-modular IS action and Hamiltonian commutator -/

abbrev FiniteComplexCarrier := MatrixCarrier 2
abbrev FiniteRelativeEnd := EndCarrier 2

def finiteRelativeISAction
    (ρ σ : InvertibleMatrix 2) (logDelta : FiniteRelativeEnd)
    (X : FiniteComplexCarrier) : FiniteComplexCarrier :=
  relativeModular ρ σ X - X - logDelta X

def finiteRelativeHamiltonianAction
    (ρ σ : InvertibleMatrix 2) (K : FiniteRelativeEnd)
    (X : FiniteComplexCarrier) : FiniteComplexCarrier :=
  relativeModular ρ σ X - X + K X

theorem finite_relative_modular_is_hamiltonian_action
    (ρ σ : InvertibleMatrix 2) (logDelta K : FiniteRelativeEnd)
    (hK : ∀ X, logDelta X = -(K X)) (X : FiniteComplexCarrier) :
    finiteRelativeISAction ρ σ logDelta X =
      finiteRelativeHamiltonianAction ρ σ K X := by
  unfold finiteRelativeISAction finiteRelativeHamiltonianAction
  rw [hK X]
  simp [sub_eq_add_neg, add_assoc]

theorem modular_hamiltonian_commutator_zero
    (K Delta : FiniteCarrier) (h : K * Delta = Delta * K) :
    matrixCommutator K Delta = 0 := by
  simp [matrixCommutator, h]

/-! ## Finite self-adjoint Hamiltonian and eigenstates -/

def diagonalHamiltonian {n : ℕ} (energy : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal energy

theorem diagonalHamiltonian_self_adjoint {n : ℕ} (energy : Fin n → ℝ) :
    (diagonalHamiltonian energy).transpose = diagonalHamiltonian energy := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [diagonalHamiltonian]
  · simp [diagonalHamiltonian, h, Ne.symm h]

theorem diagonalHamiltonian_trace_eq_energy_sum {n : ℕ}
    (energy : Fin n → ℝ) :
    Matrix.trace (diagonalHamiltonian energy) = ∑ i : Fin n, energy i := by
  classical
  exact Matrix.trace_diagonal (d := energy)

theorem diagonalHamiltonian_exp_det_eq_exp_trace {n : ℕ}
    (energy : Fin n → ℝ) :
    Matrix.det (NormedSpace.exp (diagonalHamiltonian energy)) =
      NormedSpace.exp (Matrix.trace (diagonalHamiltonian energy)) := by
  exact InfoGeometry.Canonical.MatrixExponentialTraceDet.det_exp_diagonal_eq_exp_trace energy

theorem diagonalHamiltonian_exp_trace_eq_energy_exponential_sum {n : ℕ}
    (energy : Fin n → ℝ) :
    Matrix.trace (NormedSpace.exp (diagonalHamiltonian energy)) =
      ∑ i : Fin n, NormedSpace.exp (energy i) := by
  rw [diagonalHamiltonian, Matrix.exp_diagonal, Matrix.trace_diagonal]
  simp [Pi.coe_exp]

theorem diagonalHamiltonian_boltzmann_trace_eq_partition {n : ℕ}
    [Nonempty (Fin n)] (energy : Fin n → ℝ) (β : ℝ) :
    Matrix.trace
        (NormedSpace.exp ((-β) • diagonalHamiltonian energy)) =
      InfoGeometry.Thermal.Hamiltonian.partition energy β := by
  have hdiag :
      (-β) • diagonalHamiltonian energy =
        Matrix.diagonal (fun i => -β * energy i) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [diagonalHamiltonian]
    · simp [diagonalHamiltonian, hij]
  rw [hdiag, Matrix.exp_diagonal, Matrix.trace_diagonal]
  simp [InfoGeometry.Thermal.Hamiltonian.partition,
    InfoGeometry.MaxEnt.partition, Pi.coe_exp, Real.exp_eq_exp_ℝ, mul_comm]

theorem diagonalHamiltonian_thermal_density_trace_one {n : ℕ}
    [Nonempty (Fin n)] (energy : Fin n → ℝ) (β : ℝ) :
    Matrix.trace
        (InfoGeometry.Thermal.Hamiltonian.densityMatrix energy β) = 1 := by
  rw [InfoGeometry.Thermal.Hamiltonian.densityMatrix,
    Matrix.trace_diagonal]
  exact InfoGeometry.Thermal.Hamiltonian.gibbsWeight_sum_one energy β

theorem diagonalHamiltonian_thermal_density_self_adjoint {n : ℕ}
    [Nonempty (Fin n)] (energy : Fin n → ℝ) (β : ℝ) :
    (InfoGeometry.Thermal.Hamiltonian.densityMatrix energy β).transpose =
      InfoGeometry.Thermal.Hamiltonian.densityMatrix energy β := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [InfoGeometry.Thermal.Hamiltonian.densityMatrix]
  · simp [InfoGeometry.Thermal.Hamiltonian.densityMatrix, hij, Ne.symm hij]

theorem diagonalHamiltonian_thermal_density_posSemidef {n : ℕ}
    [Nonempty (Fin n)] (energy : Fin n → ℝ) (β : ℝ) :
    (InfoGeometry.Thermal.Hamiltonian.densityMatrix energy β).PosSemidef := by
  rw [InfoGeometry.Thermal.Hamiltonian.densityMatrix]
  exact Matrix.PosSemidef.diagonal (fun i =>
    InfoGeometry.Thermal.Hamiltonian.gibbsWeight_nonneg energy β i)

theorem diagonalHamiltonian_thermal_density_basis_eigenvector {n : ℕ}
    [Nonempty (Fin n)] (energy : Fin n → ℝ) (β : ℝ) (i : Fin n) :
    InfoGeometry.Thermal.Hamiltonian.densityMatrix energy β *ᵥ
        (Pi.single i (1 : ℝ)) =
      InfoGeometry.Thermal.Hamiltonian.gibbsWeight energy β i •
        (Pi.single i (1 : ℝ) : Fin n → ℝ) := by
  rw [InfoGeometry.Thermal.Hamiltonian.densityMatrix]
  rw [Matrix.diagonal_mulVec_single]
  ext j
  by_cases h : j = i
  · subst j
    simp
  · simp [h]

theorem diagonalHamiltonian_thermal_expectation_eq_trace {n : ℕ}
    [Nonempty (Fin n)] (energy observable : Fin n → ℝ) (β : ℝ) :
    Matrix.trace
        (InfoGeometry.Thermal.Hamiltonian.densityMatrix energy β *
          diagonalHamiltonian observable) =
      InfoGeometry.Thermal.Hamiltonian.thermalState energy β observable := by
  simp [InfoGeometry.Thermal.Hamiltonian.densityMatrix,
    diagonalHamiltonian, InfoGeometry.Thermal.Hamiltonian.thermalState,
    Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]

theorem diagonalHamiltonian_basis_eigenvector {n : ℕ}
    (energy : Fin n → ℝ) (i : Fin n) :
    diagonalHamiltonian energy *ᵥ (Pi.single i (1 : ℝ)) =
      (energy i : ℝ) • (Pi.single i (1 : ℝ) : Fin n → ℝ) := by
  ext j
  by_cases h : j = i
  · subst j
    simp [diagonalHamiltonian]
  · simp [diagonalHamiltonian, h]

/-! ### General finite Jost polynomial

This is the real `Fin n` counterpart of the repository's prime-Cantor
Berry--Keating Jost owner.  It is a characteristic determinant, so its zero
locus is proved algebraically and does not invoke an infinite resolvent or a
Fredholm analytic continuation.
-/

def finiteJostDeterminant {n : ℕ} (energy : Fin n → ℝ) (z : ℝ) : ℝ :=
  Matrix.det (z • (1 : Matrix (Fin n) (Fin n) ℝ) - diagonalHamiltonian energy)

theorem finiteJostDeterminant_eq_energy_product {n : ℕ}
    (energy : Fin n → ℝ) (z : ℝ) :
    finiteJostDeterminant energy z = ∏ i : Fin n, (z - energy i) := by
  unfold finiteJostDeterminant diagonalHamiltonian
  rw [show z • (1 : Matrix (Fin n) (Fin n) ℝ) - Matrix.diagonal energy =
      Matrix.diagonal (fun i => z - energy i) by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]]
  exact Matrix.det_diagonal

theorem finiteJostDeterminant_eq_zero_iff {n : ℕ}
    (energy : Fin n → ℝ) (z : ℝ) :
    finiteJostDeterminant energy z = 0 ↔
      ∃ i : Fin n, z = energy i := by
  rw [finiteJostDeterminant_eq_energy_product]
  simp only [Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨i, -, hi⟩
    exact ⟨i, sub_eq_zero.mp hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, Finset.mem_univ i, sub_eq_zero.mpr hi⟩

/-! Away from the finite spectrum, the Jost logarithmic derivative is the
sum of the inverse spectral gaps. -/
theorem finiteJostDeterminant_logDeriv_eq_sum_inv_of_ne_zero {n : ℕ}
    (energy : Fin n → ℝ) (z : ℝ)
    (hz : finiteJostDeterminant energy z ≠ 0) :
    logDeriv (finiteJostDeterminant energy) z =
      ∑ i : Fin n, (z - energy i)⁻¹ := by
  rw [show finiteJostDeterminant energy =
      (fun w : ℝ => ∏ i : Fin n, (w - energy i)) by
    funext w
    exact finiteJostDeterminant_eq_energy_product energy w]
  rw [logDeriv_prod]
  · simp only [logDeriv]
    congr 1
    funext i
    simp [sub_eq_add_neg]
  · intro i hi hzero
    apply hz
    rw [finiteJostDeterminant_eq_energy_product]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hzero
  · intro i hi
    simpa using (hasDerivAt_id z).sub_const (energy i)

theorem finiteJostDeterminant_zero_iff_eigenstate {n : ℕ}
    (energy : Fin n → ℝ) (z : ℝ) :
    finiteJostDeterminant energy z = 0 ↔
      ∃ v : Fin n → ℝ, v ≠ 0 ∧
        diagonalHamiltonian energy *ᵥ v = z • v := by
  rw [finiteJostDeterminant_eq_zero_iff]
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨Pi.single i (1 : ℝ), ?_, diagonalHamiltonian_basis_eigenvector energy i⟩
    intro hzero
    have hi := congrFun hzero i
    simp at hi
  · rintro ⟨v, hv, heigen⟩
    by_contra hno
    push_neg at hno
    apply hv
    funext i
    have hi := congrFun heigen i
    have hi' : energy i * v i = z * v i := by
      simpa [diagonalHamiltonian, Matrix.mulVec_diagonal, smul_eq_mul] using hi
    have hscalar : energy i - z ≠ 0 := by
      intro hscalar
      apply hno i
      exact (sub_eq_zero.mp hscalar).symm
    apply (mul_eq_zero.mp ?_).resolve_left hscalar
    calc
      (energy i - z) * v i = energy i * v i - z * v i := by ring
      _ = 0 := by rw [hi']; ring

/-! ### Finite spectral/divisor readout

The spectral polynomial and the signed divisor charge remain distinct finite
objects.  This theorem records both readouts together, with the divisor side
provided by the existing finite two-term kernel owner.
-/

theorem finite_spectral_divisor_readout
    {n : ℕ} (energy : Fin n → ℝ) (z : ℝ)
    {ι : Type*} [Fintype ι] (order : ι → ℤ) :
    (diagonalHamiltonian energy).transpose = diagonalHamiltonian energy ∧
    (finiteJostDeterminant energy z = 0 ↔
      ∃ v : Fin n → ℝ, v ≠ 0 ∧
        diagonalHamiltonian energy *ᵥ v = z • v) ∧
    finiteKernelIndex (divisorKernelComplex order) = divisorIndex order := by
  exact ⟨diagonalHamiltonian_self_adjoint energy,
    finiteJostDeterminant_zero_iff_eigenstate energy z,
    divisor_kernel_index_eq_divisor_index order⟩

/-! ## Concrete finite Tomita relative modular operator -/


theorem finite_relative_modular_bijective
    (ρ σ : InvertibleMatrix 2) :
    Function.Bijective (relativeModular ρ σ) := by
  exact InfoGeometry.Canonical.OperatorialItakuraSaitoFramework.finite_relativeDelta_is_linearEquiv ρ σ

theorem finite_relative_modular_identity
    (ρ σ : InvertibleMatrix 2) :
    relativeModular ρ σ (1 : MatrixCarrier 2) = ρ.val * σ.inv := by
  exact InfoGeometry.Canonical.OperatorialItakuraSaitoFramework.finite_relativeDelta_identity ρ σ

theorem finite_relative_modular_inverse_left
    (ρ σ : InvertibleMatrix 2) (X : FiniteComplexCarrier) :
    relativeModularInverse ρ σ (relativeModular ρ σ X) = X := by
  have h := congrArg (fun T : FiniteRelativeEnd => T X)
    (relativeModular_inverse_mul ρ σ)
  simpa [LinearMap.comp_apply] using h

theorem finite_relative_modular_inverse_right
    (ρ σ : InvertibleMatrix 2) (X : FiniteComplexCarrier) :
    relativeModular ρ σ (relativeModularInverse ρ σ X) = X := by
  have h := congrArg (fun T : FiniteRelativeEnd => T X)
    (relativeModular_mul_inverse ρ σ)
  simpa [LinearMap.comp_apply] using h

/-! ## Finite diagonal surprisal and direct-limit trace readout -/

theorem finite_relative_surprisal_diagonal
    {n : ℕ} [Nonempty (Fin n)]
    (q q0 : PositiveRay (Fin n)) (i : Fin n) :
    relativeSurprisalOperator (n := n) q q0 i i =
      relativeModularPotential q q0 i := by
  exact relativeSurprisalOperator_diag q q0 i

theorem finite_relative_surprisal_cocycle
    {n : ℕ} [Nonempty (Fin n)]
    (q q0 q1 : PositiveRay (Fin n)) :
    relativeSurprisalOperator (n := n) q q1 =
      relativeSurprisalOperator (n := n) q q0 +
        relativeSurprisalOperator (n := n) q0 q1 := by
  exact relativeSurprisalOperator_cocycle q q0 q1

theorem finite_trace_commutator_colimit_zero
    (n : ℕ) (A B : MatrixStage n) :
    traceColimitFunctional
        (stageInjection n (A * B - B * A)) = 0 := by
  rw [traceColimitFunctional_stage]
  simp only [matrixTraceFunctional_apply, Matrix.trace_sub]
  rw [Matrix.trace_mul_comm A B]
  ring

/-! ## Finite circulation and divisor/Fredholm index -/

def quantumCirculation (order : ℤ) : ℝ := 2 * Real.pi * order

theorem quantumCirculation_eq_residue_multiple (order : ℤ) :
    quantumCirculation order = 2 * Real.pi * order := rfl

theorem finite_fredholm_index_eq_divisor_index
    {ι : Type*} [Fintype ι] (order : ι → ℤ) :
    finiteKernelIndex (divisorKernelComplex order) = divisorIndex order := by
  exact divisor_kernel_index_eq_divisor_index order

set_option maxHeartbeats 400000 in
theorem finite_fredholm_index_eq_residue_sum
    {ι : Type*} [Fintype ι]
    (data : ι → LocalDivisorData ℤ) :
    finiteKernelIndex
        (InfoGeometry.Arithmetic.RiemannPoleZeroMonodromy.divisorKernelComplex
          (fun a => (data a).order)) =
      ∑ a : ι, residue (chargeForm (data a)) := by
  exact InfoGeometry.Arithmetic.RiemannPoleZeroMonodromy.divisor_kernel_index_eq_residue_sum data

end InfoGeometry.Canonical.FiniteMadelungTomitaQuantization

end noncomputable section
