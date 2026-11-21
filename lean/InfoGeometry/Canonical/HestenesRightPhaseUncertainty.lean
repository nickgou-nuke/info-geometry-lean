/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.CenteredOperatorialUncertainty
import InfoGeometry.Canonical.Cl11GNSRealDoubledKreinBridge
import proofs.HestenesQuaternionCore

/-!
# Native Hestenes right phase on the real Hilbert carrier

The algebraic inputs are the existing native `ClPlus14`, the even sector of
the real Clifford algebra with quadratic form of signature `(+---)`.
Its faithful real algebra equivalence with the finite Pauli matrix model
and the already constructed real Hilbert--Schmidt readout supply the
coordinate transport. All observables and the phase below are bounded
real-linear operators on the native doubled real Hilbert space.

The phase is right multiplication by the actual native spatial bivector
`HestenesQuaternionCore.q₃ = γ₂ γ₁`. It commutes with left observables by
associativity. This is not an identification of that bivector with a central
scalar, nor an identification of a square-minus-one phase with the Krein
fundamental symmetry. The uncertainty theorem uses the positive Hilbert
form; it does not use the signed Krein quadratic form as a variance.
-/

noncomputable section

namespace InfoGeometry.Canonical.HestenesRightPhaseUncertainty

open HestenesCl14 HestenesPauliSheetBridge HestenesEvenPauliEquiv
open HestenesHermitianAdjoint HestenesHermitianMatrixBridge
open _root_.HestenesQuaternionCore
open InfoGeometry.Krein
open InfoGeometry.Canonical.Cl11GNSRealDoubledKreinBridge
open InfoGeometry.Canonical.OperatorialUncertainty
open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.HestenesModularBregman
open FiniteHestenesHilbertSchmidtStandardForm
open scoped InnerProductSpace

/-- The eight-dimensional real Hilbert carrier of the native even spacetime
algebra, through its existing finite standard-form coordinates. -/
abbrev H := DoubledSpace (EuclideanSpace ℝ (Fin 2 × Fin 2))

/-- Readout of a native even Clifford element into real Hilbert coordinates. -/
def nativeReadout (x : ClPlus14) : H :=
  realDoubledReadout (clPlusToPauli x)

/-- Left action of a native even Clifford element, as a bounded real-linear
operator on the positive Hilbert carrier. -/
def leftObservable (a : ClPlus14) : H →L[ℝ] H :=
  realDoubledLeftAction (clPlusToPauli a)

/-- Hestenes phase as right multiplication by the fixed native spin-plane
bivector. No external scalar imaginary is a parameter of this definition. -/
def rightPhase : H →L[ℝ] H :=
  realDoubledRightAction (clPlusToPauli q₃)

/-- The existing quaternion generator is precisely the native spatial
bivector `γ₂ γ₁`, with the repository's orientation convention. -/
theorem q₃_eq_spatial_bivector :
    q₃ = (CliffordAlgebra.even.ι Q14).bilin (basisVec 2) (basisVec 1) := by
  apply clPlusToPauli_injective
  rw [clPlusToPauli_on_pair]
  simp only [q₃, map_mul, clPlusToPauli_volumeEven, clPlusToPauli_sigma2]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [pauli3, paravector, paravectorConj, basisVec,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem nativeReadout_injective : Function.Injective nativeReadout := by
  intro x y h
  exact clPlusToPauli_injective (realDoubledReadout_injective h)

theorem nativeReadout_surjective : Function.Surjective nativeReadout := by
  intro u
  obtain ⟨X, hX⟩ := realDoubledReadout_surjective u
  obtain ⟨x, hx⟩ := clPlusToPauli_surjective X
  refine ⟨x, ?_⟩
  simpa only [nativeReadout, hx] using hX

@[simp] theorem nativeReadout_add (x y : ClPlus14) :
    nativeReadout (x + y) = nativeReadout x + nativeReadout y := by
  simp only [nativeReadout, map_add, realDoubledReadout_add]

@[simp] theorem nativeReadout_real_smul (r : ℝ) (x : ClPlus14) :
    nativeReadout (r • x) = r • nativeReadout x := by
  rw [nativeReadout, map_smul]
  have hs : r • clPlusToPauli x = (r : ℂ) • clPlusToPauli x := by
    ext i j
    simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
  rw [hs]
  exact realDoubledReadout_real_smul r (clPlusToPauli x)

@[simp] theorem leftObservable_nativeReadout (a x : ClPlus14) :
    leftObservable a (nativeReadout x) = nativeReadout (a * x) := by
  simp only [leftObservable, nativeReadout, realDoubledLeftAction_readout,
    FiniteHestenesHilbertSchmidtStandardForm.leftActionLinear_apply, map_mul]

@[simp] theorem rightPhase_nativeReadout (x : ClPlus14) :
    rightPhase (nativeReadout x) = nativeReadout (x * q₃) := by
  simp only [rightPhase, nativeReadout, realDoubledRightAction_readout,
    FiniteHestenesHilbertSchmidtStandardForm.rightActionLinear_apply, map_mul]

/-- The native bivector square law survives the faithful real readout. -/
theorem rightPhase_sq :
    rightPhase.comp rightPhase = -(ContinuousLinearMap.id ℝ H) := by
  apply realDoubledRightAction_sq_of_mul_self
  simpa only [map_mul, map_neg, map_one] using
    congrArg clPlusToPauli q₃_sq

theorem rightPhase_isRealComplexStructure :
    IsRealComplexStructure rightPhase.toLinearMap := by
  change rightPhase.toLinearMap.comp rightPhase.toLinearMap = -LinearMap.id
  exact congrArg ContinuousLinearMap.toLinearMap rightPhase_sq

/-- The positive Hilbert adjoint follows from the already proved native
Hestenes adjoint of `q₃`, not from a Krein selfadjointness assertion. -/
theorem rightPhase_star : star rightPhase = -rightPhase := by
  change (realDoubledRightAction (clPlusToPauli q₃)).adjoint =
    -realDoubledRightAction (clPlusToPauli q₃)
  rw [realDoubledRightAction_adjoint, ← clPlusToPauli_hestenesAdjoint,
    adjoint_q₃, map_neg, realDoubledRightAction_neg]

/-- Orthogonality is a consequence of the constructed square and adjoint
laws on the actual real Hilbert carrier. -/
theorem rightPhase_inner (u v : H) :
    ⟪rightPhase u, rightPhase v⟫_ℝ = ⟪u, v⟫_ℝ :=
  InfoGeometry.Geometry.RealHamiltonianMoment.inner_map_map rightPhase
    rightPhase_isRealComplexStructure rightPhase_star u v

/-- Every left Clifford observable commutes with the right spin-plane
phase, independently of whether its Clifford coefficient commutes with `q₃`. -/
theorem leftObservable_commutes_rightPhase (a : ClPlus14) :
    (leftObservable a).comp rightPhase = rightPhase.comp (leftObservable a) :=
  realDoubledLeftRightAction_commute (clPlusToPauli a) (clPlusToPauli q₃)

/-- Native Hestenes Hermitian elements act as Hilbert-selfadjoint real
operators. This hypothesis is distinct from the native Krein adjoint. -/
theorem leftObservable_isSelfAdjoint
    (a : ClPlus14) (ha : hestenesAdjoint a = a) :
    IsSelfAdjoint (leftObservable a) := by
  apply realDoubledLeftAction_isSelfAdjoint
  rw [← clPlusToPauli_hestenesAdjoint, ha]

theorem leftObservable_comp (a b : ClPlus14) :
    (leftObservable a).comp (leftObservable b) = leftObservable (a * b) := by
  simp only [leftObservable, map_mul, realDoubledLeftAction_comp]

theorem leftObservable_injective : Function.Injective leftObservable := by
  intro a b h
  apply clPlusToPauli_injective
  exact realDoubledLeftAction_injective h

/-- The real operator representation retains native Clifford
noncommutativity. -/
theorem leftObservable_noncommute
    (a b : ClPlus14) (hab : a * b ≠ b * a) :
    (leftObservable a).comp (leftObservable b) ≠
      (leftObservable b).comp (leftObservable a) := by
  intro h
  rw [leftObservable_comp, leftObservable_comp] at h
  exact hab (leftObservable_injective h)

theorem hestenesAdjoint_sigmaEven (k : Fin 3) :
    hestenesAdjoint (sigmaEven k) = sigmaEven k := by
  apply clPlusToPauli_injective
  rw [clPlusToPauli_hestenesAdjoint]
  fin_cases k <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauli1, pauli2, pauli3, Matrix.conjTranspose_apply]

theorem sigma0_sigma1_noncommute :
    sigmaEven 0 * sigmaEven 1 ≠ sigmaEven 1 * sigmaEven 0 := by
  intro h
  have hm := congrArg clPlusToPauli h
  have him := congrArg (fun M : HestenesPauliSheetBridge.Sheet => (M 0 0).im) hm
  norm_num [map_mul, pauli1, pauli2, Matrix.mul_apply, Fin.sum_univ_two] at him

/-- A concrete pair of noncommuting Hilbert-selfadjoint observables from
the full native even spacetime algebra. -/
theorem sigma_leftObservables_noncommute :
    (leftObservable (sigmaEven 0)).comp (leftObservable (sigmaEven 1)) ≠
      (leftObservable (sigmaEven 1)).comp (leftObservable (sigmaEven 0)) :=
  leftObservable_noncommute _ _ sigma0_sigma1_noncommute

/-- Centered Robertson--Schrödinger inequality for native Hestenes
observables and the actual right spin-plane phase. The state is an arbitrary
even Clifford element; normalization is not required for the geometric
norm inequality. -/
theorem centered_uncertainty
    (ψ a b : ClPlus14)
    (ha : hestenesAdjoint a = a) (hb : hestenesAdjoint b = b) :
    hilbertCovarianceAt (nativeReadout ψ) (leftObservable a) (leftObservable b) ^ 2 +
        phaseCommutatorAt rightPhase (nativeReadout ψ)
          (leftObservable a) (leftObservable b) ^ 2 / 4 ≤
      hilbertVarianceAt (nativeReadout ψ) (leftObservable a) *
        hilbertVarianceAt (nativeReadout ψ) (leftObservable b) := by
  exact hilbertCovariance_sq_add_phaseCommutator_sq_div_four_le
    rightPhase (nativeReadout ψ) (leftObservable a) (leftObservable b)
    rightPhase_isRealComplexStructure rightPhase_star
    (leftObservable_isSelfAdjoint a ha) (leftObservable_isSelfAdjoint b hb)
    (leftObservable_commutes_rightPhase a) (leftObservable_commutes_rightPhase b)

/-- The native noncommuting Pauli pair is an actual consumer of the
right-bivector uncertainty theorem. -/
theorem sigma_centered_uncertainty (ψ : ClPlus14) :
    hilbertCovarianceAt (nativeReadout ψ)
        (leftObservable (sigmaEven 0)) (leftObservable (sigmaEven 1)) ^ 2 +
      phaseCommutatorAt rightPhase (nativeReadout ψ)
        (leftObservable (sigmaEven 0)) (leftObservable (sigmaEven 1)) ^ 2 / 4 ≤
      hilbertVarianceAt (nativeReadout ψ) (leftObservable (sigmaEven 0)) *
        hilbertVarianceAt (nativeReadout ψ) (leftObservable (sigmaEven 1)) :=
  centered_uncertainty ψ _ _ (hestenesAdjoint_sigmaEven 0)
    (hestenesAdjoint_sigmaEven 1)

private theorem nativeReadout_inner_eq_hilbertSchmidt (x y : ClPlus14) :
    ⟪nativeReadout x, nativeReadout y⟫_ℝ =
      (hilbertSchmidtInner (clPlusToPauli x) (clPlusToPauli y)).re := by
  change doubledHilbertBilin (realDoubledReadout (clPlusToPauli x))
      (realDoubledReadout (clPlusToPauli y)) = _
  exact (realPart_hilbertSchmidtInner_eq_doubledHilbertBilin
    (clPlusToPauli x) (clPlusToPauli y)).symm

/-- The Clifford unit has squared norm two in the existing unnormalized
Hilbert--Schmidt carrier; this example is not a unit-state expectation. -/
theorem nativeReadout_one_norm_sq :
    ‖nativeReadout (1 : ClPlus14)‖ ^ 2 = 2 := by
  rw [← real_inner_self_eq_norm_sq, nativeReadout_inner_eq_hilbertSchmidt]
  norm_num [hilbertSchmidtInner, Fin.sum_univ_two]

theorem sigma0_expectationAt_one :
    hilbertExpectationAt (nativeReadout (1 : ClPlus14))
      (leftObservable (sigmaEven 0)) = 0 := by
  unfold hilbertExpectationAt
  rw [leftObservable_nativeReadout, mul_one, nativeReadout_inner_eq_hilbertSchmidt]
  norm_num [hilbertSchmidtInner, pauli1, Fin.sum_univ_two]

theorem sigma1_expectationAt_one :
    hilbertExpectationAt (nativeReadout (1 : ClPlus14))
      (leftObservable (sigmaEven 1)) = 0 := by
  unfold hilbertExpectationAt
  rw [leftObservable_nativeReadout, mul_one, nativeReadout_inner_eq_hilbertSchmidt]
  norm_num [hilbertSchmidtInner, pauli2, Fin.sum_univ_two]

theorem sigma0_varianceAt_one :
    hilbertVarianceAt (nativeReadout (1 : ClPlus14))
      (leftObservable (sigmaEven 0)) = 2 := by
  simp only [hilbertVarianceAt, centeredObservable_apply, sigma0_expectationAt_one,
    zero_smul, sub_zero, leftObservable_nativeReadout, mul_one]
  rw [← real_inner_self_eq_norm_sq, nativeReadout_inner_eq_hilbertSchmidt]
  norm_num [hilbertSchmidtInner, pauli1, Fin.sum_univ_two]

theorem sigma1_varianceAt_one :
    hilbertVarianceAt (nativeReadout (1 : ClPlus14))
      (leftObservable (sigmaEven 1)) = 2 := by
  simp only [hilbertVarianceAt, centeredObservable_apply, sigma1_expectationAt_one,
    zero_smul, sub_zero, leftObservable_nativeReadout, mul_one]
  rw [← real_inner_self_eq_norm_sq, nativeReadout_inner_eq_hilbertSchmidt]
  norm_num [hilbertSchmidtInner, pauli2, Fin.sum_univ_two]

theorem sigma_covarianceAt_one :
    hilbertCovarianceAt (nativeReadout (1 : ClPlus14))
      (leftObservable (sigmaEven 0)) (leftObservable (sigmaEven 1)) = 0 := by
  simp only [hilbertCovarianceAt, centeredObservable_apply,
    sigma0_expectationAt_one, sigma1_expectationAt_one, zero_smul, sub_zero,
    leftObservable_nativeReadout, mul_one]
  rw [nativeReadout_inner_eq_hilbertSchmidt]
  norm_num [hilbertSchmidtInner, pauli1, pauli2, Fin.sum_univ_two]

/-- The actual ordered commutator read against the right-phase-rotated
state is positive four. This directly unfolds the commutator readout and
does not infer nonvanishing merely from operator noncommutativity. -/
theorem sigma_phaseCommutatorAt_one :
    phaseCommutatorAt rightPhase (nativeReadout (1 : ClPlus14))
      (leftObservable (sigmaEven 0)) (leftObservable (sigmaEven 1)) = 4 := by
  unfold phaseCommutatorAt transportCommutator
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    rightPhase_nativeReadout, leftObservable_nativeReadout, mul_one, one_mul]
  rw [inner_sub_right, nativeReadout_inner_eq_hilbertSchmidt,
    nativeReadout_inner_eq_hilbertSchmidt]
  norm_num [q₃, map_mul, hilbertSchmidtInner, pauli1, pauli2, pauli3,
    Matrix.mul_apply, Fin.sum_univ_two]

theorem sigma_phaseCommutatorAt_one_ne_zero :
    phaseCommutatorAt rightPhase (nativeReadout (1 : ClPlus14))
      (leftObservable (sigmaEven 0)) (leftObservable (sigmaEven 1)) ≠ 0 := by
  rw [sigma_phaseCommutatorAt_one]
  norm_num

/-- Sharpness of the full centered area inequality at the native unit:
the covariance contribution is zero and the phase contribution is four. -/
theorem sigma_uncertainty_at_one_eq :
    hilbertCovarianceAt (nativeReadout (1 : ClPlus14))
        (leftObservable (sigmaEven 0)) (leftObservable (sigmaEven 1)) ^ 2 +
      phaseCommutatorAt rightPhase (nativeReadout (1 : ClPlus14))
        (leftObservable (sigmaEven 0)) (leftObservable (sigmaEven 1)) ^ 2 / 4 =
      hilbertVarianceAt (nativeReadout (1 : ClPlus14))
          (leftObservable (sigmaEven 0)) *
        hilbertVarianceAt (nativeReadout (1 : ClPlus14))
          (leftObservable (sigmaEven 1)) := by
  rw [sigma_covarianceAt_one, sigma_phaseCommutatorAt_one,
    sigma0_varianceAt_one, sigma1_varianceAt_one]
  norm_num


end InfoGeometry.Canonical.HestenesRightPhaseUncertainty

end
