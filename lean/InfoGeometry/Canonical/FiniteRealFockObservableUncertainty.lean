/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.FiniteRealFockQuadraticAdjoint
import InfoGeometry.Physics.NuclearDoubledConfiguration
import InfoGeometry.Canonical.PhaseObservableUncertainty

/-!
# Real uncertainty for finite quadratic Fock observables

Symmetric coefficient matrices give genuine Hilbert-self-adjoint operators
on the existing positive finite Fock space. The existing paired lift acts on
both real legs, preserves adjoints and ordered composition, and commutes with
the internal phase. These proved properties discharge the hypotheses of the
real covariance-plus-commutator uncertainty theorem.

The commutator below is the paired lift of the actual ordered quadratic Fock
commutator. No simultaneous diagonalization or mutual commutativity is assumed.
The finite sum has not yet been identified here with the separate generic
`exteriorLift` API, and no infinite-mode or continuous-wavelet claim is made.
-/

noncomputable section

namespace InfoGeometry.Canonical.FiniteRealFockObservableUncertainty

open InfoGeometry.Clifford
open InfoGeometry.Clifford.ClNNNeutralChevalleyBridge
open InfoGeometry.Krein
open InfoGeometry.Krein.PhaseLinearObservableCommutator
open InfoGeometry.Physics.NuclearDoubledConfiguration
open scoped InnerProductSpace

attribute [local instance] fockNormedAddCommGroup fockInnerProductSpace
  fockQuadraticFiniteDimensional fockQuadraticCompleteSpace

/-- The real Robertson--Schrödinger inequality for arbitrary symmetric
coefficient matrices acting on every finite exterior-Fock degree. -/
theorem paired_fock_robertson_schrodinger (n : ℕ)
    (M N : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) (hN : N.IsSymm)
    (a b : ℝ) (ψ : DoubledSpace (SpinorSpace (Vector n))) :
    let A := fockQuadraticCLM n M
    let B := fockQuadraticCLM n N
    (⟪centeredVector (pairedLift A) a ψ,
        centeredVector (pairedLift B) b ψ⟫_ℝ) ^ 2 +
      (1 / 4 : ℝ) *
        (⟪complex_i ψ, pairedLift (A.comp B - B.comp A) ψ⟫_ℝ) ^ 2 ≤
      ‖centeredVector (pairedLift A) a ψ‖ ^ 2 *
        ‖centeredVector (pairedLift B) b ψ‖ ^ 2 := by
  have hA : IsSelfAdjoint (pairedLift (fockQuadraticCLM n M)) := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff', pairedLift_adjoint]
    exact congrArg pairedLift
      (ContinuousLinearMap.isSelfAdjoint_iff'.mp
        (fockQuadraticCLM_isSelfAdjoint n M hM))
  have hB : IsSelfAdjoint (pairedLift (fockQuadraticCLM n N)) := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff', pairedLift_adjoint]
    exact congrArg pairedLift
      (ContinuousLinearMap.isSelfAdjoint_iff'.mp
        (fockQuadraticCLM_isSelfAdjoint n N hN))
  simpa only [pairedLift_sub, pairedLift_comp] using
    PhaseObservableUncertainty.centered_robertson_schrodinger
      (pairedLift (fockQuadraticCLM n M)) (pairedLift (fockQuadraticCLM n N))
      hA hB
      (pairedLift_comp_clockAxis (fockQuadraticCLM n M))
      (pairedLift_comp_clockAxis (fockQuadraticCLM n N)) a b ψ

end InfoGeometry.Canonical.FiniteRealFockObservableUncertainty
