import InfoGeometry.Quantum.QutritBraidIncidenceBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Quantum.QutritMobiusTripotentOrientationBridge
import InfoGeometry.Twistor.ProjectiveNullConfigurationAssociatedDeckMonodromy

/-!
# Qutrit permutation representation and associated twistor monodromy

The qutrit lane supplies a genuine representation of the finite deck group
`Equiv.Perm (Fin 3)` on the native qutrit space.  The existing associated
monodromy construction then transports this representation to the unordered
projective-null configuration space.

This owner does not identify the finite quotient with a full Artin braid
representation and does not introduce a regular deck-module intermediary.
-/

noncomputable section

namespace InfoGeometry.Twistor.QutritPermutationAssociatedTwistorMonodromy

open InfoGeometry.Quantum.Qutrit
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.FiniteMatrix
open InfoGeometry.Quantum.QutritBraidIncidenceBridge
open InfoGeometry.Quantum.QutritMobiusTripotentOrientationBridge
open InfoGeometry.Twistor.ProjectiveNullConfiguration
open InfoGeometry.Twistor.ProjectiveNullConfigurationAssociatedDeckMonodromy
open InfoGeometry.Twistor.ProjectiveNullConfigurationTopology
open InfoGeometry.Twistor.ProjectiveNullOrderedExchangePath
open InfoGeometry.Twistor.ProjectiveNullUnorderedConfiguration

/-- Semantic permutation of qutrit coordinates: `|i⟩ ↦ |σ i⟩`. -/
def qutritPermutationLinearEquiv
    (σ : Equiv.Perm (Fin 3)) : QutritSpace ≃ₗ[ℂ] QutritSpace where
  toFun ψ := matrixOp (qutritPermutationMatrix σ) ψ
  invFun ψ := matrixOp (qutritPermutationMatrix σ.symm) ψ
  left_inv ψ := by
    change (matrixOp (qutritPermutationMatrix σ.symm)).comp
        (matrixOp (qutritPermutationMatrix σ)) ψ = ψ
    rw [matrixOp_comp, qutritPermutationMatrix_symm_mul, matrixOp_id]
    rfl
  right_inv ψ := by
    change (matrixOp (qutritPermutationMatrix σ)).comp
        (matrixOp (qutritPermutationMatrix σ.symm)) ψ = ψ
    rw [matrixOp_comp, qutritPermutationMatrix_mul_symm, matrixOp_id]
    rfl
  map_add' ψ φ := by
    exact (matrixOp (qutritPermutationMatrix σ)).map_add ψ φ
  map_smul' c ψ := by
    exact (matrixOp (qutritPermutationMatrix σ)).map_smul c ψ

@[simp]
theorem qutritPermutationLinearEquiv_apply_ket
    (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    qutritPermutationLinearEquiv σ (ket i) = ket (σ i) := by
  simpa [qutritPermutationLinearEquiv, ket_eq_ketPi] using
    qutritPermutationMatrix_matrixOp_ket σ i

/-- The native general-linear qutrit representation of `S₃`. -/
def qutritPermutationRepresentation :
    Equiv.Perm (Fin 3) →*
      LinearMap.GeneralLinearGroup ℂ QutritSpace where
  toFun σ := LinearMap.GeneralLinearGroup.ofLinearEquiv
    (qutritPermutationLinearEquiv σ)
  map_one' := by
    apply Units.ext
    apply LinearMap.ext
    intro ψ
    change matrixOp (qutritPermutationMatrix 1) ψ = ψ
    rw [qutritPermutationMatrix_one, matrixOp_id]
    rfl
  map_mul' σ τ := by
    apply Units.ext
    apply LinearMap.ext
    intro ψ
    change matrixOp (qutritPermutationMatrix (σ * τ)) ψ =
      matrixOp (qutritPermutationMatrix σ) (matrixOp (qutritPermutationMatrix τ) ψ)
    rw [← ContinuousLinearMap.comp_apply, matrixOp_comp]
    rw [qutritPermutationMatrix_mul]

@[simp]
theorem qutritPermutationRepresentation_apply_ket
    (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    (qutritPermutationRepresentation σ : QutritSpace →ₗ[ℂ] QutritSpace)
        (ket i) = ket (σ i) := by
  exact qutritPermutationLinearEquiv_apply_ket σ i

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The qutrit representation transported through the existing covering
permutation monodromy. -/
def qutritAssociatedTwistorMonodromy
    [TopologicalSpace V]
    (Q : QuadraticForm K V)
    (hLC : @LocallyCompactSpace (Ordered Q 3)
      (orderedConfigurationTopology Q 3))
    (hT2 : @T2Space (Ordered Q 3) (orderedConfigurationTopology Q 3))
    (p : Ordered Q 3) :
    @FundamentalGroup (Unordered Q 3)
        (unorderedConfigurationTopology Q 3) (Quotient.mk' p) →*
      LinearMap.GeneralLinearGroup ℂ QutritSpace :=
  associatedDeckLinearMonodromy Q 3 hLC hT2 p
    (qutritPermutationRepresentation)

@[simp]
theorem qutritAssociatedTwistorMonodromy_orderedExchange
    [TopologicalSpace V]
    (Q : QuadraticForm K V)
    (hLC : @LocallyCompactSpace (Ordered Q 3)
      (orderedConfigurationTopology Q 3))
    (hT2 : @T2Space (Ordered Q 3) (orderedConfigurationTopology Q 3))
    (p : Ordered Q 3) (σ : Equiv.Perm (Fin 3))
    (γ : @Path (Ordered Q 3) (orderedConfigurationTopology Q 3)
      p (permute Q 3 σ p)) :
    qutritAssociatedTwistorMonodromy Q hLC hT2 p
        (orderedExchangeLoopClass Q 3 p σ γ) =
      qutritPermutationRepresentation σ := by
  exact associatedDeckLinearMonodromy_orderedExchangeLoopClass
    Q 3 hLC hT2 p σ γ qutritPermutationRepresentation

@[simp]
theorem qutritAssociatedTwistorMonodromy_cycle
    [TopologicalSpace V]
    (Q : QuadraticForm K V)
    (hLC : @LocallyCompactSpace (Ordered Q 3)
      (orderedConfigurationTopology Q 3))
    (hT2 : @T2Space (Ordered Q 3) (orderedConfigurationTopology Q 3))
    (p : Ordered Q 3) (γ : @Path (Ordered Q 3)
      (orderedConfigurationTopology Q 3) p (permute Q 3 qutritCycle p)) :
    qutritAssociatedTwistorMonodromy Q hLC hT2 p
        (orderedExchangeLoopClass Q 3 p qutritCycle γ) =
      qutritPermutationRepresentation
          InfoGeometry.Topology.ArtinBraidS3Quotient.sigma1 *
        qutritPermutationRepresentation
          InfoGeometry.Topology.ArtinBraidS3Quotient.sigma2 := by
  rw [qutritAssociatedTwistorMonodromy_orderedExchange]
  simpa only [qutritCycle_eq_sigma1_mul_sigma2] using
    (qutritPermutationRepresentation.map_mul
      InfoGeometry.Topology.ArtinBraidS3Quotient.sigma1
      InfoGeometry.Topology.ArtinBraidS3Quotient.sigma2)

end InfoGeometry.Twistor.QutritPermutationAssociatedTwistorMonodromy
