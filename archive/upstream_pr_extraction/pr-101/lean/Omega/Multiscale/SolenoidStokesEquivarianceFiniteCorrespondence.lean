import Omega.Multiscale.SolenoidFundamentalCurrentAndStokes

namespace Omega.Multiscale

noncomputable section

open NormalizedStokesFiniteCoverInverseTowerSystem

/-- Concrete source and target degree functions for a finite correspondence. -/
structure SolenoidFiniteCorrespondence where
  sourceDegree : ℕ → ℕ
  targetDegree : ℕ → ℕ

namespace SolenoidFiniteCorrespondence

/-- Pull back along the target leg and normalize along the source leg. -/
def levelTransfer (C : SolenoidFiniteCorrespondence) (ξ : ℕ → ℝ) (n : ℕ) : ℝ :=
  (C.sourceDegree n : ℝ)⁻¹ * (C.targetDegree n : ℝ) * ξ n

def cylindricalTransfer (C : SolenoidFiniteCorrespondence) (ξ : ℕ → ℝ) : ℕ → ℝ :=
  fun n => C.levelTransfer ξ n

lemma levelTransfer_eq_self (C : SolenoidFiniteCorrespondence)
    (sourceDegree_pos : ∀ n, 0 < C.sourceDegree n)
    (degree_eq : ∀ n, C.sourceDegree n = C.targetDegree n)
    (ξ : ℕ → ℝ) (n : ℕ) : C.levelTransfer ξ n = ξ n := by
  have hdeg :
      (C.targetDegree n : ℝ) = (C.sourceDegree n : ℝ) := by
    exact_mod_cast (degree_eq n).symm
  have hsrc_ne : (C.sourceDegree n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (sourceDegree_pos n)
  unfold levelTransfer
  rw [hdeg]
  simp [hsrc_ne]

end SolenoidFiniteCorrespondence

open SolenoidFiniteCorrespondence

/-- An equidegree finite correspondence preserves normalized cylindrical bulk integrals and
commutes with differential and boundary readouts. -/
theorem paper_app_solenoid_stokes_equivariance_finite_correspondence
    (S : NormalizedStokesFiniteCoverInverseTowerSystem)
    (C : SolenoidFiniteCorrespondence)
    (sourceDegree_pos : ∀ n, 0 < C.sourceDegree n)
    (degree_eq : ∀ n, C.sourceDegree n = C.targetDegree n)
    (levelwiseStokes : ∀ n, S.differentialIntegral n = S.boundaryIntegral n) :
    (∀ n, C.cylindricalTransfer (fun k => normalizedBulk S k) n =
      normalizedBulk S n) ∧
      (∀ n, C.cylindricalTransfer (fun k => normalizedDifferential S k) n =
        C.cylindricalTransfer (fun k => normalizedBoundary S k) n) ∧
        (∀ n, C.cylindricalTransfer (fun k => normalizedBoundary S k) n =
          normalizedBoundary S n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    simpa [SolenoidFiniteCorrespondence.cylindricalTransfer] using
      C.levelTransfer_eq_self sourceDegree_pos degree_eq (fun k => normalizedBulk S k) n
  · intro n
    rw [SolenoidFiniteCorrespondence.cylindricalTransfer,
      SolenoidFiniteCorrespondence.cylindricalTransfer]
    rw [C.levelTransfer_eq_self sourceDegree_pos degree_eq
        (fun k => normalizedDifferential S k) n,
      C.levelTransfer_eq_self sourceDegree_pos degree_eq
        (fun k => normalizedBoundary S k) n]
    simpa using
      normalizedStokes_levelwise S levelwiseStokes n
  · intro n
    simpa [SolenoidFiniteCorrespondence.cylindricalTransfer]
      using C.levelTransfer_eq_self sourceDegree_pos degree_eq
        (fun k => normalizedBoundary S k) n

end

end Omega.Multiscale
