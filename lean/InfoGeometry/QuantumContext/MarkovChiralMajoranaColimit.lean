/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Clifford.CliffordBitWordEquivalence
import InfoGeometry.QuantumContext.MarkovChiralBipolarLift
import InfoGeometry.QuantumContext.MarkovJordanWignerActionNonvanishing
import InfoGeometry.QuantumContext.MarkovGroupInverseStageColimit

/-!
# Chiral Majorana and Markov group inverse in the matrix-stage colimit

The recursive Clifford index is transported by the repository's explicit
`idxBitWordEquiv` to a complex `BitWord` matrix stage, then by the canonical
quotient-colimit homomorphism. This preserves multiplication identities,
nonzero finite-stage generators, and supplied group-inverse equations. It
does not transport the ordered softmax interpretation or weighted real
pairing to the complex colimit.
-/

open scoped TensorProduct DirectSum Matrix Kronecker

namespace InfoGeometry.QuantumContext.MarkovChiralMajoranaColimit

open InfoGeometry.Algebra.CliffordBitWordEquivalence
open InfoGeometry.Canonical.ComplexMatrixStage
open InfoGeometry.Canonical.HartwigSouriauFrameDrazin
open InfoGeometry.Canonical.MatrixStageInductiveLimit
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.TowerMatrix
open InfoGeometry.QuantumContext.MarkovDrazin
open InfoGeometry.QuantumContext.MarkovDrazin.ChiralBipolarLift
open InfoGeometry.QuantumContext.MarkovDrazin.JordanWigner
open InfoGeometry.QuantumContext.MarkovGroupInverseStageColimit

/-- The finite real Clifford-stage algebra map into its complex `BitWord`
matrix stage and the quotient direct colimit. -/
noncomputable def realCliffordStageToLimit (k : ℕ) :
    MatStage (k + 1) →+* MatrixStageLimit :=
  ((canonicalStageHom (k + 1)).toAlgHom.toRingHom).comp
    (realMatrixToComplexStage (k + 1) (idxBitWordEquiv (k + 1))).toRingHom

/-- The lifted chiral Majorana represented in the quotient matrix-stage
colimit. -/
noncomputable def chiralMajoranaAtLimit (k : ℕ) : MatrixStageLimit :=
  realCliffordStageToLimit k (liftedChiralMajorana k)

/-- The symmetric-softmax Markov Laplacian represented in the same quotient
matrix-stage colimit as the chiral Majorana. -/
noncomputable def softmaxLaplacianAtLimit (k : ℕ)
    (scores : Idx (k + 1) → Idx (k + 1) → ℝ) : MatrixStageLimit :=
  realCliffordStageToLimit k
    (1 - FiniteSoftmaxMarkovKernel.softmaxAttentionMatrix scores)

private theorem realCliffordStageToLimit_injective (k : ℕ) :
    Function.Injective (realCliffordStageToLimit k) := by
  intro A B h
  have hstage :
      canonicalStageHom (k + 1)
          (realMatrixToComplexStage (k + 1) (idxBitWordEquiv (k + 1)) A) =
        canonicalStageHom (k + 1)
          (realMatrixToComplexStage (k + 1) (idxBitWordEquiv (k + 1)) B) := h
  have hcomplex := canonicalStageHom_injective (k + 1) hstage
  exact (realMatrixToComplexStage (k + 1)
    (idxBitWordEquiv (k + 1))).injective hcomplex

/-- The chiral Majorana does not vanish when transported from the real
Clifford matrix stage to the complex quotient colimit. -/
theorem chiralMajoranaAtLimit_ne_zero (k : ℕ) :
    chiralMajoranaAtLimit k ≠ 0 := by
  intro h
  have hmap : realCliffordStageToLimit k (liftedChiralMajorana k) =
      realCliffordStageToLimit k 0 := by
    simpa [chiralMajoranaAtLimit] using h
  have hstage : liftedChiralMajorana k = 0 :=
    (realCliffordStageToLimit_injective k) hmap
  exact liftedChiralMajorana_ne_zero k hstage

/-- The chiral grading anticommutation law survives the explicit carrier
transport and canonical quotient-colimit inclusion. -/
theorem chiralMajoranaAtLimit_anticommutes_globalChirality (k : ℕ) :
    realCliffordStageToLimit k (globalChirality (k + 1)) *
        chiralMajoranaAtLimit k +
      chiralMajoranaAtLimit k *
        realCliffordStageToLimit k (globalChirality (k + 1)) = 0 := by
  have h := congrArg (realCliffordStageToLimit k)
    (liftedChiralMajorana_anticommutes_globalChirality k)
  simpa only [map_add, map_mul, map_zero, chiralMajoranaAtLimit,
    realCliffordStageToLimit] using h

/-- The finite symmetric-softmax Markov group inverse and the nonzero chiral
Majorana coexist in the quotient matrix-stage colimit. The theorem asserts
the transported algebraic group-inverse equations and chiral anticommutation;
it does not assert stochasticity, positivity, or energy-pairing identities
over the complex colimit. -/
theorem exists_symmetricSoftmax_groupInverse_chiralMajorana_inMatrixStageLimit
    (k : ℕ) (scores : Idx (k + 1) → Idx (k + 1) → ℝ)
    (hsymm : ∀ i j, scores i j = scores j i)
    (entropyForce : Matrix (Idx (k + 1)) (Idx (k + 1)) ℝ) :
    ∃ G : MatrixStageLimit,
      IsGroupInverse (softmaxLaplacianAtLimit k scores) G ∧
      ∃ G₀ : Matrix (Idx (k + 1)) (Idx (k + 1)) ℝ,
        G = realCliffordStageToLimit k G₀ ∧
        realCliffordStageToLimit k
            (G₀ * markovLeftOnsager
              (FiniteSoftmaxMarkovKernel.softmaxAttentionMatrix scores) entropyForce) =
          realCliffordStageToLimit k
            (markovRangeIdempotent
              (FiniteSoftmaxMarkovKernel.softmaxAttentionMatrix scores) G₀ * entropyForce) ∧
      chiralMajoranaAtLimit k ≠ 0 ∧
      realCliffordStageToLimit k (globalChirality (k + 1)) *
          chiralMajoranaAtLimit k +
        chiralMajoranaAtLimit k *
          realCliffordStageToLimit k (globalChirality (k + 1)) = 0 := by
  obtain ⟨G₀, hG₀, hRecovery, _hEnergy, _hMajorana, _hNoncomm⟩ :=
    exists_symmetricSoftmax_groupInverse_majorana_balance
      k scores hsymm entropyForce
  let Gstage := realMatrixToComplexStage (k + 1)
    (idxBitWordEquiv (k + 1)) G₀
  have hGstage := groupInverse_realMatrixToComplexStage
    (k + 1) (idxBitWordEquiv (k + 1))
    (1 - FiniteSoftmaxMarkovKernel.softmaxAttentionMatrix scores) G₀ hG₀
  have hRecoveryLimit := congrArg (realCliffordStageToLimit k) hRecovery
  refine ⟨canonicalStageHom (k + 1) Gstage, ?_,
    ⟨G₀, rfl, ?_, ?_, ?_⟩⟩
  · simpa [softmaxLaplacianAtLimit, realCliffordStageToLimit,
      Gstage] using groupInverse_canonicalStageHom
        (k + 1)
        (realMatrixToComplexStage (k + 1)
          (idxBitWordEquiv (k + 1))
          (1 - FiniteSoftmaxMarkovKernel.softmaxAttentionMatrix scores))
        Gstage hGstage
  · simpa [realCliffordStageToLimit, map_mul] using hRecoveryLimit
  · exact chiralMajoranaAtLimit_ne_zero k
  · exact chiralMajoranaAtLimit_anticommutes_globalChirality k

end InfoGeometry.QuantumContext.MarkovChiralMajoranaColimit
