import Mathlib.Tactic
import InfoGeometry.Canonical.CantorKMSState

/-!
# Finite KMS/Tomita symmetry on the Cantor stages

The pointwise complement has no fixed binary word.  The finite normalized KMS
trace nevertheless is invariant because complement is a permutation of the
finite word basis.  This is the honest finite precursor of an invariant mixed
state; no infinite Radon extension is asserted here.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorKMSFiniteTomitaBridge

open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.CantorKMSState

def wordComplement {n : ℕ} (w : BitWord n) : BitWord n :=
  fun i => !(w i)

def wordComplementEquiv (n : ℕ) : BitWord n ≃ BitWord n where
  toFun := wordComplement
  invFun := wordComplement
  left_inv w := by
    funext i
    cases h : w i <;> simp [wordComplement, h]
  right_inv w := by
    funext i
    cases h : w i <;> simp [wordComplement, h]

@[simp] theorem wordComplementEquiv_apply (n : ℕ) (w : BitWord n) :
    wordComplementEquiv n w = wordComplement w :=
  rfl

theorem wordComplement_involutive (n : ℕ) (w : BitWord n) :
    wordComplement (wordComplement w) = w := by
  funext i
  cases h : w i <;> simp [wordComplement, h]

def complementPullback {n : ℕ} (f : DiagAlg n) : DiagAlg n :=
  fun w => f (wordComplement w)

@[simp] theorem complementPullback_zero {n : ℕ} :
    complementPullback (0 : DiagAlg n) = 0 := by
  rfl

@[simp] theorem complementPullback_one {n : ℕ} :
    complementPullback (1 : DiagAlg n) = 1 := by
  rfl

theorem wordComplement_prefixSucc (n : ℕ) (w : BitWord (n + 1)) :
    wordComplement (prefixSucc n w) =
      prefixSucc n (wordComplement w) := by
  funext i
  rfl

theorem complementPullback_diagEmbedSucc
    (n : ℕ) (f : DiagAlg n) :
    complementPullback (diagEmbedSucc n f) =
      diagEmbedSucc n (complementPullback f) := by
  ext w
  unfold complementPullback diagEmbedSucc
  change f (prefixSucc n (wordComplement w)) =
    f (wordComplement (prefixSucc n w))
  rw [wordComplement_prefixSucc]

theorem complementPullback_add {n : ℕ} (f g : DiagAlg n) :
    complementPullback (f + g) =
      complementPullback f + complementPullback g := by
  rfl

theorem complementPullback_mul {n : ℕ} (f g : DiagAlg n) :
    complementPullback (f * g) =
      complementPullback f * complementPullback g := by
  rfl

theorem complementPullback_star {n : ℕ} (f : DiagAlg n) :
    complementPullback (star f) = star (complementPullback f) := by
  rfl

theorem complementPullback_involutive {n : ℕ} (f : DiagAlg n) :
    complementPullback (complementPullback f) = f := by
  funext w
  dsimp [complementPullback]
  congr 1
  funext i
  cases h : w i <;> simp [wordComplement, h]

theorem complementPullback_cylinderIndicator
    (n : ℕ) (w : BitWord n) :
    complementPullback (cylinderIndicator n w) =
      cylinderIndicator n (wordComplement w) := by
  ext v
  unfold complementPullback cylinderIndicator
  by_cases h : wordComplement v = w
  · have hw : wordComplement w = v := by
      rw [← h]
      exact wordComplement_involutive n v
    simp [h, hw]
  · have hw : v ≠ wordComplement w := by
      intro hv
      apply h
      rw [hv]
      exact wordComplement_involutive n w
    simp [h, hw]

theorem DiagTrace_complement_invariant (n : ℕ) (f : DiagAlg n) :
    DiagTrace n (complementPullback f) = DiagTrace n f := by
  unfold DiagTrace complementPullback
  have hsum :
      (∑ w : BitWord n, f (wordComplement w)) = ∑ w : BitWord n, f w := by
    simpa [wordComplementEquiv_apply] using
      (Equiv.sum_comp (wordComplementEquiv n) f)
  rw [hsum]

theorem DiagTrace_state_complement_invariant (n : ℕ) (f : DiagAlg n) :
    (DiagTrace_state n).val (complementPullback f) =
      (DiagTrace_state n).val f := by
  exact DiagTrace_complement_invariant n f

theorem DiagTrace_complementPullback_cylinderIndicator
    (n : ℕ) (w : BitWord n) :
    DiagTrace n (complementPullback (cylinderIndicator n w)) =
      DiagTrace n (cylinderIndicator n w) := by
  exact DiagTrace_complement_invariant n (cylinderIndicator n w)

theorem DiagTrace_state_complementPullback_cylinderIndicator
    (n : ℕ) (w : BitWord n) :
    (DiagTrace_state n).val
        (complementPullback (cylinderIndicator n w)) =
      (DiagTrace_state n).val (cylinderIndicator n w) := by
  exact DiagTrace_state_complement_invariant n (cylinderIndicator n w)

end InfoGeometry.Canonical.CantorKMSFiniteTomitaBridge
