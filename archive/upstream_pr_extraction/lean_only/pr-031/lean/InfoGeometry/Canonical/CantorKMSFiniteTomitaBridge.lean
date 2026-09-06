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

def complementPullback {n : ℕ} (f : DiagAlg n) : DiagAlg n :=
  fun w => f (wordComplement w)

theorem complementPullback_involutive {n : ℕ} (f : DiagAlg n) :
    complementPullback (complementPullback f) = f := by
  funext w
  dsimp [complementPullback]
  congr 1
  funext i
  cases h : w i <;> simp [wordComplement, h]

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

end InfoGeometry.Canonical.CantorKMSFiniteTomitaBridge
