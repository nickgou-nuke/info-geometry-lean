/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev.
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.
-/
import InfoGeometry.Canonical.FiniteFibonacciAnyonBraiding
import InfoGeometry.Algebra.InfiniteInductiveSUSY

/-!
# Stable Fibonacci Anyonic Braiding Direct Limit

This module formalizes the stable infinite-dimensional braid limit for Fibonacci anyons.

We prove the compatibility of the evaluation-factored projective Fibonacci gates
with the stable direct-limit TQFT phase mappings under any compatible cone.
-/

open InfoGeometry.Canonical.FiniteFibonacciAnyonBraiding
open InfoGeometry.Canonical.FiniteMajoranaBraiding
open InfoGeometry.Canonical.FiniteMajoranaProjectiveBraiding
open InfoGeometry.Algebra.InfiniteInductiveSUSY

namespace InfoGeometry.Canonical.StableFibonacciAnyonBraidLimit

variable {Gate : ℕ → Type*} [∀ n : ℕ, SMul (Units ℂ) (Gate n)]
variable {LGate : Type*} [SMul (Units ℂ) LGate]
variable (φ : ∀ n : ℕ, Gate n → Gate (Nat.succ n))
variable (ι : ∀ n : ℕ, Gate n → LGate)

/-- Step-wise compatibility of the homomorphism with scalar multiplication. -/
def SemiLinearMap (f : ∀ n : ℕ, Gate n → Gate (Nat.succ n)) : Prop :=
  ∀ (n : ℕ) (u : Units ℂ) (g : Gate n), f n (u • g) = u • f n g

/-- Step-wise compatibility of the target maps with scalar multiplication. -/
def SemiLinearCone (ι : ∀ n : ℕ, Gate n → LGate) : Prop :=
  ∀ (n : ℕ) (u : Units ℂ) (g : Gate n), ι n (u • g) = u • ι n g

/-- Compatibility cone predicate for braid gates. -/
def CompatibleBraidCone (f : ∀ n : ℕ, Gate n → Gate (Nat.succ n)) (ι : ∀ n : ℕ, Gate n → LGate) : Prop :=
  ∀ (n : ℕ) (g : Gate n), ι (Nat.succ n) (f n g) = ι n g

/--
Theorem: The stable infinite-dimensional Fibonacci projective gate readout is compatible
with the step-wise TQFT maps, meaning that the direct-limit image commutes with the TQFT transport.
-/
theorem stable_fibonacci_projective_gate_compat
    (phase : FibonacciBraidPhase)
    (readout : ∀ n, Equiv.Perm ℕ → Gate n)
    (w : FibonacciBraidWord)
    (h_readout : ∀ n : ℕ, ∀ p, φ n (readout n p) = readout (Nat.succ n) p)
    (h_ι_smul : SemiLinearCone ι)
    (h_cone : CompatibleBraidCone φ ι)
    (n : ℕ) :
    ι (Nat.succ n) (fibonacciProjectiveGate (Gate (Nat.succ n)) phase (readout (Nat.succ n)) w) =
      ι n (fibonacciProjectiveGate (Gate n) phase (readout n) w) := by
  dsimp [fibonacciProjectiveGate, projectiveBraidGate]
  rw [h_ι_smul (Nat.succ n), h_ι_smul n]
  have h_step : φ n (readout n (evalBraidWord w)) = readout (Nat.succ n) (evalBraidWord w) := h_readout n (evalBraidWord w)
  have h_cone_apply := h_cone n (readout n (evalBraidWord w))
  rw [h_step] at h_cone_apply
  exact congrArg (fun x => phase w • x) h_cone_apply

end InfoGeometry.Canonical.StableFibonacciAnyonBraidLimit
