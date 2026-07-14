import InfoGeometry.Canonical.StableFibonacciAnyonBraidLimit
import InfoGeometry.Topological.FibonacciColimit

/-!
# InfoGeometry.Categorical.FibonacciBraidDirectLimit

Direct-limit braid-action API for the finite Fibonacci matrix lane.

This file packages the existing direct-limit transport theorems around the
finite Fibonacci `R` and `B = F R F` matrices.  It deliberately stays below the
level of a `BraidedCategory`: finite Artin and scalar phase identities remain
explicit hypotheses, then the direct-limit API transports them through
`DirectLimitSuperClosure`.
-/

noncomputable section

set_option autoImplicit false

namespace FibonacciBraidDirectLimit

open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.Topological.FibonacciAnyons
open InfoGeometry.Canonical.FiniteFibonacciAnyonBraiding
open InfoGeometry.Canonical.StableFibonacciAnyonBraidLimit

universe u

/-! ## Matrix braid generators in an algebraic direct limit -/

/-- The algebraic direct limit for a one-step commutative-ring tower. -/
abbrev BraidLimit
    {Stage : Nat → Type u} [∀ n : Nat, CommRing (Stage n)]
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1)) :=
  DirectLimitSuperClosure (Stage := Stage) bond

/-- The direct-limit image of the finite `R` generator. -/
def limitRMatrix
    {Stage : Nat → Type u} [∀ n : Nat, CommRing (Stage n)]
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (n : Nat) (q qInv : Stage n) :
    Matrix (Fin 2) (Fin 2) (BraidLimit (Stage := Stage) bond) :=
  R_matrixOf
    (directLimitOf (Stage := Stage) bond n q)
    (directLimitOf (Stage := Stage) bond n qInv)

/-- The direct-limit image of the finite middle generator `B = F R F`. -/
def limitBMatrix
    {Stage : Nat → Type u} [∀ n : Nat, CommRing (Stage n)]
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (n : Nat) (q qInv τ sqrtτ : Stage n) :
    Matrix (Fin 2) (Fin 2) (BraidLimit (Stage := Stage) bond) :=
  B_matrixOf
    (directLimitOf (Stage := Stage) bond n q)
    (directLimitOf (Stage := Stage) bond n qInv)
    (directLimitOf (Stage := Stage) bond n τ)
    (directLimitOf (Stage := Stage) bond n sqrtτ)

/-- A finite-stage Artin relation transports to the algebraic braid limit. -/
theorem limit_artin_relation_of_finite_stage
    {Stage : Nat → Type u} [∀ n : Nat, CommRing (Stage n)]
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (n : Nat) (q qInv τ sqrtτ : Stage n)
    (hArtin :
      R_matrixOf q qInv * B_matrixOf q qInv τ sqrtτ * R_matrixOf q qInv =
        B_matrixOf q qInv τ sqrtτ * R_matrixOf q qInv *
          B_matrixOf q qInv τ sqrtτ) :
    limitRMatrix bond n q qInv * limitBMatrix bond n q qInv τ sqrtτ *
        limitRMatrix bond n q qInv =
      limitBMatrix bond n q qInv τ sqrtτ * limitRMatrix bond n q qInv *
        limitBMatrix bond n q qInv τ sqrtτ := by
  change
    R_matrixOf (directLimitOf (Stage := Stage) bond n q)
        (directLimitOf (Stage := Stage) bond n qInv) *
        B_matrixOf (directLimitOf (Stage := Stage) bond n q)
          (directLimitOf (Stage := Stage) bond n qInv)
          (directLimitOf (Stage := Stage) bond n τ)
          (directLimitOf (Stage := Stage) bond n sqrtτ) *
        R_matrixOf (directLimitOf (Stage := Stage) bond n q)
          (directLimitOf (Stage := Stage) bond n qInv) =
      B_matrixOf (directLimitOf (Stage := Stage) bond n q)
          (directLimitOf (Stage := Stage) bond n qInv)
          (directLimitOf (Stage := Stage) bond n τ)
          (directLimitOf (Stage := Stage) bond n sqrtτ) *
        R_matrixOf (directLimitOf (Stage := Stage) bond n q)
          (directLimitOf (Stage := Stage) bond n qInv) *
          B_matrixOf (directLimitOf (Stage := Stage) bond n q)
            (directLimitOf (Stage := Stage) bond n qInv)
            (directLimitOf (Stage := Stage) bond n τ)
            (directLimitOf (Stage := Stage) bond n sqrtτ)
  exact fibonacci_colimit_artin_relation_of_finite_stage
    (Stage := Stage) bond n q qInv τ sqrtτ hArtin

/-- The finite inverse-pair relation transports to the algebraic braid limit. -/
theorem limit_inverse_relation_of_finite_stage
    {Stage : Nat → Type u} [∀ n : Nat, CommRing (Stage n)]
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (n : Nat) (q qInv : Stage n)
    (h : q * qInv = 1) :
    directLimitOf (Stage := Stage) bond n q *
        directLimitOf (Stage := Stage) bond n qInv = 1 :=
  fibonacci_colimit_inverse_relation_of_finite_stage
    (Stage := Stage) bond n q qInv h

/-- The finite golden-ratio relation transports to the algebraic braid limit. -/
theorem limit_tau_relation_of_finite_stage
    {Stage : Nat → Type u} [∀ n : Nat, CommRing (Stage n)]
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (n : Nat) (τ : Stage n)
    (h : τ ^ 2 + τ = 1) :
    directLimitOf (Stage := Stage) bond n τ ^ 2 +
        directLimitOf (Stage := Stage) bond n τ = 1 :=
  fibonacci_colimit_tau_relation_of_finite_stage
    (Stage := Stage) bond n τ h

/-- The finite square-root relation transports to the algebraic braid limit. -/
theorem limit_sqrt_tau_relation_of_finite_stage
    {Stage : Nat → Type u} [∀ n : Nat, CommRing (Stage n)]
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (n : Nat) (τ sqrtτ : Stage n)
    (h : sqrtτ ^ 2 = τ) :
    directLimitOf (Stage := Stage) bond n sqrtτ ^ 2 =
      directLimitOf (Stage := Stage) bond n τ :=
  fibonacci_colimit_sqrt_tau_relation_of_finite_stage
    (Stage := Stage) bond n τ sqrtτ h

/-- The finite phase-to-`τ` relation transports to the algebraic braid limit. -/
theorem limit_phase_relation_of_finite_stage
    {Stage : Nat → Type u} [∀ n : Nat, CommRing (Stage n)]
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (n : Nat) (q qInv τ : Stage n)
    (h : q ^ 2 + qInv ^ 2 = τ) :
    directLimitOf (Stage := Stage) bond n q ^ 2 +
        directLimitOf (Stage := Stage) bond n qInv ^ 2 =
      directLimitOf (Stage := Stage) bond n τ :=
  fibonacci_colimit_phase_relation_of_finite_stage
    (Stage := Stage) bond n q qInv τ h

/-! ## Stable projective gate cone readout -/

variable {Gate : ℕ → Type*} [∀ n : ℕ, SMul (Units ℂ) (Gate n)]
variable {LGate : Type*} [SMul (Units ℂ) LGate]

/--
Existing stable projective Fibonacci gate compatibility, exposed from the
direct-limit braid-action namespace.
-/
theorem stable_projective_gate_cone_compat
    (φ : ∀ n : ℕ, Gate n → Gate (Nat.succ n))
    (ι : ∀ n : ℕ, Gate n → LGate)
    (phase : FibonacciBraidPhase)
    (readout : ∀ n, Equiv.Perm ℕ → Gate n)
    (w : FibonacciBraidWord)
    (h_readout : ∀ n : ℕ, ∀ p, φ n (readout n p) = readout (Nat.succ n) p)
    (h_ι_smul : SemiLinearCone ι)
    (h_cone : CompatibleBraidCone φ ι)
    (n : ℕ) :
    ι (Nat.succ n) (fibonacciProjectiveGate (Gate (Nat.succ n)) phase (readout (Nat.succ n)) w) =
      ι n (fibonacciProjectiveGate (Gate n) phase (readout n) w) :=
  stable_fibonacci_projective_gate_compat
    (φ := φ) (ι := ι) phase readout w h_readout h_ι_smul h_cone n

end FibonacciBraidDirectLimit
