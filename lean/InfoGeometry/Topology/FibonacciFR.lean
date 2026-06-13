import InfoGeometry.Categorical.FibonacciBraiding

/-!
# Fibonacci F/R finite matrix surface

This module projects the existing finite Fibonacci matrix owners into the
topology namespace.  It does not construct a full modular tensor category,
conformal-block monodromy theorem, or laboratory realization.

#### BUCKET 1: CLOSED FINITE THEOREMS

`fibonacci_F_involutive`, `fibonacci_F_det`, and `fibonacci_B_eq_FRF`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES

`fibonacci_FR_artin_from_identity` and `fibonacci_FR_packet`, conditional on an
explicit finite matrix Artin identity.

#### BUCKET 3: OPEN CLOSURE DEBT

Exact cyclotomic specialization of the Artin identity is currently witnessed by
Sage/SymPy scripts, not proved in Lean in this file.  The full categorical
hexagon/pentagon coherence and parafermion CFT realization are also open here.
-/

noncomputable section

namespace InfoGeometry.Topology.FibonacciFR

open Matrix
open InfoGeometry.Canonical.FiniteFibonacciFusionMatrix

/-- Complex `2 x 2` matrices used by the finite Fibonacci F/R surface. -/
abbrev Mat2C := Matrix (Fin 2) (Fin 2) ℂ

/-- Local notation for the finite Fibonacci `F` matrix. -/
def F (τ s : ℂ) : Mat2C :=
  fibonacciFusionMatrix τ s

/-- Local notation for the finite Fibonacci `R` matrix. -/
def R (q : Units ℂ) : Mat2C :=
  fibonacciRMatrix q

/-- Local notation for the middle braid generator `B = F R F`. -/
def B (q : Units ℂ) (τ s : ℂ) : Mat2C :=
  fibonacciBMatrix q τ s

/-- Exact finite readout: `F^2 = I` under the scalar Fibonacci relations. -/
theorem fibonacci_F_involutive {τ s : ℂ}
    (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    F τ s * F τ s = 1 := by
  exact fibonacciFusionMatrix_sq hs hτ

/-- Exact finite readout: `det F = -1` under the scalar Fibonacci relations. -/
theorem fibonacci_F_det {τ s : ℂ}
    (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    (F τ s).det = -1 := by
  exact det_fibonacciFusionMatrix hs hτ

/-- The chosen convention for the second generator is `B = F R F`. -/
theorem fibonacci_B_eq_FRF (q : Units ℂ) (τ s : ℂ) :
    B q τ s = F τ s * R q * F τ s := by
  rfl

/--
Conditional Artin/Yang--Baxter readout for the local two-generator Fibonacci
matrix surface.
-/
theorem fibonacci_FR_artin_from_identity
    (q : Units ℂ) (τ s : ℂ)
    (hArtin : R q * B q τ s * R q = B q τ s * R q * B q τ s) :
    R q * B q τ s * R q = B q τ s * R q * B q τ s :=
  hArtin

/-- Combined theorem-safe finite F/R packet. -/
theorem fibonacci_FR_packet
    (q : Units ℂ) {τ s : ℂ}
    (hs : s ^ 2 = τ)
    (hτ : τ ^ 2 + τ = 1)
    (hArtin : R q * B q τ s * R q = B q τ s * R q * B q τ s) :
    F τ s * F τ s = 1 ∧
      (F τ s).det = -1 ∧
      B q τ s = F τ s * R q * F τ s ∧
      R q * B q τ s * R q = B q τ s * R q * B q τ s := by
  exact ⟨
    fibonacci_F_involutive hs hτ,
    fibonacci_F_det hs hτ,
    fibonacci_B_eq_FRF q τ s,
    fibonacci_FR_artin_from_identity q τ s hArtin⟩

end InfoGeometry.Topology.FibonacciFR

end noncomputable section
