import InfoGeometry.Canonical.FiniteFibonacciElectronIndependence

/-!
# InfoGeometry.Canonical.FiniteFibonacciElectronPaperBridge

Finite paper-facing bridge for the `n = 4` Fibonacci sector with arbitrary
`3 * r` electrons.

The paper's section 4 shows that the extra electron-dependent factor is
invariant under anyon permutations and that the finite braid matrices on the
Fibonacci channel do not depend on `r`.

This file exposes only that finite algebraic content:

* electron counts are multiples of three;
* an explicit symmetric electron factor hypothesis is invariant under anyon permutations;
* the `R`, `F`, and `B = F R F` readouts are independent of `r`;
* a base-sector Artin matrix identity transports unchanged to every `r` sector.

No electron-coordinate polynomials.
No hypergeometric continuation.
No conformal blocks.
No analytic braid computation.
-/

namespace InfoGeometry.Canonical.FiniteFibonacciElectronPaperBridge

open Matrix
open InfoGeometry.Canonical.FiniteFibonacciElectronIndependence
open InfoGeometry.Canonical.FiniteFibonacciFusionMatrix
open InfoGeometry.Canonical.FiniteFibonacciMonodromyInterface

/-- The allowed electron count in the section-4 sector is a multiple of three. -/
theorem electronCount_three_dvd (r : ℕ) :
    3 ∣ electronCount r :=
  three_dvd_electronCount r

/-- A symmetric electron factor is invariant under swapping anyon labels. -/
theorem symmetricElectronFactor_swap_invariant
    {ElectronData Value : Type*}
    (eval : ElectronData → Value)
    (permute : Equiv.Perm (Fin 4) → ElectronData → ElectronData)
    (hperm : ∀ (σ : Equiv.Perm (Fin 4)) (z : ElectronData), eval (permute σ z) = eval z)
    (z : ElectronData) :
    eval (permute (Equiv.swap (0 : Fin 4) 1) z) = eval z :=
  electronFactor_swap01_invariant eval permute hperm z

/-- The diagonal `R` matrix in the electron sector is independent of `r`. -/
theorem fibonacciRMatrixWithElectrons_independent (r s : ℕ) (q : Units ℂ) :
    fibonacciRMatrixWithElectrons r q = fibonacciRMatrixWithElectrons s q :=
  fibonacciRMatrixWithElectrons_independent_of_r r s q

/-- The fusion matrix in the electron sector is independent of `r`. -/
theorem fibonacciFusionMatrixWithElectrons_independent (r s : ℕ)
    (τ root : ℂ) :
    fibonacciFusionMatrixWithElectrons r τ root =
      fibonacciFusionMatrixWithElectrons s τ root :=
  fibonacciFusionMatrixWithElectrons_independent_of_r r s τ root

/-- The middle braid matrix in the electron sector is independent of `r`. -/
theorem fibonacciBMatrixWithElectrons_independent (r s : ℕ)
    (q : Units ℂ) (τ root : ℂ) :
    fibonacciBMatrixWithElectrons r q τ root =
      fibonacciBMatrixWithElectrons s q τ root :=
  fibonacciBMatrixWithElectrons_independent_of_r r s q τ root

/-- The electron-sector fusion matrix is involutive in every `r` sector. -/
theorem fibonacciFusionMatrixWithElectrons_sq
    (r : ℕ) {τ root : ℂ} (hroot : root ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    fibonacciFusionMatrixWithElectrons r τ root *
        fibonacciFusionMatrixWithElectrons r τ root = 1 :=
  InfoGeometry.Canonical.FiniteFibonacciElectronIndependence.fibonacciFusionMatrixWithElectrons_sq
    r hroot hτ

/-- The electron-sector fusion matrix has determinant `-1` in every `r` sector. -/
theorem det_fibonacciFusionMatrixWithElectrons
    (r : ℕ) {τ root : ℂ} (hroot : root ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    (fibonacciFusionMatrixWithElectrons r τ root).det = -1 :=
  InfoGeometry.Canonical.FiniteFibonacciElectronIndependence.det_fibonacciFusionMatrixWithElectrons
    r hroot hτ

/-- The electron-sector middle braid matrix is the `F R F` conjugate. -/
theorem fibonacciBMatrixWithElectrons_eq_FRF
    (r : ℕ) (q : Units ℂ) (τ root : ℂ) :
    fibonacciBMatrixWithElectrons r q τ root =
      fibonacciFusionMatrixWithElectrons r τ root *
        fibonacciRMatrixWithElectrons r q *
          fibonacciFusionMatrixWithElectrons r τ root :=
  InfoGeometry.Canonical.FiniteFibonacciElectronIndependence.fibonacciBMatrixWithElectrons_eq_FRF
    r q τ root

/-- A base-sector Artin matrix identity transports unchanged to every electron sector. -/
theorem fibonacciWithElectrons_artin_from_matrix_identity
    (r : ℕ) (q : Units ℂ) (τ root : ℂ)
    (hArtin : fibonacciRMatrix q * fibonacciBMatrix q τ root * fibonacciRMatrix q =
      fibonacciBMatrix q τ root * fibonacciRMatrix q * fibonacciBMatrix q τ root) :
    fibonacciRMatrixWithElectrons r q * fibonacciBMatrixWithElectrons r q τ root *
        fibonacciRMatrixWithElectrons r q =
      fibonacciBMatrixWithElectrons r q τ root *
        fibonacciRMatrixWithElectrons r q *
          fibonacciBMatrixWithElectrons r q τ root :=
  by
    simpa [fibonacciRMatrixWithElectrons, fibonacciBMatrixWithElectrons] using hArtin

end InfoGeometry.Canonical.FiniteFibonacciElectronPaperBridge
