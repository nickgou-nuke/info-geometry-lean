import InfoGeometry.Canonical.FiniteFibonacciFusionMatrix
import InfoGeometry.Canonical.FiniteFibonacciMonodromyInterface

/-!
# InfoGeometry.Canonical.FiniteFibonacciElectronIndependence

Finite braid/fusion interface for four Fibonacci anyons with `3 * r` electrons.

Section 4 of the paper shows analytically that adding `r` triples of electron
fields does not change the braid matrices for the four Fibonacci anyons: the
extra electron-dependent factor is symmetric in the four anyon variables, and
braiding acts only on the anyon coordinates.  This file formalizes only the
finite algebraic interface for that conclusion:

* electron counts are multiples of three;
* a symmetric/electron factor is represented as data invariant under any anyon
  permutation;
* the finite `R`, `F`, and `B = F R F` readouts are independent of `r`;
* the Artin compatibility interface is likewise independent of `r` when supplied
  as an explicit finite matrix identity.

No electron-coordinate polynomials.
No conformal-block or hypergeometric construction.
No analytic continuation theorem.
No Laughlin-factor braid-matrix derivation.
-/

namespace FiniteFibonacciElectronIndependence

open Matrix
open FiniteFibonacciFusionMatrix
open FiniteFibonacciMonodromyInterface

/-- Symmetry under swapping the first two anyon labels from an explicit permutation-invariance hypothesis. -/
theorem electronFactor_swap01_invariant {ElectronData Value : Type*}
    (eval : ElectronData → Value)
    (permute : Equiv.Perm (Fin 4) → ElectronData → ElectronData)
    (hperm : ∀ (σ : Equiv.Perm (Fin 4)) (z : ElectronData), eval (permute σ z) = eval z)
    (z : ElectronData) :
    eval (permute (Equiv.swap (0 : Fin 4) 1) z) = eval z :=
  hperm (Equiv.swap (0 : Fin 4) 1) z

/-- Symmetry under swapping the middle two anyon labels from an explicit hypothesis. -/
theorem electronFactor_swap12_invariant {ElectronData Value : Type*}
    (eval : ElectronData → Value)
    (permute : Equiv.Perm (Fin 4) → ElectronData → ElectronData)
    (hperm : ∀ (σ : Equiv.Perm (Fin 4)) (z : ElectronData), eval (permute σ z) = eval z)
    (z : ElectronData) :
    eval (permute (Equiv.swap (1 : Fin 4) 2) z) = eval z :=
  hperm (Equiv.swap (1 : Fin 4) 2) z

/-- Symmetry under swapping the last two anyon labels from an explicit hypothesis. -/
theorem electronFactor_swap23_invariant {ElectronData Value : Type*}
    (eval : ElectronData → Value)
    (permute : Equiv.Perm (Fin 4) → ElectronData → ElectronData)
    (hperm : ∀ (σ : Equiv.Perm (Fin 4)) (z : ElectronData), eval (permute σ z) = eval z)
    (z : ElectronData) :
    eval (permute (Equiv.swap (2 : Fin 4) 3) z) = eval z :=
  hperm (Equiv.swap (2 : Fin 4) 3) z

/-- The four-anyon `R` matrix in the sector with `3 * r` electrons. -/
noncomputable def fibonacciRMatrixWithElectrons (_r : ℕ) (q : Units ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  fibonacciRMatrix q

/-- The four-anyon fusion matrix in the sector with `3 * r` electrons. -/
noncomputable def fibonacciFusionMatrixWithElectrons (_r : ℕ) (τ s : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  fibonacciFusionMatrix τ s

/-- The four-anyon middle braid matrix in the sector with `3 * r` electrons. -/
noncomputable def fibonacciBMatrixWithElectrons (_r : ℕ) (q : Units ℂ) (τ s : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  fibonacciBMatrix q τ s

/-- The electron count in this sector is a multiple of three. -/
theorem electronCountWithElectrons_three_dvd (r : ℕ) :
    3 ∣ electronCount r :=
  three_dvd_electronCount r

/-- The diagonal `R` readout is independent of the number of electron triples. -/
theorem fibonacciRMatrixWithElectrons_independent_of_r
    (r s : ℕ) (q : Units ℂ) :
    fibonacciRMatrixWithElectrons r q = fibonacciRMatrixWithElectrons s q := by
  change fibonacciRMatrix q = fibonacciRMatrix q
  rfl

/-- The fusion matrix is independent of the number of electron triples. -/
theorem fibonacciFusionMatrixWithElectrons_independent_of_r
    (r s : ℕ) (τ root : ℂ) :
    fibonacciFusionMatrixWithElectrons r τ root =
      fibonacciFusionMatrixWithElectrons s τ root := by
  change fibonacciFusionMatrix τ root = fibonacciFusionMatrix τ root
  rfl

/-- The middle braid matrix `B = F R F` is independent of the number of electron triples. -/
theorem fibonacciBMatrixWithElectrons_independent_of_r
    (r s : ℕ) (q : Units ℂ) (τ root : ℂ) :
    fibonacciBMatrixWithElectrons r q τ root =
      fibonacciBMatrixWithElectrons s q τ root := by
  change fibonacciBMatrix q τ root = fibonacciBMatrix q τ root
  rfl

/-- In every electron sector, the fusion matrix remains involutive. -/
theorem fibonacciFusionMatrixWithElectrons_sq
    (r : ℕ) {τ root : ℂ} (hroot : root ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    fibonacciFusionMatrixWithElectrons r τ root *
        fibonacciFusionMatrixWithElectrons r τ root = 1 :=
  fibonacciFusionMatrix_sq hroot hτ

/-- In every electron sector, the fusion matrix has determinant `-1`. -/
theorem det_fibonacciFusionMatrixWithElectrons
    (r : ℕ) {τ root : ℂ} (hroot : root ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    (fibonacciFusionMatrixWithElectrons r τ root).det = -1 :=
  det_fibonacciFusionMatrix hroot hτ

/-- In every electron sector, the middle braid readout is `F R F`. -/
theorem fibonacciBMatrixWithElectrons_eq_FRF
    (r : ℕ) (q : Units ℂ) (τ root : ℂ) :
    fibonacciBMatrixWithElectrons r q τ root =
      fibonacciFusionMatrixWithElectrons r τ root *
        fibonacciRMatrixWithElectrons r q *
          fibonacciFusionMatrixWithElectrons r τ root := by
  change fibonacciBMatrix q τ root = fibonacciFusionMatrix τ root * fibonacciRMatrix q * fibonacciFusionMatrix τ root
  change fibonacciFusionMatrix τ root * fibonacciRMatrix q * fibonacciFusionMatrix τ root =
      fibonacciFusionMatrix τ root * fibonacciRMatrix q * fibonacciFusionMatrix τ root
  rfl

/--
Artin compatibility is independent of `r` when supplied as the same explicit
finite matrix identity in the electron-free sector.
-/
theorem fibonacciWithElectrons_artin_from_matrix_identity
    (r : ℕ) (q : Units ℂ) (τ root : ℂ)
    (hArtin : fibonacciRMatrix q * fibonacciBMatrix q τ root * fibonacciRMatrix q =
      fibonacciBMatrix q τ root * fibonacciRMatrix q * fibonacciBMatrix q τ root) :
    fibonacciRMatrixWithElectrons r q * fibonacciBMatrixWithElectrons r q τ root *
        fibonacciRMatrixWithElectrons r q =
      fibonacciBMatrixWithElectrons r q τ root * fibonacciRMatrixWithElectrons r q *
        fibonacciBMatrixWithElectrons r q τ root :=
  hArtin

end FiniteFibonacciElectronIndependence
