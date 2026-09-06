import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import InfoGeometry.Section5

/-!
# Section 18: Clifford hierarchy, finite arithmetic and gamma shadows

This file repairs the Section 18 prose into theorem-safe finite claims.

#### BUCKET 1: CLOSED FINITE THEOREMS
The complex Clifford hierarchy's dimension arithmetic is verified:
`dim M_{2^k}(C) = 2^(2k)` for even level and
`dim (M_{2^k}(C) ⊕ M_{2^k}(C)) = 2^(2k+1)` for odd level.  The finite
sequence through `Cl(8,C)` is encoded by these formulas.  The Dirac gamma
matrices from Section 5 satisfy the finite Jordan/anticommutator readout
`γ_mu γ_nu + γ_nu γ_mu = 2 η_{mu,nu} I`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
None.  These are direct arithmetic and finite matrix facts.

#### BUCKET 3: OPEN CLOSURE DEBT
No algebra isomorphism object for all complex Clifford algebras is constructed
here.  The tensor-product recursion, "Chirla torsion hierarchy", real
Minkowski Clifford algebra, octonionic and exceptional-group claims, spin
statistics, CPT, gauge fields, supersymmetry, noncommutative geometry, quantum
computing, TQFT, and any physical derivation remain outside this finite module.
-/

noncomputable section

namespace Section18

abbrev DiracMatrix := Section5.DiracMatrix

/-- Matrix size in the complex Clifford classification at level `k`. -/
def complexMatrixSize (k : ℕ) : ℕ :=
  2 ^ k

/-- Complex dimension of `M_n(C)` as a vector space. -/
def matrixAlgebraDim (n : ℕ) : ℕ :=
  n * n

/-- Complex dimension of the direct sum `M_n(C) ⊕ M_n(C)`. -/
def doubledMatrixAlgebraDim (n : ℕ) : ℕ :=
  2 * matrixAlgebraDim n

/-- Even complex Clifford dimension arithmetic: `M_{2^k}(C)` has dimension `2^(2k)`. -/
theorem even_level_dimension (k : ℕ) :
    matrixAlgebraDim (complexMatrixSize k) = 2 ^ (2 * k) := by
  unfold matrixAlgebraDim complexMatrixSize
  rw [← pow_add]
  congr 1
  omega

/--
Odd complex Clifford dimension arithmetic:
`M_{2^k}(C) ⊕ M_{2^k}(C)` has dimension `2^(2k+1)`.
-/
theorem odd_level_dimension (k : ℕ) :
    doubledMatrixAlgebraDim (complexMatrixSize k) = 2 ^ (2 * k + 1) := by
  unfold doubledMatrixAlgebraDim matrixAlgebraDim complexMatrixSize
  rw [← pow_add]
  rw [show 2 * 2 ^ (k + k) = 2 ^ 1 * 2 ^ (k + k) by simp]
  rw [← pow_add]
  congr 1
  omega

/-- The finite sequence through `Cl(8,C)` has the expected complex dimensions. -/
theorem finite_clifford_dimension_sequence :
    matrixAlgebraDim (complexMatrixSize 0) = 1 ∧
    doubledMatrixAlgebraDim (complexMatrixSize 0) = 2 ∧
    matrixAlgebraDim (complexMatrixSize 1) = 4 ∧
    doubledMatrixAlgebraDim (complexMatrixSize 1) = 8 ∧
    matrixAlgebraDim (complexMatrixSize 2) = 16 ∧
    doubledMatrixAlgebraDim (complexMatrixSize 2) = 32 ∧
    matrixAlgebraDim (complexMatrixSize 3) = 64 ∧
    doubledMatrixAlgebraDim (complexMatrixSize 3) = 128 ∧
    matrixAlgebraDim (complexMatrixSize 4) = 256 := by
  norm_num [matrixAlgebraDim, doubledMatrixAlgebraDim, complexMatrixSize]

/-- Section 5's finite gamma matrices provide the Jordan metric readout. -/
theorem gamma_jordan_metric_readout (mu nu : Fin 4) :
    Section5.γ mu * Section5.γ nu + Section5.γ nu * Section5.γ mu =
      (2 * Section5.η mu nu) • (1 : DiracMatrix) :=
  Section5.clifford_anticomm_full mu nu

theorem section18_capstone :
    (∀ k : ℕ, matrixAlgebraDim (complexMatrixSize k) = 2 ^ (2 * k)) ∧
    (∀ k : ℕ, doubledMatrixAlgebraDim (complexMatrixSize k) = 2 ^ (2 * k + 1)) ∧
    (∀ mu nu : Fin 4,
      Section5.γ mu * Section5.γ nu + Section5.γ nu * Section5.γ mu =
        (2 * Section5.η mu nu) • (1 : DiracMatrix)) := by
  exact ⟨even_level_dimension, odd_level_dimension, gamma_jordan_metric_readout⟩

end Section18
