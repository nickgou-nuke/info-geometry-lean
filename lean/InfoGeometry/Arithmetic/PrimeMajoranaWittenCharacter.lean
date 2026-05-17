import InfoGeometry.Arithmetic.SplitMajoranaPrimon

/-!
# InfoGeometry.Arithmetic.PrimeMajoranaWittenCharacter

Focused finite real Majorana Witten character layer.

This module owns the naming corridor

`equivariant real Witten character`
`Dirichlet Witten character`
`Möbius graded thermal character`

for the finite theorem

`Tr(Γ_Λ exp(-s H_Λ)) = ∏_{p≤Λ} (1 - q_p)`.

The theorem-bearing finite product is imported from `SplitMajoranaPrimon`.
No infinite Euler product, analytic continuation, Pfaffian determinant, or RH
claim is asserted here.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.PrimeMajoranaWittenCharacter

open scoped BigOperators
open InfoGeometry.Arithmetic.PrimeBitWittenIndex
open InfoGeometry.Arithmetic.SplitMajoranaPrimon

/-- Equivariant real Witten character alias. -/
def equivariantRealWittenCharacter
    (P : PrimeRegister) (q : ℕ → ℝ) : ℝ :=
  dirichletWittenCharacter P q

/-- Dirichlet Witten character alias. -/
def dirichletWittenCharacterReadout
    (P : PrimeRegister) (q : ℕ → ℝ) : ℝ :=
  dirichletWittenCharacter P q

/-- Möbius graded thermal character alias. -/
def mobiusGradedThermalCharacter
    (P : PrimeRegister) (q : ℕ → ℝ) : ℝ :=
  dirichletWittenCharacter P q

/-- The equivariant real Witten character is the finite reciprocal Euler product. -/
theorem equivariantRealWittenCharacter_eq_eulerProduct
    (P : PrimeRegister) (q : ℕ → ℝ) :
    equivariantRealWittenCharacter P q =
      finiteEulerProduct P q := by
  exact dirichletWittenCharacter_eq_eulerProduct P q

/-- The Dirichlet Witten character is the finite reciprocal Euler product. -/
theorem dirichletWittenCharacterReadout_eq_eulerProduct
    (P : PrimeRegister) (q : ℕ → ℝ) :
    dirichletWittenCharacterReadout P q =
      finiteEulerProduct P q := by
  exact dirichletWittenCharacter_eq_eulerProduct P q

/-- The Möbius graded thermal character is the finite Möbius squarefree sum. -/
theorem mobiusGradedThermalCharacter_eq_mobius_sum
    (P : PrimeRegister) (q : ℕ → ℝ) :
    mobiusGradedThermalCharacter P q =
      ∑ S ∈ P.primes.powerset,
        ((ArithmeticFunction.moebius (∏ p ∈ S, p) : ℤ) : ℝ) *
          ∏ p ∈ S, q p := by
  exact dirichletWittenCharacter_eq_mobius_sum P q

/--
Witness-gated infinite reciprocal-zeta readout.

This is deliberately only a bridge socket: the finite character above becomes
`1 / ζ(s)` only after an analytic Euler-product convergence witness.
-/
abbrev InfiniteReciprocalZetaCharacterBridge :=
  InfiniteEulerProductZetaBridge

/-! ## 2b. Owner target -/

/-- Owner target for the finite real Majorana Witten character surface. -/
def PrimeMajoranaWittenCharacterOwnerTarget : Prop :=
  ∀ (P : PrimeRegister) (q : ℕ → ℝ),
    equivariantRealWittenCharacter P q = finiteEulerProduct P q ∧
    dirichletWittenCharacterReadout P q = finiteEulerProduct P q ∧
    mobiusGradedThermalCharacter P q =
      ∑ S ∈ P.primes.powerset,
        ((ArithmeticFunction.moebius (∏ p ∈ S, p) : ℤ) : ℝ) *
          ∏ p ∈ S, q p

/-- The finite real Majorana Witten readouts agree with the finite Euler/Möbius surfaces. -/
theorem primeMajoranaWittenCharacterOwnerTarget :
    PrimeMajoranaWittenCharacterOwnerTarget := by
  intro P q
  exact ⟨equivariantRealWittenCharacter_eq_eulerProduct P q,
    dirichletWittenCharacterReadout_eq_eulerProduct P q,
    mobiusGradedThermalCharacter_eq_mobius_sum P q⟩

end InfoGeometry.Arithmetic.PrimeMajoranaWittenCharacter
