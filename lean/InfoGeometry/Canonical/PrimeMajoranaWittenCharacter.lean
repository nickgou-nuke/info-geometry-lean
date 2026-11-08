import InfoGeometry.Arithmetic.MobiusPrimonParity
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.SplitMajoranaPrimon
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.OwnerTarget

/-!
# InfoGeometry.Canonical.PrimeMajoranaWittenCharacter

Canonical finite split-Majorana / Dirichlet Witten character bridge.

This file is theorem-native and finite:

* the finite Dirichlet/Witten character is re-exported from the arithmetic owner;
* the finite split-Majorana chirality character is re-exported from the
  square-free Möbius parity owner;
* the finite signed Pfaffian readout is re-exported from the primon Majorana
  owner.

No infinite Euler-product convergence, zeta zero claim, or RH statement is
asserted here.
-/

noncomputable section

namespace InfoGeometry.Canonical.PrimeMajoranaWittenCharacter

open scoped BigOperators

open InfoGeometry.Arithmetic.PrimeBitWittenIndex
open InfoGeometry.Arithmetic.SplitMajoranaPrimon
open InfoGeometry.Arithmetic.MobiusPrimonParity

/-- Canonical finite Dirichlet Witten character. -/
def finiteDirichletWittenCharacter
    (P : PrimeRegister) (q : ℕ → ℝ) : ℝ :=
  dirichletWittenCharacter P q

/-- Canonical finite split-Majorana chirality character. -/
def finiteSplitMajoranaChiralityCharacter
    (P : PrimeRegister) (q : ℕ → ℝ) : ℝ :=
  finiteMajoranaChiralityCharacter P q

/-- Canonical finite signed Pfaffian character readout. -/
def finiteSignedPfaffianCharacter
    (P : PrimeRegister) (q : ℕ → ℝ) : ℝ :=
  majoranaPfaffianProduct P q

/-- The finite Dirichlet Witten character is the finite reciprocal Euler product. -/
theorem finiteDirichletWittenCharacter_eq_eulerProduct
    (P : PrimeRegister) (q : ℕ → ℝ) :
    finiteDirichletWittenCharacter P q = finiteEulerProduct P q := by
  simpa [finiteDirichletWittenCharacter] using
    dirichletWittenCharacter_eq_eulerProduct P q

/-- The split-Majorana chirality character is the finite reciprocal Euler product. -/
theorem finiteSplitMajoranaChiralityCharacter_eq_eulerProduct
    (P : PrimeRegister) (q : ℕ → ℝ) :
    finiteSplitMajoranaChiralityCharacter P q = finiteEulerProduct P q := by
  simpa [finiteSplitMajoranaChiralityCharacter] using
    finiteMajoranaChiralityCharacter_eq_eulerProduct P q

/-- The split-Majorana chirality character equals the finite Dirichlet Witten character. -/
theorem finiteSplitMajoranaChiralityCharacter_eq_dirichletWittenCharacter
    (P : PrimeRegister) (q : ℕ → ℝ) :
    finiteSplitMajoranaChiralityCharacter P q =
      finiteDirichletWittenCharacter P q := by
  rw [finiteSplitMajoranaChiralityCharacter_eq_eulerProduct,
    finiteDirichletWittenCharacter_eq_eulerProduct]

/-- The finite signed Pfaffian readout is the finite reciprocal Euler product. -/
theorem finiteSignedPfaffianCharacter_eq_eulerProduct
    (P : PrimeRegister) (q : ℕ → ℝ) :
    finiteSignedPfaffianCharacter P q = finiteEulerProduct P q := by
  calc
    finiteSignedPfaffianCharacter P q = majoranaPfaffianProduct P q := by
      rfl
    _ = dirichletWittenCharacter P q := by
      exact majoranaPfaffianProduct_eq_dirichletWittenCharacter P q
    _ = finiteEulerProduct P q := by
      exact dirichletWittenCharacter_eq_eulerProduct P q

/-- The finite signed Pfaffian readout equals the finite Dirichlet Witten character. -/
theorem finiteSignedPfaffianCharacter_eq_dirichletWittenCharacter
    (P : PrimeRegister) (q : ℕ → ℝ) :
    finiteSignedPfaffianCharacter P q =
      finiteDirichletWittenCharacter P q := by
  calc
    finiteSignedPfaffianCharacter P q = majoranaPfaffianProduct P q := by
      rfl
    _ = dirichletWittenCharacter P q := by
      exact majoranaPfaffianProduct_eq_dirichletWittenCharacter P q
    _ = finiteDirichletWittenCharacter P q := by
      rfl

/--
Finite prime-bit Witten-index cancellation on a nonempty prime register.

This is the arithmetic owner readback of the balanced finite supertrace
`∑ (-1)^F = 0`; it is not an infinite-temperature or analytic-continuation
claim.
-/
theorem finitePrimeBitWittenIndex_cancel
    (P : PrimeRegister) (hP : P.primes.Nonempty) :
    (∑ S ∈ P.primes.powerset, (-1 : ℤ) ^ S.card) = 0 :=
  finite_witten_supertrace_cancel P hP

/-- Canonical finite owner target for the split-Majorana / Dirichlet lane. -/
@[owner_target_tag]
def PrimeMajoranaWittenCharacterOwnerTarget : Prop :=
  ∀ (P : PrimeRegister) (q : ℕ → ℝ),
    finiteDirichletWittenCharacter P q = finiteEulerProduct P q ∧
    finiteSplitMajoranaChiralityCharacter P q = finiteEulerProduct P q ∧
    finiteSignedPfaffianCharacter P q = finiteEulerProduct P q

/-- The canonical finite owner target is proved. -/
theorem primeMajoranaWittenCharacterOwnerTarget :
    PrimeMajoranaWittenCharacterOwnerTarget := by
  intro P q
  exact ⟨finiteDirichletWittenCharacter_eq_eulerProduct P q,
    finiteSplitMajoranaChiralityCharacter_eq_eulerProduct P q,
    finiteSignedPfaffianCharacter_eq_eulerProduct P q⟩

end InfoGeometry.Canonical.PrimeMajoranaWittenCharacter
