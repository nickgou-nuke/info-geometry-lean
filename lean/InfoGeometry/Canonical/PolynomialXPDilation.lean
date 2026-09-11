import Mathlib.Algebra.Polynomial.Derivative
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic
import InfoGeometry.Canonical.FirstQuantizedChiralConeBridge

/-!
# Algebraic first quantization of the dilation observable

This file is deliberately algebraic.  On the polynomial module over `ℂ`,
`position` is multiplication by `X` and `momentum` is the formal derivative.
The canonical commutator and the symmetrized `xp` generator are proved
without introducing a Hilbert-space completion, an unbounded-operator
domain, or a finite-dimensional surrogate for the dilation operator.
-/

noncomputable section

namespace InfoGeometry.Canonical.PolynomialXPDilation

open InfoGeometry.Canonical.FirstQuantizedChiralConeBridge

abbrev State := Polynomial ℂ

/-- Multiplication by the coordinate polynomial `X`. -/
def position (p : State) : State := Polynomial.X * p

/-- The formal momentum operator, namely polynomial differentiation. -/
def momentum (p : State) : State := Polynomial.derivative p

/-- The position operator as a native `LinearMap`. -/
def positionLinear : State →ₗ[ℂ] State where
  toFun := position
  map_add' p q := by
    simpa [position] using (mul_add Polynomial.X p q)
  map_smul' c p := by
    simp [position, mul_comm]

/-- The momentum operator as the native polynomial derivative linear map. -/
def momentumLinear : State →ₗ[ℂ] State := Polynomial.derivative

/-- The algebraic commutator `[p̂, x̂]` applied to a polynomial state. -/
def positionMomentumCommutator (p : State) : State :=
  momentum (position p) - position (momentum p)

theorem momentum_position_commutator (p : State) :
    positionMomentumCommutator p = p := by
  simp [positionMomentumCommutator, momentum, position,
    Polynomial.derivative_mul, Polynomial.derivative_X]

/-- The symmetric quantization of the classical observable `x * p`. -/
def symmetricXPDilation (p : State) : State :=
  (1 / 2 : ℂ) •
    (position (momentum p) + momentum (position p))

/-- The symmetrized `xp` observable as a native linear operator. -/
def symmetricXPDilationLinear : State →ₗ[ℂ] State :=
  (1 / 2 : ℂ) •
    (positionLinear.comp momentumLinear + momentumLinear.comp positionLinear)

@[simp] theorem positionLinear_apply (p : State) :
    positionLinear p = position p := rfl

@[simp] theorem momentumLinear_apply (p : State) :
    momentumLinear p = momentum p := rfl

@[simp] theorem symmetricXPDilationLinear_apply (p : State) :
    symmetricXPDilationLinear p = symmetricXPDilation p := by
  simp [symmetricXPDilationLinear, symmetricXPDilation, positionLinear,
    momentumLinear, position, momentum]

theorem symmetricXPDilation_eq_position_momentum_add_half (p : State) :
    symmetricXPDilation p =
      position (momentum p) + (1 / 2 : ℂ) • p := by
  simp [symmetricXPDilation, position, momentum,
    Polynomial.derivative_mul, Polynomial.derivative_X]
  module

theorem symmetricXPDilation_commutator_position (p : State) :
    symmetricXPDilation (position p) -
        position (symmetricXPDilation p) = position p := by
  rw [symmetricXPDilation_eq_position_momentum_add_half,
    symmetricXPDilation_eq_position_momentum_add_half]
  simp [position, momentum, Polynomial.derivative_mul,
    Polynomial.derivative_X, Polynomial.smul_eq_C_mul]
  ring

theorem symmetricXPDilation_commutator_momentum (p : State) :
    symmetricXPDilation (momentum p) -
        momentum (symmetricXPDilation p) = -momentum p := by
  rw [symmetricXPDilation_eq_position_momentum_add_half,
    symmetricXPDilation_eq_position_momentum_add_half]
  simp [position, momentum, Polynomial.derivative_mul,
    Polynomial.derivative_X]

/-!
## Native operator commutators

The preceding pointwise identities are now packaged as equalities of native
Mathlib linear maps.  This is the algebraic first-quantization layer; no
topological or unbounded-operator structure is asserted here.
-/

theorem momentumLinear_comp_positionLinear_sub_positionLinear_comp_momentumLinear :
    momentumLinear.comp positionLinear - positionLinear.comp momentumLinear =
      LinearMap.id := by
  apply LinearMap.ext
  intro p
  simpa [LinearMap.sub_apply] using momentum_position_commutator p

theorem symmetricXPDilationLinear_comp_positionLinear_sub_positionLinear_comp_symmetricXPDilationLinear :
    symmetricXPDilationLinear.comp positionLinear -
        positionLinear.comp symmetricXPDilationLinear = positionLinear := by
  apply LinearMap.ext
  intro p
  simpa [LinearMap.sub_apply] using symmetricXPDilation_commutator_position p

theorem symmetricXPDilationLinear_comp_momentumLinear_sub_momentumLinear_comp_symmetricXPDilationLinear :
    symmetricXPDilationLinear.comp momentumLinear -
        momentumLinear.comp symmetricXPDilationLinear = -momentumLinear := by
  apply LinearMap.ext
  intro p
  simpa [LinearMap.sub_apply] using symmetricXPDilation_commutator_momentum p

theorem symmetricXPDilationLinear_eq_positionLinear_comp_momentumLinear_add_half_id :
    symmetricXPDilationLinear =
      positionLinear.comp momentumLinear +
        (1 / 2 : ℂ) • LinearMap.id := by
  apply LinearMap.ext
  intro p
  change symmetricXPDilation p =
    position (momentum p) + (1 / 2 : ℂ) • p
  exact symmetricXPDilation_eq_position_momentum_add_half p

theorem symmetricXPDilation_monomial (n : ℕ) :
    symmetricXPDilation (Polynomial.X ^ n) =
      ((n : ℂ) + (1 / 2 : ℂ)) • Polynomial.X ^ n := by
  have hderiv : ∀ m : ℕ,
      (Polynomial.X : Polynomial ℂ) *
          Polynomial.derivative ((Polynomial.X : Polynomial ℂ) ^ m) =
        (m : ℂ) • (Polynomial.X : Polynomial ℂ) ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [pow_succ, Polynomial.derivative_mul, Polynomial.derivative_X]
        simp only [mul_one, mul_add]
        rw [← mul_assoc, ih]
        simp [Nat.cast_succ, add_smul]
        rw [mul_comm]
  rw [symmetricXPDilation_eq_position_momentum_add_half]
  simp only [position, momentum, hderiv]
  rw [add_smul]

/-!
## Reuse of the generic Weyl/Jordan canonical-pair owner
-/

def polynomialCanonicalPair :
    WeylOrderedXP.CanonicalPair (A := ℂ) (M := State) where
  X := positionLinear
  P := momentumLinear
  center := -1
  commutation := by
    apply LinearMap.ext
    intro p
    simp only [LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, neg_one_smul]
    change position (momentum p) - momentum (position p) = -p
    calc
      position (momentum p) - momentum (position p) =
          -(momentum (position p) - position (momentum p)) := by abel
      _ = -p := by
        change -positionMomentumCommutator p = -p
        rw [momentum_position_commutator]

theorem polynomialCanonicalPair_symmetricPart :
    polynomialCanonicalPair.symmetricPart = symmetricXPDilationLinear := by
  apply LinearMap.ext
  intro p
  simp [polynomialCanonicalPair, WeylOrderedXP.CanonicalPair.symmetricPart,
    symmetricXPDilationLinear]

theorem polynomialCanonicalPair_center :
    polynomialCanonicalPair.center = (-1 : ℂ) := rfl

end InfoGeometry.Canonical.PolynomialXPDilation
