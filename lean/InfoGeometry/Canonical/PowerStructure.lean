import Mathlib.Algebra.Group.Defs
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic

/-!
# Power-Structure Laws and Pre-Lambda Readouts

This file formalizes the finite algebraic core of abstract power structures
without introducing proof-carrying structures.  A power structure is represented
by a function `G → R → G` together with the predicate `IsPowerStructure`.
Pre-lambda readouts are represented as ordinary functions satisfying
`IsAddMulHom`.

## Audit Protocol Map
- BUCKET 1: CLOSED FINITE THEOREMS:
  `powerStructure_pow_zero`, `powerStructure_pow_one`,
  `powerStructure_mul_pow`, `powerStructure_pow_add`,
  `powerStructure_pow_mul`, `lambdaFromPowerStructure_isAddMulHom`,
  `pow_one_base`, `powMonoidHom`, `power_structure_hom_compat`.
- BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES:
  The lambda and exponentiation readouts are conditional on the explicit
  predicate `IsPowerStructure pow`; homomorphism compatibility is conditional
  on the explicit compatibility equation.
- BUCKET 3: OPEN CLOSURE DEBT:
  The Grothendieck ring of complex quasi-projective varieties, the Kapranov
  zeta function, and the geometric power structure by symmetric powers of
  varieties are not asserted here.
-/

universe u v

namespace InfoGeometry.Canonical

/-- A raw abstract power action. -/
def PowerAction (G : Type u) (R : Type v) : Type (max u v) :=
  G → R → G

/-- Predicate expressing the algebraic laws of a power structure. -/
def IsPowerStructure {G : Type u} {R : Type v} [CommGroup G] [CommRing R]
    (pow : PowerAction G R) : Prop :=
  (∀ A : G, pow A 0 = 1) ∧
    (∀ A : G, pow A 1 = A) ∧
    (∀ (A B : G) (m : R), pow (A * B) m = pow A m * pow B m) ∧
    (∀ (A : G) (m n : R), pow A (m + n) = pow A m * pow A n) ∧
    (∀ (A : G) (m n : R), pow (pow A n) m = pow A (m * n))

theorem powerStructure_pow_zero {G : Type u} {R : Type v} [CommGroup G] [CommRing R]
    {pow : PowerAction G R} (hpow : IsPowerStructure pow) :
    ∀ A : G, pow A 0 = 1 := by
  exact hpow.1

theorem powerStructure_pow_one {G : Type u} {R : Type v} [CommGroup G] [CommRing R]
    {pow : PowerAction G R} (hpow : IsPowerStructure pow) :
    ∀ A : G, pow A 1 = A := by
  exact hpow.2.1

theorem powerStructure_mul_pow {G : Type u} {R : Type v} [CommGroup G] [CommRing R]
    {pow : PowerAction G R} (hpow : IsPowerStructure pow) :
    ∀ (A B : G) (m : R), pow (A * B) m = pow A m * pow B m := by
  exact hpow.2.2.1

theorem powerStructure_pow_add {G : Type u} {R : Type v} [CommGroup G] [CommRing R]
    {pow : PowerAction G R} (hpow : IsPowerStructure pow) :
    ∀ (A : G) (m n : R), pow A (m + n) = pow A m * pow A n := by
  exact hpow.2.2.2.1

theorem powerStructure_pow_mul {G : Type u} {R : Type v} [CommGroup G] [CommRing R]
    {pow : PowerAction G R} (hpow : IsPowerStructure pow) :
    ∀ (A : G) (m n : R), pow (pow A n) m = pow A (m * n) := by
  exact hpow.2.2.2.2

/-- Predicate for additive-to-multiplicative homomorphisms. -/
def IsAddMulHom {R : Type u} {G : Type v} [AddMonoid R] [CommMonoid G]
    (f : R → G) : Prop :=
  f 0 = 1 ∧ ∀ x y, f (x + y) = f x * f y

/-- The pre-lambda readout associated to a fixed base element. -/
def lambdaFromPowerStructure {G : Type u} {R : Type v} (pow : PowerAction G R) (A₀ : G) :
    R → G :=
  fun m => pow A₀ m

/-- A power structure defines an additive-to-multiplicative pre-lambda readout. -/
theorem lambdaFromPowerStructure_isAddMulHom {G : Type u} {R : Type v}
    [CommGroup G] [CommRing R] {pow : PowerAction G R}
    (hpow : IsPowerStructure pow) (A₀ : G) :
    IsAddMulHom (lambdaFromPowerStructure pow A₀) := by
  refine ⟨?_, ?_⟩
  · exact powerStructure_pow_zero hpow A₀
  · intro m n
    exact powerStructure_pow_add hpow A₀ m n

/-- Any power structure sends the multiplicative identity of `G` to itself. -/
theorem pow_one_base {G : Type u} {R : Type v} [CommGroup G] [CommRing R]
    {pow : PowerAction G R} (hpow : IsPowerStructure pow) (m : R) :
    pow 1 m = (1 : G) := by
  have h_idem : pow 1 m = pow 1 m * pow 1 m := by
    calc
      pow 1 m = pow (1 * 1) m := by rw [mul_one]
      _ = pow 1 m * pow 1 m := powerStructure_mul_pow hpow 1 1 m
  calc
    pow 1 m = pow 1 m * 1 := by rw [mul_one]
    _ = pow 1 m * (pow 1 m * (pow 1 m)⁻¹) := by rw [mul_inv_cancel]
    _ = (pow 1 m * pow 1 m) * (pow 1 m)⁻¹ := by rw [mul_assoc]
    _ = pow 1 m * (pow 1 m)⁻¹ := by rw [← h_idem]
    _ = 1 := by rw [mul_inv_cancel]

/-- Exponentiation by a fixed element of `R` is a multiplicative group homomorphism. -/
def powMonoidHom {G : Type u} {R : Type v} [CommGroup G] [CommRing R]
    {pow : PowerAction G R} (hpow : IsPowerStructure pow) (m : R) : G →* G where
  toFun A := pow A m
  map_one' := pow_one_base hpow m
  map_mul' A B := powerStructure_mul_pow hpow A B m

/-- Homomorphism compatibility of two explicitly compatible power structures. -/
theorem power_structure_hom_compat
    {G₁ G₂ : Type u} [CommGroup G₁] [CommGroup G₂]
    {R₁ R₂ : Type v} [CommRing R₁] [CommRing R₂]
    {pow₁ : PowerAction G₁ R₁} {pow₂ : PowerAction G₂ R₂}
    (psi : G₁ →* G₂) (phi : R₁ →+* R₂)
    (h_compat : ∀ (A : G₁) (m : R₁), psi (pow₁ A m) = pow₂ (psi A) (phi m))
    (A₀ : G₁) (m : R₁) :
    psi (pow₁ A₀ m) = pow₂ (psi A₀) (phi m) := by
  exact h_compat A₀ m

end InfoGeometry.Canonical
