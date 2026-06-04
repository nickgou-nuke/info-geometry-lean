import Mathlib

set_option autoImplicit false

/-!
# InfoGeometry.Krein.FiniteDecompositionAudit

This file packages a small finite algebraic decomposition around an involutive
real linear map `J` and a symmetric bilinear pairing `B : V → V → ℝ`.

The closed results here are algebraic readback identities only:
- `xPlus` is fixed by `J`;
- `xMinus` is negated by `J`;
- the Krein-style readback `bKrein B J x y = B x (J y)` agrees with `B` on the
  `xPlus` component;
- the same readback is the negated `B` pairing on the `xMinus` component.

This file does not define a full `KreinSpace` instance and does not prove
positivity, negative-definiteness, nondegeneracy, or analytic Krein-space
results.

#### BUCKET 1: CLOSED FINITE THEOREMS
- `J_J`
- `xPlus`
- `xMinus`
- `J_xPlus`
- `J_xMinus`
- `bKrein`
- `B_neg_right`
- `bKrein_xPlus_self`
- `bKrein_xMinus_self`

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
Theorems are conditional on explicit witnesses such as:
- `hJ2 : J.comp J = LinearMap.id`
- `hBcomm : ∀ x y, B x y = B y x`
- `hBsmulLeft : ∀ r x y, B (r • x) y = r * B x y`

#### BUCKET 3: OPEN CLOSURE DEBT
- No compile debt remains in this finite owner file.
- No positivity, negative-definiteness, or nondegeneracy theorem is proved.
-/

namespace InfoGeometry.Krein.FiniteDecompositionAudit

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

lemma J_J (J : V →ₗ[ℝ] V) (hJ2 : J.comp J = LinearMap.id) (x : V) : J (J x) = x := by
  have h := LinearMap.congr_fun hJ2 x
  simpa using h

/-- The `+1`-eigenspace-style component attached to an involution `J`. -/
def xPlus (half : ℝ) (J : V →ₗ[ℝ] V) (x : V) : V :=
  half • (x + J x)

/-- The `-1`-eigenspace-style component attached to an involution `J`. -/
def xMinus (half : ℝ) (J : V →ₗ[ℝ] V) (x : V) : V :=
  half • (x - J x)

lemma J_xPlus (half : ℝ) (J : V →ₗ[ℝ] V) (hJ2 : J.comp J = LinearMap.id) (x : V) :
    J (xPlus half J x) = xPlus half J x := by
  unfold xPlus
  rw [map_smul, map_add, J_J J hJ2 x, add_comm]

lemma J_xMinus (half : ℝ) (J : V →ₗ[ℝ] V) (hJ2 : J.comp J = LinearMap.id) (x : V) :
    J (xMinus half J x) = -(xMinus half J x) := by
  unfold xMinus
  rw [map_smul, map_sub, J_J J hJ2 x]
  have h : J x - x = -(x - J x) := by
    abel
  rw [h, smul_neg]

/-- Finite Krein-style readback pairing induced by `J`. -/
def bKrein (B : V → V → ℝ) (J : V →ₗ[ℝ] V) (x y : V) : ℝ :=
  B x (J y)

theorem bKrein_xPlus_self
    (B : V → V → ℝ) (half : ℝ) (J : V →ₗ[ℝ] V)
    (hJ2 : J.comp J = LinearMap.id) (x : V) :
    bKrein B J (xPlus half J x) (xPlus half J x) = B (xPlus half J x) (xPlus half J x) := by
  unfold bKrein
  rw [J_xPlus half J hJ2 x]

lemma B_neg_right
    (B : V → V → ℝ)
    (hBcomm : ∀ x y, B x y = B y x)
    (hBsmulLeft : ∀ r x y, B (r • x) y = r * B x y)
    (u v : V) : B u (-v) = -B u v := by
  rw [hBcomm u (-v)]
  have h1 : -v = (-1 : ℝ) • v := by
    exact (neg_one_smul ℝ v).symm
  rw [h1]
  rw [hBsmulLeft (-1) v u]
  rw [hBcomm v u]
  ring

theorem bKrein_xMinus_self
    (B : V → V → ℝ) (hBcomm : ∀ x y, B x y = B y x)
    (hBsmulLeft : ∀ r x y, B (r • x) y = r * B x y)
    (half : ℝ) (J : V →ₗ[ℝ] V)
    (hJ2 : J.comp J = LinearMap.id) (x : V) :
    bKrein B J (xMinus half J x) (xMinus half J x) = -B (xMinus half J x) (xMinus half J x) := by
  unfold bKrein
  rw [J_xMinus half J hJ2 x]
  exact B_neg_right B hBcomm hBsmulLeft (xMinus half J x) (xMinus half J x)

end InfoGeometry.Krein.FiniteDecompositionAudit
