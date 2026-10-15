/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
# Formalization of Grassmann-Clifford Differential Algebras (chakravala Archetypes)

This module formalizes the core mathematical architecture of Michael Reed's
`chakravala` differential geometric algebra suite (`Grassmann.jl`, `DirectSum.jl`, `Cartan.jl`):
1. `Parity`: The ℤ₂-grading module for bosonic and fermionic spaces.
2. `koszulSign`: The sign functor with symmetry and additive homomorphism laws.
3. `superBracket`: The graded Lie superalgebra bracket with skew-supersymmetry.
4. `clifford_anticommutator`: The fundamental polarization theorem for Clifford spaces.
5. `grassmann_anticomm` & `grassmann_nilpotent`: Nilpotent exterior/Grassmann algebra.
6. `mathlib_exteriorAlgebra_*`: Direct connection to Mathlib's native `ExteriorAlgebra`.
7. `geometric_bivector_sq_neg_one`: Formal proof that the 2D geometric bivector squares to -1.
8. The displayed theorems are independent kernel-checked consequences of the
   corresponding algebraic hypotheses; no aggregate evidence certificate is
   introduced.
-/

namespace ChakravalaGA

/-! ### Archetypes I & II: Parity Grading & The Koszul Sign Functor -/

/-- Parity grading for supergeometry: Even (Bosonic) and Odd (Fermionic). -/
inductive Parity : Type
  | even : Parity
  | odd  : Parity
  deriving DecidableEq, Repr

/-- Additive group law on Parity: ℤ₂ addition. -/
def Parity.add : Parity → Parity → Parity
  | .even, p => p
  | .odd, .even => .odd
  | .odd, .odd => .even

instance : Add Parity where
  add := Parity.add

variable {R : Type*} [CommRing R]

/-- The Koszul sign factor $(-1)^{p \cdot q}$ in the base ring `R`. -/
def koszulSign (p q : Parity) : R :=
  match p, q with
  | .odd, .odd => -1
  | _, _ => 1

@[simp]
theorem koszulSign_even_left (q : Parity) : koszulSign (R := R) .even q = 1 := by
  cases q <;> rfl

@[simp]
theorem koszulSign_even_right (p : Parity) : koszulSign (R := R) p .even = 1 := by
  cases p <;> rfl

@[simp]
theorem koszulSign_odd_odd : koszulSign (R := R) .odd .odd = -1 := rfl

/-- Koszul sign is symmetric: $(-1)^{p q} = (-1)^{q p}$. -/
theorem koszulSign_symm (p q : Parity) :
    koszulSign (R := R) p q = koszulSign (R := R) q p := by
  cases p <;> cases q <;> rfl

/-- Koszul sign respects the additive grading: $(-1)^{(p₁ + p₂) q} = (-1)^{p₁ q} (-1)^{p₂ q}$. -/
theorem koszulSign_add_left (p₁ p₂ q : Parity) :
    koszulSign (R := R) (p₁ + p₂) q = koszulSign (R := R) p₁ q * koszulSign (R := R) p₂ q := by
  cases p₁ <;> cases p₂ <;> cases q <;> {
    dsimp [HAdd.hAdd, Add.add, Parity.add, koszulSign]
    ring
  }

/-! ### Archetypes III & IV: Graded Superbracket -/

variable {A : Type*} [Ring A] [Algebra R A]

/-- The graded supercommutator: $[x, y] = x y - (-1)^{|x||y|} y x$. -/
def superBracket (p q : Parity) (x y : A) : A :=
  x * y - koszulSign (R := R) p q • (y * x)

/-- Fermionic generators anticommute under the superbracket: $[x, y] = x y + y x$. -/
theorem superBracket_fermionic (x y : A) :
    superBracket (R := R) .odd .odd x y = x * y + y * x := by
  dsimp [superBracket, koszulSign]
  rw [neg_one_smul, sub_neg_eq_add]

/-- Bosonic generators commute under the superbracket: $[x, y] = x y - y x$. -/
theorem superBracket_bosonic (x y : A) :
    superBracket (R := R) .even .even x y = x * y - y * x := by
  dsimp [superBracket, koszulSign]
  rw [one_smul]

/-- Skew-supersymmetry of the superbracket: $[x, y] = - (-1)^{|x||y|} [y, x]$. -/
theorem superBracket_skew (p q : Parity) (x y : A) :
    superBracket (R := R) p q x y = - (koszulSign (R := R) p q • superBracket (R := R) q p y x) := by
  cases p <;> cases q
  · dsimp [superBracket, koszulSign]
    simp only [one_smul, neg_sub]
  · dsimp [superBracket, koszulSign]
    simp only [one_smul, neg_sub]
  · dsimp [superBracket, koszulSign]
    simp only [one_smul, neg_sub]
  · dsimp [superBracket, koszulSign]
    simp only [neg_one_smul, sub_neg_eq_add, neg_neg, add_comm]

/-! ### Archetype V: Polarization & Clifford Anticommutation -/

variable {M : Type*} [AddCommGroup M] [Module R M]

/-- The polar bilinear form $B(v, w) = Q(v + w) - Q(v) - Q(w)$. -/
def polar (Q : M → R) (v w : M) : R :=
  Q (v + w) - Q v - Q w

/-- 
Fundamental Clifford Polarization Identity:
If $\iota(v)^2 = Q(v)$, then $\iota(v)\iota(w) + \iota(w)\iota(v) = Q(v + w) - Q(v) - Q(w)$.
-/
theorem clifford_anticommutator
    (ι : M → A) (Q : M → R) (algebraMapRing : R →+* A)
    (h_add : ∀ x y : M, ι (x + y) = ι x + ι y)
    (h_sq : ∀ v : M, ι v * ι v = algebraMapRing (Q v)) (v w : M) :
    ι v * ι w + ι w * ι v =
      algebraMapRing (Q (v + w)) - algebraMapRing (Q v) - algebraMapRing (Q w) := by
  have h_exp : (ι v + ι w) * (ι v + ι w) =
      ι v * ι w + ι w * ι v + algebraMapRing (Q v) + algebraMapRing (Q w) := by
    rw [add_mul, mul_add, mul_add, h_sq v, h_sq w]
    abel
  have h_tot : (ι v + ι w) * (ι v + ι w) = algebraMapRing (Q (v + w)) := by
    rw [← h_add, h_sq (v + w)]
  rw [h_exp] at h_tot
  rw [← h_tot]
  abel

/-- Orthogonal vectors in a Clifford algebra anticommute. -/
theorem clifford_orthogonal_swap
    (ι : M → A) (Q : M → R) (algebraMapRing : R →+* A)
    (h_add : ∀ x y : M, ι (x + y) = ι x + ι y)
    (h_sq : ∀ v : M, ι v * ι v = algebraMapRing (Q v))
    (v w : M) (h_ortho : polar Q v w = 0) :
    ι v * ι w = - (ι w * ι v) := by
  have h := clifford_anticommutator ι Q algebraMapRing h_add h_sq v w
  have h_pol : algebraMapRing (Q (v + w)) - algebraMapRing (Q v) - algebraMapRing (Q w) = 0 := by
    have hp : algebraMapRing (polar Q v w) = 0 := by rw [h_ortho, map_zero]
    dsimp [polar] at hp
    rw [map_sub, map_sub] at hp
    exact hp
  rw [h_pol] at h
  rw [← add_eq_zero_iff_eq_neg]
  exact h

/-! ### Archetype VI: Grassmann Limit (Q = 0) & Exterior Algebra -/

/-- In the pure Grassmann limit ($Q = 0$), generators anticommute unconditionally. -/
theorem grassmann_anticomm
    (ι : M → A) (h_add : ∀ x y : M, ι (x + y) = ι x + ι y)
    (h_sq : ∀ v : M, ι v * ι v = 0) (v w : M) :
    ι v * ι w + ι w * ι v = 0 := by
  have h_exp : (ι v + ι w) * (ι v + ι w) = ι v * ι w + ι w * ι v := by
    rw [add_mul, mul_add, mul_add, h_sq v, h_sq w, zero_add, add_zero]
  have h_tot : (ι v + ι w) * (ι v + ι w) = 0 := by
    rw [← h_add, h_sq (v + w)]
  rw [h_exp] at h_tot
  exact h_tot

/-- Fermionic nilpotency of Grassmann generators: $\theta^2 = 0$. -/
theorem grassmann_nilpotent
    (ι : M → A) (h_sq : ∀ v : M, ι v * ι v = 0) (v : M) :
    (ι v) ^ 2 = 0 := by
  rw [pow_two]
  exact h_sq v

/-- Mathlib's native `ExteriorAlgebra.ι` anticommutes. -/
theorem mathlib_exteriorAlgebra_anticomm (v w : M) :
    ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R w +
    ExteriorAlgebra.ι R w * ExteriorAlgebra.ι R v = 0 := by
  apply grassmann_anticomm (ExteriorAlgebra.ι R)
  · intro x y; exact map_add (ExteriorAlgebra.ι R) x y
  · intro x; exact ExteriorAlgebra.ι_sq_zero x

/-- Mathlib's native `ExteriorAlgebra.ι` generators swap with a minus sign. -/
theorem mathlib_exteriorAlgebra_swap (v w : M) :
    ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R w =
    - (ExteriorAlgebra.ι R w * ExteriorAlgebra.ι R v) := by
  rw [← add_eq_zero_iff_eq_neg]
  exact mathlib_exteriorAlgebra_anticomm v w

/-- Mathlib's native `ExteriorAlgebra.ι` generators are strictly nilpotent. -/
theorem mathlib_exteriorAlgebra_nilpotent (v : M) :
    (ExteriorAlgebra.ι R v) ^ 2 = 0 := by
  rw [pow_two]
  exact ExteriorAlgebra.ι_sq_zero v

/-- 
Canonical Supergeometry Theorem:
The fermionic superbracket of exterior generators vanishes identically.
-/
theorem mathlib_exteriorAlgebra_superBracket_zero (v w : M) :
    superBracket (R := R) .odd .odd (ExteriorAlgebra.ι R v) (ExteriorAlgebra.ι R w) = 0 := by
  rw [superBracket_fermionic]
  exact mathlib_exteriorAlgebra_anticomm v w

/-! ### Archetype VII: Geometric Bivector Complex Structure (I² = -1) -/

/--
The 2D Euclidean bivector $I = e₁ e₂$ generates an imaginary unit ($I^2 = -1$).
-/
theorem geometric_bivector_sq_neg_one
    (e₁ e₂ : A)
    (h₁ : e₁ * e₁ = 1)
    (h₂ : e₂ * e₂ = 1)
    (h_anticomm : e₁ * e₂ = - (e₂ * e₁)) :
    (e₁ * e₂) * (e₁ * e₂) = - 1 := by
  have h_swap : e₂ * e₁ = - (e₁ * e₂) := by
    rw [h_anticomm, neg_neg]
  have step1 : (e₁ * e₂) * (e₁ * e₂) = e₁ * (e₂ * e₁) * e₂ := by
    simp only [mul_assoc]
  rw [step1, h_swap]
  have step2 : e₁ * - (e₁ * e₂) * e₂ = - ((e₁ * e₁) * (e₂ * e₂)) := by
    simp only [mul_neg, neg_mul, mul_assoc]
  rw [step2, h₁, h₂, mul_one]

end ChakravalaGA
