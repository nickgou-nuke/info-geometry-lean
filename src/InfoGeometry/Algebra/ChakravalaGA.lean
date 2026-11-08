/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Formalization of Grassmann-Clifford Differential Algebras (chakravala Archetypes)

This module formalizes the core mathematical architecture of Michael Reed's
`chakravala` differential geometric algebra suite (`Grassmann.jl`, `DirectSum.jl`, `Cartan.jl`):
1. `Parity`: The ℤ₂-grading module for bosonic and fermionic spaces.
2. `koszulSign`: The sign functor with symmetry, involution, and additive homomorphism laws.
3. `superBracket`: The graded Lie superalgebra bracket with bosonic, fermionic, mixed, and skew-supersymmetry laws.
4. `clifford_anticommutator`, `clifford_representation_anticommutator`, & `mathlib_cliffordAlgebra_*`:
   Fundamental polarization and native Mathlib `CliffordAlgebra` instantiation.
5. `grassmann_anticomm`, `grassmann_nilpotent`, `mathlib_exteriorAlgebra_*`, & `mathlib_cliffordAlgebra_zero_*`:
   Nilpotent exterior/Grassmann algebra and degenerate `Q = 0` Clifford limit.
6. `geometric_bivector_sq_neg_one`, `hyperbolic_bivector_sq_pos_one`, `degenerate_bivector_sq_zero`, &
   `mathlib_cliffordAlgebra_bivector_sq_neg_one`: Bivector squares across Euclidean `(2,0,0)`,
   Lorentzian `(1,1,0)`, and PGA/Cartan `(1,0,1)` signatures.
-/

namespace ChakravalaGA

/-! ### Archetypes I & II: Parity Grading & The Koszul Sign Functor -/

/-- Parity grading for supergeometry: Even (Bosonic) and Odd (Fermionic). -/
inductive Parity : Type
  | even : Parity
  | odd  : Parity
  deriving DecidableEq, Repr, Inhabited

/-- Additive group law on Parity: ℤ₂ addition. -/
def Parity.add : Parity → Parity → Parity
  | .even, p => p
  | .odd, .even => .odd
  | .odd, .odd => .even

instance : Add Parity where
  add := Parity.add

/-- The even and odd parity grades are distinct. -/
theorem even_ne_odd : Parity.even ≠ Parity.odd := by
  decide

section KoszulSign

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

/-- Koszul sign respects the additive grading on the left: $(-1)^{(p₁ + p₂) q} = (-1)^{p₁ q} (-1)^{p₂ q}$. -/
theorem koszulSign_add_left (p₁ p₂ q : Parity) :
    koszulSign (R := R) (p₁ + p₂) q = koszulSign (R := R) p₁ q * koszulSign (R := R) p₂ q := by
  cases p₁ <;> cases p₂ <;> cases q <;> {
    dsimp [HAdd.hAdd, Add.add, Parity.add, koszulSign]
    ring
  }

/-- Koszul sign respects the additive grading on the right: $(-1)^{p (q₁ + q₂)} = (-1)^{p q₁} (-1)^{p q₂}$. -/
theorem koszulSign_add_right (p q₁ q₂ : Parity) :
    koszulSign (R := R) p (q₁ + q₂) = koszulSign (R := R) p q₁ * koszulSign (R := R) p q₂ := by
  cases p <;> cases q₁ <;> cases q₂ <;> {
    dsimp [HAdd.hAdd, Add.add, Parity.add, koszulSign]
    ring
  }

/-- Koszul sign is an involution in `R`: $((-1)^{p q})^2 = 1$. -/
theorem koszulSign_sq_one (p q : Parity) :
    koszulSign (R := R) p q * koszulSign (R := R) p q = 1 := by
  cases p <;> cases q <;> {
    dsimp [koszulSign]
    ring
  }

end KoszulSign

/-! ### Archetypes III & IV: Graded Superbracket -/

section SuperBracket

variable {R : Type*} [CommRing R] {A : Type*} [Ring A] [Algebra R A]

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

/-- Mixed even-odd generators use the commutator under the superbracket: $[x, y] = x y - y x$. -/
theorem superBracket_even_odd (x y : A) :
    superBracket (R := R) .even .odd x y = x * y - y * x := by
  dsimp [superBracket, koszulSign]
  rw [one_smul]

/-- Mixed odd-even generators use the commutator under the superbracket: $[x, y] = x y - y x$. -/
theorem superBracket_odd_even (x y : A) :
    superBracket (R := R) .odd .even x y = x * y - y * x := by
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

end SuperBracket

/-! ### Archetype V: Polarization & Clifford Anticommutation -/

/-- The polar bilinear form $B(v, w) = Q(v + w) - Q(v) - Q(w)$. -/
def polar {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M]
    (Q : M → R) (v w : M) : R :=
  Q (v + w) - Q v - Q w

/--
Fundamental Clifford Polarization Identity:
If $\iota(v)^2 = Q(v)$, then $\iota(v)\iota(w) + \iota(w)\iota(v) = Q(v + w) - Q(v) - Q(w)$.
-/
theorem clifford_anticommutator
    {R : Type*} [CommRing R] {A : Type*} [Ring A] {M : Type*} [AddCommGroup M]
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

/--
The Clifford polarization identity transported through an algebra
representation. This specializes Mathlib's universal Clifford generator
relation to the represented operators, so downstream arguments need not
restate additivity and the square law for the generator map.
-/
theorem clifford_representation_anticommutator
    {R : Type*} [CommRing R] {A : Type*} [Ring A] [Algebra R A]
    {M : Type*} [AddCommGroup M] [Module R M]
    (Q : QuadraticForm R M) (ρ : CliffordAlgebra Q →ₐ[R] A) (v w : M) :
    ρ (CliffordAlgebra.ι Q v) * ρ (CliffordAlgebra.ι Q w) +
      ρ (CliffordAlgebra.ι Q w) * ρ (CliffordAlgebra.ι Q v) =
        algebraMap R A (QuadraticMap.polar Q v w) := by
  calc
    _ = ρ (CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q w +
        CliffordAlgebra.ι Q w * CliffordAlgebra.ι Q v) := by
      simp only [map_add, map_mul]
    _ = ρ (algebraMap R (CliffordAlgebra Q) (QuadraticMap.polar Q v w)) := by
      rw [CliffordAlgebra.ι_mul_ι_add_swap]
    _ = algebraMap R A (QuadraticMap.polar Q v w) := by simp

/-- Orthogonal vectors in a Clifford algebra anticommute. -/
theorem clifford_orthogonal_swap
    {R : Type*} [CommRing R] {A : Type*} [Ring A] {M : Type*} [AddCommGroup M]
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

section MathlibClifford

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- Native Mathlib `CliffordAlgebra Q` anticommutator equals the polarized quadratic form. -/
theorem mathlib_cliffordAlgebra_anticommutator (Q : QuadraticForm R M) (v w : M) :
    CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q w +
      CliffordAlgebra.ι Q w * CliffordAlgebra.ι Q v =
      algebraMap R (CliffordAlgebra Q) (polar Q v w) := by
  have h := clifford_anticommutator (CliffordAlgebra.ι Q) Q (algebraMap R (CliffordAlgebra Q))
    (fun x y => map_add (CliffordAlgebra.ι Q) x y) (CliffordAlgebra.ι_sq_scalar Q) v w
  rw [h]
  dsimp [polar]
  rw [map_sub, map_sub]

/-- Native Mathlib `CliffordAlgebra Q` odd-odd superbracket equals the polarized quadratic form. -/
theorem mathlib_cliffordAlgebra_superBracket_odd (Q : QuadraticForm R M) (v w : M) :
    superBracket (R := R) .odd .odd (CliffordAlgebra.ι Q v) (CliffordAlgebra.ι Q w) =
      algebraMap R (CliffordAlgebra Q) (polar Q v w) := by
  rw [superBracket_fermionic]
  exact mathlib_cliffordAlgebra_anticommutator Q v w

/-- Orthogonal vectors in Mathlib's native `CliffordAlgebra Q` anticommute. -/
theorem mathlib_cliffordAlgebra_orthogonal_swap
    (Q : QuadraticForm R M) (v w : M) (h_ortho : polar Q v w = 0) :
    CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q w =
      - (CliffordAlgebra.ι Q w * CliffordAlgebra.ι Q v) := by
  exact clifford_orthogonal_swap (CliffordAlgebra.ι Q) Q (algebraMap R (CliffordAlgebra Q))
    (fun x y => map_add (CliffordAlgebra.ι Q) x y) (CliffordAlgebra.ι_sq_scalar Q) v w h_ortho

end MathlibClifford

/-! ### Archetype VI: Grassmann Limit (Q = 0) & Exterior Algebra -/

/-- In the pure Grassmann limit ($Q = 0$), generators anticommute unconditionally. -/
theorem grassmann_anticomm
    {A : Type*} [Ring A] {M : Type*} [AddCommGroup M]
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
    {A : Type*} [Ring A] {M : Type*}
    (ι : M → A) (h_sq : ∀ v : M, ι v * ι v = 0) (v : M) :
    (ι v) ^ 2 = 0 := by
  rw [pow_two]
  exact h_sq v

section MathlibExteriorAndZeroClifford

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

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

/-- Generators of the degenerate Clifford algebra `CliffordAlgebra 0` square to zero. -/
theorem mathlib_cliffordAlgebra_zero_sq (v : M) :
    CliffordAlgebra.ι (0 : QuadraticForm R M) v *
      CliffordAlgebra.ι (0 : QuadraticForm R M) v = 0 := by
  rw [CliffordAlgebra.ι_sq_scalar]
  exact map_zero (algebraMap R (CliffordAlgebra (0 : QuadraticForm R M)))

/-- The odd-odd superbracket in the degenerate Clifford algebra `CliffordAlgebra 0` vanishes. -/
theorem mathlib_cliffordAlgebra_zero_superBracket (v w : M) :
    superBracket (R := R) .odd .odd
      (CliffordAlgebra.ι (0 : QuadraticForm R M) v)
      (CliffordAlgebra.ι (0 : QuadraticForm R M) w) = 0 := by
  rw [superBracket_fermionic]
  exact grassmann_anticomm (CliffordAlgebra.ι (0 : QuadraticForm R M))
    (fun x y => map_add (CliffordAlgebra.ι (0 : QuadraticForm R M)) x y)
    mathlib_cliffordAlgebra_zero_sq v w

end MathlibExteriorAndZeroClifford

/-- First canonical generator of the 2D degenerate Clifford algebra `CliffordAlgebra 0`. -/
noncomputable def cliffZeroGen₁ {R : Type*} [CommRing R] :
    CliffordAlgebra (0 : QuadraticForm R (R × R)) :=
  CliffordAlgebra.ι (0 : QuadraticForm R (R × R)) (1, 0)

/-- Second canonical generator of the 2D degenerate Clifford algebra `CliffordAlgebra 0`. -/
noncomputable def cliffZeroGen₂ {R : Type*} [CommRing R] :
    CliffordAlgebra (0 : QuadraticForm R (R × R)) :=
  CliffordAlgebra.ι (0 : QuadraticForm R (R × R)) (0, 1)

/-- Closed anticommutation witness for canonical generators of `CliffordAlgebra 0`. -/
theorem cliffZeroGen_anticomm {R : Type*} [CommRing R] :
    cliffZeroGen₁ (R := R) * cliffZeroGen₂ (R := R) +
      cliffZeroGen₂ (R := R) * cliffZeroGen₁ (R := R) = 0 := by
  dsimp [cliffZeroGen₁, cliffZeroGen₂]
  exact grassmann_anticomm (CliffordAlgebra.ι (0 : QuadraticForm R (R × R)))
    (fun x y => map_add (CliffordAlgebra.ι (0 : QuadraticForm R (R × R))) x y)
    mathlib_cliffordAlgebra_zero_sq (1, 0) (0, 1)

/-! ### Archetype VII: Geometric Bivector Complex Structure (I² = -1) & Split/Null Signatures -/

section BivectorSignatures

variable {A : Type*} [Ring A]

/--
The 2D Euclidean `(2,0,0)` bivector $I = e₁ e₂$ generates an imaginary unit ($I^2 = -1$).
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

/--
The 2D Lorentzian/split `(1,1,0)` bivector $I = e₁ e₂$ generates a hyperbolic unit ($I^2 = +1$).
-/
theorem hyperbolic_bivector_sq_pos_one
    (e₁ e₂ : A)
    (h₁ : e₁ * e₁ = 1)
    (h₂ : e₂ * e₂ = - 1)
    (h_anticomm : e₁ * e₂ = - (e₂ * e₁)) :
    (e₁ * e₂) * (e₁ * e₂) = 1 := by
  have h_swap : e₂ * e₁ = - (e₁ * e₂) := by
    rw [h_anticomm, neg_neg]
  have step1 : (e₁ * e₂) * (e₁ * e₂) = e₁ * (e₂ * e₁) * e₂ := by
    simp only [mul_assoc]
  rw [step1, h_swap]
  have step2 : e₁ * - (e₁ * e₂) * e₂ = - ((e₁ * e₁) * (e₂ * e₂)) := by
    simp only [mul_neg, neg_mul, mul_assoc]
  rw [step2, h₁, h₂, one_mul, neg_neg]

/--
The 2D PGA/Cartan `(1,0,1)` degenerate bivector $I = e₁ e₀$ is nilpotent ($I^2 = 0$).
-/
theorem degenerate_bivector_sq_zero
    (e₁ e₀ : A)
    (h₁ : e₁ * e₁ = 1)
    (h₀ : e₀ * e₀ = 0)
    (h_anticomm : e₁ * e₀ = - (e₀ * e₁)) :
    (e₁ * e₀) * (e₁ * e₀) = 0 := by
  have h_swap : e₀ * e₁ = - (e₁ * e₀) := by
    rw [h_anticomm, neg_neg]
  have step1 : (e₁ * e₀) * (e₁ * e₀) = e₁ * (e₀ * e₁) * e₀ := by
    simp only [mul_assoc]
  rw [step1, h_swap]
  have step2 : e₁ * - (e₁ * e₀) * e₀ = - ((e₁ * e₁) * (e₀ * e₀)) := by
    simp only [mul_neg, neg_mul, mul_assoc]
  rw [step2, h₁, h₀, mul_zero, neg_zero]

end BivectorSignatures

/--
In Mathlib's native `CliffordAlgebra Q`, the bivector of two orthogonal unit vectors squares to `-1`.
-/
theorem mathlib_cliffordAlgebra_bivector_sq_neg_one
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (Q : QuadraticForm R M) (e₁ e₂ : M)
    (h₁ : Q e₁ = 1) (h₂ : Q e₂ = 1) (h_ortho : polar Q e₁ e₂ = 0) :
    (CliffordAlgebra.ι Q e₁ * CliffordAlgebra.ι Q e₂) *
      (CliffordAlgebra.ι Q e₁ * CliffordAlgebra.ι Q e₂) = -1 := by
  apply geometric_bivector_sq_neg_one
  · rw [CliffordAlgebra.ι_sq_scalar, h₁, map_one]
  · rw [CliffordAlgebra.ι_sq_scalar, h₂, map_one]
  · exact mathlib_cliffordAlgebra_orthogonal_swap Q e₁ e₂ h_ortho

end ChakravalaGA

namespace InfoGeometry.Algebra.ChakravalaGA

export _root_.ChakravalaGA (
  Parity
  even_ne_odd
  koszulSign
  koszulSign_even_left
  koszulSign_even_right
  koszulSign_odd_odd
  koszulSign_symm
  koszulSign_add_left
  koszulSign_add_right
  koszulSign_sq_one
  superBracket
  superBracket_fermionic
  superBracket_bosonic
  superBracket_even_odd
  superBracket_odd_even
  superBracket_skew
  polar
  clifford_anticommutator
  clifford_representation_anticommutator
  clifford_orthogonal_swap
  mathlib_cliffordAlgebra_anticommutator
  mathlib_cliffordAlgebra_superBracket_odd
  mathlib_cliffordAlgebra_orthogonal_swap
  grassmann_anticomm
  grassmann_nilpotent
  mathlib_exteriorAlgebra_anticomm
  mathlib_exteriorAlgebra_swap
  mathlib_exteriorAlgebra_nilpotent
  mathlib_exteriorAlgebra_superBracket_zero
  mathlib_cliffordAlgebra_zero_sq
  mathlib_cliffordAlgebra_zero_superBracket
  cliffZeroGen₁
  cliffZeroGen₂
  cliffZeroGen_anticomm
  geometric_bivector_sq_neg_one
  hyperbolic_bivector_sq_pos_one
  degenerate_bivector_sq_zero
  mathlib_cliffordAlgebra_bivector_sq_neg_one
)

end InfoGeometry.Algebra.ChakravalaGA
