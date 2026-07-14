import Mathlib

/-!
# InfoGeometry.Canonical.CartanSuperbracketClosure

Concrete algebraic closure laws for an involutive Cartan grading.

This file proves the finite algebraic core behind the statement:

  superbracket extension, not analytic continuation.

Given a grading endomorphism `θ`, an element is:

* even if `θ x = x`;
* odd if `θ x = -x`.

Then the associative commutator and anticommutator obey the expected Cartan
sector rules:

* `[even, even]` is even;
* `[even, odd]` is odd;
* `[odd, odd]` is even;
* `{odd, odd}` is even;
* the square of an odd element is even.

No wrappers.
No Lie-superalgebra packet.
No compactification claim.
No `sorry`.
-/

namespace CartanSuperbracketClosure

variable {A : Type*} [Ring A]

/--
Even-even commutator closure.

If `x` and `y` are fixed by the grading, then `[x,y]` is fixed.
-/
theorem cartan_even_even_comm_even
    (θ : A →+* A)
    {x y : A}
    (hx : θ x = x)
    (hy : θ y = y) :
    θ (x * y - y * x) = x * y - y * x := by
  calc
    θ (x * y - y * x)
        = θ (x * y) - θ (y * x) := by simp
    _   = θ x * θ y - θ y * θ x := by simp
    _   = x * y - y * x := by rw [hx, hy]

/--
Even-odd commutator closure.

If `x` is even and `y` is odd, then `[x,y]` is odd.
-/
theorem cartan_even_odd_comm_odd
    (θ : A →+* A)
    {x y : A}
    (hx : θ x = x)
    (hy : θ y = -y) :
    θ (x * y - y * x) = -(x * y - y * x) := by
  calc
    θ (x * y - y * x)
        = θ (x * y) - θ (y * x) := by simp
    _   = θ x * θ y - θ y * θ x := by simp
    _   = x * (-y) - (-y) * x := by rw [hx, hy]
    _   = -(x * y - y * x) := by noncomm_ring

/--
Odd-even commutator closure.

If `x` is odd and `y` is even, then `[x,y]` is odd.
-/
theorem cartan_odd_even_comm_odd
    (θ : A →+* A)
    {x y : A}
    (hx : θ x = -x)
    (hy : θ y = y) :
    θ (x * y - y * x) = -(x * y - y * x) := by
  calc
    θ (x * y - y * x)
        = θ (x * y) - θ (y * x) := by simp
    _   = θ x * θ y - θ y * θ x := by simp
    _   = (-x) * y - y * (-x) := by rw [hx, hy]
    _   = -(x * y - y * x) := by noncomm_ring

/--
Odd-odd commutator closure.

If `x` and `y` are odd, then `[x,y]` is even.
-/
theorem cartan_odd_odd_comm_even
    (θ : A →+* A)
    {x y : A}
    (hx : θ x = -x)
    (hy : θ y = -y) :
    θ (x * y - y * x) = x * y - y * x := by
  calc
    θ (x * y - y * x)
        = θ (x * y) - θ (y * x) := by simp
    _   = θ x * θ y - θ y * θ x := by simp
    _   = (-x) * (-y) - (-y) * (-x) := by rw [hx, hy]
    _   = x * y - y * x := by noncomm_ring

/--
Odd-odd anticommutator closure.

If `x` and `y` are odd, then `{x,y}` is even.
This is the core superbracket closure law for the odd sector.
-/
theorem cartan_odd_odd_anticomm_even
    (θ : A →+* A)
    {x y : A}
    (hx : θ x = -x)
    (hy : θ y = -y) :
    θ (x * y + y * x) = x * y + y * x := by
  calc
    θ (x * y + y * x)
        = θ (x * y) + θ (y * x) := by simp
    _   = θ x * θ y + θ y * θ x := by simp
    _   = (-x) * (-y) + (-y) * (-x) := by rw [hx, hy]
    _   = x * y + y * x := by noncomm_ring

/--
Odd square is even.

This is the local algebraic fact behind nilpotent/odd lanes producing
even Hamiltonian/projector data through quadratic closure.
-/
theorem cartan_odd_square_even
    (θ : A →+* A)
    {q : A}
    (hq : θ q = -q) :
    θ (q * q) = q * q := by
  calc
    θ (q * q)
        = θ q * θ q := by simp
    _   = (-q) * (-q) := by rw [hq]
    _   = q * q := by noncomm_ring

/--
If an odd operator is square-zero, its transported square is still zero.

This is the nilpotent lane in the Cartan grading.
-/
theorem cartan_odd_square_zero_stable
    (θ : A →+* A)
    {q : A}
    (hzero : q * q = 0) :
    θ (q * q) = 0 := by
  rw [hzero]
  simp

/--
Cartan superbracket closure profile.

This collects the concrete sector laws without defining any new superalgebra
structure.
-/
theorem cartan_superbracket_closure_profile
    (θ : A →+* A)
    {e₁ e₂ o₁ o₂ : A}
    (he₁ : θ e₁ = e₁)
    (he₂ : θ e₂ = e₂)
    (ho₁ : θ o₁ = -o₁)
    (ho₂ : θ o₂ = -o₂) :
    θ (e₁ * e₂ - e₂ * e₁) = e₁ * e₂ - e₂ * e₁ ∧
    θ (e₁ * o₁ - o₁ * e₁) = -(e₁ * o₁ - o₁ * e₁) ∧
    θ (o₁ * e₁ - e₁ * o₁) = -(o₁ * e₁ - e₁ * o₁) ∧
    θ (o₁ * o₂ - o₂ * o₁) = o₁ * o₂ - o₂ * o₁ ∧
    θ (o₁ * o₂ + o₂ * o₁) = o₁ * o₂ + o₂ * o₁ ∧
    θ (o₁ * o₁) = o₁ * o₁ := by
  exact
    ⟨cartan_even_even_comm_even θ he₁ he₂,
     cartan_even_odd_comm_odd θ he₁ ho₁,
     cartan_odd_even_comm_odd θ ho₁ he₁,
     cartan_odd_odd_comm_even θ ho₁ ho₂,
     cartan_odd_odd_anticomm_even θ ho₁ ho₂,
     cartan_odd_square_even θ ho₁⟩

end CartanSuperbracketClosure
