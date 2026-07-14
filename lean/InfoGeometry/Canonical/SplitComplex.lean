import Mathlib.Tactic

/-!
# Split complex numbers

This module isolates the smallest split-sign carrier used by the causal/Krein
layer.

The theorem surface is intentionally narrow:

* the split generator `ε` satisfies `ε² = 1`;
* `1 ± ε` are explicit nonzero zero divisors;
* `(1 ± ε)/2` are orthogonal idempotents, under `2 ≠ 0`.

The nilpotent lightrays are not `1 ± ε`; they live in the supported corner
arrows between idempotent sectors and are handled by the incidence layer
elsewhere.
-/

noncomputable section

namespace SplitComplex

/-- The split-complex carrier. -/
@[ext]
structure Carrier (R : Type*) where
  re : R
  im : R

namespace Carrier

variable {R : Type*}

instance [Zero R] : Zero (Carrier R) where
  zero := ⟨0, 0⟩

instance [One R] [Zero R] : One (Carrier R) where
  one := ⟨1, 0⟩

instance [One R] [Zero R] : OfNat (Carrier R) 1 where
  ofNat := ⟨1, 0⟩

instance [Add R] : Add (Carrier R) where
  add x y := ⟨x.re + y.re, x.im + y.im⟩

instance [Neg R] : Neg (Carrier R) where
  neg x := ⟨-x.re, -x.im⟩

instance [Sub R] : Sub (Carrier R) where
  sub x y := ⟨x.re - y.re, x.im - y.im⟩

instance [Add R] [Mul R] : Mul (Carrier R) where
  mul x y := ⟨x.re * y.re + x.im * y.im, x.re * y.im + x.im * y.re⟩

/-- The split generator `ε`. -/
def eps [Zero R] [One R] : Carrier R :=
  ⟨0, 1⟩

@[simp] theorem zero_re [Zero R] : (0 : Carrier R).re = 0 := rfl
@[simp] theorem zero_im [Zero R] : (0 : Carrier R).im = 0 := rfl
@[simp] theorem one_re [One R] [Zero R] : (1 : Carrier R).re = 1 := rfl
@[simp] theorem one_im [One R] [Zero R] : (1 : Carrier R).im = 0 := rfl
@[simp] theorem eps_re [Zero R] [One R] : (eps (R := R)).re = 0 := rfl
@[simp] theorem eps_im [Zero R] [One R] : (eps (R := R)).im = 1 := rfl
@[simp] theorem add_re [Add R] (x y : Carrier R) : (x + y).re = x.re + y.re := rfl
@[simp] theorem add_im [Add R] (x y : Carrier R) : (x + y).im = x.im + y.im := rfl
@[simp] theorem sub_re [Sub R] (x y : Carrier R) : (x - y).re = x.re - y.re := rfl
@[simp] theorem sub_im [Sub R] (x y : Carrier R) : (x - y).im = x.im - y.im := rfl
@[simp] theorem neg_re [Neg R] (x : Carrier R) : (-x).re = -x.re := rfl
@[simp] theorem neg_im [Neg R] (x : Carrier R) : (-x).im = -x.im := rfl
@[simp] theorem mul_re [Add R] [Mul R] (x y : Carrier R) :
    (x * y).re = x.re * y.re + x.im * y.im := rfl
@[simp] theorem mul_im [Add R] [Mul R] (x y : Carrier R) :
    (x * y).im = x.re * y.im + x.im * y.re := rfl

/-- The split generator squares to `1`. -/
theorem eps_sq [CommRing R] :
    eps (R := R) * eps (R := R) = (1 : Carrier R) := by
  ext <;> simp [eps]

/-- The two split-null factors `1 + ε` and `1 - ε` multiply to zero. -/
theorem one_add_eps_mul_one_sub_eps [CommRing R] :
    ((1 : Carrier R) + eps (R := R)) * ((1 : Carrier R) - eps (R := R)) = 0 := by
  ext <;> simp [eps]

/-- The opposite order also multiplies to zero. -/
theorem one_sub_eps_mul_one_add_eps [CommRing R] :
    ((1 : Carrier R) - eps (R := R)) * ((1 : Carrier R) + eps (R := R)) = 0 := by
  ext <;> simp [eps]

section ZeroDivisors

variable [CommRing R] [Nontrivial R]

def u : Carrier R := (1 : Carrier R) + eps (R := R)

def v : Carrier R := (1 : Carrier R) - eps (R := R)

theorem u_ne_zero : u (R := R) ≠ 0 := by
  intro h
  have h' : (1 : R) = 0 := by
    simpa [u, eps] using congrArg Carrier.re h
  exact one_ne_zero h'

theorem v_ne_zero : v (R := R) ≠ 0 := by
  intro h
  have h' : (1 : R) = 0 := by
    simpa [v, eps] using congrArg Carrier.re h
  exact one_ne_zero h'

/-- The split sign gives explicit nonzero zero divisors. -/
theorem splitSign_has_nonzero_zero_divisors :
    ∃ u v : Carrier R, u ≠ 0 ∧ v ≠ 0 ∧ u * v = 0 := by
  refine ⟨u (R := R), v (R := R), u_ne_zero (R := R), v_ne_zero (R := R), ?_⟩
  simpa [u, v] using (one_add_eps_mul_one_sub_eps (R := R))

end ZeroDivisors

section Projectors

variable [Field R] [CharZero R]

/-- The positive half-projector `(1 + ε)/2`. -/
def pPlus : Carrier R :=
  ⟨(2 : R)⁻¹, (2 : R)⁻¹⟩

/-- The negative half-projector `(1 - ε)/2`. -/
def pMinus : Carrier R :=
  ⟨(2 : R)⁻¹, -(2 : R)⁻¹⟩

/-- The positive half-projector is idempotent. -/
theorem pPlus_sq : pPlus (R := R) * pPlus (R := R) = pPlus (R := R) := by
  ext <;> simp [pPlus]
  · have h2 : (2 : R) ≠ 0 := two_ne_zero
    field_simp [h2]
    ring
  · have h2 : (2 : R) ≠ 0 := two_ne_zero
    field_simp [h2]
    ring

@[simp] theorem pPlus_idempotent : pPlus (R := R) * pPlus (R := R) = pPlus (R := R) := by
  simpa using (pPlus_sq (R := R))

/-- The negative half-projector is idempotent. -/
theorem pMinus_sq : pMinus (R := R) * pMinus (R := R) = pMinus (R := R) := by
  ext <;> simp [pMinus]
  · have h2 : (2 : R) ≠ 0 := two_ne_zero
    field_simp [h2]
    ring
  · have h2 : (2 : R) ≠ 0 := two_ne_zero
    field_simp [h2]
    ring

@[simp] theorem pMinus_idempotent : pMinus (R := R) * pMinus (R := R) = pMinus (R := R) := by
  simpa using (pMinus_sq (R := R))

/-- The projectors are orthogonal. -/
theorem pPlus_mul_pMinus : pPlus (R := R) * pMinus (R := R) = 0 := by
  ext <;> simp [pPlus, pMinus]

/-- The projectors are orthogonal in the opposite order as well. -/
theorem pMinus_mul_pPlus : pMinus (R := R) * pPlus (R := R) = 0 := by
  ext <;> simp [pPlus, pMinus]

end Projectors

end Carrier

end SplitComplex
