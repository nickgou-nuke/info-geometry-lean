import InfoGeometry.Algebra.NonAssocIteratedLeibnizTransport
import InfoGeometry.Lie.BaezG2SplitOctonion
import Mathlib.Tactic

/-!
# Kernels and constants of integration for nonassociative derivations

This file records the exact algebraic content of the phrase "constant of
integration" for a nonassociative derivation.

For a linear endomorphism satisfying the Leibniz rule and for a supplied
 two-sided unit `1`, we prove:

* `D 1 = 0`;
* `D (c • 1) = 0` for every scalar `c`;
* `D x = D y` iff `x - y ∈ ker D`;
* the solution fiber of `D u = v`, once inhabited by `u₀`, is the affine
  translate `u₀ + ker D`;
* every positive iterate of `D` kills every scalar multiple of the unit.

The final section specializes these statements to the repository-native real
split-Cayley/Zorn carrier and the native `SplitCayleyG2Derivation` type.

No exponential, convergence theorem, ODE, or path-ordered transport is
postulated here.
-/

namespace InfoGeometry.Algebra.NonAssocDerivationKernel

section LinearLeibniz

variable {R A : Type*}
variable [CommRing R] [AddCommGroup A] [Module R A] [One A] [Mul A]

/-- A linear Leibniz endomorphism kills a supplied two-sided unit.  This is the
`Module.End` formulation used by the native `G₂` derivation carrier. -/
theorem linearDerivation_kills_one
    (D : Module.End R A)
    (hD : ∀ x y : A, D (x * y) = D x * y + x * D y)
    (one_mul' : ∀ x : A, (1 : A) * x = x)
    (mul_one' : ∀ x : A, x * (1 : A) = x) :
    D (1 : A) = 0 := by
  have h : D (1 : A) = D (1 : A) + D (1 : A) := by
    calc
      D (1 : A) = D ((1 : A) * (1 : A)) := by rw [one_mul']
      _ = D (1 : A) * (1 : A) + (1 : A) * D (1 : A) := hD 1 1
      _ = D (1 : A) + D (1 : A) := by rw [mul_one', one_mul']
  abel at h

/-- Every scalar multiple of the unit lies in the kernel of a linear
nonassociative derivation. -/
theorem linearDerivation_kills_smul_one
    (D : Module.End R A)
    (hD : ∀ x y : A, D (x * y) = D x * y + x * D y)
    (one_mul' : ∀ x : A, (1 : A) * x = x)
    (mul_one' : ∀ x : A, x * (1 : A) = x)
    (c : R) :
    D (c • (1 : A)) = 0 := by
  rw [D.map_smul, linearDerivation_kills_one D hD one_mul' mul_one', smul_zero]

/-- Set-membership form of `linearDerivation_kills_smul_one`. -/
theorem smul_one_mem_linearDerivation_ker
    (D : Module.End R A)
    (hD : ∀ x y : A, D (x * y) = D x * y + x * D y)
    (one_mul' : ∀ x : A, (1 : A) * x = x)
    (mul_one' : ∀ x : A, x * (1 : A) = x)
    (c : R) :
    c • (1 : A) ∈ LinearMap.ker D := by
  rw [LinearMap.mem_ker]
  exact linearDerivation_kills_smul_one D hD one_mul' mul_one' c

/-- Two inputs have the same derivation precisely when their difference lies
in the linear kernel.  This statement uses only linearity. -/
theorem apply_eq_iff_sub_mem_ker
    (D : Module.End R A) (x y : A) :
    D x = D y ↔ x - y ∈ LinearMap.ker D := by
  rw [LinearMap.mem_ker, D.map_sub, sub_eq_zero]

/-- If `u₀` is one solution of `D u = v`, then all solutions are exactly the
affine translate of `ker D` through `u₀`. -/
theorem apply_eq_value_iff_sub_mem_ker
    (D : Module.End R A) (u₀ u v : A)
    (hu₀ : D u₀ = v) :
    D u = v ↔ u - u₀ ∈ LinearMap.ker D := by
  rw [← hu₀]
  exact apply_eq_iff_sub_mem_ker D u u₀

/-- Additive parametrization of an inhabited solution fiber by the kernel. -/
theorem apply_add_eq_value_iff_mem_ker
    (D : Module.End R A) (u₀ k v : A)
    (hu₀ : D u₀ = v) :
    D (u₀ + k) = v ↔ k ∈ LinearMap.ker D := by
  rw [D.map_add, hu₀, LinearMap.mem_ker]
  constructor
  · intro h
    exact add_left_cancel (by simpa using h)
  · intro hk
    rw [hk, add_zero]

/-- Once `D x = 0`, every positive power of the endomorphism also kills `x`. -/
theorem pow_apply_eq_zero_of_apply_eq_zero
    (D : Module.End R A) {x : A}
    (hx : D x = 0) {n : ℕ} (hn : 0 < n) :
    (D ^ n) x = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [pow_succ, Module.End.mul_apply, hx, map_zero]

/-- Every positive iterate kills every scalar multiple of the unit. -/
theorem pow_kills_smul_one
    (D : Module.End R A)
    (hD : ∀ x y : A, D (x * y) = D x * y + x * D y)
    (one_mul' : ∀ x : A, (1 : A) * x = x)
    (mul_one' : ∀ x : A, x * (1 : A) = x)
    (c : R) {n : ℕ} (hn : 0 < n) :
    (D ^ n) (c • (1 : A)) = 0 :=
  pow_apply_eq_zero_of_apply_eq_zero D
    (linearDerivation_kills_smul_one D hD one_mul' mul_one' c) hn

end LinearLeibniz

section Bundled

variable {R A : Type*}
variable [CommRing R] [NonUnitalNonAssocRing A] [Module R A]
variable [IsScalarTower R A A] [SMulCommClass R A A] [One A]

/-- The existing bundled nonassociative derivation theorem, exposed in scalar
kernel form. -/
theorem bundledDerivation_kills_smul_one
    (D : InfoGeometry.Algebra.NonAssocDerivation R A)
    (one_mul' : ∀ x : A, (1 : A) * x = x)
    (mul_one' : ∀ x : A, x * (1 : A) = x)
    (c : R) :
    D (c • (1 : A)) = 0 := by
  rw [InfoGeometry.Algebra.NonAssocDerivation.map_smul]
  rw [InfoGeometry.Algebra.NonAssocIteratedLeibnizTransport.derivation_kills_unit
    D 1 one_mul' mul_one']
  exact smul_zero c

/-- Positive iterates of a bundled derivation kill scalar identity directions. -/
theorem bundledIterD_kills_smul_one
    (D : InfoGeometry.Algebra.NonAssocDerivation R A)
    (one_mul' : ∀ x : A, (1 : A) * x = x)
    (mul_one' : ∀ x : A, x * (1 : A) = x)
    (c : R) {n : ℕ} (hn : 0 < n) :
    InfoGeometry.Algebra.NonAssocIteratedLeibnizTransport.iterD D n
        (c • (1 : A)) = 0 := by
  apply InfoGeometry.Algebra.NonAssocIteratedLeibnizTransport.iterD_eq_zero_of_apply_eq_zero
    D (bundledDerivation_kills_smul_one D one_mul' mul_one' c) hn

end Bundled

/-! ## Native real split-Cayley specialization -/

namespace SplitCayley

open InfoGeometry.Lie.BaezG2SplitOctonion

/-- The native Zorn identity is a left unit. -/
theorem one_mul (x : SplitCayley) : (1 : SplitCayley) * x = x := by
  rcases x with ⟨a, b, x, y⟩
  ext i <;>
    simp [InfoGeometry.Canonical.ZornMatrix.mul_def,
      InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]

/-- The native Zorn identity is a right unit. -/
theorem mul_one (x : SplitCayley) : x * (1 : SplitCayley) = x := by
  rcases x with ⟨a, b, x, y⟩
  ext i <;>
    simp [InfoGeometry.Canonical.ZornMatrix.mul_def,
      InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]

/-- Every native split-Cayley `G₂` derivation kills the identity. -/
theorem derivation_kills_one (D : SplitCayleyG2Derivation) :
    (D.1 : Module.End ℝ SplitCayley) (1 : SplitCayley) = 0 :=
  linearDerivation_kills_one D.1 D.2 one_mul mul_one

/-- Every real scalar identity direction lies in the kernel of every native
split-Cayley `G₂` derivation. -/
theorem derivation_kills_smul_one
    (D : SplitCayleyG2Derivation) (c : ℝ) :
    (D.1 : Module.End ℝ SplitCayley) (c • (1 : SplitCayley)) = 0 :=
  linearDerivation_kills_smul_one D.1 D.2 one_mul mul_one c

/-- Kernel-membership form of the scalar-identity theorem. -/
theorem smul_one_mem_derivation_ker
    (D : SplitCayleyG2Derivation) (c : ℝ) :
    c • (1 : SplitCayley) ∈ LinearMap.ker (D.1 : Module.End ℝ SplitCayley) :=
  smul_one_mem_linearDerivation_ker D.1 D.2 one_mul mul_one c

/-- Exact constant-of-integration theorem on the native split-Cayley carrier. -/
theorem derivation_apply_eq_iff_sub_mem_ker
    (D : SplitCayleyG2Derivation) (x y : SplitCayley) :
    D.1 x = D.1 y ↔
      x - y ∈ LinearMap.ker (D.1 : Module.End ℝ SplitCayley) :=
  apply_eq_iff_sub_mem_ker D.1 x y

/-- Exact affine solution-fiber theorem on the native split-Cayley carrier. -/
theorem derivation_apply_eq_value_iff_sub_mem_ker
    (D : SplitCayleyG2Derivation) (u₀ u v : SplitCayley)
    (hu₀ : D.1 u₀ = v) :
    D.1 u = v ↔
      u - u₀ ∈ LinearMap.ker (D.1 : Module.End ℝ SplitCayley) :=
  apply_eq_value_iff_sub_mem_ker D.1 u₀ u v hu₀

/-- Positive powers of a native `G₂` derivation kill scalar identity directions. -/
theorem derivation_pow_kills_smul_one
    (D : SplitCayleyG2Derivation) (c : ℝ)
    {n : ℕ} (hn : 0 < n) :
    ((D.1 : Module.End ℝ SplitCayley) ^ n) (c • (1 : SplitCayley)) = 0 :=
  pow_kills_smul_one D.1 D.2 one_mul mul_one c hn

end SplitCayley

end InfoGeometry.Algebra.NonAssocDerivationKernel
