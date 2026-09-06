import InfoGeometry.Algebra.H3ZornJordanIdentity
import Mathlib.Algebra.Jordan.Basic

/-!
# The H3Zorn Jordan algebra instance

This module installs the candidate product as a commutative non-associative
ring on the H3Zorn carrier and derives the commutative Jordan axiom from the
already proved global product law in `H3ZornJordanIdentity`.
-/

namespace InfoGeometry.Algebra

open H3Zorn

/-- Multiplication on the real split carrier is its verified candidate Jordan
product. -/
noncomputable instance h3ZornJordanMul : Mul (H3Zorn ℝ) where
  mul := candidateJordanMul

@[simp] theorem candidateJordanMul_eq_mul (X Y : H3Zorn ℝ) :
    candidateJordanMul X Y = X * Y := rfl

/-- The verified product is a commutative bilinear multiplication on the
existing additive commutative group. No associativity is asserted. -/
noncomputable instance h3ZornJordanNonUnitalNonAssocCommRing :
    NonUnitalNonAssocCommRing (H3Zorn ℝ) where
  mul_zero X := by
    change candidateJordanMul X 0 = 0
    simpa using candidateJordanMul_smul_right (0 : ℝ) X (0 : H3Zorn ℝ)
  zero_mul X := by
    change candidateJordanMul 0 X = 0
    simpa using candidateJordanMul_smul_left (0 : ℝ) (0 : H3Zorn ℝ) X
  left_distrib X Y Z := by
    change candidateJordanMul X (Y + Z) = _
    exact candidateJordanMul_add_right X Y Z
  right_distrib X Y Z := by
    change candidateJordanMul (X + Y) Z = _
    exact candidateJordanMul_add_left X Y Z
  mul_comm := candidateJordanMul_comm

/-- The installed product satisfies Mathlib's commutative Jordan identity. -/
noncomputable instance h3ZornJordanIsCommJordan : IsCommJordan (H3Zorn ℝ) :=
  isCommJordan_of_cubicJordanDatum h3zornCubicJordanDatum

/-- Native closure of the repository's named global product law. -/
theorem h3ZornJordanProductLaw : H3ZornJordanProductLaw := by
  intro X Y
  change candidateJordanMul (candidateJordanMul X Y) (candidateJordanMul X X) =
    candidateJordanMul X (candidateJordanMul Y (candidateJordanMul X X))
  simpa only [candidateJordanMul_eq_mul] using
    (IsCommJordan.lmul_comm_rmul_rmul X Y)

/-- Native closure of the equivalent scalar-free `T`-commutation law. -/
theorem h3ZornTJordanCommutation : TJordanCommutation :=
  H3ZornJordanProductLaw_iff_TJordanCommutation.mp h3ZornJordanProductLaw

/-- Native closure of the paper-facing Jordan identity target. -/
theorem h3ZornJordanIdentityTarget : H3ZornJordanIdentityTarget :=
  h3ZornJordanProductLaw

/--
Literature-facing readout for Baez's octonionic/Jordan-algebra discussion:
the real split `H3Zorn` carrier, with the verified candidate product installed
as multiplication, satisfies Mathlib's commutative Jordan algebra axiom.

This theorem records the kernel-checked algebraic fact available in this file
for the installed product.
-/
theorem h3Zorn_isCommJordan : IsCommJordan (H3Zorn ℝ) :=
  inferInstance

/-- Native Mathlib form of the Jordan identity for the installed product. -/
theorem h3Zorn_jordan_identity (x y : H3Zorn ℝ) :
    x * y * (x * x) = x * (y * (x * x)) := by
  exact IsCommJordan.lmul_comm_rmul_rmul x y

/-- The multiplication and quadratic-representation operators commute in the
native Jordan-algebra interface. -/
theorem h3Zorn_lmul_comm_rmul_sq (x : H3Zorn ℝ) :
    Commute (AddMonoid.End.mulLeft x)
      (AddMonoid.End.mulRight (x * x)) := by
  exact commute_lmul_rmul_sq x

/-- The left multiplication operators satisfy the standard Jordan quadratic
commutation relation. -/
theorem h3Zorn_lmul_comm_lmul_sq (x : H3Zorn ℝ) :
    Commute (AddMonoid.End.mulLeft x)
      (AddMonoid.End.mulLeft (x * x)) := by
  exact commute_lmul_lmul_sq x

end InfoGeometry.Algebra
