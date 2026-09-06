import Mathlib
import InfoGeometry.Canonical.H3ZornJordanTripleG2Bridge
import InfoGeometry.Algebra.JordanInnerDerivations
import InfoGeometry.Algebra.KantorTripleFiveGrading

noncomputable section

namespace InfoGeometry.Canonical.H3ZornJordanKantorCapstone

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Algebra.KantorTripleFiveGrading
open InfoGeometry.Canonical.H3ZornJordanTripleG2Bridge

abbrev H3 := H3Zorn ℝ

/-! ## Operator normal form -/

/-- The Jordan triple operator is the sum of left multiplication by `x ∘ y`
and the inner Jordan derivation `[L_x,L_y]`. -/
theorem jordanTripleD_eq_left_add_inner (x y : H3) :
    jordanTripleD x y =
      jordanLeft (x * y) + jordanInner x y := by
  apply LinearMap.ext
  intro z
  simp only [jordanTripleD_apply, jordanTriple, jordanInner_apply,
    LinearMap.add_apply]
  simp only [candidateJordanMul_eq_mul]
  simp [mul_comm]
  abel

/-- The native `jordanInner` is exactly the already certified split-Albert
inner derivation. -/
theorem jordanInner_eq_baez (x y : H3) :
    jordanInner x y =
      (h3ZornJordanInnerDerivation x y : Module.End ℝ H3) := by
  apply LinearMap.ext
  intro z
  simp only [jordanInner_apply, h3ZornJordanInnerDerivation_apply]
  simp only [candidateJordanMul_eq_mul]

/-- Hence every `jordanInner x y` is a genuine Leibniz derivation. -/
theorem jordanInner_isDerivation (x y : H3) :
    H3ZornJordanDerivation (jordanInner x y) := by
  rw [jordanInner_eq_baez]
  exact (h3ZornJordanInnerDerivation x y).property

/-- Inner derivations are skew in their two parameters. -/
theorem jordanInner_skew (x y : H3) :
    jordanInner y x = -jordanInner x y := by
  apply LinearMap.ext
  intro z
  simp only [jordanInner_apply, LinearMap.neg_apply]
  simp only [candidateJordanMul_eq_mul]
  abel

/-- Left multiplication is additive in its parameter. -/
@[simp] theorem jordanLeft_add (x y : H3) :
    jordanLeft (x + y) = jordanLeft x + jordanLeft y := by
  apply LinearMap.ext
  intro z
  simp [jordanLeft, candidateJordanMul_add_left]

/-- Left multiplication is homogeneous in its parameter. -/
@[simp] theorem jordanLeft_smul (r : ℝ) (x : H3) :
    jordanLeft (r • x) = r • jordanLeft x := by
  apply LinearMap.ext
  intro z
  simp [jordanLeft, candidateJordanMul_smul_left]

/-- Triple operators are additive in the first parameter. -/
@[simp] theorem jordanTripleD_add_left (x₁ x₂ y : H3) :
    jordanTripleD (x₁ + x₂) y = jordanTripleD x₁ y + jordanTripleD x₂ y := by
  apply LinearMap.ext
  intro z
  simp [jordanTripleD_apply]

/-- Triple operators are homogeneous in the first parameter. -/
@[simp] theorem jordanTripleD_smul_left (r : ℝ) (x y : H3) :
    jordanTripleD (r • x) y = r • jordanTripleD x y := by
  apply LinearMap.ext
  intro z
  simp [jordanTripleD_apply]

/-- Triple operators are additive in the middle parameter. -/
@[simp] theorem jordanTripleD_add_middle (x y₁ y₂ : H3) :
    jordanTripleD x (y₁ + y₂) = jordanTripleD x y₁ + jordanTripleD x y₂ := by
  apply LinearMap.ext
  intro z
  simp [jordanTripleD_apply]

/-- Triple operators are homogeneous in the middle parameter. -/
@[simp] theorem jordanTripleD_smul_middle (r : ℝ) (x y : H3) :
    jordanTripleD x (r • y) = r • jordanTripleD x y := by
  apply LinearMap.ext
  intro z
  simp [jordanTripleD_apply]

/-! ## The single linearized Jordan identity needed by the triple system -/

/-- Operator form of the fully linearized Jordan identity:
`[L_{a∘x},L_y] - [L_x,L_{a∘y}] = [L_a,L_{x∘y}]`.

This is derived from mathlib's native
`two_nsmul_lie_lmul_lmul_add_add_eq_zero`; no associativity is used. -/
theorem jordanInner_linearized (a x y : H3) :
    jordanInner (a * x) y - jordanInner x (a * y) =
      jordanInner a (x * y) := by
  apply LinearMap.ext
  intro z
  have hraw := congrArg (fun f : AddMonoid.End H3 => f z)
    (two_nsmul_lie_lmul_lmul_add_add_eq_zero (A := H3) a x y)
  have h2 :
      2 • ((a * ((x * y) * z) - (x * y) * (a * z)) +
        (x * ((y * a) * z) - (y * a) * (x * z)) +
        (y * ((a * x) * z) - (a * x) * (y * z))) = 0 := by
    simpa [Ring.lie_def, AddMonoid.End.mulLeft] using hraw
  have h0 :
      (a * ((x * y) * z) - (x * y) * (a * z)) +
        (x * ((y * a) * z) - (y * a) * (x * z)) +
        (y * ((a * x) * z) - (a * x) * (y * z)) = 0 := by
    exact (nsmul_eq_zero_iff_right (M := H3) (n := 2) (by norm_num)).mp h2
  simp only [LinearMap.sub_apply, jordanInner_apply]
  simp only [candidateJordanMul_eq_mul]
  simp [mul_comm] at h0 ⊢
  abel_nf at h0 ⊢
  exact h0

/-! ## Commutator calculus for triple operators -/

/-- A certified inner derivation acts on left multiplication by commutator. -/
theorem jordanInner_lie_jordanLeft (u v a : H3) :
    ⁅jordanInner u v, jordanLeft a⁆ =
      jordanLeft (jordanInner u v a) := by
  rw [jordanInner_eq_baez]
  have h := h3Zorn_derivation_lie_jordanLmul
    (h3ZornJordanInnerDerivation u v) a
  apply LinearMap.ext
  intro z
  have hz := LinearMap.congr_fun h z
  simpa [jordanLeft, jordanLmul, candidateJordanMul_eq_mul] using hz

/-- Commuting an inner derivation through a triple operator differentiates the
two parameter slots. -/
theorem jordanInner_lie_tripleD (u v x y : H3) :
    ⁅jordanInner u v, jordanTripleD x y⁆ =
      jordanTripleD (jordanInner u v x) y +
        jordanTripleD x (jordanInner u v y) := by
  apply LinearMap.ext
  intro z
  change
    jordanInner u v (jordanTriple x y z) -
        jordanTriple x y (jordanInner u v z) = _
  have h := jordanTriple_derivation (jordanInner u v)
    (jordanInner_isDerivation u v) x y z
  rw [h]
  simp only [jordanTripleD_apply, LinearMap.add_apply]
  abel

/-- The complementary commutator with a bare left multiplication is the
linearized-Jordan part of the triple identity. -/
theorem jordanLeft_lie_tripleD (a x y : H3) :
    ⁅jordanLeft a, jordanTripleD x y⁆ =
      jordanTripleD (a * x) y - jordanTripleD x (a * y) := by
  rw [jordanTripleD_eq_left_add_inner]
  simp only [lie_add]
  have hJL := jordanInner_lie_jordanLeft x y a
  have hLJ :
      ⁅jordanLeft a, jordanInner x y⁆ =
        -jordanLeft (jordanInner x y a) := by
    apply neg_injective
    simpa only [neg_neg, lie_skew] using hJL
  rw [hLJ]
  rw [jordanTripleD_eq_left_add_inner,
    jordanTripleD_eq_left_add_inner]
  rw [jordanInner_linearized]
  apply LinearMap.ext
  intro z
  simp only [Ring.lie_def, Module.End.mul_apply, LinearMap.sub_apply,
    LinearMap.add_apply, LinearMap.neg_apply, jordanLeft,
    jordanInner_apply]
  simp only [candidateJordanMul_eq_mul]
  simp [mul_comm]
  abel

/-- The triple operator itself splits pointwise into the multiplication and
inner-derivation pieces. -/
theorem jordanTriple_eq_mul_add_inner (u v x : H3) :
    jordanTriple u v x = (u * v) * x + jordanInner u v x := by
  have h := LinearMap.congr_fun (jordanTripleD_eq_left_add_inner u v) x
  simpa [jordanTripleD_apply, jordanLeft] using h

/-- Reversing the first two triple parameters changes only the inner part. -/
theorem jordanTriple_reverse_eq_mul_sub_inner (u v y : H3) :
    jordanTriple v u y = (u * v) * y - jordanInner u v y := by
  rw [jordanTriple_eq_mul_add_inner]
  rw [mul_comm v u]
  have hs := LinearMap.congr_fun (jordanInner_skew u v) y
  simp only [LinearMap.neg_apply] at hs
  rw [hs]
  abel

/-- The standard Jordan triple satisfies the first Freudenthal--Kantor
identity in operator form. -/
theorem jordanTripleD_comm (u v x y : H3) :
    ⁅jordanTripleD u v, jordanTripleD x y⁆ =
      jordanTripleD (jordanTriple u v x) y -
        jordanTripleD x (jordanTriple v u y) := by
  rw [jordanTripleD_eq_left_add_inner]
  simp only [add_lie]
  rw [jordanLeft_lie_tripleD, jordanInner_lie_tripleD]
  rw [jordanTriple_eq_mul_add_inner,
    jordanTriple_reverse_eq_mul_sub_inner]
  rw [jordanTripleD_add_left, jordanTripleD_add_middle]
  rw [show (u * v) * y - jordanInner u v y =
      (u * v) * y + (-1 : ℝ) • jordanInner u v y by module]
  rw [jordanTripleD_add_middle, jordanTripleD_smul_middle]
  module

/-- First Freudenthal--Kantor identity for the native split-Albert Jordan
triple. -/
theorem jordanTriple_first_identity (u v x y z : H3) :
    jordanTriple u v (jordanTriple x y z) -
        jordanTriple x y (jordanTriple u v z) =
      jordanTriple (jordanTriple u v x) y z -
        jordanTriple x (jordanTriple v u y) z := by
  have h := LinearMap.congr_fun (jordanTripleD_comm u v x y) z
  simpa [Ring.lie_def, jordanTripleD_apply] using h

/-! ## The Jordan boundary: K = 0 -/

@[simp] theorem jordanTriple_zero_left (y z : H3) :
    jordanTriple 0 y z = 0 := by
  simpa using jordanTriple_smul_left (0 : ℝ) z y z

@[simp] theorem jordanTriple_zero_middle (x z : H3) :
    jordanTriple x 0 z = 0 := by
  simpa using jordanTriple_smul_middle (0 : ℝ) x z z

@[simp] theorem jordanTriple_zero_right (x y : H3) :
    jordanTriple x y 0 = 0 := by
  simpa using jordanTriple_smul_right (0 : ℝ) x y 0

/-- Second Freudenthal--Kantor identity.  For the Jordan triple it collapses
because outer symmetry makes every `K` expression vanish. -/
theorem jordanTriple_second_identity (u v x y z : H3) :
    jordanTriple (jordanTriple u x v - jordanTriple v x u) z y -
        jordanTriple y z (jordanTriple u x v - jordanTriple v x u) =
      jordanTriple y x (jordanTriple u z v - jordanTriple v z u) +
        (jordanTriple u (jordanTriple x y z) v -
          jordanTriple v (jordanTriple x y z) u) := by
  rw [jordanTriple_outer_symm u x v,
    jordanTriple_outer_symm u z v,
    jordanTriple_outer_symm u (jordanTriple x y z) v]
  simp

/-- The native split-Albert Jordan triple is therefore a concrete
Freudenthal--Kantor triple system. -/
noncomputable def h3JordanKantorTripleSystem :
    KantorTripleSystem ℝ H3 where
  triple := jordanTriple
  triple_add_left := jordanTriple_add_left
  triple_smul_left := jordanTriple_smul_left
  triple_add_middle := jordanTriple_add_middle
  triple_smul_middle := jordanTriple_smul_middle
  triple_add_right := jordanTriple_add_right
  triple_smul_right := jordanTriple_smul_right
  first_identity := jordanTriple_first_identity
  second_identity := jordanTriple_second_identity

/-- This concrete Kantor triple system lies on the Jordan boundary: its
`K`-operator vanishes identically. -/
theorem h3JordanKantor_isJordan :
    h3JordanKantorTripleSystem.IsJordan := by
  exact h3JordanKantorTripleSystem.isJordan_of_outerSymm
    jordanTriple_outer_symm

/-- The previously proved unconditional split-G2 action is a derivation of the
concrete Kantor triple product in all three slots. -/
theorem g2_derives_h3KantorTriple
    (D : G2Der) (x y z : H3) :
    liftG2End D (h3JordanKantorTripleSystem.triple x y z) =
      h3JordanKantorTripleSystem.triple (liftG2End D x) y z +
        h3JordanKantorTripleSystem.triple x (liftG2End D y) z +
          h3JordanKantorTripleSystem.triple x y (liftG2End D z) := by
  exact g2_jordanTriple_derivation D x y z

end InfoGeometry.Canonical.H3ZornJordanKantorCapstone
