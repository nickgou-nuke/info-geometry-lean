import Mathlib
import InfoGeometry.Canonical.H3ZornJordanTripleG2Bridge
import InfoGeometry.Algebra.JordanInnerDerivations
import InfoGeometry.Algebra.KantorTripleFiveGrading

noncomputable section

namespace InfoGeometry.Canonical.H3ZornKantorTripleSystem

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Algebra.KantorTripleFiveGrading
open InfoGeometry.Canonical.H3ZornJordanTripleG2Bridge

abbrev H3 := H3Zorn ℝ

private abbrev inner (x y : H3) : Module.End ℝ H3 :=
  (h3ZornJordanInnerDerivation x y : Module.End ℝ H3)

/-- The standard Jordan triple operator splits into left multiplication by
`x*y` plus the inner derivation `[L_x,L_y]`. -/
theorem jordanTriple_eq_mul_add_inner (x y z : H3) :
    jordanTriple x y z = (x * y) * z + inner x y z := by
  change
    candidateJordanMul (candidateJordanMul x y) z +
        candidateJordanMul (candidateJordanMul z y) x -
          candidateJordanMul (candidateJordanMul x z) y =
      (x * y) * z + (x * (y * z) - y * (x * z))
  simp only [candidateJordanMul_eq_mul]
  rw [mul_comm (z * y) x, mul_comm (x * z) y]
  abel

/-- Reversing the two parameters reverses the inner Jordan derivation. -/
theorem inner_swap_apply (x y z : H3) :
    inner y x z = - inner x y z := by
  simp [inner, h3ZornJordanInnerDerivation_apply]

/-- Pointwise form of the fully linearized Jordan identity used by the triple
system.  It is the cyclic left-multiplication relation
`[L_uv,L_xy] = [L_(uv*x),L_y] - [L_x,L_(uv*y)]`.

The proof consumes Mathlib's `two_nsmul_lie_lmul_lmul_add_add_eq_zero` and
cancels the factor two over `ℝ`. -/
theorem inner_product_cyclic_relation
    (u v x y z : H3) :
    inner (u * v) (x * y) z =
      inner ((u * v) * x) y z - inner x ((u * v) * y) z := by
  have hraw :=
    two_nsmul_lie_lmul_lmul_add_add_eq_zero
      (A := H3) (u * v) x y
  have hz := congrArg (fun f : AddMonoid.End H3 => f z) hraw
  have hz' := congrArg (fun w : H3 => (1 / 2 : ℝ) • w) hz
  have hcyc :
      (u * v) * ((x * y) * z) - (x * y) * ((u * v) * z) +
          (x * ((y * (u * v)) * z) - (y * (u * v)) * (x * z)) +
          (y * (((u * v) * x) * z) - ((u * v) * x) * (y * z)) = 0 := by
    simpa [Ring.lie_def, two_nsmul, smul_smul] using hz'
  simp only [inner, h3ZornJordanInnerDerivation_apply]
  rw [mul_comm y (u * v), mul_comm y ((u * v) * x)] at hcyc
  abel_nf at hcyc ⊢
  exact hcyc

/-- Commuting two inner Jordan derivations differentiates their two
parameters.  This is the pointwise Jacobi/Leibniz law needed by the first
Freudenthal--Kantor identity. -/
theorem inner_comm_inner_apply
    (u v x y z : H3) :
    inner u v (inner x y z) - inner x y (inner u v z) =
      inner (inner u v x) y z + inner x (inner u v y) z := by
  let I := h3ZornJordanInnerDerivation u v
  have hI := I.property
  change
    (I : Module.End ℝ H3) (x * (y * z) - y * (x * z)) -
        (x * (y * (I : Module.End ℝ H3) z) -
          y * (x * (I : Module.End ℝ H3) z)) =
      ((I : Module.End ℝ H3) x) * (y * z) -
          y * (((I : Module.End ℝ H3) x) * z) +
        (x * (((I : Module.End ℝ H3) y) * z) -
          ((I : Module.End ℝ H3) y) * (x * z))
  rw [map_sub, hI x (y * z), hI y (x * z), hI y z, hI x z]
  abel

/-- **Freudenthal--Kantor first identity** for the concrete split-Albert
Jordan triple. -/
theorem jordanTriple_first_identity (u v x y z : H3) :
    jordanTriple u v (jordanTriple x y z) -
        jordanTriple x y (jordanTriple u v z) =
      jordanTriple (jordanTriple u v x) y z -
        jordanTriple x (jordanTriple v u y) z := by
  let I : Module.End ℝ H3 := inner u v
  let J : Module.End ℝ H3 := inner x y
  let P : H3 := u * v
  let Q : H3 := x * y
  have hIprod (a b : H3) : I (a * b) = I a * b + a * I b := by
    exact (h3ZornJordanInnerDerivation u v).property a b
  have hJprod (a b : H3) : J (a * b) = J a * b + a * J b := by
    exact (h3ZornJordanInnerDerivation x y).property a b
  have hPQ :
      inner P Q z = inner (P * x) y z - inner x (P * y) z := by
    simpa [P, Q] using inner_product_cyclic_relation u v x y z
  have hcomm :
      I (J z) - J (I z) = inner (I x) y z + inner x (I y) z := by
    simpa [I, J] using inner_comm_inner_apply u v x y z
  have hswapY : inner v u y = - I y := by
    simpa [I] using inner_swap_apply u v y
  calc
    jordanTriple u v (jordanTriple x y z) -
          jordanTriple x y (jordanTriple u v z) =
        P * (Q * z) - Q * (P * z) +
          (I Q) * z - (J P) * z + (I (J z) - J (I z)) := by
      rw [jordanTriple_eq_mul_add_inner,
        jordanTriple_eq_mul_add_inner,
        jordanTriple_eq_mul_add_inner,
        jordanTriple_eq_mul_add_inner]
      change
        P * (Q * z + J z) + I (Q * z + J z) -
            (Q * (P * z + I z) + J (P * z + I z)) = _
      rw [mul_add, map_add, mul_add, map_add, hIprod, hJprod]
      abel
    _ = inner P Q z + (I Q) * z - (J P) * z +
          inner (I x) y z + inner x (I y) z := by
      rw [hcomm]
      simp only [inner, h3ZornJordanInnerDerivation_apply]
      abel
    _ = inner (P * x) y z - inner x (P * y) z +
          (I Q) * z - (J P) * z +
          inner (I x) y z + inner x (I y) z := by
      rw [hPQ]
    _ = jordanTriple (jordanTriple u v x) y z -
          jordanTriple x (jordanTriple v u y) z := by
      rw [jordanTriple_eq_mul_add_inner,
        jordanTriple_eq_mul_add_inner,
        jordanTriple_eq_mul_add_inner,
        jordanTriple_eq_mul_add_inner]
      rw [hswapY]
      change
        inner (P * x) y z - inner x (P * y) z +
            (I Q) * z - (J P) * z +
            inner (I x) y z + inner x (I y) z =
          ((P * x + I x) * y) * z + inner (P * x + I x) y z -
            (x * (P * y - I y) * z + inner x (P * y - I y) z)
      rw [hIprod x y]
      simp only [inner, h3ZornJordanInnerDerivation_apply]
      rw [mul_add, add_mul, mul_sub, sub_mul]
      simp only [J, P, Q, I]
      abel

/-- **Freudenthal--Kantor second identity**.  For this Jordan triple the
Kantor `K`-operator vanishes by outer symmetry, so the second identity reduces
to trilinearity and the same outer-symmetry equation. -/
theorem jordanTriple_second_identity (u v x y z : H3) :
    jordanTriple (jordanTriple u x v - jordanTriple v x u) z y -
        jordanTriple y z (jordanTriple u x v - jordanTriple v x u) =
      jordanTriple y x (jordanTriple u z v - jordanTriple v z u) +
        (jordanTriple u (jordanTriple x y z) v -
          jordanTriple v (jordanTriple x y z) u) := by
  rw [jordanTriple_K_expression_zero u v x,
    jordanTriple_K_expression_zero u v z,
    jordanTriple_K_expression_zero u v (jordanTriple x y z)]
  simp [jordanTriple]

/-- The native split-Albert Jordan triple now satisfies the complete abstract
`KantorTripleSystem` interface. -/
noncomputable def h3KantorTripleSystem : KantorTripleSystem ℝ H3 where
  triple := jordanTriple
  triple_add_left := jordanTriple_add_left
  triple_smul_left := jordanTriple_smul_left
  triple_add_middle := jordanTriple_add_middle
  triple_smul_middle := jordanTriple_smul_middle
  triple_add_right := jordanTriple_add_right
  triple_smul_right := jordanTriple_smul_right
  first_identity := jordanTriple_first_identity
  second_identity := jordanTriple_second_identity

/-- The installed concrete Kantor triple is on the Jordan boundary: its
abstract `K` operator vanishes identically. -/
theorem h3Kantor_isJordan : h3KantorTripleSystem.IsJordan := by
  exact h3KantorTripleSystem.isJordan_of_outerSymm jordanTriple_outer_symm

/-- The generic Kantor `D` operator is exactly the concrete triple operator. -/
@[simp] theorem h3Kantor_D_eq_jordanTripleD (x y : H3) :
    h3KantorTripleSystem.D x y = jordanTripleD x y := by
  ext z
  rfl

/-- Native grade-zero closure obtained by consuming the generic first-identity
API rather than reproving the commutator calculation. -/
theorem h3Kantor_D_comm_D (u v x y : H3) :
    KantorTripleSystem.endCommutator
        (h3KantorTripleSystem.D u v) (h3KantorTripleSystem.D x y) =
      h3KantorTripleSystem.D (h3KantorTripleSystem.D u v x) y -
        h3KantorTripleSystem.D x (h3KantorTripleSystem.D v u y) := by
  exact h3KantorTripleSystem.D_comm_D u v x y

/-- The same closure theorem read directly on the previously defined concrete
triple operators. -/
theorem jordanTripleD_commutator (u v x y : H3) :
    KantorTripleSystem.endCommutator
        (jordanTripleD u v) (jordanTripleD x y) =
      jordanTripleD (jordanTriple u v x) y -
        jordanTripleD x (jordanTriple v u y) := by
  simpa [h3Kantor_D_eq_jordanTripleD] using h3Kantor_D_comm_D u v x y

end InfoGeometry.Canonical.H3ZornKantorTripleSystem
