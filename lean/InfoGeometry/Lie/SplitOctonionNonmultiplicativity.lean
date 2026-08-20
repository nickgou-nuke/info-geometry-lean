import InfoGeometry.Lie.SplitOctonionImaginaryAction
import InfoGeometry.Lie.SplitOctonionCliffordAction
import InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
import InfoGeometry.Canonical.ZornVectorMatrixExplicit
import InfoGeometry.Clifford.SplitCl44CausalEnvelope

/-!
# Nonmultiplicativity Obstruction for Split-Octonion Left Multiplication

This module formalizes the exact obstruction to left multiplication preserving
the split-octonion product.

**Theorem (Nonmultiplicativity):**
There exist imaginary split octonions `X, Y` such that
`imaginaryLeftMul X * imaginaryLeftMul Y ≠ imaginaryLeftMul (X * Y)`.

The obstruction is the failure of the assignment `X ↦ L_X` to define an
algebra homomorphism from the split-octonion algebra to the associative
endomorphism algebra.
-/

noncomputable section
namespace InfoGeometry.Lie.SplitOctonionNonmultiplicativity

open InfoGeometry.Lie.SplitOctonionImaginaryAction
open InfoGeometry.Algebra.Zorn
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Canonical
open InfoGeometry.Canonical.ZornMatrix

@[simp] theorem imaginaryLeftMul_apply (X : Imaginary) (Z : CanonicalZorn) :
    imaginaryLeftMul X Z = X.1 * Z := rfl



def ex_associator : CanonicalZorn :=
  (ex_X.1 * ex_Y.1) * ex_Z.1 - ex_X.1 * (ex_Y.1 * ex_Z.1)

theorem ex_associator_ne_zero : ex_associator ≠ 0 := by
  intro h
  have h_comp := congr_arg (fun Z : CanonicalZorn => Z.a) h
  simp [ex_associator, ex_X, ex_Y, ex_Z, mul, dot, cross] at h_comp
  have h_zero : (0 : CanonicalZorn).a = 0 := rfl
  rw [h_zero] at h_comp
  norm_num at h_comp

theorem ex_prod_imaginary :
    realZornTrace (ex_X.1 * ex_Y.1) = 0 := by
  simp [ex_X, ex_Y, realZornTrace, mul, dot, cross]

/-- The nonmultiplicativity obstruction: explicit imaginary split octonions
X, Y such that the operator composition `L_X ∘ L_Y` differs from `L_{X*Y}`. -/
theorem nonmultiplicativity_obstruction :
    ∃ (X Y : Imaginary) (h : realZornTrace (X.1 * Y.1) = 0),
      imaginaryLeftMul X * imaginaryLeftMul Y ≠
      imaginaryLeftMul (⟨X.1 * Y.1, (mem_imaginary_iff (X.1 * Y.1)).mpr h⟩ : Imaginary) := by
  use ex_X, ex_Y, ex_prod_imaginary
  intro h
  have h₁ := congr_arg (fun f : Module.End ℝ CanonicalZorn => f ex_Z.1) h
  simp only [Module.End.mul_apply, imaginaryLeftMul_apply] at h₁
  have h₂ : ex_associator = 0 := by
    change (ex_X.1 * ex_Y.1) * ex_Z.1 - ex_X.1 * (ex_Y.1 * ex_Z.1) = 0
    rw [← h₁]
    simp
  exact ex_associator_ne_zero h₂

/-- Stronger form: the associator is nonzero for some triple of imaginary split octonions,
witnessing the nonassociativity of the split-octonion multiplication. -/
theorem associator_obstruction :
    ∃ (X Y Z : Imaginary),
      (X.1 * Y.1) * Z.1 ≠ X.1 * (Y.1 * Z.1) := by
  use ex_X, ex_Y, ex_Z
  intro h_eq
  have h_sub : ex_associator = 0 := sub_eq_zero.mpr h_eq
  exact ex_associator_ne_zero h_sub

/-- Concrete obstruction property using the idempotent basis:
Let e₊ = (1,0,0,0), e₋ = (0,1,0,0), u₁ = (0,0,1,0) in the Zorn model.
Then `L_{e₊} L_{e₋}` and `L_{e₊*e₋}` differ when evaluated on `ex_Z.1`. -/
theorem explicit_counterexample :
    ∃ (X Y : Imaginary) (h : realZornTrace (X.1 * Y.1) = 0),
      (imaginaryLeftMul X * imaginaryLeftMul Y) ex_Z.1 ≠
      imaginaryLeftMul (⟨X.1 * Y.1, (mem_imaginary_iff (X.1 * Y.1)).mpr h⟩ : Imaginary) ex_Z.1 := by
  use ex_X, ex_Y, ex_prod_imaginary
  intro h
  simp only [Module.End.mul_apply, imaginaryLeftMul_apply] at h
  have h₂ : ex_associator = 0 := by
    change (ex_X.1 * ex_Y.1) * ex_Z.1 - ex_X.1 * (ex_Y.1 * ex_Z.1) = 0
    rw [← h]
    simp
  exact ex_associator_ne_zero h₂

/-! ## 16D Bi-Split-Octonion Clifford Chiral Action Section -/
section BiActionSection

/--
Conjugation (involution) on the split-octonions `CanonicalZorn`.
Maps `Z = ⟨a, b, x, y⟩` to `⟨b, a, -x, -y⟩`.
-/
def zornConj (Z : CanonicalZorn) : CanonicalZorn :=
  { a := Z.b, b := Z.a, x := -Z.x, y := -Z.y }

/--
The 16-dimensional representation space of Bi-Split-Octonions,
isomorphic to the Cl(4,4) spinor module S_+ ⊕ S_-.
-/
abbrev BiSplitOctonions := CanonicalZorn × CanonicalZorn

/--
Chiral Clifford action of a split-octonion `Z` on the 16D BiSplitOctonions,
mapping `(p, q) ↦ (Z * q, - (zornConj Z * p))`.
-/
def zornBiAction (Z : CanonicalZorn) (pq : BiSplitOctonions) : BiSplitOctonions :=
  (Z * pq.2, - (zornConj Z * pq.1))

/--
**The Clifford Square Law on Bi-Split-Octonions:**
Proves natively that the chiral action of any Zorn matrix Z squares to the scalar
value given by the negative determinant.
-/
@[simp] theorem mul_neg (Z W : CanonicalZorn) : Z * (-W) = - (Z * W) := by
  refine ZornMatrix.ext ?_ ?_ (funext fun i => ?_) (funext fun i => ?_)
  · dsimp [mul, dot, cross]; ring
  · dsimp [mul, dot, cross]; ring
  · fin_cases i <;> { dsimp [mul, dot, cross]; ring }
  · fin_cases i <;> { dsimp [mul, dot, cross]; ring }

@[simp] theorem neg_mul (Z W : CanonicalZorn) : (-Z) * W = - (Z * W) := by
  refine ZornMatrix.ext ?_ ?_ (funext fun i => ?_) (funext fun i => ?_)
  · dsimp [mul, dot, cross]; ring
  · dsimp [mul, dot, cross]; ring
  · fin_cases i <;> { dsimp [mul, dot, cross]; ring }
  · fin_cases i <;> { dsimp [mul, dot, cross]; ring }

theorem zorn_mul_conj_mul (Z W : CanonicalZorn) :
    Z * (zornConj Z * W) = ZornMatrix.detZ Z • W := by
  rcases Z with ⟨Za, Zb, Zx, Zy⟩
  rcases W with ⟨Wa, Wb, Wx, Wy⟩
  refine ZornMatrix.ext ?_ ?_ (funext fun i => ?_) (funext fun i => ?_)
  · dsimp [zornConj, ZornMatrix.detZ, mul, dot, cross]; ring
  · dsimp [zornConj, ZornMatrix.detZ, mul, dot, cross]; ring
  · fin_cases i <;> { dsimp [zornConj, ZornMatrix.detZ, mul, dot, cross]; ring }
  · fin_cases i <;> { dsimp [zornConj, ZornMatrix.detZ, mul, dot, cross]; ring }

theorem zornConj_mul_zorn_mul (Z W : CanonicalZorn) :
    zornConj Z * (Z * W) = ZornMatrix.detZ Z • W := by
  rcases Z with ⟨Za, Zb, Zx, Zy⟩
  rcases W with ⟨Wa, Wb, Wx, Wy⟩
  refine ZornMatrix.ext ?_ ?_ (funext fun i => ?_) (funext fun i => ?_)
  · dsimp [zornConj, ZornMatrix.detZ, mul, dot, cross]; ring
  · dsimp [zornConj, ZornMatrix.detZ, mul, dot, cross]; ring
  · fin_cases i <;> { dsimp [zornConj, ZornMatrix.detZ, mul, dot, cross]; ring }
  · fin_cases i <;> { dsimp [zornConj, ZornMatrix.detZ, mul, dot, cross]; ring }

/--
**The Clifford Square Law on Bi-Split-Octonions:**
Proves natively that the chiral action of any Zorn matrix Z squares to the scalar
value given by the negative determinant.
-/
theorem zornBiAction_sq (Z : CanonicalZorn) (pq : BiSplitOctonions) :
    zornBiAction Z (zornBiAction Z pq) = - ZornMatrix.detZ Z • pq := by
  refine Prod.ext ?_ ?_
  · change Z * -(zornConj Z * pq.1) = (-ZornMatrix.detZ Z) • pq.1
    rw [mul_neg, zorn_mul_conj_mul, neg_smul]
  · change -(zornConj Z * (Z * pq.2)) = (-ZornMatrix.detZ Z) • pq.2
    rw [zornConj_mul_zorn_mul, neg_smul]

end BiActionSection

/-! ## Clifford stage-4 matching section -/
section CliffordSection

open InfoGeometry.Clifford.SplitCl44CausalEnvelope
open InfoGeometry.Clifford.ClNNBilinear
open InfoGeometry.CliffordTower

/--
Explicit linear equivalence between the 8D Zorn split-octonion carrier `CanonicalZorn`
and the Cl(4,4) vector representation space `SplitCl44Carrier`.
-/
def e : CanonicalZorn ≃ₗ[ℝ] SplitCl44Carrier where
  toFun Z := (
    ((Z.a - Z.b)/2, (Z.a + Z.b)/2),
    ((Z.x 0 + Z.y 0)/2, (Z.x 0 - Z.y 0)/2),
    ((Z.x 1 + Z.y 1)/2, (Z.x 1 - Z.y 1)/2),
    ((Z.x 2 + Z.y 2)/2, (Z.x 2 - Z.y 2)/2),
    fun i => Fin.elim0 i
  )
  invFun v := {
    a := v.1.1 + v.1.2
    b := v.1.2 - v.1.1
    x := ![v.2.1.1 + v.2.1.2, v.2.2.1.1 + v.2.2.1.2, v.2.2.2.1.1 + v.2.2.2.1.2]
    y := ![v.2.1.1 - v.2.1.2, v.2.2.1.1 - v.2.2.1.2, v.2.2.2.1.1 - v.2.2.2.1.2]
  }
  map_add' Z W := by
    dsimp
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
    · ext <;> { dsimp; ring }
    · ext <;> { dsimp; ring }
    · ext <;> { dsimp; ring }
    · ext <;> { dsimp; ring }
    · funext i; exact Fin.elim0 i
  map_smul' r Z := by
    dsimp
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
    · ext <;> { dsimp; ring }
    · ext <;> { dsimp; ring }
    · ext <;> { dsimp; ring }
    · ext <;> { dsimp; ring }
    · funext i; exact Fin.elim0 i
  left_inv Z := by
    rcases Z with ⟨a, b, x, y⟩
    dsimp
    refine ZornMatrix.ext ?_ ?_ (funext fun i => ?_) (funext fun i => ?_)
    · ring
    · ring
    · fin_cases i <;> { dsimp; ring }
    · fin_cases i <;> { dsimp; ring }
  right_inv v := by
    rcases v with ⟨⟨t0, s0⟩, ⟨t1, s1⟩, ⟨t2, s2⟩, ⟨t3, s3⟩, f⟩
    dsimp
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
    · ext <;> { dsimp; ring }
    · ext <;> { dsimp; ring }
    · ext <;> { dsimp; ring }
    · ext <;> { dsimp; ring }
    · funext i; exact Fin.elim0 i

/--
Global compatibility showing that the pullback of the hyperbolic signature (4,4) quadratic form
coincides with the negative determinant form on all of `CanonicalZorn`.
-/
theorem splitCl44Quad_compat_global (Z : CanonicalZorn) :
    SplitCl44Quad (e Z) = -ZornMatrix.detZ Z := by
  dsimp [e, SplitCl44Quad, InfoGeometry.Clifford.ClNNBilinear.hyperbolicQuadratic, ZornMatrix.detZ, dot]
  rw [Qsplit_succ_apply 3, Qsplit_succ_apply 2, Qsplit_succ_apply 1, Qsplit_succ_apply 0, Qsplit_zero_apply]
  rw [CliffordTower.Q11_apply, CliffordTower.Q11_apply, CliffordTower.Q11_apply, CliffordTower.Q11_apply]
  dsimp [InfoGeometry.Clifford.splitQ11]
  ring

/--
Compatibility on the 7D imaginary split-octonion subspace: the Clifford quadratic form matches
the hyperbolic form on the embedded subspace.
-/
theorem splitCl44Quad_compat (X : Imaginary) :
    leftCliffordQuadratic X = SplitCl44Quad (e X.1) := by
  rw [leftCliffordQuadratic_eq_neg_det, splitCl44Quad_compat_global]

end CliffordSection

end InfoGeometry.Lie.SplitOctonionNonmultiplicativity
