import InfoGeometry.Lie.SplitOctonionImaginaryAction
import InfoGeometry.Lie.SplitOctonionCliffordAction
import InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
import InfoGeometry.Canonical.ZornVectorMatrixExplicit
import InfoGeometry.Clifford.SplitCl44CausalEnvelope

noncomputable section
namespace InfoGeometry.Lie.SplitOctonionNonmultiplicativity

open InfoGeometry.Lie.SplitOctonionImaginaryAction
open InfoGeometry.Algebra.Zorn
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Canonical
open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Clifford.SplitCl44CausalEnvelope
open InfoGeometry.CliffordTower

def e : CanonicalZorn ≃ₗ[ℝ] SplitCl44Carrier where
  toFun Z := (
    ((Z.a - Z.b)/2, (Z.a + Z.b)/2),
    ((Z.x 0 + Z.y 0)/2, (Z.x 0 - Z.y 0)/2),
    ((Z.x 1 + Z.y 1)/2, (Z.x 1 - Z.y 1)/2),
    ((Z.x 2 + Z.y 2)/2, (Z.x 2 - Z.y 2)/2),
    fun _ => (0, 0)
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
    · apply Prod.ext <;> { dsimp; ring }
    · apply Prod.ext <;> { dsimp; ring }
    · apply Prod.ext <;> { dsimp; ring }
    · apply Prod.ext <;> { dsimp; ring }
    · ext i <;> { nomatch i }
  map_smul' r Z := by
    dsimp
    have h_a : (r • Z).a = r * Z.a := rfl
    have h_b : (r • Z).b = r * Z.b := rfl
    have h_x : (r • Z).x = r • Z.x := rfl
    have h_y : (r • Z).y = r • Z.y := rfl
    rw [h_a, h_b, h_x, h_y]
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
    · apply Prod.ext <;> { dsimp; ring }
    · apply Prod.ext <;> { dsimp; ring }
    · apply Prod.ext <;> { dsimp; ring }
    · apply Prod.ext <;> { dsimp; ring }
    · ext i <;> { nomatch i }
  left_inv Z := by
    rcases Z with ⟨a, b, x, y⟩
    dsimp
    ext1
    · ring
    · ring
    · ext i
      fin_cases i <;> { dsimp; ring }
    · ext i
      fin_cases i <;> { dsimp; ring }
  right_inv v := by
    rcases v with ⟨⟨t0, s0⟩, ⟨t1, s1⟩, ⟨t2, s2⟩, ⟨t3, s3⟩, f⟩
    dsimp
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
    · apply Prod.ext <;> { dsimp; ring }
    · apply Prod.ext <;> { dsimp; ring }
    · apply Prod.ext <;> { dsimp; ring }
    · apply Prod.ext <;> { dsimp; ring }
    · ext i <;> { nomatch i }

theorem splitCl44Quad_compat_global (Z : CanonicalZorn) :
    SplitCl44Quad (e Z) = -ZornMatrix.detZ realCrossProduct3 Z := by
  dsimp [e, SplitCl44Quad, InfoGeometry.Clifford.ClNNBilinear.hyperbolicQuadratic, ZornMatrix.detZ, realCrossProduct3, dot]
  rw [Qsplit_succ_apply 3, Qsplit_succ_apply 2, Qsplit_succ_apply 1, Qsplit_succ_apply 0, Qsplit_zero_apply]
  rw [CliffordTower.Q11_apply, CliffordTower.Q11_apply, CliffordTower.Q11_apply, CliffordTower.Q11_apply]
  ring

theorem splitCl44Quad_compat (X : Imaginary) :
    leftCliffordQuadratic X = SplitCl44Quad (e X.1) := by
  rw [leftCliffordQuadratic_eq_neg_det, splitCl44Quad_compat_global]

/-- Spinor representation placeholder representing open closure debt. -/
noncomputable def spinorRep : SplitCl44Algebra →ₐ[ℝ] Module.End ℝ SplitCl44Carrier := sorry

/-- Clifford embedding placeholder representing open closure debt. -/
def cliffordIota : SplitCl44Carrier →ₗ[ℝ] SplitCl44Algebra :=
  CliffordAlgebra.ι SplitCl44Quad

theorem split_octonion_pseudoReal_matches_Cl44_spinor :
  ∃ (e : CanonicalZorn ≃ₗ[ℝ] SplitCl44Carrier),
    (∀ (X : Imaginary), leftCliffordQuadratic X = SplitCl44Quad (e X)) ∧
    (∀ (X : Imaginary), (e ∘ₗ imaginaryLeftMul X ∘ₗ e.symm) = spinorRep (cliffordIota (e X))) ∧
    (Set.range (e ∘ (Subtype.val : Imaginary → CanonicalZorn)) = {v : SplitCl44Carrier | SplitCl44Quad v = 0 ∧ v ≠ 0}) := by
  use e
  refine ⟨splitCl44Quad_compat, ?_, ?_⟩
  · sorry
  · sorry

end InfoGeometry.Lie.SplitOctonionNonmultiplicativity
