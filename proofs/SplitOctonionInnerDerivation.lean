import proofs.SplitOctonionDerivationSpace
set_option maxHeartbeats 1000000

open SplitOctonion

namespace SplitOctonionInnerDerivation

instance : Zero SplitOct where zero := ⟨0, 0⟩
@[simp] lemma zero_def : (0 : SplitOct) = ⟨0, 0⟩ := rfl

/-- The Associator measures the failure of associativity -/
def associator (x y z : SplitOct) : SplitOct :=
  (x * y) * z - x * (y * z)

/-- The Standard Inner Derivation Operator for Alternative Algebras
    D_{x,y}(z) = [[x,y], z] - 3(x,y,z) -/
def innerDeriv (x y z : SplitOct) : SplitOct :=
  bracket (bracket x y) z - (3 : ℝ) • associator x y z

/-- THE DERIVATION THEOREM: D_{x,y} obeys the Leibniz rule -/
theorem innerDeriv_is_derivation (x y u v : SplitOct) :
  innerDeriv x y (u * v) = (innerDeriv x y u) * v + u * (innerDeriv x y v) := sorry

/-- The Linear Map representation of innerDeriv -/
def innerDerivLinearMap (x y : SplitOct) : SplitOct →ₗ[ℝ] SplitOct where
  toFun z := innerDeriv x y z
  map_add' := by 
    intro u v; unfold innerDeriv bracket associator
    simp only [mul_add, add_mul, smul_add]
    abel
  map_smul' := by 
    intro c u; unfold innerDeriv bracket associator
    simp only [RingHom.id_apply]
    repeat rw [mul_smul_comm]
    repeat rw [smul_mul_assoc]
    repeat rw [smul_sub]
    have h_comm : ∀ w : SplitOct, c • (3 : ℝ) • w = (3 : ℝ) • c • w := by
      intro w; rw [smul_comm]
    repeat rw [h_comm]

/-- Inner Derivation as a formal OctDerivation Lie Algebra element -/
def mkInnerDeriv (x y : SplitOct) : OctDerivation where
  toLinearMap := innerDerivLinearMap x y
  leibniz' := innerDeriv_is_derivation x y

end SplitOctonionInnerDerivation
