import InfoGeometry.OperatorAlgebra.PeirceSpine.BlockCharges

/-!
# Orthogonal projections onto the five supported components

The projections act on the full integer-linear endomorphism ring. Their
orthogonality comes from Peirce supports, independently of characteristic.
-/
namespace InfoGeometry.OperatorAlgebra.PeirceSpine
variable {B : Type*} [Ring B]

private theorem block_add (P : B) (i j : Fin 3) (K L : Module.End ℤ B) :
    endomorphismBlock P i j (K + L) =
      endomorphismBlock P i j K + endomorphismBlock P i j L := by
  simp only [endomorphismBlock, mul_add, add_mul]

private theorem block_smul (P : B) (i j : Fin 3) (n : ℤ) (K : Module.End ℤ B) :
    endomorphismBlock P i j (n • K) = n • endomorphismBlock P i j K := by
  simp only [endomorphismBlock, mul_smul_comm, smul_mul_assoc]

/-- The support-defined component is a native linear projection candidate. -/
def supportedProjector (P : B) (d : Fin 5) : Module.End ℤ (Module.End ℤ B) where
  toFun K := fiveSupportedComponent P K d
  map_add' K L := by
    fin_cases d <;> simp [fiveSupportedComponent, block_add] <;> abel
  map_smul' n K := by
    fin_cases d <;> dsimp [fiveSupportedComponent] <;>
      simp only [block_smul, smul_add]

@[simp] theorem supportedProjector_apply (P : B) (d : Fin 5) (K : Module.End ℤ B) :
    supportedProjector P d K = fiveSupportedComponent P K d := rfl

/-- Distinct support degrees are orthogonal even when their integer charges coincide. -/
theorem supportedProjector_extract {P : B} (hP : P * P = P)
    (d e : Fin 5) (K : Module.End ℤ B) :
    supportedProjector P d (supportedProjector P e K) =
      if d = e then supportedProjector P d K else 0 := by
  simp only [supportedProjector_apply]
  fin_cases d <;> fin_cases e <;>
    simp [fiveSupportedComponent, block_add, endomorphismBlock_extract hP]

theorem supportedProjector_mul {P : B} (hP : P * P = P) (d e : Fin 5) :
    supportedProjector P d * supportedProjector P e =
      if d = e then supportedProjector P d else 0 := by
  apply LinearMap.ext
  intro K
  by_cases h : d = e <;>
    simpa only [Module.End.mul_apply, h, ite_true, ite_false, LinearMap.zero_apply] using
      supportedProjector_extract hP d e K

theorem supportedProjector_idempotent {P : B} (hP : P * P = P) (d : Fin 5) :
    supportedProjector P d * supportedProjector P d = supportedProjector P d := by
  simpa only [ite_true] using supportedProjector_mul hP d d

theorem supportedProjector_sum (P : B) :
    ∑ d, supportedProjector P d = 1 := by
  apply LinearMap.ext
  intro K
  simpa only [LinearMap.sum_apply, supportedProjector_apply, Module.End.one_apply] using
    fiveSupportedComponent_sum P K

/-- A decomposition into fixed supported components is uniquely determined. -/
theorem supportedProjector_unique {P : B} (hP : P * P = P)
    (F : Fin 5 → Module.End ℤ B)
    (hF : ∀ d, supportedProjector P d (F d) = F d) (d : Fin 5) :
    supportedProjector P d (∑ e, F e) = F d := by
  rw [map_sum]
  have hextract (e : Fin 5) :
      supportedProjector P d (F e) = if d = e then F d else 0 := by
    rw [← hF e, supportedProjector_extract hP]
    by_cases h : d = e
    · subst e
      simp [hF]
    · simp [h]
  simp_rw [hextract]
  simp

end InfoGeometry.OperatorAlgebra.PeirceSpine
