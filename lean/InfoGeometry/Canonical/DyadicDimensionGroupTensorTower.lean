import InfoGeometry.Canonical.DyadicDimensionGroup
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.TensorTowerColimit

namespace InfoGeometry.Canonical

/-!
# The dyadic dimension system as a compatible tensor-tower diagram

The stages are copies of `ℤ`, the bonding map is multiplication by `2`, and
the stage readout is the exact dyadic rational `z / 2^n`.  This packages the
concrete construction through the existing generic finite-stage compatibility
lemmas; it does not assert a universal categorical colimit.
-/

def dyadicDouble : ℤ →ₗ[ℤ] ℤ where
  toFun z := 2 * z
  map_add' x y := by ring
  map_smul' c x := by
    simp only [smul_eq_mul, RingHom.id_apply]
    ring

def dyadicStageLinearMap (n : ℕ) : ℤ →ₗ[ℤ] DyadicRational where
  toFun := dyadicStageMap n
  map_add' x y := by
    apply Subtype.ext
    change ((x + y : ℤ) : ℚ) / (2 : ℚ) ^ n =
      (x : ℚ) / (2 : ℚ) ^ n + (y : ℚ) / (2 : ℚ) ^ n
    push_cast
    ring
  map_smul' c x := by
    apply Subtype.ext
    change ((c * x : ℤ) : ℚ) / (2 : ℚ) ^ n =
      c • ((x : ℚ) / (2 : ℚ) ^ n)
    simp only [Int.cast_mul, zsmul_eq_mul]
    have hn : (2 : ℚ) ^ n ≠ 0 := by positivity
    field_simp [hn]

theorem dyadicStageLinearMap_compat (n : ℕ) :
    (dyadicStageLinearMap (n + 1)).comp dyadicDouble =
      dyadicStageLinearMap n := by
  apply LinearMap.ext
  intro z
  simpa [LinearMap.comp_apply, dyadicDouble] using
    (dyadicStageMap_succ n z)

theorem dyadicStageLinearMap_iterated_compat (n m : ℕ) :
    (dyadicStageLinearMap (n + m)).comp
        (iota_seq (fun _ : ℕ => ℤ) (fun _ => dyadicDouble) n m) =
      dyadicStageLinearMap n := by
  exact psi_comp_iota_seq
    (A := fun _ : ℕ => ℤ)
    (iota := fun _ => dyadicDouble)
    (A_inf := DyadicRational)
    (psi := dyadicStageLinearMap)
    (psi_comm := dyadicStageLinearMap_compat)
    n m

end InfoGeometry.Canonical
