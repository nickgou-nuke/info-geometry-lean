import InfoGeometry.Exceptional.FreudenthalGenericJacobiClosure
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Exceptional.FreudenthalFiveGradedBracketScalarBilinearity
import InfoGeometry.Exceptional.FreudenthalJacobiLaneFiniteReconstruction
import InfoGeometry.Exceptional.FreudenthalFiveGradedExtremeJacobi
import InfoGeometry.Exceptional.FreudenthalFiveGradedExtremeDualJacobi
import InfoGeometry.Exceptional.FreudenthalExtremeJacobiCells

/-!
# Bilinear carrier for the global Jacobi frontier

This is the exact reduction frontier for the Freudenthal carrier.  The
homogeneous cells remain hypotheses: this file does not manufacture the
missing cells or install a Lie-algebra instance prematurely.
-/

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

/-- The bracket, packaged as the bilinear map required by the generic
Leibniz-decomposition theorem. -/
def fiveGradedBracketBilinear :
    FiveGradedCarrier D →ₗ[ℝ] FiveGradedCarrier D →ₗ[ℝ] FiveGradedCarrier D :=
  LinearMap.mk₂ ℝ (fiveGradedBracket D)
    (fiveGradedBracket_add_left D)
    (fiveGradedBracket_smul_left D)
    (fiveGradedBracket_add_right D)
    (fiveGradedBracket_smul_right D)

theorem fiveGradedBracketBilinear_apply (u v : FiveGradedCarrier D) :
    fiveGradedBracketBilinear D u v = fiveGradedBracket D u v := rfl

theorem sum_lanePartLinear (x : FiveGradedCarrier D) :
    (∑ lane : JacobiLane, lanePartLinear D lane x) = x := by
  classical
  have huniv : (Finset.univ : Finset JacobiLane) =
      {.minus2, .minus1, .zeroSymp, .zeroScale, .plus1, .plus2} := by
    ext lane
    cases lane <;> simp
  rw [huniv]
  simp only [lanePartLinear_apply]
  simpa [Finset.sum_insert, add_assoc] using sum_lanePart D x

theorem leibnizDefect_bracket_eq_jacobiator (u v w : FiveGradedCarrier D) :
    leibnizDefect (fiveGradedBracketBilinear D) u v w = fiveJacobiator D u v w := by
  dsimp [leibnizDefect, fiveJacobiator, fiveGradedBracketBilinear]
  rw [sub_eq_add_neg, sub_eq_add_neg]
  rw [fiveGradedBracket_skew D v w, fiveGradedBracket_skew D u v,
    fiveGradedBracket_skew D u w]
  have hA := fiveGradedBracket_smul_right D (-1) u (fiveGradedBracket D w v)
  have hB := fiveGradedBracket_smul_left D (-1) (fiveGradedBracket D v u) w
  have hC := fiveGradedBracket_smul_right D (-1) v (fiveGradedBracket D w u)
  have hA' : fiveGradedBracket D u (-fiveGradedBracket D w v) =
      -fiveGradedBracket D u (fiveGradedBracket D w v) := by simpa using hA
  have hB' : fiveGradedBracket D (-fiveGradedBracket D v u) w =
      -fiveGradedBracket D (fiveGradedBracket D v u) w := by simpa using hB
  have hC' : fiveGradedBracket D v (-fiveGradedBracket D w u) =
      -fiveGradedBracket D v (fiveGradedBracket D w u) := by simpa using hC
  have hD := fiveGradedBracket_smul_right D (-1) w (fiveGradedBracket D v u)
  have hD' : fiveGradedBracket D w (-fiveGradedBracket D v u) =
      -fiveGradedBracket D w (fiveGradedBracket D v u) := by simpa using hD
  rw [hA', hB', hC']
  rw [hD', fiveGradedBracket_skew D w (fiveGradedBracket D v u)]
  abel

theorem fiveJacobiator_add_left (u u' v w : FiveGradedCarrier D) :
    fiveJacobiator D (u + u') v w =
      fiveJacobiator D u v w + fiveJacobiator D u' v w := by
  dsimp [fiveJacobiator]
  simp only [fiveGradedBracket_add_left, fiveGradedBracket_add_right]
  abel

theorem fiveJacobiator_add_mid (u v v' w : FiveGradedCarrier D) :
    fiveJacobiator D u (v + v') w =
      fiveJacobiator D u v w + fiveJacobiator D u v' w := by
  dsimp [fiveJacobiator]
  simp only [fiveGradedBracket_add_left, fiveGradedBracket_add_right]
  abel

theorem fiveJacobiator_add_right (u v w w' : FiveGradedCarrier D) :
    fiveJacobiator D u v (w + w') =
      fiveJacobiator D u v w + fiveJacobiator D u v w' := by
  dsimp [fiveJacobiator]
  simp only [fiveGradedBracket_add_left, fiveGradedBracket_add_right]
  abel

theorem fiveJacobiator_smul_left (c : ℝ) (u v w : FiveGradedCarrier D) :
    fiveJacobiator D (c • u) v w = c • fiveJacobiator D u v w := by
  dsimp [fiveJacobiator]
  simp only [fiveGradedBracket_smul_left, fiveGradedBracket_smul_right,
    smul_add]

theorem fiveJacobiator_smul_mid (c : ℝ) (u v w : FiveGradedCarrier D) :
    fiveJacobiator D u (c • v) w = c • fiveJacobiator D u v w := by
  dsimp [fiveJacobiator]
  simp only [fiveGradedBracket_smul_left, fiveGradedBracket_smul_right,
    smul_add]

theorem fiveJacobiator_smul_right (c : ℝ) (u v w : FiveGradedCarrier D) :
    fiveJacobiator D u v (c • w) = c • fiveJacobiator D u v w := by
  dsimp [fiveJacobiator]
  simp only [fiveGradedBracket_smul_left, fiveGradedBracket_smul_right,
    smul_add]

theorem projected_jacobi_zeroScale_zeroScale_minus2
    (x y z : FiveGradedCarrier D) :
    fiveJacobiator D (lanePartLinear D .zeroScale x)
      (lanePartLinear D .zeroScale y) (lanePartLinear D .minus2 z) = 0 := by
  have hx : lanePartLinear D .zeroScale x = x.zero_scale • genHscale D 1 := by
    apply FiveGradedCarrier.ext <;> simp [lanePartLinear, lanePart, genHscale]
  have hy : lanePartLinear D .zeroScale y = y.zero_scale • genHscale D 1 := by
    apply FiveGradedCarrier.ext <;> simp [lanePartLinear, lanePart, genHscale]
  have hz : lanePartLinear D .minus2 z = z.minus2 • genEminus D 1 := by
    apply FiveGradedCarrier.ext <;> simp [lanePartLinear, lanePart, genEminus]
  rw [hx, hy, hz, fiveJacobiator_smul_left, fiveJacobiator_smul_mid,
    fiveJacobiator_smul_right]
  simp only [jacobi_scale_scale_extremeMinus, smul_zero]

theorem projected_jacobi_zeroScale_zeroScale_plus2
    (x y z : FiveGradedCarrier D) :
    fiveJacobiator D (lanePartLinear D .zeroScale x)
      (lanePartLinear D .zeroScale y) (lanePartLinear D .plus2 z) = 0 := by
  have hx : lanePartLinear D .zeroScale x = x.zero_scale • genHscale D 1 := by
    apply FiveGradedCarrier.ext <;> simp [lanePartLinear, lanePart, genHscale]
  have hy : lanePartLinear D .zeroScale y = y.zero_scale • genHscale D 1 := by
    apply FiveGradedCarrier.ext <;> simp [lanePartLinear, lanePart, genHscale]
  have hz : lanePartLinear D .plus2 z = z.plus2 • genEplus D 1 := by
    apply FiveGradedCarrier.ext <;> simp [lanePartLinear, lanePart, genEplus]
  rw [hx, hy, hz, fiveJacobiator_smul_left, fiveJacobiator_smul_mid,
    fiveJacobiator_smul_right]
  simp only [jacobi_scale_scale_extremePlus, smul_zero]

theorem projected_jacobi_zeroScale_zeroScale_minus1
    (x y z : FiveGradedCarrier D) :
    fiveJacobiator D (lanePartLinear D .zeroScale x)
      (lanePartLinear D .zeroScale y) (lanePartLinear D .minus1 z) = 0 := by
  have hx : lanePartLinear D .zeroScale x = x.zero_scale • genHscale D 1 := by
    apply FiveGradedCarrier.ext <;> simp [lanePartLinear, lanePart, genHscale]
  have hy : lanePartLinear D .zeroScale y = y.zero_scale • genHscale D 1 := by
    apply FiveGradedCarrier.ext <;> simp [lanePartLinear, lanePart, genHscale]
  rw [hx, hy, fiveJacobiator_smul_left, fiveJacobiator_smul_mid]
  simpa [lanePartLinear_apply, lanePart, injChargeMinus] using
    congrArg (fun q : FiveGradedCarrier D => x.zero_scale • (y.zero_scale • q))
      (jacobi_scale_scale_chargeMinus D z.minus1)

theorem projected_jacobi_zeroScale_zeroScale_plus1
    (x y z : FiveGradedCarrier D) :
    fiveJacobiator D (lanePartLinear D .zeroScale x)
      (lanePartLinear D .zeroScale y) (lanePartLinear D .plus1 z) = 0 := by
  have hx : lanePartLinear D .zeroScale x = x.zero_scale • genHscale D 1 := by
    apply FiveGradedCarrier.ext <;> simp [lanePartLinear, lanePart, genHscale]
  have hy : lanePartLinear D .zeroScale y = y.zero_scale • genHscale D 1 := by
    apply FiveGradedCarrier.ext <;> simp [lanePartLinear, lanePart, genHscale]
  rw [hx, hy, fiveJacobiator_smul_left, fiveJacobiator_smul_mid]
  simpa [lanePartLinear_apply, lanePart, injChargePlus] using
    congrArg (fun q : FiveGradedCarrier D => x.zero_scale • (y.zero_scale • q))
      (jacobi_scale_scale_chargePlus D z.plus1)

theorem projected_jacobi_zeroScale_zeroScale_zeroSymp
    (x y z : FiveGradedCarrier D) :
    fiveJacobiator D (lanePartLinear D .zeroScale x)
      (lanePartLinear D .zeroScale y) (lanePartLinear D .zeroSymp z) = 0 := by
  have hx : lanePartLinear D .zeroScale x = x.zero_scale • genHscale D 1 := by
    apply FiveGradedCarrier.ext <;> simp [lanePartLinear, lanePart, genHscale]
  have hy : lanePartLinear D .zeroScale y = y.zero_scale • genHscale D 1 := by
    apply FiveGradedCarrier.ext <;> simp [lanePartLinear, lanePart, genHscale]
  rw [hx, hy, fiveJacobiator_smul_left, fiveJacobiator_smul_mid]
  simpa [lanePartLinear_apply, lanePart, injSympZero] using
    congrArg (fun q : FiveGradedCarrier D => x.zero_scale • (y.zero_scale • q))
      (jacobi_scale_scale_sympZero D ⟨z.zero_symp, by
        intro X Y
        exact z.zero_symp.property X Y⟩)

theorem projected_jacobi_zeroScale_zeroScale_zeroScale
    (x y z : FiveGradedCarrier D) :
    fiveJacobiator D (lanePartLinear D .zeroScale x)
      (lanePartLinear D .zeroScale y) (lanePartLinear D .zeroScale z) = 0 := by
  have hx : lanePartLinear D .zeroScale x = x.zero_scale • genHscale D 1 := by
    apply FiveGradedCarrier.ext <;> simp [lanePartLinear, lanePart, genHscale]
  have hy : lanePartLinear D .zeroScale y = y.zero_scale • genHscale D 1 := by
    apply FiveGradedCarrier.ext <;> simp [lanePartLinear, lanePart, genHscale]
  have hz : lanePartLinear D .zeroScale z = z.zero_scale • genHscale D 1 := by
    apply FiveGradedCarrier.ext <;> simp [lanePartLinear, lanePart, genHscale]
  rw [hx, hy, hz, fiveJacobiator_smul_left, fiveJacobiator_smul_mid,
    fiveJacobiator_smul_right]
  rw [fiveJacobiator_diagonal]
  simp

theorem projected_jacobi_zeroScale_minus2_plus1
    (x y z : FiveGradedCarrier D) :
    fiveJacobiator D (lanePartLinear D .zeroScale x)
      (lanePartLinear D .minus2 y) (lanePartLinear D .plus1 z) = 0 := by
  have hx : lanePartLinear D .zeroScale x = x.zero_scale • genHscale D 1 := by
    apply FiveGradedCarrier.ext <;> simp [lanePartLinear, lanePart, genHscale]
  have hy : lanePartLinear D .minus2 y = y.minus2 • genEminus D 1 := by
    apply FiveGradedCarrier.ext <;> simp [lanePartLinear, lanePart, genEminus]
  rw [hx, hy, fiveJacobiator_smul_left, fiveJacobiator_smul_mid]
  simpa [lanePartLinear_apply, lanePart, injChargePlus] using
    congrArg (fun q : FiveGradedCarrier D => x.zero_scale • (y.minus2 • q))
      (jacobi_scale_extremeMinus_chargePlus D 1 1 z.plus1)

theorem projected_jacobi_zeroScale_plus2_minus1
    (x y z : FiveGradedCarrier D) :
    fiveJacobiator D (lanePartLinear D .zeroScale x)
      (lanePartLinear D .plus2 y) (lanePartLinear D .minus1 z) = 0 := by
  have hx : lanePartLinear D .zeroScale x = x.zero_scale • genHscale D 1 := by
    apply FiveGradedCarrier.ext <;> simp [lanePartLinear, lanePart, genHscale]
  have hy : lanePartLinear D .plus2 y = y.plus2 • genEplus D 1 := by
    apply FiveGradedCarrier.ext <;> simp [lanePartLinear, lanePart, genEplus]
  rw [hx, hy, fiveJacobiator_smul_left, fiveJacobiator_smul_mid]
  simpa [lanePartLinear_apply, lanePart, injChargeMinus] using
    congrArg (fun q : FiveGradedCarrier D => x.zero_scale • (y.plus2 • q))
      (jacobi_scale_extremePlus_chargeMinus D 1 1 z.minus1)

theorem projected_jacobi_zeroScale_zeroSymp_minus1
    (x y z : FiveGradedCarrier D) :
    fiveJacobiator D (lanePartLinear D .zeroScale x)
      (lanePartLinear D .zeroSymp y) (lanePartLinear D .minus1 z) = 0 := by
  have hx : lanePartLinear D .zeroScale x = x.zero_scale • genHscale D 1 := by
    apply FiveGradedCarrier.ext <;> simp [lanePartLinear, lanePart, genHscale]
  have hy : lanePartLinear D .zeroSymp y = injSympZero D ⟨y.zero_symp, by
    intro X Y
    exact y.zero_symp.property X Y⟩ := by rfl
  rw [hx, hy, fiveJacobiator_smul_left]
  simpa [lanePartLinear_apply, lanePart, injChargeMinus] using
    congrArg (fun q : FiveGradedCarrier D => x.zero_scale • q)
      (jacobi_scale_sympZero_chargeMinus D 1 ⟨y.zero_symp, by
        intro X Y
        exact y.zero_symp.property X Y⟩ z.minus1)

theorem projected_jacobi_zeroScale_zeroSymp_plus1
    (x y z : FiveGradedCarrier D) :
    fiveJacobiator D (lanePartLinear D .zeroScale x)
      (lanePartLinear D .zeroSymp y) (lanePartLinear D .plus1 z) = 0 := by
  have hx : lanePartLinear D .zeroScale x = x.zero_scale • genHscale D 1 := by
    apply FiveGradedCarrier.ext <;> simp [lanePartLinear, lanePart, genHscale]
  have hy : lanePartLinear D .zeroSymp y = injSympZero D ⟨y.zero_symp, by
    intro X Y
    exact y.zero_symp.property X Y⟩ := by rfl
  rw [hx, hy, fiveJacobiator_smul_left]
  simpa [lanePartLinear_apply, lanePart, injChargePlus] using
    congrArg (fun q : FiveGradedCarrier D => x.zero_scale • q)
      (jacobi_scale_sympZero_chargePlus D 1 ⟨y.zero_symp, by
        intro X Y
        exact y.zero_symp.property X Y⟩ z.plus1)

theorem projected_jacobi_zeroScale_minus2_plus2
    (x y z : FiveGradedCarrier D) :
    fiveJacobiator D (lanePartLinear D .zeroScale x)
      (lanePartLinear D .minus2 y) (lanePartLinear D .plus2 z) = 0 := by
  have hx : lanePartLinear D .zeroScale x = x.zero_scale • genHscale D 1 := by
    apply FiveGradedCarrier.ext <;> simp [lanePartLinear, lanePart, genHscale]
  have hy : lanePartLinear D .minus2 y = y.minus2 • genEminus D 1 := by
    apply FiveGradedCarrier.ext <;> simp [lanePartLinear, lanePart, genEminus]
  have hz : lanePartLinear D .plus2 z = z.plus2 • genEplus D 1 := by
    apply FiveGradedCarrier.ext <;> simp [lanePartLinear, lanePart, genEplus]
  rw [hx, hy, hz, fiveJacobiator_smul_left, fiveJacobiator_smul_mid,
    fiveJacobiator_smul_right]
  simpa using congrArg (fun q : FiveGradedCarrier D =>
    x.zero_scale • (y.minus2 • (z.plus2 • q)))
    (jacobi_scale_extremeMinus_extremePlus D 1 1 1)

theorem projected_jacobi_zeroScale_plus2_minus2
    (x y z : FiveGradedCarrier D) :
    fiveJacobiator D (lanePartLinear D .zeroScale x)
      (lanePartLinear D .plus2 y) (lanePartLinear D .minus2 z) = 0 := by
  have hx : lanePartLinear D .zeroScale x = x.zero_scale • genHscale D 1 := by
    apply FiveGradedCarrier.ext <;> simp [lanePartLinear, lanePart, genHscale]
  have hy : lanePartLinear D .plus2 y = y.plus2 • genEplus D 1 := by
    apply FiveGradedCarrier.ext <;> simp [lanePartLinear, lanePart, genEplus]
  have hz : lanePartLinear D .minus2 z = z.minus2 • genEminus D 1 := by
    apply FiveGradedCarrier.ext <;> simp [lanePartLinear, lanePart, genEminus]
  rw [hx, hy, hz, fiveJacobiator_smul_left, fiveJacobiator_smul_mid,
    fiveJacobiator_smul_right]
  simpa using congrArg (fun q : FiveGradedCarrier D =>
    x.zero_scale • (y.plus2 • (z.minus2 • q)))
    (jacobi_scale_extremePlus_extremeMinus D 1 1 1)

theorem projected_jacobi_minus2_plus2_plus2
    (x y z : FiveGradedCarrier D) :
    fiveJacobiator D (lanePartLinear D .minus2 x)
      (lanePartLinear D .plus2 y) (lanePartLinear D .plus2 z) = 0 := by
  have hx : lanePartLinear D .minus2 x = x.minus2 • genEminus D 1 := by
    apply FiveGradedCarrier.ext <;> simp [lanePartLinear, lanePart, genEminus]
  have hy : lanePartLinear D .plus2 y = y.plus2 • genEplus D 1 := by
    apply FiveGradedCarrier.ext <;> simp [lanePartLinear, lanePart, genEplus]
  have hz : lanePartLinear D .plus2 z = z.plus2 • genEplus D 1 := by
    apply FiveGradedCarrier.ext <;> simp [lanePartLinear, lanePart, genEplus]
  rw [hx, hy, hz, fiveJacobiator_smul_left, fiveJacobiator_smul_mid,
    fiveJacobiator_smul_right]
  simpa using congrArg (fun q : FiveGradedCarrier D =>
    x.minus2 • (y.plus2 • (z.plus2 • q)))
    (jacobi_extremeMinus_extremePlus_extremePlus D 1 1 1)

theorem projected_jacobi_plus2_minus2_minus2
    (x y z : FiveGradedCarrier D) :
    fiveJacobiator D (lanePartLinear D .plus2 x)
      (lanePartLinear D .minus2 y) (lanePartLinear D .minus2 z) = 0 := by
  have hx : lanePartLinear D .plus2 x = x.plus2 • genEplus D 1 := by
    apply FiveGradedCarrier.ext <;> simp [lanePartLinear, lanePart, genEplus]
  have hy : lanePartLinear D .minus2 y = y.minus2 • genEminus D 1 := by
    apply FiveGradedCarrier.ext <;> simp [lanePartLinear, lanePart, genEminus]
  have hz : lanePartLinear D .minus2 z = z.minus2 • genEminus D 1 := by
    apply FiveGradedCarrier.ext <;> simp [lanePartLinear, lanePart, genEminus]
  rw [hx, hy, hz, fiveJacobiator_smul_left, fiveJacobiator_smul_mid,
    fiveJacobiator_smul_right]
  have hbase : fiveJacobiator D (genEplus D 1) (genEminus D 1)
      (genEminus D 1) = 0 := by
    rw [fiveJacobiator_cyclic_left]
    exact jacobi_extremeMinus_extremePlus_extremeMinus D 1 1 1
  simpa using congrArg (fun q : FiveGradedCarrier D =>
    x.plus2 • (y.minus2 • (z.minus2 • q)))
    hbase

theorem projected_jacobi_plus2_minus2_plus2
    (x y z : FiveGradedCarrier D) :
    fiveJacobiator D (lanePartLinear D .plus2 x)
      (lanePartLinear D .minus2 y) (lanePartLinear D .plus2 z) = 0 := by
  have hx : lanePartLinear D .plus2 x = x.plus2 • genEplus D 1 := by
    apply FiveGradedCarrier.ext <;> simp [lanePartLinear, lanePart, genEplus]
  have hy : lanePartLinear D .minus2 y = y.minus2 • genEminus D 1 := by
    apply FiveGradedCarrier.ext <;> simp [lanePartLinear, lanePart, genEminus]
  rw [hx, hy, fiveJacobiator_smul_left, fiveJacobiator_smul_mid]
  have hz : lanePartLinear D .plus2 z = z.plus2 • genEplus D 1 := by
    apply FiveGradedCarrier.ext <;> simp [lanePartLinear, lanePart, genEplus]
  rw [hz, fiveJacobiator_smul_right]
  have hbase : fiveJacobiator D (genEplus D 1) (genEminus D 1)
      (genEplus D 1) = 0 := by
    exact jacobi_extremePlus_extremeMinus_extremePlus D 1 1 1
  simpa using congrArg (fun q : FiveGradedCarrier D =>
    x.plus2 • (y.minus2 • (z.plus2 • q))) hbase

theorem projected_jacobi_minus2_minus2_minus1
    (x y z : FiveGradedCarrier D) :
    fiveJacobiator D (lanePartLinear D .minus2 x)
      (lanePartLinear D .minus2 y) (lanePartLinear D .minus1 z) = 0 := by
  have hx : lanePartLinear D .minus2 x = x.minus2 • genEminus D 1 := by
    apply FiveGradedCarrier.ext <;> simp [lanePartLinear, lanePart, genEminus]
  have hy : lanePartLinear D .minus2 y = y.minus2 • genEminus D 1 := by
    apply FiveGradedCarrier.ext <;> simp [lanePartLinear, lanePart, genEminus]
  rw [hx, hy, fiveJacobiator_smul_left, fiveJacobiator_smul_mid]
  simpa [lanePartLinear_apply, lanePart, injChargeMinus] using
    congrArg (fun q : FiveGradedCarrier D => x.minus2 • (y.minus2 • q))
      (jacobi_extremeMinus_extremeMinus_chargeMinus D 1 1 z.minus1)

theorem projected_jacobi_minus2_minus2_plus2
    (x y z : FiveGradedCarrier D) :
    fiveJacobiator D (lanePartLinear D .minus2 x)
      (lanePartLinear D .minus2 y) (lanePartLinear D .plus2 z) = 0 := by
  have hx : lanePartLinear D .minus2 x = x.minus2 • genEminus D 1 := by
    apply FiveGradedCarrier.ext <;> simp [lanePartLinear, lanePart, genEminus]
  have hy : lanePartLinear D .minus2 y = y.minus2 • genEminus D 1 := by
    apply FiveGradedCarrier.ext <;> simp [lanePartLinear, lanePart, genEminus]
  have hz : lanePartLinear D .plus2 z = z.plus2 • genEplus D 1 := by
    apply FiveGradedCarrier.ext <;> simp [lanePartLinear, lanePart, genEplus]
  rw [hx, hy, hz, fiveJacobiator_smul_left, fiveJacobiator_smul_mid,
    fiveJacobiator_smul_right]
  simpa using congrArg (fun q : FiveGradedCarrier D =>
    x.minus2 • (y.minus2 • (z.plus2 • q)))
    (jacobi_extremeMinus_extremeMinus_extremePlus D 1 1 1)

theorem projected_jacobi_plus2_plus2_minus2
    (x y z : FiveGradedCarrier D) :
    fiveJacobiator D (lanePartLinear D .plus2 x)
      (lanePartLinear D .plus2 y) (lanePartLinear D .minus2 z) = 0 := by
  have hx : lanePartLinear D .plus2 x = x.plus2 • genEplus D 1 := by
    apply FiveGradedCarrier.ext <;> simp [lanePartLinear, lanePart, genEplus]
  have hy : lanePartLinear D .plus2 y = y.plus2 • genEplus D 1 := by
    apply FiveGradedCarrier.ext <;> simp [lanePartLinear, lanePart, genEplus]
  have hz : lanePartLinear D .minus2 z = z.minus2 • genEminus D 1 := by
    apply FiveGradedCarrier.ext <;> simp [lanePartLinear, lanePart, genEminus]
  rw [hx, hy, hz, fiveJacobiator_smul_left, fiveJacobiator_smul_mid,
    fiveJacobiator_smul_right]
  simpa using congrArg (fun q : FiveGradedCarrier D =>
    x.plus2 • (y.plus2 • (z.minus2 • q)))
    (jacobi_extremePlus_extremePlus_extremeMinus D 1 1 1)

theorem projected_jacobi_minus1_minus1_zeroSymp
    (x y z : FiveGradedCarrier D) :
    fiveJacobiator D (lanePartLinear D .minus1 x)
      (lanePartLinear D .minus1 y) (lanePartLinear D .zeroSymp z) = 0 := by
  have hz : lanePartLinear D .zeroSymp z = injSympZero D ⟨z.zero_symp, by
    intro X Y
    exact z.zero_symp.property X Y⟩ := by rfl
  rw [hz]
  simpa [lanePartLinear_apply, lanePart, injChargeMinus, injSympZero] using
    jacobi_chargeMinus_chargeMinus_sympZero D x.minus1 y.minus1
      ⟨z.zero_symp, by
        intro X Y
        exact z.zero_symp.property X Y⟩

theorem projected_jacobi_minus1_minus1_plus1
    (x y z : FiveGradedCarrier D) :
    fiveJacobiator D (lanePartLinear D .minus1 x)
      (lanePartLinear D .minus1 y) (lanePartLinear D .plus1 z) = 0 := by
  simpa [lanePartLinear_apply, lanePart, injChargeMinus, injChargePlus] using
    jacobi_chargeMinus_chargeMinus_chargePlus D x.minus1 y.minus1 z.plus1

theorem projected_jacobi_plus1_plus1_minus1
    (x y z : FiveGradedCarrier D) :
    fiveJacobiator D (lanePartLinear D .plus1 x)
      (lanePartLinear D .plus1 y) (lanePartLinear D .minus1 z) = 0 := by
  simpa [lanePartLinear_apply, lanePart, injChargeMinus, injChargePlus] using
    jacobi_chargePlus_chargePlus_chargeMinus D x.plus1 y.plus1 z.minus1

theorem projected_jacobi_minus1_minus1_zeroScale
    (x y z : FiveGradedCarrier D) :
    fiveJacobiator D (lanePartLinear D .minus1 x)
      (lanePartLinear D .minus1 y) (lanePartLinear D .zeroScale z) = 0 := by
  have hz : lanePartLinear D .zeroScale z = z.zero_scale • genHscale D 1 := by
    apply FiveGradedCarrier.ext <;> simp [lanePartLinear, lanePart, genHscale]
  rw [hz, fiveJacobiator_smul_right]
  simpa [lanePartLinear_apply, lanePart, injChargeMinus] using congrArg
    (fun q : FiveGradedCarrier D => z.zero_scale • q)
    (jacobi_chargeMinus_chargeMinus_scale D x.minus1 y.minus1 1)

theorem projected_jacobi_zeroSymp_zeroSymp_zeroSymp
    (x y z : FiveGradedCarrier D) :
    fiveJacobiator D (lanePartLinear D .zeroSymp x)
      (lanePartLinear D .zeroSymp y) (lanePartLinear D .zeroSymp z) = 0 := by
  have hx : lanePartLinear D .zeroSymp x = injSympZero D ⟨x.zero_symp, by
    intro X Y
    exact x.zero_symp.property X Y⟩ := by rfl
  have hy : lanePartLinear D .zeroSymp y = injSympZero D ⟨y.zero_symp, by
    intro X Y
    exact y.zero_symp.property X Y⟩ := by rfl
  have hz : lanePartLinear D .zeroSymp z = injSympZero D ⟨z.zero_symp, by
    intro X Y
    exact z.zero_symp.property X Y⟩ := by rfl
  rw [hx, hy, hz]
  exact jacobi_zero_zero_zero D _ _ _

theorem projected_jacobi_plus1_plus1_zeroScale
    (x y z : FiveGradedCarrier D) :
    fiveJacobiator D (lanePartLinear D .plus1 x)
      (lanePartLinear D .plus1 y) (lanePartLinear D .zeroScale z) = 0 := by
  have hz : lanePartLinear D .zeroScale z = z.zero_scale • genHscale D 1 := by
    apply FiveGradedCarrier.ext <;> simp [lanePartLinear, lanePart, genHscale]
  rw [hz, fiveJacobiator_smul_right]
  simpa [lanePartLinear_apply, lanePart, injChargePlus] using congrArg
    (fun q : FiveGradedCarrier D => z.zero_scale • q)
    (jacobi_chargePlus_chargePlus_scale D x.plus1 y.plus1 1)

theorem global_fiveGraded_jacobi_of_homogeneous
    (h_cells : ∀ (i j k : JacobiLane) (x y z : FiveGradedCarrier D),
      fiveJacobiator D (lanePartLinear D i x) (lanePartLinear D j y)
        (lanePartLinear D k z) = 0)
    (x y z : FiveGradedCarrier D) : fiveJacobiator D x y z = 0 := by
  rw [← leibnizDefect_bracket_eq_jacobiator D x y z]
  apply global_leibniz_of_homogeneous (fiveGradedBracketBilinear D)
    (fun i => lanePartLinear D i) (sum_lanePartLinear D)
  intro i j k u v w
  rw [leibnizDefect_bracket_eq_jacobiator]
  exact h_cells i j k u v w

/-- The same globalization packaged for the repository's proof-carrying
homogeneous-data interface.  Constructing this datum remains exactly the
unresolved homogeneous-cell frontier. -/
theorem global_fiveGraded_jacobi_of_data
    (data : FiveGradedHomogeneousJacobiData D)
    (x y z : FiveGradedCarrier D) : fiveJacobiator D x y z = 0 := by
  apply global_fiveGraded_jacobi_of_homogeneous D
  intro i j k u v w
  simpa only [lanePartLinear_apply] using data.cell_jacobi i j k u v w

/-- A first concrete projected homogeneous cell, transported from the
existing extreme/charge owner theorem. -/
theorem projected_jacobi_minus2_minus2_plus1
    (x y z : FiveGradedCarrier D) :
    fiveJacobiator D (lanePartLinear D .minus2 x)
      (lanePartLinear D .minus2 y) (lanePartLinear D .plus1 z) = 0 := by
  simpa only [lanePartLinear_apply] using
    jacobi_extremeMinus_extremeMinus_chargePlus D x.minus2 y.minus2 z.plus1

theorem projected_jacobi_plus2_plus2_minus1
    (x y z : FiveGradedCarrier D) :
    fiveJacobiator D (lanePartLinear D .plus2 x)
      (lanePartLinear D .plus2 y) (lanePartLinear D .minus1 z) = 0 := by
  simpa only [lanePartLinear_apply] using
    jacobi_extremePlus_extremePlus_chargeMinus D x.plus2 y.plus2 z.minus1

theorem projected_jacobi_minus2_minus2_minus2
    (x y z : FiveGradedCarrier D) :
    fiveJacobiator D (lanePartLinear D .minus2 x)
      (lanePartLinear D .minus2 y) (lanePartLinear D .minus2 z) = 0 := by
  simpa only [lanePartLinear_apply] using
    jacobi_extremeMinus_extremeMinus_extremeMinus D x.minus2 y.minus2 z.minus2

theorem projected_jacobi_plus2_plus2_plus2
    (x y z : FiveGradedCarrier D) :
    fiveJacobiator D (lanePartLinear D .plus2 x)
      (lanePartLinear D .plus2 y) (lanePartLinear D .plus2 z) = 0 := by
  simpa only [lanePartLinear_apply] using
    jacobi_extremePlus_extremePlus_extremePlus D x.plus2 y.plus2 z.plus2

theorem projected_jacobi_minus1_minus1_minus1
    (x y z : FiveGradedCarrier D) :
    fiveJacobiator D (lanePartLinear D .minus1 x)
      (lanePartLinear D .minus1 y) (lanePartLinear D .minus1 z) = 0 := by
  simpa only [lanePartLinear_apply] using
    jacobi_chargeMinus_chargeMinus_chargeMinus D x.minus1 y.minus1 z.minus1

theorem projected_jacobi_plus1_plus1_plus1
    (x y z : FiveGradedCarrier D) :
    fiveJacobiator D (lanePartLinear D .plus1 x)
      (lanePartLinear D .plus1 y) (lanePartLinear D .plus1 z) = 0 := by
  simpa only [lanePartLinear_apply] using
    jacobi_chargePlus_chargePlus_chargePlus D x.plus1 y.plus1 z.plus1

theorem projected_jacobi_minus2_minus1_minus1
    (x y z : FiveGradedCarrier D) :
    fiveJacobiator D (lanePartLinear D .minus2 x)
      (lanePartLinear D .minus1 y) (lanePartLinear D .minus1 z) = 0 := by
  simpa only [lanePartLinear_apply] using
    jacobi_extremeMinus_chargeMinus_chargeMinus D x.minus2 y.minus1 z.minus1

theorem projected_jacobi_plus2_plus1_plus1
    (x y z : FiveGradedCarrier D) :
    fiveJacobiator D (lanePartLinear D .plus2 x)
      (lanePartLinear D .plus1 y) (lanePartLinear D .plus1 z) = 0 := by
  simpa only [lanePartLinear_apply] using
    jacobi_extremePlus_chargePlus_chargePlus D x.plus2 y.plus1 z.plus1

/-- Cyclic transport for any already-proved projected cell. -/
theorem projected_jacobi_cyclic_left
    {i j k : JacobiLane}
    (h : ∀ x y z : FiveGradedCarrier D,
      fiveJacobiator D (lanePartLinear D i x) (lanePartLinear D j y)
        (lanePartLinear D k z) = 0)
    (x y z : FiveGradedCarrier D) :
    fiveJacobiator D (lanePartLinear D j y) (lanePartLinear D k z)
      (lanePartLinear D i x) = 0 := by
  rw [fiveJacobiator_cyclic_left]
  exact h x y z

theorem projected_jacobi_cyclic_right
    {i j k : JacobiLane}
    (h : ∀ x y z : FiveGradedCarrier D,
      fiveJacobiator D (lanePartLinear D i x) (lanePartLinear D j y)
        (lanePartLinear D k z) = 0)
    (x y z : FiveGradedCarrier D) :
    fiveJacobiator D (lanePartLinear D k z) (lanePartLinear D i x)
      (lanePartLinear D j y) = 0 := by
  rw [fiveJacobiator_cyclic_right]
  exact h x y z

end InfoGeometry.Exceptional.Freudenthal
