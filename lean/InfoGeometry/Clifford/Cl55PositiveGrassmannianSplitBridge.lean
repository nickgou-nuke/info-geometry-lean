import InfoGeometry.Clifford.Cl55Q55NativeSplitBridge
import InfoGeometry.Clifford.ParaKahler55FiveGradedSUSYClosure
import InfoGeometry.Clifford.SuperGrassmannianTKK
import InfoGeometry.Algebra.SuperGrassmannianClifford
import InfoGeometry.Canonical.DecomposableBivector

/-!
# Positive Grassmannian blades in the symmetric `Cl(5,5)` tower

The positive `Gr(2,4)` chart is represented by an exterior two-vector in the
five-mode spinor carrier. Its existing isotropic Clifford map followed by the
native `Q55 ≃ Qsplit 5` isometry gives an element of the recursive symmetric
split Clifford algebra. This file proves that the image is a Clifford-even
element, and transports that fact to the exterior model's even super-grade.

The argument concerns the image of the blade under the Clifford map; it does
not identify exterior wedge multiplication with Clifford multiplication.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl55PositiveGrassmannianSplitBridge

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.SpinorRep
open InfoGeometry.Clifford.ParaKahler55FiveGradedSUSYClosure
open InfoGeometry.Clifford.SuperGrassmannianTKK
open InfoGeometry.Clifford.Cl55SuperTKK
open InfoGeometry.Algebra.SuperGrassmannianClifford
open InfoGeometry.CliffordTower

/-- Strict positivity of the chart's maximal minors forces its two rows to be
linearly independent. The proof uses the positive leading `2 × 2` minor. -/
theorem positiveGrassmannianRows_linearIndependent
    (C : Matrix (Fin 2) (Fin 4) ℝ)
    (hC : InfoGeometry.Canonical.HasPositiveMaximalMinors C) :
    LinearIndependent ℝ (fun i : Fin 2 => grassmannianRow55 C i) := by
  apply Fintype.linearIndependent_iff.mpr
  intro g hsum i
  have h0 : g 0 * C 0 0 + g 1 * C 1 0 = 0 := by
    have h := congrFun hsum 0
    simpa [Fin.sum_univ_two, grassmannianRow55, smul_eq_mul] using h
  have h1 : g 0 * C 0 1 + g 1 * C 1 1 = 0 := by
    have h := congrFun hsum 1
    simpa [Fin.sum_univ_two, grassmannianRow55, smul_eq_mul] using h
  have hdet : 0 < C 0 0 * C 1 1 - C 0 1 * C 1 0 := by
    have hpos := hC ![0, 1] (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> norm_num at *)
    change 0 < Matrix.det
      (!![C 0 0, C 0 1; C 1 0, C 1 1] : Matrix (Fin 2) (Fin 2) ℝ) at hpos
    rw [Matrix.det_fin_two_of] at hpos
    exact hpos
  have hg0 : g 0 = 0 := by
    have hmul : g 0 * (C 0 0 * C 1 1 - C 0 1 * C 1 0) = 0 := by
      calc
        g 0 * (C 0 0 * C 1 1 - C 0 1 * C 1 0) =
            C 1 1 * (g 0 * C 0 0 + g 1 * C 1 0) -
              C 1 0 * (g 0 * C 0 1 + g 1 * C 1 1) := by ring
        _ = 0 := by rw [h0, h1]; ring
    rcases mul_eq_zero.mp hmul with h | h
    · exact h
    · exact False.elim ((ne_of_gt hdet) h)
  have hg1 : g 1 = 0 := by
    have hmul : g 1 * (C 0 0 * C 1 1 - C 0 1 * C 1 0) = 0 := by
      calc
        g 1 * (C 0 0 * C 1 1 - C 0 1 * C 1 0) =
            C 0 0 * (g 0 * C 0 1 + g 1 * C 1 1) -
              C 0 1 * (g 0 * C 0 0 + g 1 * C 1 0) := by ring
        _ = 0 := by rw [h0, h1]; ring
    rcases mul_eq_zero.mp hmul with h | h
    · exact h
    · exact False.elim ((ne_of_gt hdet) h)
  fin_cases i <;> assumption

/-- A strictly positive `Gr(2,4)` chart blade is nonzero in the native
exterior spinor algebra. This is the projectivization prerequisite; purity
requires the separate maximal-annihilator theorem. -/
theorem positiveGrassmannianBlade_ne_zero_of_positive
    (C : Matrix (Fin 2) (Fin 4) ℝ)
    (hC : InfoGeometry.Canonical.HasPositiveMaximalMinors C) :
    positiveGrassmannianBlade C ≠ 0 := by
  have hpow := InfoGeometry.Canonical.exteriorPower_ιMulti_ne_zero_of_linearIndependent
    (fun i : Fin 2 => grassmannianRow55 C i)
    (positiveGrassmannianRows_linearIndependent C hC)
  have hblade : positiveGrassmannianBlade C =
      ExteriorAlgebra.ιMulti ℝ 2 (fun i : Fin 2 => grassmannianRow55 C i) := by
    rw [positiveGrassmannianBlade, ExteriorAlgebra.ιMulti_succ_apply]
    have htail : Matrix.vecTail (fun i : Fin 2 => grassmannianRow55 C i) =
        fun _ : Fin 1 => grassmannianRow55 C 1 := by
      funext j
      fin_cases j
      rfl
    rw [htail]
    simp [ExteriorAlgebra.ιMulti_apply]
  intro hz
  apply hpow
  apply Subtype.ext
  have hzero : ExteriorAlgebra.ιMulti ℝ 2
      (fun i : Fin 2 => grassmannianRow55 C i) = 0 := by
    rw [← hblade]
    exact hz
  simpa only [exteriorPower.ιMulti_apply_coe, Submodule.coe_zero] using hzero

/-- The Clifford image of the positive Grassmannian chart blade, transported
from `Q55` to the recursive `Qsplit 5` presentation. -/
def positiveGrassmannianBladeSplitImage
    (C : Matrix (Fin 2) (Fin 4) ℝ) :
    CliffordAlgebra (SplitQuad 5) :=
  cl55ToSplitCl55 (twistorMapAlgHom (positiveGrassmannianBlade C))

/-- The vacuum-ideal representation of the symmetric split Clifford algebra,
transported from the existing `Cl55` representation along the native algebra
equivalence `Cl55 ≃ₐ[ℝ] Clsplit 5`. -/
noncomputable def splitCl55VacuumIdealActionRingHom :
    CliffordAlgebra (SplitQuad 5) →+* EndV :=
  cl55VacuumIdealActionRingHom.comp cl55ToSplitCl55.symm.toRingHom

/-- The positive Grassmannian blade's TKK action factors through its image in
the recursive symmetric split Clifford algebra. This identifies the two
existing representation lanes on the actual chart element. -/
theorem positiveGrassmannianBladeTKKAction_eq_splitAction
    (C : Matrix (Fin 2) (Fin 4) ℝ) :
    positiveGrassmannianBladeTKKAction C =
      splitCl55VacuumIdealActionRingHom
        (positiveGrassmannianBladeSplitImage C) := by
  simp [positiveGrassmannianBladeTKKAction, exteriorToVacuumTKK,
    splitCl55VacuumIdealActionRingHom, positiveGrassmannianBladeSplitImage]

/-- On generators, the isotropic exterior-to-Clifford algebra map is the
diagonal null generator used by the `Cl(5,5)` owner. -/
theorem twistorMapAlgHom_generator (v : Fin 5 → ℝ) :
    twistorMapAlgHom (ExteriorAlgebra.ι ℝ v) =
      ι55 (diagonalNull55 v) := by
  simp [twistorMapAlgHom, twistorGeneratorMap]

/-- The split Clifford image of the chart blade is the product of the two
transported null generators. -/
theorem positiveGrassmannianBladeSplitImage_eq_generators
    (C : Matrix (Fin 2) (Fin 4) ℝ) :
    positiveGrassmannianBladeSplitImage C =
      CliffordAlgebra.ι (SplitQuad 5)
          (q55ToSplit5 (diagonalNull55 (grassmannianRow55 C 0))) *
        CliffordAlgebra.ι (SplitQuad 5)
          (q55ToSplit5 (diagonalNull55 (grassmannianRow55 C 1))) := by
  change cl55ToSplitCl55
      (twistorMapAlgHom
        (ExteriorAlgebra.ι ℝ (grassmannianRow55 C 0) *
          ExteriorAlgebra.ι ℝ (grassmannianRow55 C 1))) = _
  rw [map_mul]
  rw [twistorMapAlgHom_generator, twistorMapAlgHom_generator, map_mul,
    cl55ToSplitCl55_map_ι, cl55ToSplitCl55_map_ι]

/-- Every positive Grassmannian chart blade maps into the even part of the
native symmetric split Clifford algebra. Positivity is not needed for this
parity law; it selects the geometric chart, while the blade has degree two. -/
theorem positiveGrassmannianBladeSplitImage_mem_even
    (C : Matrix (Fin 2) (Fin 4) ℝ) :
    positiveGrassmannianBladeSplitImage C ∈
      CliffordAlgebra.evenOdd (SplitQuad 5) 0 := by
  rw [positiveGrassmannianBladeSplitImage_eq_generators]
  exact CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero
    (Q := SplitQuad 5)
    (q55ToSplit5 (diagonalNull55 (grassmannianRow55 C 0)))
    (q55ToSplit5 (diagonalNull55 (grassmannianRow55 C 1)))

/-- In the native exterior model of `Qsplit 5`, the same split Clifford image
lies in super-grade zero. This uses the repository's Clifford/exterior
equivalence and preserves the distinction between the two products. -/
theorem positiveGrassmannianBladeSplitImage_mem_exteriorSuperGradeZero
    (C : Matrix (Fin 2) (Fin 4) ℝ) :
    CliffordAlgebra.equivExterior (SplitQuad 5)
        (positiveGrassmannianBladeSplitImage C) ∈
      superGrade (SplitQuad 5) (0 : ZMod 2) := by
  change (cliffordExteriorEquiv (SplitQuad 5)).symm
      ((cliffordExteriorEquiv (SplitQuad 5))
        (positiveGrassmannianBladeSplitImage C)) ∈
      CliffordAlgebra.evenOdd (SplitQuad 5) 0
  simpa using positiveGrassmannianBladeSplitImage_mem_even C

end InfoGeometry.Clifford.Cl55PositiveGrassmannianSplitBridge

end noncomputable section
