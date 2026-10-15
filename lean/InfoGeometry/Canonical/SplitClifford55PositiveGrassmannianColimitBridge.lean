import InfoGeometry.Clifford.Cl55PositiveGrassmannianFockBridge
import InfoGeometry.Canonical.SplitClifford55PositiveGrassmannianMatrixBridge
import InfoGeometry.Canonical.SplitCliffordSuperGradeColimit

/-!
# Positive Grassmannian blades in the symmetric split-Clifford colimit

This bridge follows one positive `Gr(2,4)` chart blade through the repository's
native `Cl(5,5)` and exterior-supergrade owners into the canonical direct limit
of the symmetric `Cl(N,N)` tower.  The colimit conclusion is a fixed-point
statement for the lifted Clifford grade involution.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitClifford55PositiveGrassmannianColimitBridge

open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Canonical.SplitCliffordMatrixLimitSoldering
open InfoGeometry.Canonical.SplitCliffordSuperGradeColimit
open InfoGeometry.Canonical.SplitClifford55PositiveGrassmannianMatrixBridge
open InfoGeometry.Canonical.SplitCliffordTensorBridge
open InfoGeometry.Clifford.Cl55PositiveGrassmannianSplitBridge
open InfoGeometry.Clifford.Cl55PositiveGrassmannianFockBridge
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.SplitClifford55ExteriorSpinor
open InfoGeometry.Clifford.SplitClifford55ProjectivePureSpinor
open InfoGeometry.Clifford.SplitClifford55PureSpinorGrassmannianBridge
open InfoGeometry.Clifford.SplitClifford55ExteriorSpinor
open InfoGeometry.Clifford.SpinorRep
open InfoGeometry.CliffordTower
open InfoGeometry.Clifford.ParaKahler55FiveGradedSUSYClosure
open InfoGeometry.Algebra.SuperGrassmannianClifford
open scoped LinearAlgebra.Projectivization

/-- The exterior-supergrade-zero image of a positive Grassmannian chart blade
is fixed by the grade involution on the symmetric `Cl(N,N)` direct limit. -/
theorem positiveGrassmannianBlade_colimit_superGrade_zero_fixed
    (C : Matrix (Fin 2) (Fin 4) ℝ) :
    (CliffordAlgebra.equivExterior (InfoGeometry.Clifford.SpinorRep.SplitQuad 5)
        (positiveGrassmannianBladeSplitImage C) ∈
      superGrade (InfoGeometry.Clifford.SpinorRep.SplitQuad 5) (0 : ZMod 2)) ∧
    splitCliffordInfinityInvolute
        (DirectLimit.Algebra.of SplitClNNAlg
          (fun i j hij => splitCliffordMap i j hij) 5
          (positiveGrassmannianBladeSplitImage C)) =
      DirectLimit.Algebra.of SplitClNNAlg
        (fun i j hij => splitCliffordMap i j hij) 5
        (positiveGrassmannianBladeSplitImage C) := by
  refine ⟨positiveGrassmannianBladeSplitImage_mem_exteriorSuperGradeZero C, ?_⟩
  exact directLimit_of_even_fixed 5
    (x := positiveGrassmannianBladeSplitImage C)
    (positiveGrassmannianBladeSplitImage_mem_even C)

/-- The same finite `Cl(5,5)` chart element has matching even-sector readouts
in the native matrix representation and the symmetric-Clifford colimit: its
matrix odd projection vanishes, and its colimit grade-involution image is
fixed. This statement does not assert that the matrix tower map itself lifts
to the colimit. -/
theorem positiveGrassmannianBlade_matrixParity_and_colimitFixed
    (C : Matrix (Fin 2) (Fin 4) ℝ) :
    (splitEven 5 (stageMap 5 (positiveGrassmannianBladeSplitImage C)) =
        stageMap 5 (positiveGrassmannianBladeSplitImage C) ∧
      splitOdd 5 (stageMap 5 (positiveGrassmannianBladeSplitImage C)) = 0) ∧
    (splitCliffordInfinityInvolute
        (DirectLimit.Algebra.of SplitClNNAlg
          (fun i j hij => splitCliffordMap i j hij) 5
          (positiveGrassmannianBladeSplitImage C)) =
      DirectLimit.Algebra.of SplitClNNAlg
        (fun i j hij => splitCliffordMap i j hij) 5
        (positiveGrassmannianBladeSplitImage C)) := by
  exact ⟨positiveGrassmannianBlade_matrix_even_odd C,
    (positiveGrassmannianBlade_colimit_superGrade_zero_fixed C).2⟩

/-- Under the finite recursive spinor representation, the transported total
grading conjugation fixes the represented chart blade. This is the explicit
matrix-side intertwining form of its native Clifford-even theorem. -/
theorem positiveGrassmannianBlade_totalGrading_conjugation_fixed
    (C : Matrix (Fin 2) (Fin 4) ℝ) :
    totalGrading 5 * stageMap 5 (positiveGrassmannianBladeSplitImage C) *
        totalGrading 5 =
      stageMap 5 (positiveGrassmannianBladeSplitImage C) := by
  rw [← stageMap_involute_eq_totalGrading_conj]
  rw [CliffordAlgebra.involute_eq_of_mem_even
    (positiveGrassmannianBladeSplitImage_mem_even C)]

/-- The positive chart blade remains in the native even subalgebra after
every transition from its `Cl(5,5)` stage to a later symmetric `Cl(N,N)` stage. -/
theorem positiveGrassmannianBlade_mem_even_at_later_stage
    (C : Matrix (Fin 2) (Fin 4) ℝ) (N : ℕ) (h : 5 ≤ N) :
    splitCliffordMap 5 N h (positiveGrassmannianBladeSplitImage C) ∈
      CliffordAlgebra.evenOdd (Qsplit N) 0 :=
  splitCliffordMap_mem_even_of_mem_even 5 N h
    (positiveGrassmannianBladeSplitImage_mem_even C)

/-- The stage-`N` representative of the positive chart blade is fixed by the
lifted grade involution in the canonical symmetric split-Clifford colimit. -/
theorem positiveGrassmannianBlade_laterStage_colimit_fixed
    (C : Matrix (Fin 2) (Fin 4) ℝ) (N : ℕ) (h : 5 ≤ N) :
    splitCliffordInfinityInvolute
        (DirectLimit.Algebra.of SplitClNNAlg
          (fun i j hij => splitCliffordMap i j hij) N
          (splitCliffordMap 5 N h (positiveGrassmannianBladeSplitImage C))) =
      DirectLimit.Algebra.of SplitClNNAlg
        (fun i j hij => splitCliffordMap i j hij) N
        (splitCliffordMap 5 N h (positiveGrassmannianBladeSplitImage C)) := by
  exact directLimit_of_even_fixed N
    (x := splitCliffordMap 5 N h (positiveGrassmannianBladeSplitImage C))
    (positiveGrassmannianBlade_mem_even_at_later_stage C N h)

/-- Products of two positive-Grassmannian chart blades remain in the even
Clifford sector, and hence are fixed by the grade involution on the symmetric
split-Clifford colimit. This records closure under the actual Clifford product,
not only the parity of each blade separately. -/
theorem positiveGrassmannianBlade_product_colimit_fixed
    (C D : Matrix (Fin 2) (Fin 4) ℝ) :
    splitCliffordInfinityInvolute
        (DirectLimit.Algebra.of SplitClNNAlg
          (fun i j hij => splitCliffordMap i j hij) 5
          (positiveGrassmannianBladeSplitImage C *
            positiveGrassmannianBladeSplitImage D)) =
      DirectLimit.Algebra.of SplitClNNAlg
        (fun i j hij => splitCliffordMap i j hij) 5
        (positiveGrassmannianBladeSplitImage C *
          positiveGrassmannianBladeSplitImage D) := by
  apply directLimit_of_even_fixed
  apply (CliffordAlgebra.evenOdd_mul_le (Qsplit 5) 0 0)
  exact Submodule.mul_mem_mul
    (positiveGrassmannianBladeSplitImage_mem_even C)
    (positiveGrassmannianBladeSplitImage_mem_even D)

/-- The same product remains in the even sector at every later symmetric
`Cl(N,N)` stage, so its later-stage colimit representative is fixed as well.
This uses the canonical algebra transition and its proved preservation of the
native Clifford even component. -/
theorem positiveGrassmannianBlade_product_laterStage_colimit_fixed
    (C D : Matrix (Fin 2) (Fin 4) ℝ) (N : ℕ) (h : 5 ≤ N) :
    splitCliffordInfinityInvolute
        (DirectLimit.Algebra.of SplitClNNAlg
          (fun i j hij => splitCliffordMap i j hij) N
          (splitCliffordMap 5 N h
            (positiveGrassmannianBladeSplitImage C *
              positiveGrassmannianBladeSplitImage D))) =
      DirectLimit.Algebra.of SplitClNNAlg
        (fun i j hij => splitCliffordMap i j hij) N
        (splitCliffordMap 5 N h
          (positiveGrassmannianBladeSplitImage C *
            positiveGrassmannianBladeSplitImage D)) := by
  apply directLimit_of_even_fixed
  apply splitCliffordMap_mem_even_of_mem_even 5 N h
  apply (CliffordAlgebra.evenOdd_mul_le (Qsplit 5) 0 0)
  exact Submodule.mul_mem_mul
    (positiveGrassmannianBladeSplitImage_mem_even C)
    (positiveGrassmannianBladeSplitImage_mem_even D)

/-- Every later-stage representative of the chart blade is the same
canonical direct-limit element as its original `Cl(5,5)` representative. -/
theorem positiveGrassmannianBlade_laterStage_eq_stage5_in_colimit
    (C : Matrix (Fin 2) (Fin 4) ℝ) (N : ℕ) (h : 5 ≤ N) :
    DirectLimit.Algebra.of SplitClNNAlg
        (fun i j hij => splitCliffordMap i j hij) N
        (splitCliffordMap 5 N h (positiveGrassmannianBladeSplitImage C)) =
      DirectLimit.Algebra.of SplitClNNAlg
        (fun i j hij => splitCliffordMap i j hij) 5
        (positiveGrassmannianBladeSplitImage C) := by
  exact DirectLimit.Algebra.of_f
    (f := fun i j hij => splitCliffordMap i j hij) h
    (positiveGrassmannianBladeSplitImage C)

/-- The five-mode Fock output of the split-Clifford chart element, transported
back from coordinate spinors, is the exterior chart blade with the native
normalization factor `4`. -/
noncomputable def positiveGrassmannianFockVacuumSpinor
    (C : Matrix (Fin 2) (Fin 4) ℝ) : Spinor :=
  spinorCoordinateEquiv.symm
    (splitCliffordFockAction (positiveGrassmannianBladeSplitImage C)
      (spinorCoordinateEquiv (1 : Spinor)))

theorem positiveGrassmannianFockVacuumSpinor_eq
    (C : Matrix (Fin 2) (Fin 4) ℝ) :
    positiveGrassmannianFockVacuumSpinor C =
      (4 : ℝ) • positiveGrassmannianBlade C := by
  rw [positiveGrassmannianFockVacuumSpinor,
    positiveGrassmannianBlade_splitFockAction_vacuum]
  exact spinorCoordinateEquiv.symm_apply_apply _

/-- On a homogeneous exterior spinor of degree `d`, the symmetric split
Clifford chart element acts through the finite Fock representation as exterior
multiplication by the degree-two chart blade, with its native normalization
factor `4`; the result has exterior degree `d + 2`. -/
theorem positiveGrassmannianFockAction_exteriorGradeShift
    (C : Matrix (Fin 2) (Fin 4) ℝ) (d : ℕ)
    {ψ : Exterior55}
    (hψ : ψ ∈ ExteriorGrade ℝ
      InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.V5 d) :
    (splitCliffordFockAction (positiveGrassmannianBladeSplitImage C)
        (spinorCoordinateEquiv ψ) =
      spinorCoordinateEquiv (4 • (positiveGrassmannianBlade C * ψ))) ∧
    (4 : ℝ) • (positiveGrassmannianBlade C * ψ) ∈
      ExteriorGrade ℝ
        InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.V5 (2 + d) := by
  exact ⟨positiveGrassmannianBlade_splitFockAction_apply C ψ,
    positiveGrassmannianBlade_fockDegreeShift C d hψ⟩

/-- The positive-chart Clifford action preserves the exterior parity label of
every homogeneous Fock spinor. Its output degree rises by two, while the
`ZMod 2` label remains `gradeParity d`. This parity label belongs to the
five-dimensional Fock spinor carrier, not to the ten-dimensional split
Clifford exterior carrier. -/
theorem positiveGrassmannianFockAction_preserves_exteriorParity
    (C : Matrix (Fin 2) (Fin 4) ℝ) (d : ℕ)
    {ψ : Exterior55}
    (hψ : ψ ∈ ExteriorGrade ℝ
      InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.V5 d) :
    (splitCliffordFockAction (positiveGrassmannianBladeSplitImage C)
        (spinorCoordinateEquiv ψ) =
      spinorCoordinateEquiv (4 • (positiveGrassmannianBlade C * ψ))) ∧
    (4 : ℝ) • (positiveGrassmannianBlade C * ψ) ∈
      ExteriorGrade ℝ
        InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.V5 (2 + d) ∧
    gradeParity (2 + d) = gradeParity d := by
  obtain ⟨hact, hdegree⟩ :=
    positiveGrassmannianFockAction_exteriorGradeShift C d hψ
  refine ⟨hact, hdegree, ?_⟩
  dsimp [gradeParity]
  rw [Nat.cast_add, ZMod.natCast_self, zero_add]

/-- The Fock vacuum output of a positive chart blade is a homogeneous
two-vector in the five-dimensional spinor exterior algebra. -/
theorem positiveGrassmannianFockVacuumSpinor_mem_exteriorGrade_two
    (C : Matrix (Fin 2) (Fin 4) ℝ) :
    positiveGrassmannianFockVacuumSpinor C ∈
      ExteriorGrade ℝ
        InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.V5 2 := by
  rw [positiveGrassmannianFockVacuumSpinor_eq]
  exact (ExteriorGrade ℝ
      InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.V5 2).smul_mem
    4 (positiveGrassmannianBlade_mem_exteriorGrade_two C)

/-- The Fock vacuum output is a pure spinor whenever the Grassmannian chart is
positive. Its normalization is irrelevant by the native projective
scale-invariance theorem. -/
theorem positiveGrassmannianFockVacuumSpinor_isPureSpinor
    (C : Matrix (Fin 2) (Fin 4) ℝ)
    (hC : InfoGeometry.Canonical.HasPositiveMaximalMinors C) :
    IsPureSpinor (positiveGrassmannianFockVacuumSpinor C) := by
  rw [positiveGrassmannianFockVacuumSpinor_eq]
  exact (isPureSpinor_smul_iff 4 (positiveGrassmannianBlade C) (by norm_num)).2
    (positiveGrassmannianBlade_isPureSpinor_of_positive C hC)

/-- Projectivization forgets the nonzero normalization factor in the Fock
vacuum calculation. -/
theorem positiveGrassmannianFockVacuumProjective_eq
    (C : Matrix (Fin 2) (Fin 4) ℝ)
    (hC : InfoGeometry.Canonical.HasPositiveMaximalMinors C) :
    Projectivization.mk ℝ (positiveGrassmannianFockVacuumSpinor C)
        (positiveGrassmannianFockVacuumSpinor_isPureSpinor C hC).1 =
      Projectivization.mk ℝ (positiveGrassmannianBlade C)
        (positiveGrassmannianBlade_ne_zero_of_positive C hC) := by
  apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
  refine ⟨4, ?_⟩
  rw [positiveGrassmannianFockVacuumSpinor_eq]

/-- The pure-spinor Grassmannian point read from the Fock vacuum output. -/
noncomputable def positiveGrassmannianFockVacuumGrassmannianPoint
    (C : Matrix (Fin 2) (Fin 4) ℝ)
    (hC : InfoGeometry.Canonical.HasPositiveMaximalMinors C) :
    MaximalNeutralGrassmannian :=
  projectivePureSpinorGrassmannianPoint
    ⟨Projectivization.mk ℝ (positiveGrassmannianFockVacuumSpinor C)
        (positiveGrassmannianFockVacuumSpinor_isPureSpinor C hC).1,
      (projectivePureSpinor_mk_iff _
        (positiveGrassmannianFockVacuumSpinor_isPureSpinor C hC).1).2
        (positiveGrassmannianFockVacuumSpinor_isPureSpinor C hC)⟩

/-- The Fock output's projective pure-spinor readout is exactly the
maximal-neutral Grassmannian point already associated to the positive chart.
This identifies the operator action, exterior spinor, projective pure spinor,
and annihilator-plane carriers on this chart. -/
theorem positiveGrassmannianFockVacuumGrassmannianPoint_eq
    (C : Matrix (Fin 2) (Fin 4) ℝ)
    (hC : InfoGeometry.Canonical.HasPositiveMaximalMinors C) :
    positiveGrassmannianFockVacuumGrassmannianPoint C hC =
      positiveGrassmannianMaximalNeutralPoint C hC := by
  apply Subtype.ext
  change (projectivePureSpinorGrassmannianPoint _).1 = _
  rw [projectivePureSpinorGrassmannianPoint_val,
    projectivePureSpinorAnnihilator_mk,
    positiveGrassmannianMaximalNeutralPoint_val,
    positiveGrassmannianMaximalNullCandidate_eq_neutralAnnihilator]
  rw [positiveGrassmannianFockVacuumSpinor_eq,
    neutralAnnihilator_smul 4 (positiveGrassmannianBlade C) (by norm_num)]
  all_goals exact hC

/-- The connected positive-chart synthesis across the symmetric Clifford
colimit, its transported supergrade, the finite Fock representation, and the
pure-spinor/maximal-neutral Grassmannian readout. The clauses retain their
native carriers and state the maps between them explicitly. -/
theorem positiveGrassmannian_symmetricClifford_fock_grassmannian_synthesis
    (C : Matrix (Fin 2) (Fin 4) ℝ)
    (hC : InfoGeometry.Canonical.HasPositiveMaximalMinors C) :
    (CliffordAlgebra.equivExterior (InfoGeometry.Clifford.SpinorRep.SplitQuad 5)
        (positiveGrassmannianBladeSplitImage C) ∈
      superGrade (InfoGeometry.Clifford.SpinorRep.SplitQuad 5) (0 : ZMod 2)) ∧
    (splitCliffordInfinityInvolute
        (DirectLimit.Algebra.of SplitClNNAlg
          (fun i j hij => splitCliffordMap i j hij) 5
          (positiveGrassmannianBladeSplitImage C)) =
      DirectLimit.Algebra.of SplitClNNAlg
        (fun i j hij => splitCliffordMap i j hij) 5
        (positiveGrassmannianBladeSplitImage C)) ∧
    (splitEven 5 (stageMap 5 (positiveGrassmannianBladeSplitImage C)) =
        stageMap 5 (positiveGrassmannianBladeSplitImage C) ∧
      splitOdd 5 (stageMap 5 (positiveGrassmannianBladeSplitImage C)) = 0) ∧
    (totalGrading 5 * stageMap 5 (positiveGrassmannianBladeSplitImage C) *
        totalGrading 5 =
      stageMap 5 (positiveGrassmannianBladeSplitImage C)) ∧
    (spinorCoordinateEquiv (positiveGrassmannianFockVacuumSpinor C) =
      splitCliffordFockAction (positiveGrassmannianBladeSplitImage C)
        (spinorCoordinateEquiv (1 : Spinor))) ∧
    positiveGrassmannianFockVacuumSpinor C ∈
      ExteriorGrade ℝ
        InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.V5 2 ∧
    IsPureSpinor (positiveGrassmannianFockVacuumSpinor C) ∧
    positiveGrassmannianFockVacuumGrassmannianPoint C hC =
      positiveGrassmannianMaximalNeutralPoint C hC := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact positiveGrassmannianBlade_colimit_superGrade_zero_fixed C |>.1
  · exact positiveGrassmannianBlade_colimit_superGrade_zero_fixed C |>.2
  · exact positiveGrassmannianBlade_matrix_even_odd C
  · exact positiveGrassmannianBlade_totalGrading_conjugation_fixed C
  · rw [positiveGrassmannianFockVacuumSpinor_eq]
    exact (positiveGrassmannianBlade_splitFockAction_vacuum C).symm
  · exact positiveGrassmannianFockVacuumSpinor_mem_exteriorGrade_two C
  · exact positiveGrassmannianFockVacuumSpinor_isPureSpinor C hC
  · exact positiveGrassmannianFockVacuumGrassmannianPoint_eq C hC

end InfoGeometry.Canonical.SplitClifford55PositiveGrassmannianColimitBridge

end noncomputable section
