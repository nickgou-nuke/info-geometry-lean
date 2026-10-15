import InfoGeometry.Clifford.Cl55PositiveGrassmannianSplitBridge
import InfoGeometry.Clifford.Cl55NeutralHyperbolicIsometry
import InfoGeometry.Clifford.Cl55FockMatrixIntertwiner
import Mathlib.LinearAlgebra.Dual.Lemmas
import InfoGeometry.Clifford.SplitClifford55ProjectivePureSpinor
import InfoGeometry.Clifford.SplitClifford55PureSpinorGrassmannianBridge

/-!
# Positive Grassmannian blades in the symmetric split Clifford Fock model

The positive `Gr(2,4)` chart already maps to the recursive symmetric
`Cl(5,5)` algebra.  This file calculates the action of that image in the
native exterior Fock model, tracking the normalization between diagonal null
generators and wedge generators.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl55PositiveGrassmannianFockBridge

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.Cl55NeutralHyperbolicIsometry
open InfoGeometry.Clifford.Cl55FockMatrixIntertwiner
open InfoGeometry.Clifford.Cl55PositiveGrassmannianSplitBridge
open InfoGeometry.Clifford.ParaKahler55FiveGradedSUSYClosure
open InfoGeometry.Clifford.SpinorRep
open InfoGeometry.Clifford.SplitClifford55ExteriorSpinor
open InfoGeometry.Clifford.SplitClifford55ProjectivePureSpinor
open InfoGeometry.Clifford.SplitClifford55PureSpinorGrassmannianBridge
open InfoGeometry.Algebra.SuperGrassmannianClifford
open InfoGeometry.CliffordTower
open scoped LinearAlgebra.Projectivization

/-- The recursive symmetric `Cl(5,5)` algebra acting on the coordinate Fock
space, transported through the existing quadratic-space and Clifford
equivalences. -/
noncomputable def splitCliffordFockAction :
    CliffordAlgebra (SplitQuad 5) →ₐ[ℝ]
      Module.End ℝ InfoGeometry.Algebra.FiniteSpin.Vec32R :=
  neutralCliffordFockAlgEquiv.toAlgHom.comp
    (neutralCliffordAlgEquiv.symm.toAlgHom.comp
      cl55ToSplitCl55.symm.toAlgHom)

/-- The symmetric split Clifford algebra acts faithfully and surjectively on
the repository's five-mode exterior Fock space. This is the composite of the
existing quadratic-space and Clifford algebra equivalences, not a separately
postulated matrix representation. -/
noncomputable def splitCliffordFockAlgEquiv :
    CliffordAlgebra (SplitQuad 5) ≃ₐ[ℝ]
      Module.End ℝ InfoGeometry.Algebra.FiniteSpin.Vec32R :=
  cl55ToSplitCl55.symm.trans
    (neutralCliffordAlgEquiv.symm.trans neutralCliffordFockAlgEquiv)

/-- The geometric exterior model of `Cl(5,5)` is linearly equivalent to the
Fock endomorphism algebra. Its multiplication on the source is the transported
Clifford geometric product. -/
noncomputable def splitExteriorFockEquiv :
    SplitExteriorStage 5 ≃ₗ[ℝ]
      Module.End ℝ InfoGeometry.Algebra.FiniteSpin.Vec32R :=
  (cliffordExteriorEquiv (SplitQuad 5)).symm.trans
    splitCliffordFockAlgEquiv.toLinearEquiv

/-- The equivalence between the ten-dimensional exterior model and the
five-mode Fock endomorphisms carries the native Clifford geometric product to
operator composition. -/
theorem splitExteriorFockEquiv_geometricProduct
    (x y : SplitExteriorStage 5) :
    splitExteriorFockEquiv
        (geometricProduct (SplitQuad 5) x y) =
      splitExteriorFockEquiv x * splitExteriorFockEquiv y := by
  change splitCliffordFockAlgEquiv
      ((cliffordExteriorEquiv (SplitQuad 5)).symm
        (geometricProduct (SplitQuad 5) x y)) =
    splitCliffordFockAlgEquiv ((cliffordExteriorEquiv (SplitQuad 5)).symm x) *
      splitCliffordFockAlgEquiv ((cliffordExteriorEquiv (SplitQuad 5)).symm y)
  rw [geometricProduct_toClifford]
  exact splitCliffordFockAlgEquiv.map_mul _ _

/-- A diagonal null generator in `Q55`, transported to the neutral Fock
coordinates, is twice exterior multiplication by its `V₅` component. -/
theorem splitCliffordFockAction_diagonalNull (v : Fin 5 → ℝ) :
    splitCliffordFockAction
        (CliffordAlgebra.ι (SplitQuad 5)
          (q55ToSplit5 (diagonalNull55 v))) =
      spinorCoordinateEquiv.conjAlgEquiv ℝ (2 • wedge v) := by
  have hsplit :
      cl55ToSplitCl55.symm
          (CliffordAlgebra.ι (SplitQuad 5)
            (q55ToSplit5 (diagonalNull55 v))) =
        ι55 (diagonalNull55 v) := by
    apply cl55ToSplitCl55.injective
    rw [cl55ToSplitCl55.apply_symm_apply,
      cl55ToSplitCl55_map_ι]
  change neutralCliffordFockAlgEquiv
    (neutralCliffordAlgEquiv.symm
      (cl55ToSplitCl55.symm
        (CliffordAlgebra.ι (SplitQuad 5)
          (q55ToSplit5 (diagonalNull55 v))))) = _
  rw [hsplit, neutralCliffordAlgEquiv_symm_ι55,
    neutralCliffordFockAlgEquiv_ι]
  have hneutral : neutralToV55.symm (diagonalNull55 v) = (2 • v, 0) := by
    apply Prod.ext
    · ext i
      simp [diagonalNull55, neutralToV55_symm_apply, two_smul]
    · simp [diagonalNull55, neutralToV55_symm_apply]
  rw [hneutral]
  have hact : neutralAction (2 • v,
      (0 : Module.Dual ℝ SplitClifford55ExteriorSpinor.V5)) =
        2 • wedge v := by
    apply LinearMap.ext
    intro ψ
    simp [neutralAction, wedge, contract, map_smul, smul_mul_assoc]
    change ExteriorAlgebra.ι ℝ ((2 : ℝ) • v) * ψ =
      (2 : ℝ) • (ExteriorAlgebra.ι ℝ v * ψ)
    rw [map_smul, smul_mul_assoc]
  rw [hact]

/-- Conjugating an endomorphism by the coordinate equivalence and evaluating
it on a coordinate vector is the coordinate image of the original action. -/
theorem spinorCoordinateConjugation_apply_onRange
    (T : SpinorEnd) (ψ : Spinor) :
    (spinorCoordinateEquiv.conjAlgEquiv ℝ T)
        (spinorCoordinateEquiv ψ) = spinorCoordinateEquiv (T ψ) := by
  change spinorCoordinateEquiv
      (T (spinorCoordinateEquiv.symm (spinorCoordinateEquiv ψ))) = _
  exact congrArg spinorCoordinateEquiv
    (congrArg T (spinorCoordinateEquiv.left_inv ψ))

/-- The split-Clifford image of a positive chart blade acts on the Fock vacuum
as four times the original exterior blade. The factor is the product of the
two generator normalizations in `splitCliffordFockAction_diagonalNull`. -/
theorem positiveGrassmannianBlade_splitFockAction_vacuum
    (C : Matrix (Fin 2) (Fin 4) ℝ) :
    splitCliffordFockAction (positiveGrassmannianBladeSplitImage C)
        (spinorCoordinateEquiv (1 : Exterior55)) =
      spinorCoordinateEquiv (4 • positiveGrassmannianBlade C) := by
  rw [positiveGrassmannianBladeSplitImage_eq_generators, map_mul,
    splitCliffordFockAction_diagonalNull,
    splitCliffordFockAction_diagonalNull]
  rw [Module.End.mul_apply,
    spinorCoordinateConjugation_apply_onRange,
    spinorCoordinateConjugation_apply_onRange]
  apply congrArg spinorCoordinateEquiv
  simp only [LinearMap.smul_apply, wedge_apply, mul_one,
    positiveGrassmannianBlade]
  simp only [← Nat.cast_smul_eq_nsmul ℝ]
  change (2 : ℝ) •
      (ExteriorAlgebra.ι ℝ (grassmannianRow55 C 0) *
        ((2 : ℝ) • ExteriorAlgebra.ι ℝ (grassmannianRow55 C 1))) =
    (4 : ℝ) •
      (ExteriorAlgebra.ι ℝ (grassmannianRow55 C 0) *
        ExteriorAlgebra.ι ℝ (grassmannianRow55 C 1))
  calc
    (2 : ℝ) •
        (ExteriorAlgebra.ι ℝ (grassmannianRow55 C 0) *
          ((2 : ℝ) • ExteriorAlgebra.ι ℝ (grassmannianRow55 C 1))) =
      (2 : ℝ) • ((2 : ℝ) •
        (ExteriorAlgebra.ι ℝ (grassmannianRow55 C 0) *
          ExteriorAlgebra.ι ℝ (grassmannianRow55 C 1))) := by
            rw [Algebra.mul_smul_comm]
    _ = (4 : ℝ) •
        (ExteriorAlgebra.ι ℝ (grassmannianRow55 C 0) *
          ExteriorAlgebra.ι ℝ (grassmannianRow55 C 1)) := by
            rw [smul_smul]
            norm_num

/-- On every Fock spinor, the positive-Grassmannian Clifford image acts as
four times exterior multiplication by its decomposable two-vector. This is
the representation-level bridge from the symmetric split Clifford product to
the native exterior product; the factor four records the normalization of
the two diagonal-null generators. -/
theorem positiveGrassmannianBlade_splitFockAction_apply
    (C : Matrix (Fin 2) (Fin 4) ℝ) (ψ : Exterior55) :
    splitCliffordFockAction (positiveGrassmannianBladeSplitImage C)
        (spinorCoordinateEquiv ψ) =
      spinorCoordinateEquiv (4 • (positiveGrassmannianBlade C * ψ)) := by
  rw [positiveGrassmannianBladeSplitImage_eq_generators, map_mul,
    splitCliffordFockAction_diagonalNull,
    splitCliffordFockAction_diagonalNull,
    Module.End.mul_apply,
    spinorCoordinateConjugation_apply_onRange,
    spinorCoordinateConjugation_apply_onRange]
  apply congrArg spinorCoordinateEquiv
  change (2 : ℝ) •
      (ExteriorAlgebra.ι ℝ (grassmannianRow55 C 0) *
        ((2 : ℝ) •
          (ExteriorAlgebra.ι ℝ (grassmannianRow55 C 1) * ψ))) =
    (4 : ℝ) •
      ((ExteriorAlgebra.ι ℝ (grassmannianRow55 C 0) *
        ExteriorAlgebra.ι ℝ (grassmannianRow55 C 1)) * ψ)
  rw [Algebra.mul_smul_comm, smul_smul]
  norm_num [positiveGrassmannianBlade, mul_assoc]

/-- The positive chart blade is homogeneous of exterior degree two in the
native Fock spinor algebra. -/
theorem positiveGrassmannianBlade_mem_exteriorGrade_two
    (C : Matrix (Fin 2) (Fin 4) ℝ) :
    positiveGrassmannianBlade C ∈
      ExteriorGrade ℝ SplitClifford55ExteriorSpinor.V5 2 := by
  have hblade : positiveGrassmannianBlade C =
      ExteriorAlgebra.ιMulti ℝ 2
        (fun i : Fin 2 => grassmannianRow55 C i) := by
    rw [positiveGrassmannianBlade, ExteriorAlgebra.ιMulti_succ_apply]
    have htail : Matrix.vecTail (fun i : Fin 2 => grassmannianRow55 C i) =
        fun _ : Fin 1 => grassmannianRow55 C 1 := by
      funext j
      fin_cases j
      rfl
    rw [htail]
    simp [ExteriorAlgebra.ιMulti_apply]
  rw [hblade]
  exact ExteriorAlgebra.ιMulti_range ℝ 2 ⟨
    (fun i : Fin 2 => grassmannianRow55 C i), rfl⟩

/-- The Fock action of the positive chart blade raises every homogeneous
spinor degree by exactly two. The scalar normalization does not affect the
homogeneous component. -/
theorem positiveGrassmannianBlade_fockDegreeShift
    (C : Matrix (Fin 2) (Fin 4) ℝ) (d : ℕ)
    {ψ : Exterior55}
    (hψ : ψ ∈ ExteriorGrade ℝ SplitClifford55ExteriorSpinor.V5 d) :
    (4 : ℝ) • (positiveGrassmannianBlade C * ψ) ∈
      ExteriorGrade ℝ SplitClifford55ExteriorSpinor.V5 (2 + d) := by
  have hblade : positiveGrassmannianBlade C ∈
      ExteriorGrade ℝ SplitClifford55ExteriorSpinor.V5 2 :=
    positiveGrassmannianBlade_mem_exteriorGrade_two C
  have hmul : positiveGrassmannianBlade C * ψ ∈
      ExteriorGrade ℝ SplitClifford55ExteriorSpinor.V5 (2 + d) := by
    exact exteriorGrade_outerProduct_mem
      ⟨positiveGrassmannianBlade C, hblade⟩ ⟨ψ, hψ⟩
  exact (ExteriorGrade ℝ SplitClifford55ExteriorSpinor.V5 (2 + d)).smul_mem 4 hmul

/-- The first row of the positive Grassmannian chart is in the neutral
annihilator of its decomposable exterior blade. -/
theorem positiveGrassmannianBlade_row0_mem_neutralAnnihilator
    (C : Matrix (Fin 2) (Fin 4) ℝ) :
    (grassmannianRow55 C 0,
      (0 : Module.Dual ℝ SplitClifford55ExteriorSpinor.V5)) ∈
      neutralAnnihilator (positiveGrassmannianBlade C) := by
  rw [mem_neutralAnnihilator_iff]
  change neutralAction (grassmannianRow55 C 0,
      (0 : Module.Dual ℝ SplitClifford55ExteriorSpinor.V5))
    (ExteriorAlgebra.ι ℝ (grassmannianRow55 C 0) *
      ExteriorAlgebra.ι ℝ (grassmannianRow55 C 1)) = 0
  exact neutralAction_leftFactor_annihilates_bivector
    (grassmannianRow55 C 0) (grassmannianRow55 C 1)

/-- The second row of the positive Grassmannian chart is in the neutral
annihilator of its decomposable exterior blade. -/
theorem positiveGrassmannianBlade_row1_mem_neutralAnnihilator
    (C : Matrix (Fin 2) (Fin 4) ℝ) :
    (grassmannianRow55 C 1,
      (0 : Module.Dual ℝ SplitClifford55ExteriorSpinor.V5)) ∈
      neutralAnnihilator (positiveGrassmannianBlade C) := by
  rw [mem_neutralAnnihilator_iff]
  change neutralAction (grassmannianRow55 C 1,
      (0 : Module.Dual ℝ SplitClifford55ExteriorSpinor.V5))
    (ExteriorAlgebra.ι ℝ (grassmannianRow55 C 0) *
      ExteriorAlgebra.ι ℝ (grassmannianRow55 C 1)) = 0
  exact neutralAction_rightFactor_annihilates_bivector
    (grassmannianRow55 C 0) (grassmannianRow55 C 1)

/-- The neutral subspace generated by the two embedded chart rows. -/
def positiveGrassmannianRowNullPlane
    (C : Matrix (Fin 2) (Fin 4) ℝ) :
    Submodule ℝ SplitClifford55ExteriorSpinor.NeutralSpace :=
  Submodule.span ℝ (Set.range fun i : Fin 2 =>
    (grassmannianRow55 C i,
      (0 : Module.Dual ℝ SplitClifford55ExteriorSpinor.V5)))

/-- Positivity makes the embedded chart rows a basis of their neutral
two-plane. -/
theorem positiveGrassmannianRowNullPlane_finrank
    (C : Matrix (Fin 2) (Fin 4) ℝ)
    (hC : InfoGeometry.Canonical.HasPositiveMaximalMinors C) :
    Module.finrank ℝ (positiveGrassmannianRowNullPlane C) = 2 := by
  change Module.finrank ℝ (Submodule.span ℝ (Set.range fun i : Fin 2 =>
    (grassmannianRow55 C i,
      (0 : Module.Dual ℝ SplitClifford55ExteriorSpinor.V5)))) = 2
  have hrows := positiveGrassmannianRows_linearIndependent C hC
  have hembedded : LinearIndependent ℝ (fun i : Fin 2 =>
      (grassmannianRow55 C i,
        (0 : Module.Dual ℝ SplitClifford55ExteriorSpinor.V5))) := by
    apply Fintype.linearIndependent_iff.mpr
    intro g hg i
    have hfst : ∑ j : Fin 2, g j • grassmannianRow55 C j = 0 := by
      have h := congrArg Prod.fst hg
      simpa using h
    exact (Fintype.linearIndependent_iff.mp hrows) g hfst i
  simpa using (finrank_span_eq_card hembedded)

/-- The complete embedded chart row plane is contained in the neutral
annihilator of its exterior blade. -/
theorem positiveGrassmannianRowNullPlane_le_neutralAnnihilator
    (C : Matrix (Fin 2) (Fin 4) ℝ) :
    positiveGrassmannianRowNullPlane C ≤
      neutralAnnihilator (positiveGrassmannianBlade C) := by
  change Submodule.span ℝ (Set.range fun i : Fin 2 =>
      (grassmannianRow55 C i,
        (0 : Module.Dual ℝ SplitClifford55ExteriorSpinor.V5))) ≤ _
  apply Submodule.span_le.mpr
  intro z hz
  rcases Set.mem_range.mp hz with ⟨i, hi⟩
  rw [← hi]
  fin_cases i
  · exact positiveGrassmannianBlade_row0_mem_neutralAnnihilator C
  · exact positiveGrassmannianBlade_row1_mem_neutralAnnihilator C

/-- The two-plane spanned by the positive chart rows in the five-mode vector
carrier. -/
def positiveGrassmannianRowSubspace
    (C : Matrix (Fin 2) (Fin 4) ℝ) :
    Submodule ℝ SplitClifford55ExteriorSpinor.V5 :=
  Submodule.span ℝ (Set.range (grassmannianRow55 C))

/-- The split-neutral subspace consisting of the chart row plane together with
all covectors that vanish on that plane. -/
def positiveGrassmannianMaximalNullCandidate
    (C : Matrix (Fin 2) (Fin 4) ℝ) :
    Submodule ℝ SplitClifford55ExteriorSpinor.NeutralSpace :=
  (positiveGrassmannianRowSubspace C).prod
    (positiveGrassmannianRowSubspace C).dualAnnihilator

/-- The positive chart row subspace has dimension two. -/
theorem positiveGrassmannianRowSubspace_finrank
    (C : Matrix (Fin 2) (Fin 4) ℝ)
    (hC : InfoGeometry.Canonical.HasPositiveMaximalMinors C) :
    Module.finrank ℝ (positiveGrassmannianRowSubspace C) = 2 := by
  change Module.finrank ℝ
    (Submodule.span ℝ (Set.range (grassmannianRow55 C))) = 2
  simpa using
    (finrank_span_eq_card (positiveGrassmannianRows_linearIndependent C hC))

/-- The row-plane/covector-annihilator candidate has the maximal neutral
dimension five. -/
theorem positiveGrassmannianMaximalNullCandidate_finrank
    (C : Matrix (Fin 2) (Fin 4) ℝ)
    (hC : InfoGeometry.Canonical.HasPositiveMaximalMinors C) :
    Module.finrank ℝ (positiveGrassmannianMaximalNullCandidate C) = 5 := by
  let P := positiveGrassmannianRowSubspace C
  have hP : Module.finrank ℝ P = 2 :=
    positiveGrassmannianRowSubspace_finrank C hC
  letI : Module.Finite ℝ P.dualAnnihilator := inferInstance
  letI : Module.Free ℝ P.dualAnnihilator :=
    Module.Free.of_divisionRing ℝ P.dualAnnihilator
  have hdual : Module.finrank ℝ P.dualAnnihilator = 3 := by
    have hsum := Subspace.finrank_add_finrank_dualAnnihilator_eq P
    have hV : Module.finrank ℝ SplitClifford55ExteriorSpinor.V5 = 5 := by
      simp [SplitClifford55ExteriorSpinor.V5,
        InfoGeometry.Algebra.FiniteSpin.Vec5R]
    omega
  calc
    Module.finrank ℝ (positiveGrassmannianMaximalNullCandidate C) =
        Module.finrank ℝ (P.prod P.dualAnnihilator) := by rfl
    _ = Module.finrank ℝ (P × P.dualAnnihilator) :=
      LinearEquiv.finrank_eq (Submodule.prodEquiv P P.dualAnnihilator)
    _ = Module.finrank ℝ P + Module.finrank ℝ P.dualAnnihilator :=
      Module.finrank_prod
    _ = 5 := by rw [hP, hdual]

/-- Every covector annihilating the two chart rows defines a neutral
annihilator vector of the chart blade. -/
theorem positiveGrassmannianBlade_covector_mem_neutralAnnihilator
    (C : Matrix (Fin 2) (Fin 4) ℝ)
    (φ : Module.Dual ℝ SplitClifford55ExteriorSpinor.V5)
    (h0 : φ (grassmannianRow55 C 0) = 0)
    (h1 : φ (grassmannianRow55 C 1) = 0) :
    ((0 : SplitClifford55ExteriorSpinor.V5), φ) ∈
      neutralAnnihilator (positiveGrassmannianBlade C) := by
  rw [mem_neutralAnnihilator_iff]
  change neutralAction ((0 : SplitClifford55ExteriorSpinor.V5), φ)
    (ExteriorAlgebra.ι ℝ (grassmannianRow55 C 0) *
      ExteriorAlgebra.ι ℝ (grassmannianRow55 C 1)) = 0
  exact neutralAction_covector_annihilates_bivector
    (grassmannianRow55 C 0) (grassmannianRow55 C 1) φ h0 h1

/-- The row-plane/covector-annihilator candidate is contained in the neutral
annihilator of the chart blade. -/
theorem positiveGrassmannianMaximalNullCandidate_le_neutralAnnihilator
    (C : Matrix (Fin 2) (Fin 4) ℝ) :
    positiveGrassmannianMaximalNullCandidate C ≤
      neutralAnnihilator (positiveGrassmannianBlade C) := by
  intro z hz
  rcases z with ⟨x, φ⟩
  change x ∈ positiveGrassmannianRowSubspace C ∧
    φ ∈ (positiveGrassmannianRowSubspace C).dualAnnihilator at hz
  rcases hz with ⟨hx, hφ⟩
  have hxann : (x, (0 : Module.Dual ℝ SplitClifford55ExteriorSpinor.V5)) ∈
      neutralAnnihilator (positiveGrassmannianBlade C) := by
    change x ∈ positiveGrassmannianRowSubspace C at hx
    unfold positiveGrassmannianRowSubspace at hx
    refine Submodule.span_induction (p := fun y _ =>
      (y, (0 : Module.Dual ℝ SplitClifford55ExteriorSpinor.V5)) ∈
        neutralAnnihilator (positiveGrassmannianBlade C)) ?_ ?_ ?_ ?_ hx
    · rintro y ⟨i, rfl⟩
      fin_cases i
      · exact positiveGrassmannianBlade_row0_mem_neutralAnnihilator C
      · exact positiveGrassmannianBlade_row1_mem_neutralAnnihilator C
    · exact (neutralAnnihilator (positiveGrassmannianBlade C)).zero_mem
    · intro y w _ _ hy hw
      simpa using (neutralAnnihilator (positiveGrassmannianBlade C)).add_mem hy hw
    · intro a y _ hy
      simpa using (neutralAnnihilator (positiveGrassmannianBlade C)).smul_mem a hy
  have h0 : φ (grassmannianRow55 C 0) = 0 := by
    exact ((Submodule.mem_dualAnnihilator φ).mp hφ) _
      (Submodule.subset_span ⟨0, rfl⟩)
  have h1 : φ (grassmannianRow55 C 1) = 0 := by
    exact ((Submodule.mem_dualAnnihilator φ).mp hφ) _
      (Submodule.subset_span ⟨1, rfl⟩)
  have hφann := positiveGrassmannianBlade_covector_mem_neutralAnnihilator C φ h0 h1
  simpa using (neutralAnnihilator (positiveGrassmannianBlade C)).add_mem hxann hφann

/-- A positive `Gr(2,4)` chart blade is a pure spinor for the native split
`Cl(5,5)` neutral action. The explicit five-dimensional candidate in its
annihilator gives the lower dimension bound; total nullity gives the matching
upper bound. -/
theorem positiveGrassmannianBlade_isPureSpinor_of_positive
    (C : Matrix (Fin 2) (Fin 4) ℝ)
    (hC : InfoGeometry.Canonical.HasPositiveMaximalMinors C) :
    IsPureSpinor (positiveGrassmannianBlade C) := by
  have hblade : positiveGrassmannianBlade C ≠ 0 :=
    positiveGrassmannianBlade_ne_zero_of_positive C hC
  refine ⟨hblade, ?_⟩
  let N := neutralAnnihilator (positiveGrassmannianBlade C)
  have htotal := neutralAnnihilator_totallyNull hblade
  have hupper :=
    InfoGeometry.Clifford.SplitClifford55ProjectivePureSpinor.finrank_le_five_of_totallyNull
      N htotal
  have hlower : 5 ≤ Module.finrank ℝ N := by
    calc
      5 = Module.finrank ℝ (positiveGrassmannianMaximalNullCandidate C) :=
        (positiveGrassmannianMaximalNullCandidate_finrank C hC).symm
      _ ≤ Module.finrank ℝ N :=
        Submodule.finrank_mono
          (positiveGrassmannianMaximalNullCandidate_le_neutralAnnihilator C)
  exact Nat.le_antisymm hupper hlower

/-- The five-dimensional row-plane/covector-annihilator candidate is exactly
the neutral annihilator of the positive chart blade. -/
theorem positiveGrassmannianMaximalNullCandidate_eq_neutralAnnihilator
    (C : Matrix (Fin 2) (Fin 4) ℝ)
    (hC : InfoGeometry.Canonical.HasPositiveMaximalMinors C) :
    positiveGrassmannianMaximalNullCandidate C =
      neutralAnnihilator (positiveGrassmannianBlade C) := by
  apply Submodule.eq_of_le_of_finrank_eq
    (positiveGrassmannianMaximalNullCandidate_le_neutralAnnihilator C)
  rw [positiveGrassmannianMaximalNullCandidate_finrank C hC,
    (positiveGrassmannianBlade_isPureSpinor_of_positive C hC).2]

/-- The projective line of a positive chart blade belongs to the native
projective pure-spinor locus. -/
theorem positiveGrassmannianBlade_projectivePureSpinor
    (C : Matrix (Fin 2) (Fin 4) ℝ)
    (hC : InfoGeometry.Canonical.HasPositiveMaximalMinors C) :
    Projectivization.mk ℝ (positiveGrassmannianBlade C)
        (positiveGrassmannianBlade_ne_zero_of_positive C hC) ∈
      ProjectivePureSpinor := by
  exact (projectivePureSpinor_mk_iff (positiveGrassmannianBlade C)
    (positiveGrassmannianBlade_ne_zero_of_positive C hC)).2
      (positiveGrassmannianBlade_isPureSpinor_of_positive C hC)

/-- The positive Grassmannian chart determines a point of the repository's
maximal-neutral Grassmannian through its projective pure-spinor line. -/
noncomputable def positiveGrassmannianMaximalNeutralPoint
    (C : Matrix (Fin 2) (Fin 4) ℝ)
    (hC : InfoGeometry.Canonical.HasPositiveMaximalMinors C) :
    MaximalNeutralGrassmannian :=
  projectivePureSpinorGrassmannianPoint
    ⟨Projectivization.mk ℝ (positiveGrassmannianBlade C)
        (positiveGrassmannianBlade_ne_zero_of_positive C hC),
      positiveGrassmannianBlade_projectivePureSpinor C hC⟩

/-- The point read out in the maximal-neutral Grassmannian has the explicit
row-plane/covector-annihilator subspace as its carrier. -/
theorem positiveGrassmannianMaximalNeutralPoint_val
    (C : Matrix (Fin 2) (Fin 4) ℝ)
    (hC : InfoGeometry.Canonical.HasPositiveMaximalMinors C) :
    (positiveGrassmannianMaximalNeutralPoint C hC).1 =
      positiveGrassmannianMaximalNullCandidate C := by
  rw [positiveGrassmannianMaximalNeutralPoint,
    projectivePureSpinorGrassmannianPoint_val,
    projectivePureSpinorAnnihilator_mk]
  exact (positiveGrassmannianMaximalNullCandidate_eq_neutralAnnihilator C hC).symm

/-- Strictly positive chart data give a nonzero element of the recursive
symmetric split Clifford algebra. This follows from its faithful Fock action
on the vacuum and the already established nonzero exterior blade. -/
theorem positiveGrassmannianBladeSplitImage_ne_zero_of_positive
    (C : Matrix (Fin 2) (Fin 4) ℝ)
    (hC : InfoGeometry.Canonical.HasPositiveMaximalMinors C) :
    positiveGrassmannianBladeSplitImage C ≠ 0 := by
  intro hzero
  have hact : splitCliffordFockAction
      (positiveGrassmannianBladeSplitImage C)
      (spinorCoordinateEquiv (1 : Exterior55)) = 0 := by
    rw [hzero]
    simp
  rw [positiveGrassmannianBlade_splitFockAction_vacuum] at hact
  change spinorCoordinateEquiv
      ((4 : ℝ) • positiveGrassmannianBlade C) =
        (0 : Fin 32 → ℝ) at hact
  have hcoord : spinorCoordinateEquiv
      ((4 : ℝ) • positiveGrassmannianBlade C) =
        spinorCoordinateEquiv (0 : Exterior55) := by
    rw [map_zero]
    exact hact
  have hscaled : (4 : ℝ) • positiveGrassmannianBlade C = 0 :=
    spinorCoordinateEquiv.injective hcoord
  have hblade : positiveGrassmannianBlade C = 0 := by
    rcases smul_eq_zero.mp hscaled with hfour | hblade
    · norm_num at hfour
    · exact hblade
  exact positiveGrassmannianBlade_ne_zero_of_positive C hC hblade

end InfoGeometry.Clifford.Cl55PositiveGrassmannianFockBridge

end noncomputable section
