import InfoGeometry.Canonical.AlbertCayleyDickson
import InfoGeometry.Canonical.SplitCliffordTensorBridge
import InfoGeometry.Canonical.Cl44ConformalNormalization
import InfoGeometry.Clifford.BottPeriodicity
import InfoGeometry.Clifford.Hurwitz3DGeometricAlgebra
import InfoGeometry.Clifford.SplitCl44CausalEnvelope
import InfoGeometry.Clifford.SplitCl44Complexification
import InfoGeometry.Clifford.ConformalLift55
import InfoGeometry.Projective.SplitCl44NullBoundary
import InfoGeometry.Projective.Twistor.Incidence

/-!
# Albert / Bott / conformal bridge

This file records the route the repository actually owns:

* the Albert-Cayley-Dickson split doubling has canonical zero divisors;
* the recursive `Cl(1,1)` tensor step produces the split Bott tower;
* the split `Cl(4,4)` and `Cl(5,5)` stages are owned tower stages;
* the split `Cl(4,4)` complexification is kept as a separate comparison theorem;
* the Penrose and split `Cl(4,4)` projective-null quotients are both inhabited;
* the conformal `Cl(5,5)` null-pair construction remains explicit proof debt.

Nothing here claims `twistor space = split octonions`.
The repository keeps those lanes separate.
-/

open scoped TensorProduct

namespace InfoGeometry.Clifford.AlbertBottConformalBridge

open InfoGeometry.Canonical.AlbertCayleyDickson
open InfoGeometry.Canonical.SplitCliffordTensorBridge
open InfoGeometry.Clifford.BottPeriodicity
open InfoGeometry.Clifford.Hurwitz3DGeometricAlgebra
open InfoGeometry.Clifford.SplitCl44CausalEnvelope
open InfoGeometry.Clifford.SplitCl44Complexification

namespace TensorProduct
open GradedTensorProduct
end TensorProduct

/-- The owned Albert split-doubling property. -/
theorem splitAlbert_zero_divisors :
    ∃ x y : AlbertStep ℝ (SplitQuaternion ℝ) (1 : ℝ),
      x ≠ 0 ∧ y ≠ 0 ∧ AlbertStep.mul x y = 0 := by
  simpa [SplitOctonion, SplitQuaternion]
    using
      (AlbertStep.gamma_one_has_canonical_zero_divisors
        (F := ℝ) (A := SplitQuaternion ℝ))

/-- The owned recursive `Cl(1,1)` tensor step. -/
noncomputable abbrev cl11_tensor_step :
    SplitClNNAlg 4 ≃ₐ[ℝ] SplitClNNTensorStep 3 :=
  splitCl44_headFactorEquiv

theorem cl11_tensor_step_eq_owner :
    cl11_tensor_step = splitCliffordTensorStepEquiv 3 :=
  rfl

/-- The owned `Cl(4,4)` split Bott stage. -/
theorem cl44_stage :
    SplitCl44Algebra = SplitBottClifford 4 :=
  rfl

/-- The owned `Cl(5,5)` split Bott stage. -/
noncomputable abbrev cl55_stage_equiv :
    SplitBottClifford 5
      ≃ₐ[ℝ]
        (CliffordAlgebra.evenOdd InfoGeometry.CliffordTower.Q11 ᵍ⊗[ℝ]
          CliffordAlgebra.evenOdd (SplitBottQuad 4)) :=
  cl55_as_splitBottStep

theorem cl55_stage_equiv_eq_owner :
    cl55_stage_equiv = cl55_as_splitBottStep :=
  rfl

/--
The split Bott step admits the supergraded-braided reversed presentation
`Cl(4,4) ᵍ⊗ Cl(1,1)` as well as the owner presentation
`Cl(1,1) ᵍ⊗ Cl(4,4)`.

This is the graded-tensor braiding, not plain commutativity.
-/
noncomputable abbrev cl55_supergraded_braided_tensor_equiv :
    CliffordAlgebra.evenOdd (SplitBottQuad 4) ᵍ⊗[ℝ]
      CliffordAlgebra.evenOdd InfoGeometry.CliffordTower.Q11
      ≃ₐ[ℝ]
        SplitBottClifford 5 :=
  (GradedTensorProduct.comm
    (R := ℝ)
    (𝒜 := CliffordAlgebra.evenOdd InfoGeometry.CliffordTower.Q11)
    (ℬ := CliffordAlgebra.evenOdd (SplitBottQuad 4))).symm.trans
    cl55_as_splitBottStep.symm

theorem cl55_supergraded_braided_tensor_equiv_eq_owner :
    cl55_supergraded_braided_tensor_equiv =
      (GradedTensorProduct.comm
        (R := ℝ)
        (𝒜 := CliffordAlgebra.evenOdd InfoGeometry.CliffordTower.Q11)
        (ℬ := CliffordAlgebra.evenOdd (SplitBottQuad 4))).symm.trans
        cl55_as_splitBottStep.symm :=
  rfl

/-- The owned `Cl(4,4)` complexification equivalence, kept separate from the
split Bott route. -/
noncomputable abbrev cl44_complexification_equiv :
    InfoGeometry.Clifford.SplitCl44Complexification.Cl44Complex ≃ₐ[ℂ]
      ℂ ⊗[ℝ] InfoGeometry.Clifford.BottPeriodicity.Cl44 :=
  cl44ComplexificationEquiv

theorem cl44_complexification_equiv_eq_owner :
    cl44_complexification_equiv = cl44ComplexificationEquiv :=
  rfl

/-- The quadratic conformal closure count is `so(5,5)`-sized. -/
theorem quadratic_conformal_count :
    (InfoGeometry.Canonical.Cl44ConformalNormalization.quadraticLightSpaceDim : Nat)
      + ((InfoGeometry.Canonical.Cl44ConformalNormalization.quadraticLeviRotationDim : Nat)
          + InfoGeometry.Canonical.Cl44ConformalNormalization.dilationCharacterDim)
      + InfoGeometry.Canonical.Cl44ConformalNormalization.quadraticLightSpaceDim
        = InfoGeometry.Canonical.Cl44ConformalNormalization.quadraticConformalClosureDim :=
  InfoGeometry.Canonical.Cl44ConformalNormalization.quadratic_light_conformal_count

/-- The Penrose projective null quotient is inhabited. -/
theorem penrose_projective_null_nonempty :
    Nonempty InfoGeometry.Projective.Twistor.PenroseProjectiveNullTwistor :=
  InfoGeometry.Projective.Twistor.penroseProjectiveNullTwistor_nonempty

/-- The split `Cl(4,4)` projective null quotient is inhabited. -/
theorem splitCl44_projective_null_nonempty :
    Nonempty InfoGeometry.Projective.SplitCl44NullBoundary.SplitCl44ProjectiveNullSpace :=
  InfoGeometry.Projective.SplitCl44NullBoundary.splitCl44ProjectiveNullSpace_nonempty

/- The concrete conformal `Cl(5,5)` null pair is owned by the split Bott
   construction. The `Nonempty` theorem below is retained only as a
   compatibility readout for older route packets. -/
noncomputable abbrev conformal_null_pair :
    InfoGeometry.Clifford.ConformalLift55.ConformalNullPair :=
  InfoGeometry.Clifford.ConformalLift55.conformalNullPair

theorem conformal_null_pair_exists :
    Nonempty InfoGeometry.Clifford.ConformalLift55.ConformalNullPair :=
  ⟨conformal_null_pair⟩

/--
The actual bridge theorem the repository owns:
Albert doubling, split Bott stabilization, projective-null quotients, and
conformal null-pair debt remain separate but compatible surfaces.
-/
theorem albert_bott_conformal_route :
    ∃ x y : AlbertStep ℝ (SplitQuaternion ℝ) (1 : ℝ),
      x ≠ 0 ∧ y ≠ 0 ∧ AlbertStep.mul x y = 0 ∧
    cl11_tensor_step = splitCliffordTensorStepEquiv 3 ∧
    SplitCl44Algebra = SplitBottClifford 4 ∧
    cl55_stage_equiv = cl55_as_splitBottStep ∧
    cl55_supergraded_braided_tensor_equiv =
      (GradedTensorProduct.comm
        (R := ℝ)
        (𝒜 := CliffordAlgebra.evenOdd InfoGeometry.CliffordTower.Q11)
        (ℬ := CliffordAlgebra.evenOdd (SplitBottQuad 4))).symm.trans
        cl55_as_splitBottStep.symm ∧
    cl44_complexification_equiv = cl44ComplexificationEquiv ∧
    (InfoGeometry.Canonical.Cl44ConformalNormalization.quadraticLightSpaceDim : Nat)
      + ((InfoGeometry.Canonical.Cl44ConformalNormalization.quadraticLeviRotationDim : Nat)
          + InfoGeometry.Canonical.Cl44ConformalNormalization.dilationCharacterDim)
      + InfoGeometry.Canonical.Cl44ConformalNormalization.quadraticLightSpaceDim
        = InfoGeometry.Canonical.Cl44ConformalNormalization.quadraticConformalClosureDim ∧
    Nonempty InfoGeometry.Projective.Twistor.PenroseProjectiveNullTwistor ∧
    Nonempty InfoGeometry.Projective.SplitCl44NullBoundary.SplitCl44ProjectiveNullSpace ∧
    Nonempty InfoGeometry.Clifford.ConformalLift55.ConformalNullPair := by
  rcases splitAlbert_zero_divisors with ⟨x, y, hx, hy, hxy⟩
  refine ⟨x, y, ?_⟩
  refine ⟨hx, ?_⟩
  refine ⟨hy, ?_⟩
  refine ⟨hxy, ?_⟩
  refine ⟨cl11_tensor_step_eq_owner, ?_⟩
  refine ⟨cl44_stage, ?_⟩
  refine ⟨cl55_stage_equiv_eq_owner, ?_⟩
  refine ⟨cl55_supergraded_braided_tensor_equiv_eq_owner, ?_⟩
  refine ⟨cl44_complexification_equiv_eq_owner, ?_⟩
  refine ⟨quadratic_conformal_count, ?_⟩
  refine ⟨penrose_projective_null_nonempty, ?_⟩
  refine ⟨splitCl44_projective_null_nonempty, ?_⟩
  exact conformal_null_pair_exists

end InfoGeometry.Clifford.AlbertBottConformalBridge
