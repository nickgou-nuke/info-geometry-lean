/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.Cl11TraceGNSColimitBridge
import InfoGeometry.Canonical.CantorBernoulliCStarMatrixTraceState
import InfoGeometry.Canonical.CuntzGNSFilteredSystem
import InfoGeometry.Canonical.FilteredGNSGlobalStageRepresentation
import InfoGeometry.Canonical.FilteredGNSTomitaCore
import InfoGeometry.Canonical.FiniteHestenesHilbertSchmidtStandardForm
import InfoGeometry.Canonical.Cl11KleinFourAdjointRepresentation
import InfoGeometry.Topology.KleinBottleCliffordGlide
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances

/-!
# Finite `Cl(1,1)` trace GNS classes in the native Hilbert colimit

The finite real trace quotient maps into stage one of the repository's native
complex C⋆ matrix GNS tower, and then into its Hilbert colimit.  The map uses
the existing coherent matrix complexification and Mathlib's `CStarMatrix`
carrier.  This file does not identify the algebraic quotient with the Hilbert
space or claim that its image is dense.
-/

noncomputable section

open scoped ComplexOrder InnerProductSpace NNReal

namespace InfoGeometry.Canonical.Cl11TraceGNSHilbertColimitBridge

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1200000

open CStarStateColimit.Native.FilteredGNSHilbertColimit
open CStarStateColimit.Native.FilteredGNSGlobalStageRepresentation
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Cosmology.Cl11ParabolicVacuumQuotientBridge
open InfoGeometry.Canonical.CantorBernoulliCStarMatrixTraceState
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.Cl11CuntzCoherentIndexTopologicalBridge
open InfoGeometry.Canonical.Cl11TraceGNSColimitBridge
open InfoGeometry.Canonical.Cl11KleinFourAdjointRepresentation
open InfoGeometry.Canonical.Cl11FiniteTraceGNSAction
open InfoGeometry.Prequantum.GNSBridge.AbstractGNSState
open InfoGeometry.Projective.SplitQuaternionRankOneProjective

local instance cstarMatrixStageRealCFC (n : ℕ) :
    NonUnitalContinuousFunctionalCalculus ℝ (CStarMatrixStage n) IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus

local instance cstarMatrixStageNonnegSpectrum (n : ℕ) :
    NonnegSpectrumClass ℝ (CStarMatrixStage n) :=
  CStarAlgebra.instNonnegSpectrumClass

/-- The coherent complex matrix realization of a finite `Cl(1,1)` stage-one
representative in Mathlib's finite C⋆ matrix carrier. -/
def cl11StageOneToCStarMatrix (X : MatStage 1) : CStarMatrixStage 1 :=
  CStarMatrix.ofMatrixStarAlgEquiv (coherentComplexifyClStage 1 X)

/-- The finite Clifford realization as an explicit composite of native ring
homomorphisms: real Clifford stage, coherent complexification, then the
Mathlib matrix-to-`CStarMatrix` equivalence. -/
def cl11StageOneToCStarMatrixRingHom : MatStage 1 →+* CStarMatrixStage 1 :=
  (CStarMatrix.ofMatrixStarAlgEquiv.toRingEquiv.toRingHom).comp
    (coherentComplexifyClStage 1).toRingHom

/-- The native C⋆ matrix state restricts along coherent complexification to
the complexification of the real normalized Clifford trace. -/
theorem cstarTraceState_cl11StageOne (X : MatStage 1) :
    (cstarMatrixTraceState 1).functional (cl11StageOneToCStarMatrix X) =
      Complex.ofReal (normalizedTrace 1 X) := by
  change cstarMatrixPositiveTraceFunctional 1
    (cl11StageOneToCStarMatrix X) = _
  rw [cstarMatrixPositiveTraceFunctional_apply]
  change matrixTraceState 1
    ((CStarMatrix.ofMatrixStarAlgEquiv).symm
      (CStarMatrix.ofMatrixStarAlgEquiv (coherentComplexifyClStage 1 X))) = _
  rw [(CStarMatrix.ofMatrixStarAlgEquiv).symm_apply_apply]
  exact coherentComplexifyClStage_normalizedTrace 1 X

/-- The finite C⋆ GNS vector represented by a stage-one Clifford matrix. -/
def cl11StageOneCStarGNSVector (X : MatStage 1) :
    (cstarMatrixTraceState 1).functional.GNS :=
  ↑((cstarMatrixTraceState 1).functional.toPreGNS
    (cl11StageOneToCStarMatrix X))

/-- The faithful finite trace makes the stage-one Clifford-to-GNS vector map
injective.  Equality in the completed GNS space forces the normalized trace
of the squared difference to vanish, hence the matrices agree. -/
theorem cl11StageOneCStarGNSVector_injective :
    Function.Injective cl11StageOneCStarGNSVector := by
  intro X Y h
  let f := (cstarMatrixTraceState 1).functional
  have hsub : cl11StageOneCStarGNSVector (X - Y) = 0 := by
    change ((f.toPreGNS (cl11StageOneToCStarMatrix (X - Y)) :
      f.PreGNS) : f.GNS) = 0
    have hmapSub : cl11StageOneToCStarMatrix (X - Y) =
        cl11StageOneToCStarMatrix X - cl11StageOneToCStarMatrix Y := by
      simp [cl11StageOneToCStarMatrix]
    rw [hmapSub, map_sub, UniformSpace.Completion.coe_sub]
    apply sub_eq_zero.mpr
    change cl11StageOneCStarGNSVector X = cl11StageOneCStarGNSVector Y
    exact h
  have hnorm :
      ‖f.toPreGNS (cl11StageOneToCStarMatrix (X - Y))‖ = 0 := by
    have hnorm' := congrArg norm hsub
    simpa [cl11StageOneCStarGNSVector,
      UniformSpace.Completion.norm_coe] using hnorm'
  have hquad := f.preGNS_norm_sq
    (f.toPreGNS (cl11StageOneToCStarMatrix (X - Y)))
  rw [hnorm] at hquad
  have hstate : f
      (star (cl11StageOneToCStarMatrix (X - Y)) *
        cl11StageOneToCStarMatrix (X - Y)) = 0 := by
    simpa [PositiveLinearMap.ofPreGNS_toPreGNS] using hquad.symm
  have hmatrix : cl11StageOneToCStarMatrix (X - Y) = 0 :=
    (cstarMatrixTraceState_faithful 1 _).mp hstate
  have hmatrix' : cl11StageOneToCStarMatrix X -
      cl11StageOneToCStarMatrix Y = 0 := by
    simpa [cl11StageOneToCStarMatrix] using hmatrix
  have hmap : cl11StageOneToCStarMatrix X =
      cl11StageOneToCStarMatrix Y := by
    exact sub_eq_zero.mp hmatrix'
  apply coherentComplexifyClStage_injective 1
  exact (CStarMatrix.ofMatrixStarAlgEquiv).injective hmap

/-- The Hilbert colimit of the concrete normalized-trace C⋆ matrix tower. -/
abbrev CuntzMatrixTraceHilbertColimit : Type :=
  GNSHilbertColimit CStarMatrixStage cstarMatrixInductiveSystem
    cstarMatrixTraceStateFamily

/-- The completed GNS space at the first finite C⋆ matrix stage. -/
abbrev CuntzMatrixStageOneGNS : Type :=
  (cstarMatrixTraceState 1).functional.GNS

/-- Embed a finite stage-one C⋆ GNS vector into the completed Hilbert colimit. -/
def cl11StageOneGNSVectorToColimit (X : MatStage 1) :
    CuntzMatrixTraceHilbertColimit :=
  gnsStageToHilbertColimit CStarMatrixStage cstarMatrixInductiveSystem
    cstarMatrixTraceStateFamily 1 (cl11StageOneCStarGNSVector X)

/-- Stage-one Clifford matrices remain distinct in the global Hilbert
colimit: the finite faithful GNS map is followed by Mathlib's isometric
stage inclusion. -/
theorem cl11StageOneGNSVectorToColimit_injective :
    Function.Injective cl11StageOneGNSVectorToColimit := by
  intro X Y h
  apply cl11StageOneCStarGNSVector_injective
  exact (gnsStageToHilbertColimit CStarMatrixStage
    cstarMatrixInductiveSystem cstarMatrixTraceStateFamily 1).injective h

/-- Send a class in the finite real trace-GNS quotient to the corresponding
vector in the native complex C⋆ matrix Hilbert colimit.  Faithfulness of the
finite real trace quotient makes the representative map well-defined. -/
noncomputable def traceGNS_to_CuntzMatrixStageGNS
    (q : cl11RepresentationQuotient 1) : CuntzMatrixStageOneGNS :=
  Quotient.lift cl11StageOneCStarGNSVector (by
    intro X Y hXY
    have hEq := cl11TraceGNS_stageOne_setoid_eq hXY
    subst Y
    rfl) q

@[simp] theorem traceGNS_to_CuntzMatrixStageGNS_mk (X : MatStage 1) :
    traceGNS_to_CuntzMatrixStageGNS
      (Quotient.mk (gnsSetoid (cl11RepresentationState 1).state) X) =
        cl11StageOneCStarGNSVector X := rfl

/-- Multiplication in the finite Clifford stage becomes the native Mathlib
GNS representation action on its complexified C⋆ matrix realization. -/
theorem cl11StageOneCStarGNSVector_action (A X : MatStage 1) :
    cl11StageOneCStarGNSVector (A * X) =
      (cstarMatrixTraceState 1).functional.gnsStarAlgHom
        (cl11StageOneToCStarMatrix A)
        (cl11StageOneCStarGNSVector X) := by
  simp [cl11StageOneCStarGNSVector, cl11StageOneToCStarMatrix,
    PositiveLinearMap.gnsStarAlgHom,
    PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_coe,
    PositiveLinearMap.leftMulMapPreGNS, map_mul]

/-- The finite C⋆ GNS matrix coefficient against the cyclic unit vector is
the normalized Clifford trace.  This uses Mathlib's native pre-GNS inner
product and the explicit complexification trace theorem above. -/
theorem cl11StageOneCStarGNSVector_inner_unit (X : MatStage 1) :
    inner ℂ (cl11StageOneCStarGNSVector 1)
      (cl11StageOneCStarGNSVector X) =
        Complex.ofReal (normalizedTrace 1 X) := by
  simp only [cl11StageOneCStarGNSVector,
    UniformSpace.Completion.inner_coe,
    PositiveLinearMap.preGNS_inner_def,
    PositiveLinearMap.ofPreGNS_toPreGNS]
  change (cstarMatrixTraceState 1).functional
      (star (cl11StageOneToCStarMatrix 1) *
        cl11StageOneToCStarMatrix X) = _
  simp only [cl11StageOneToCStarMatrix, map_one, star_one, one_mul]
  exact cstarTraceState_cl11StageOne X

/-- The full Hilbert pairing of two stage-one GNS vectors is the normalized
matrix trace pairing.  This is the finite-stage Hilbert--Schmidt readout;
unlike the unit-vector specialization above, it records both matrix inputs. -/
theorem cl11StageOneCStarGNSVector_inner (X Y : MatStage 1) :
    inner ℂ (cl11StageOneCStarGNSVector X)
      (cl11StageOneCStarGNSVector Y) =
        matrixTraceState 1
          (star (coherentComplexifyClStage 1 X) *
            coherentComplexifyClStage 1 Y) := by
  simp only [cl11StageOneCStarGNSVector,
    UniformSpace.Completion.inner_coe,
    PositiveLinearMap.preGNS_inner_def,
    PositiveLinearMap.ofPreGNS_toPreGNS]
  change cstarMatrixPositiveTraceFunctional 1
    (star (cl11StageOneToCStarMatrix X) *
      cl11StageOneToCStarMatrix Y) = _
  rw [cstarMatrixPositiveTraceFunctional_apply]
  change matrixTraceState 1
    ((CStarMatrix.ofMatrixStarAlgEquiv).symm
      (star (cl11StageOneToCStarMatrix X) *
        cl11StageOneToCStarMatrix Y)) = _
  rw [map_mul, map_star]
  change matrixTraceState 1
    (star ((CStarMatrix.ofMatrixStarAlgEquiv).symm
        (cl11StageOneToCStarMatrix X)) *
      (CStarMatrix.ofMatrixStarAlgEquiv).symm
        (cl11StageOneToCStarMatrix Y)) = _
  simp [cl11StageOneToCStarMatrix]

/-- The normalized trace pairing on the full complex stage-one matrix algebra
is one half of its Hilbert--Schmidt pairing.  This is the matrix identity
underlying the GNS-to-standard-form isometry, without restricting the inputs
to the real Clifford subalgebra. -/
theorem matrixTraceState_stageOne_star_mul_eq_hilbertSchmidt
    (X Y : FiniteHestenesHilbertSchmidtStandardForm.HS2) :
    matrixTraceState 1 (star X * Y) =
      (1 / 2 : ℂ) *
        FiniteHestenesHilbertSchmidtStandardForm.hilbertSchmidtInner X Y := by
  simp [matrixTraceState_apply,
    FiniteHestenesHilbertSchmidtStandardForm.hilbertSchmidtInner,
    Matrix.trace, Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_two]
  ring

/-- In the common matrix carrier, the stage-one C⋆ GNS inner product is the
Hilbert--Schmidt pairing scaled by the normalized-trace factor `1/2`.  This
identifies the finite GNS metric with the standard-form metric, including its
normalization. -/
theorem cl11StageOneCStarGNSVector_inner_eq_hilbertSchmidt
    (X Y : MatStage 1) :
    inner ℂ (cl11StageOneCStarGNSVector X)
        (cl11StageOneCStarGNSVector Y) =
      (1 / 2 : ℂ) *
        FiniteHestenesHilbertSchmidtStandardForm.hilbertSchmidtInner
          (coherentComplexifyClStage 1 X) (coherentComplexifyClStage 1 Y) := by
  rw [cl11StageOneCStarGNSVector_inner,
    matrixTraceState_stageOne_star_mul_eq_hilbertSchmidt]

/-- The scalar converting the normalized trace norm on `M₂(ℂ)` to the
unnormalized Hilbert--Schmidt norm. -/
noncomputable def stageOneTraceHilbertSchmidtScale : ℂ :=
  (Real.sqrt 2 : ℂ) * (1 / 2 : ℂ)

theorem stageOneTraceHilbertSchmidtScale_star_mul_self :
    star stageOneTraceHilbertSchmidtScale *
      stageOneTraceHilbertSchmidtScale = (1 / 2 : ℂ) := by
  have hsqrt : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast (Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num))
  have hstar : star (Real.sqrt 2 : ℂ) = (Real.sqrt 2 : ℂ) := by
    simp
  rw [stageOneTraceHilbertSchmidtScale, star_mul, hstar]
  have hhalf : star (1 / 2 : ℂ) = (1 / 2 : ℂ) := by simp
  rw [hhalf]
  calc
    (1 / 2 : ℂ) * (Real.sqrt 2 : ℂ) *
        ((Real.sqrt 2 : ℂ) * (1 / 2 : ℂ)) =
        (Real.sqrt 2 : ℂ) ^ 2 * (1 / 2 : ℂ) ^ 2 := by ring
    _ = (1 / 2 : ℂ) := by rw [hsqrt]; norm_num

/-- Read a stage-one pre-GNS vector as a matrix in the Hilbert--Schmidt
standard form, with the positive real normalization dictated by normalized
trace. -/
def stageOnePreGNSHilbertSchmidtReadout :
    (cstarMatrixTraceState 1).functional.PreGNS →ₗ[ℂ]
      FiniteHestenesHilbertSchmidtStandardForm.HS2 where
  toFun x := stageOneTraceHilbertSchmidtScale •
    (CStarMatrix.ofMatrixStarAlgEquiv).symm
      ((cstarMatrixTraceState 1).functional.ofPreGNS x)
  map_add' x y := by simp
  map_smul' z x := by
    simp only [map_smul, smul_smul, RingHom.id_apply]
    rw [mul_comm z stageOneTraceHilbertSchmidtScale]

/-- The stage-one pre-GNS readout preserves the full complex inner product.
This is the finite-dimensional isometric core of the standard-form
identification. -/
theorem stageOnePreGNSHilbertSchmidtReadout_inner
    (x y : (cstarMatrixTraceState 1).functional.PreGNS) :
    FiniteHestenesHilbertSchmidtStandardForm.hilbertSchmidtInner
        (stageOnePreGNSHilbertSchmidtReadout x)
        (stageOnePreGNSHilbertSchmidtReadout y) = inner ℂ x y := by
  let f := (cstarMatrixTraceState 1).functional
  obtain ⟨A, rfl⟩ := f.toPreGNS.surjective x
  obtain ⟨B, rfl⟩ := f.toPreGNS.surjective y
  change FiniteHestenesHilbertSchmidtStandardForm.hilbertSchmidtInner
      (stageOneTraceHilbertSchmidtScale •
        (CStarMatrix.ofMatrixStarAlgEquiv).symm A)
      (stageOneTraceHilbertSchmidtScale •
        (CStarMatrix.ofMatrixStarAlgEquiv).symm B) = _
  rw [FiniteHestenesHilbertSchmidtStandardForm.hilbertSchmidtInner_smul_left,
    FiniteHestenesHilbertSchmidtStandardForm.hilbertSchmidtInner_smul_right]
  rw [← mul_assoc]
  rw [PositiveLinearMap.preGNS_inner_def]
  simp only [PositiveLinearMap.ofPreGNS_toPreGNS]
  rw [stageOneTraceHilbertSchmidtScale_star_mul_self]
  change (1 / 2 : ℂ) *
      FiniteHestenesHilbertSchmidtStandardForm.hilbertSchmidtInner
        ((CStarMatrix.ofMatrixStarAlgEquiv).symm A)
        ((CStarMatrix.ofMatrixStarAlgEquiv).symm B) =
    cstarMatrixPositiveTraceFunctional 1 (star A * B)
  exact (cstarMatrixTraceState_stageOne_hilbertSchmidt A B).symm

/-- The stage-one pre-GNS readout carries Mathlib's algebraic left action to
the left regular matrix action in the Hilbert--Schmidt standard form. -/
theorem stageOnePreGNSHilbertSchmidtReadout_leftAction
    (A : CStarMatrixStage 1)
    (x : (cstarMatrixTraceState 1).functional.PreGNS) :
    stageOnePreGNSHilbertSchmidtReadout
        ((cstarMatrixTraceState 1).functional.leftMulMapPreGNS A x) =
      FiniteHestenesHilbertSchmidtStandardForm.leftActionLinear
        ((CStarMatrix.ofMatrixStarAlgEquiv).symm A)
        (stageOnePreGNSHilbertSchmidtReadout x) := by
  let f := (cstarMatrixTraceState 1).functional
  obtain ⟨B, rfl⟩ := f.toPreGNS.surjective x
  simp [stageOnePreGNSHilbertSchmidtReadout,
    PositiveLinearMap.leftMulMapPreGNS,
    FiniteHestenesHilbertSchmidtStandardForm.leftActionLinear,
    map_mul]

/-- The same readout carries the native algebraic GNS Tomita core to matrix
adjunction on the Hilbert--Schmidt standard form. -/
theorem stageOnePreGNSHilbertSchmidtReadout_tomita
    (x : (cstarMatrixTraceState 1).functional.PreGNS) :
    FiniteHestenesTomitaBridge.matrixTomita
        (stageOnePreGNSHilbertSchmidtReadout x) =
      stageOnePreGNSHilbertSchmidtReadout
        (CStarStateColimit.Native.FilteredGNSTomitaCore.tomitaCore
          (cstarMatrixTraceState 1) x) := by
  let f := (cstarMatrixTraceState 1).functional
  obtain ⟨A, rfl⟩ := f.toPreGNS.surjective x
  have hscale : star stageOneTraceHilbertSchmidtScale =
      stageOneTraceHilbertSchmidtScale := by
    simp [stageOneTraceHilbertSchmidtScale]
  change Matrix.conjTranspose
      (stageOneTraceHilbertSchmidtScale •
        (CStarMatrix.ofMatrixStarAlgEquiv).symm A) =
    stageOneTraceHilbertSchmidtScale •
      (CStarMatrix.ofMatrixStarAlgEquiv).symm (star A)
  rw [Matrix.conjTranspose_smul, hscale, ← Matrix.star_eq_conjTranspose]
  simp only [map_star]

/-- The canonical Clifford fibre, represented by the established real matrix
equivalence, then by the coherent stage-one complexification in the native
C⋆ matrix carrier. -/
noncomputable def cl11FiberToCStarStageOne (
    a : CliffordAlgebra InfoGeometry.Clifford.Cl11Matrix.q11) :
    CStarMatrixStage 1 :=
  cl11StageOneToCStarMatrix
    (matrixToCl11StageOne (cl11EquivMat a))

/-- The image of the positive-signature Clifford generator is the finite-stage
implementer of the reflection in the chosen matrix representation. This is
not a positivity assertion for the C⋆ order. -/
noncomputable def cl11GlideImplementer : CStarMatrixStage 1 :=
  cl11FiberToCStarStageOne
    (CliffordAlgebra.ι _root_.InfoGeometry.Clifford.Cl11Matrix.q11 (1, 0))

/-- The implemented glide generator is self-adjoint in the native C⋆ matrix
stage.  This is proved from its concrete diagonal real-matrix value, through
the stage reindexing, coherent complexification, and Mathlib's matrix
`CStarMatrix` equivalence. -/
theorem cl11GlideImplementer_selfAdjoint :
    star cl11GlideImplementer = cl11GlideImplementer := by
  let m : MatStage 1 := matrixToCl11StageOne Eplus
  have hm : star m = m := by
    change Matrix.transpose (matrixToCl11StageOne Eplus) = _
    simp only [matrixToCl11StageOne,
      InfoGeometry.Clifford.TowerMatrix.matEquivFinPowTwo,
      Matrix.symm_reindexAlgEquiv, Matrix.coe_reindexAlgEquiv]
    rw [Matrix.transpose_reindex]
    rw [show Matrix.transpose (Eplus : Matrix (Fin 2) (Fin 2) ℝ) = Eplus by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Eplus]]
    rfl
  have hcomplex :
      star (coherentComplexifyClStage 1 m) = coherentComplexifyClStage 1 m := by
    calc
      star (coherentComplexifyClStage 1 m) =
          coherentComplexifyClStage 1 (star m) :=
        (coherentComplexifyClStage_star 1 m).symm
      _ = coherentComplexifyClStage 1 m := congrArg _ hm
  unfold cl11GlideImplementer cl11FiberToCStarStageOne
    cl11StageOneToCStarMatrix
  simp only [cl11EquivMat_iota_pos]
  change star (CStarMatrix.ofMatrixStarAlgEquiv
      (coherentComplexifyClStage 1
        (matrixToCl11StageOne Eplus))) =
    CStarMatrix.ofMatrixStarAlgEquiv
      (coherentComplexifyClStage 1
        (matrixToCl11StageOne Eplus))
  calc
    star (CStarMatrix.ofMatrixStarAlgEquiv
        (coherentComplexifyClStage 1
          (matrixToCl11StageOne Eplus))) =
        CStarMatrix.ofMatrixStarAlgEquiv
          (star (coherentComplexifyClStage 1
            (matrixToCl11StageOne Eplus))) :=
      (map_star CStarMatrix.ofMatrixStarAlgEquiv
        (coherentComplexifyClStage 1
          (matrixToCl11StageOne Eplus))).symm
    _ = CStarMatrix.ofMatrixStarAlgEquiv
        (coherentComplexifyClStage 1
          (matrixToCl11StageOne Eplus)) :=
      congrArg CStarMatrix.ofMatrixStarAlgEquiv (by simpa [m] using hcomplex)

/-- On the full algebraic stage-one GNS core, matrix Tomita commutes with the
two-sided action of the represented Klein-glide generator.  The result is
finite-stage and algebraic: it makes no assertion about the affine base
translation or a completed modular operator. -/
theorem stageOnePreGNSHilbertSchmidtReadout_tomita_glide
    (A : CStarMatrixStage 1) :
    FiniteHestenesTomitaBridge.matrixTomita
        (stageOnePreGNSHilbertSchmidtReadout
          ((cstarMatrixTraceState 1).functional.toPreGNS
            (cl11GlideImplementer * A * cl11GlideImplementer))) =
      stageOnePreGNSHilbertSchmidtReadout
        ((cstarMatrixTraceState 1).functional.toPreGNS
          (cl11GlideImplementer * star A * cl11GlideImplementer)) := by
  rw [stageOnePreGNSHilbertSchmidtReadout_tomita,
    CStarStateColimit.Native.FilteredGNSTomitaCore.tomitaCore_toPreGNS]
  simp [star_mul, cl11GlideImplementer_selfAdjoint, mul_assoc]

/-- On the represented finite Clifford algebra, the glide-induced fibre
automorphism is conjugation by its positive-generator image. This is the
stage-one transport of `cl11EquivMat_splitReflectionCliffordAuto`. -/
theorem cl11FiberToCStarStageOne_glide (a :
    CliffordAlgebra InfoGeometry.Clifford.Cl11Matrix.q11) :
    cl11FiberToCStarStageOne
        (InfoGeometry.Clifford.Cl11Matrix.splitReflectionCliffordAuto a) =
      cl11GlideImplementer * cl11FiberToCStarStageOne a *
        cl11GlideImplementer := by
  change cl11StageOneToCStarMatrixRingHom
      (matrixToCl11StageOne
        (cl11EquivMat
          (InfoGeometry.Clifford.Cl11Matrix.splitReflectionCliffordAuto a))) =
    cl11StageOneToCStarMatrixRingHom
        (matrixToCl11StageOne
          (cl11EquivMat
            (CliffordAlgebra.ι _root_.InfoGeometry.Clifford.Cl11Matrix.q11 (1, 0)))) *
      cl11StageOneToCStarMatrixRingHom
        (matrixToCl11StageOne (cl11EquivMat a)) *
      cl11StageOneToCStarMatrixRingHom
        (matrixToCl11StageOne
          (cl11EquivMat
            (CliffordAlgebra.ι _root_.InfoGeometry.Clifford.Cl11Matrix.q11 (1, 0))))
  rw [cl11EquivMat_splitReflectionCliffordAuto, adjointAlgEquiv_apply]
  have hginv : (↑(gammaUnit⁻¹) : InfoGeometry.Clifford.Cl11Matrix.Mat2) =
      (gammaUnit : InfoGeometry.Clifford.Cl11Matrix.Mat2) := rfl
  rw [hginv, map_mul, map_mul]
  simp only [cl11EquivMat_iota_pos, gammaUnit_value, map_mul]

/-- On Clifford generators, the transported fibre reflection is exactly the
linear part of the affine Klein glide, by the existing topology-to-Clifford
generator theorem. -/
theorem cl11FiberToCStarStageOne_glide_generator (v : Vec11) :
    cl11FiberToCStarStageOne
        (splitReflectionCliffordAuto (CliffordAlgebra.ι q11 v)) =
      cl11FiberToCStarStageOne
        (CliffordAlgebra.ι q11
          (InfoGeometry.Topology.KleinBottleTangentHolonomy.glideLinearPart v)) := by
  rw [InfoGeometry.Topology.KleinBottleCliffordGlide.kleinGlide_clifford_generator_action]

/-- The finite standard-form readout carries a two-sided matrix sandwich to
the commuting left and right regular actions on the Hilbert--Schmidt carrier. -/
theorem stageOnePreGNSHilbertSchmidtReadout_sandwich
    (U A : CStarMatrixStage 1) :
    stageOnePreGNSHilbertSchmidtReadout
        ((cstarMatrixTraceState 1).functional.toPreGNS (U * A * U)) =
      FiniteHestenesHilbertSchmidtStandardForm.leftActionLinear
          ((CStarMatrix.ofMatrixStarAlgEquiv).symm U)
        (FiniteHestenesHilbertSchmidtStandardForm.rightActionLinear
          ((CStarMatrix.ofMatrixStarAlgEquiv).symm U)
          (stageOnePreGNSHilbertSchmidtReadout
            ((cstarMatrixTraceState 1).functional.toPreGNS A))) := by
  rw [FiniteHestenesHilbertSchmidtStandardForm.leftActionLinear_apply,
    FiniteHestenesHilbertSchmidtStandardForm.rightActionLinear_apply]
  simp only [stageOnePreGNSHilbertSchmidtReadout,
    LinearMap.coe_mk, AddHom.coe_mk,
    PositiveLinearMap.ofPreGNS_toPreGNS]
  rw [map_mul, map_mul]
  simp only [Matrix.smul_mul, Matrix.mul_smul]
  rw [Matrix.mul_assoc]

/-- Under the finite standard-form readout, the glide reflection of a
Clifford element is the simultaneous left and right action of the positive
generator. The right factor is the Hilbert--Schmidt commutant action. This is
a stage-one/pre-GNS theorem; it includes no affine translation or
completion-level modular statement. -/
theorem stageOnePreGNSHilbertSchmidtReadout_glide
    (a : CliffordAlgebra InfoGeometry.Clifford.Cl11Matrix.q11) :
    stageOnePreGNSHilbertSchmidtReadout
        ((cstarMatrixTraceState 1).functional.toPreGNS
          (cl11FiberToCStarStageOne
            (InfoGeometry.Clifford.Cl11Matrix.splitReflectionCliffordAuto a))) =
      FiniteHestenesHilbertSchmidtStandardForm.leftActionLinear
          ((CStarMatrix.ofMatrixStarAlgEquiv).symm cl11GlideImplementer)
        (FiniteHestenesHilbertSchmidtStandardForm.rightActionLinear
          ((CStarMatrix.ofMatrixStarAlgEquiv).symm cl11GlideImplementer)
          (stageOnePreGNSHilbertSchmidtReadout
            ((cstarMatrixTraceState 1).functional.toPreGNS
              (cl11FiberToCStarStageOne a)))) := by
  rw [cl11FiberToCStarStageOne_glide]
  exact stageOnePreGNSHilbertSchmidtReadout_sandwich
    cl11GlideImplementer (cl11FiberToCStarStageOne a)

/-- The quotient-level finite Clifford action is carried to the ordinary
left GNS representation action at the complex C⋆ matrix stage. -/
theorem traceGNS_to_CuntzMatrixStageGNS_action
    (A : MatStage 1) (q : cl11RepresentationQuotient 1) :
    traceGNS_to_CuntzMatrixStageGNS (cl11Action 1 A q) =
      (cstarMatrixTraceState 1).functional.gnsStarAlgHom
        (cl11StageOneToCStarMatrix A)
        (traceGNS_to_CuntzMatrixStageGNS q) := by
  refine Quotient.inductionOn q ?_
  intro X
  rw [cl11Action_mk,
    traceGNS_to_CuntzMatrixStageGNS_mk,
    traceGNS_to_CuntzMatrixStageGNS_mk]
  exact cl11StageOneCStarGNSVector_action A X

/-- Map the finite Clifford trace-GNS quotient into the native Cuntz matrix
Hilbert colimit by first taking its stage-one C⋆ GNS vector. -/
noncomputable def traceGNS_to_CuntzMatrixHilbertColimit
    (q : cl11RepresentationQuotient 1) : CuntzMatrixTraceHilbertColimit :=
  gnsStageToHilbertColimit CStarMatrixStage cstarMatrixInductiveSystem
    cstarMatrixTraceStateFamily 1 (traceGNS_to_CuntzMatrixStageGNS q)

@[simp] theorem traceGNS_to_CuntzMatrixHilbertColimit_mk (X : MatStage 1) :
    traceGNS_to_CuntzMatrixHilbertColimit
      (Quotient.mk (gnsSetoid (cl11RepresentationState 1).state) X) =
        cl11StageOneGNSVectorToColimit X := rfl

/-- The finite real trace-GNS quotient embeds in the completed Cuntz-matrix
Hilbert colimit.  Injectivity is inherited from faithful finite-stage trace
and the isometric inclusion of that stage in the colimit. -/
theorem traceGNS_to_CuntzMatrixHilbertColimit_injective :
    Function.Injective traceGNS_to_CuntzMatrixHilbertColimit := by
  intro q r h
  revert h
  refine Quotient.inductionOn₂ q r ?_
  intro X Y h
  have hcol : cl11StageOneGNSVectorToColimit X =
      cl11StageOneGNSVectorToColimit Y := by
    simpa only [traceGNS_to_CuntzMatrixHilbertColimit_mk] using h
  have hstage : cl11StageOneCStarGNSVector X =
      cl11StageOneCStarGNSVector Y :=
    (gnsStageToHilbertColimit CStarMatrixStage
      cstarMatrixInductiveSystem cstarMatrixTraceStateFamily 1).injective hcol
  have hmatrix : X = Y := cl11StageOneCStarGNSVector_injective hstage
  subst Y
  rfl

/-- The finite Clifford left action is intertwined with the represented
stage-one observable on the native global Hilbert colimit. -/
theorem globalStageRepresentation_stageOne_apply
    (A : CStarMatrixStage 1) (x : CuntzMatrixStageOneGNS) :
    globalStageRepresentationStarAlgHom CStarMatrixStage
        cstarMatrixInductiveSystem cstarMatrixTraceStateFamily 1 A
        (gnsStageToHilbertColimit CStarMatrixStage
          cstarMatrixInductiveSystem cstarMatrixTraceStateFamily 1 x) =
      gnsStageToHilbertColimit CStarMatrixStage
        cstarMatrixInductiveSystem cstarMatrixTraceStateFamily 1
        ((cstarMatrixTraceState 1).functional.gnsStarAlgHom A x) := by
  rw [globalStageRepresentation_stage CStarMatrixStage
    cstarMatrixInductiveSystem cstarMatrixTraceStateFamily A
    ⟨1, le_refl 1⟩ x]
  change gnsStageToHilbertColimit CStarMatrixStage
      cstarMatrixInductiveSystem cstarMatrixTraceStateFamily 1
      ((cstarMatrixTraceState 1).functional.gnsStarAlgHom
        (cstarMatrixInductiveSystem.map (le_refl 1) A) x) = _
  have hmap : cstarMatrixInductiveSystem.map (le_refl 1) A = A := by
    rw [cstarMatrixInductiveSystem.map_id]
    rfl
  rw [hmap]

theorem traceGNS_to_CuntzMatrixHilbertColimit_action
    (A : MatStage 1) (q : cl11RepresentationQuotient 1) :
    traceGNS_to_CuntzMatrixHilbertColimit (cl11Action 1 A q) =
      globalStageRepresentationStarAlgHom CStarMatrixStage
        cstarMatrixInductiveSystem cstarMatrixTraceStateFamily 1
        (cl11StageOneToCStarMatrix A)
        (traceGNS_to_CuntzMatrixHilbertColimit q) := by
  change gnsStageToHilbertColimit CStarMatrixStage
      cstarMatrixInductiveSystem cstarMatrixTraceStateFamily 1
      (traceGNS_to_CuntzMatrixStageGNS (cl11Action 1 A q)) = _
  have haction := traceGNS_to_CuntzMatrixStageGNS_action A q
  rw [haction]
  exact (globalStageRepresentation_stageOne_apply
    (cl11StageOneToCStarMatrix A)
    (traceGNS_to_CuntzMatrixStageGNS q)).symm

/-- The finite GNS vacuum class maps to the image of the unit vector from the
first C⋆ matrix stage. -/
theorem traceGNS_vacuum_maps_to_colimit_unit :
    traceGNS_to_CuntzMatrixHilbertColimit
      (Quotient.mk (gnsSetoid (cl11RepresentationState 1).state)
        (1 : MatStage 1)) =
      cl11StageOneGNSVectorToColimit 1 := rfl


/-- The vacuum-spinor readout carries the left action of every trace-GNS
class to the standard matrix action.  This quotient-level form connects the
abstract finite GNS carrier directly to the soldered two-spinor lane. -/
theorem traceGNS_vacuumSpinor_left_action
    (A : RealMatrix2) (q : cl11RepresentationQuotient 1) :
    cl11TraceGNS_to_vacuumSpinor
        (cl11Action 1 (matrixToCl11StageOne A) q) =
      Matrix.mulVec A (cl11TraceGNS_to_vacuumSpinor q) := by
  refine Quotient.inductionOn q ?_
  intro X
  simpa only [cl11Action_mk,
    cl11TraceGNS_to_vacuumSpinor_mk] using
    cl11TraceGNS_to_vacuumSpinor_intertwines A X

/-- The matrix coefficient of the finite native C⋆ GNS representation at its
cyclic unit vector agrees with the trace read out from the existing
topological Cuntz colimit.  This connects the finite Hilbert-space and
categorical-colimit readouts on the same trace-GNS class. -/
theorem stageOneGNS_inner_unit_eq_topologicalColimitTrace
    (X : MatStage 1) :
    inner ℂ (cl11StageOneCStarGNSVector 1)
        (cl11StageOneCStarGNSVector X) =
      Complex.ofReal
        (CuntzMatrixTraceTopologicalGNSBridge.realTraceTopologicalColimitMap
          CuntzMatrixTraceTower.concreteData
          (traceGNS_to_CuntzTopologicalColimit
            (Quotient.mk (gnsSetoid (cl11RepresentationState 1).state) X))) := by
  rw [cl11StageOneCStarGNSVector_inner_unit]
  have htrace := traceGNS_CuntzColimit_realTrace
    (Quotient.mk (gnsSetoid (cl11RepresentationState 1).state) X)
  rw [traceGNS_eval_mk] at htrace
  rw [← htrace]

/-- Apply the explicit composite ring homomorphism to obtain the global
bounded operator associated to a finite Clifford-stage element. -/
def cl11StageOneRepresentedOperator (X : MatStage 1) :
    CuntzMatrixTraceHilbertColimit →L[ℂ]
      CuntzMatrixTraceHilbertColimit :=
  globalStageRepresentationStarAlgHom CStarMatrixStage
    cstarMatrixInductiveSystem cstarMatrixTraceStateFamily 1
    (cl11StageOneToCStarMatrix X)


/-- The represented finite-stage operator acts on a finite trace-GNS class
by the same action as the Clifford left action. -/
theorem cl11StageOneRepresentedOperator_action
    (A : MatStage 1) (q : cl11RepresentationQuotient 1) :
    (cl11StageOneRepresentedOperator A :
      CuntzMatrixTraceHilbertColimit →L[ℂ]
        CuntzMatrixTraceHilbertColimit)
        (traceGNS_to_CuntzMatrixHilbertColimit q) =
      traceGNS_to_CuntzMatrixHilbertColimit (cl11Action 1 A q) := by
  exact (traceGNS_to_CuntzMatrixHilbertColimit_action A q).symm

/-- On every finite stage-one GNS vector, the global represented observable
acts by the finite left-multiplication action. -/
theorem cl11StageOneRepresentedOperator_action_on_stage
    (A X : MatStage 1) :
    cl11StageOneRepresentedOperator A
        (cl11StageOneGNSVectorToColimit X) =
      cl11StageOneGNSVectorToColimit (A * X) := by
  rw [← traceGNS_to_CuntzMatrixHilbertColimit_mk X]
  rw [cl11StageOneRepresentedOperator_action]
  rw [cl11Action_mk, traceGNS_to_CuntzMatrixHilbertColimit_mk]

/-- On the image of the finite GNS unit, a represented stage-one observable
acts by sending the unit vector to the GNS vector of that observable. -/
theorem cl11StageOneRepresentedOperator_apply_unit (A : MatStage 1) :
    cl11StageOneRepresentedOperator A
        (cl11StageOneGNSVectorToColimit 1) =
      cl11StageOneGNSVectorToColimit A := by
  rw [cl11StageOneRepresentedOperator_action_on_stage]
  simp

/-- The finite stage-one Clifford algebra acts faithfully as bounded
operators on the repository's global Cuntz-matrix GNS Hilbert colimit. -/
theorem cl11StageOneRepresentedOperator_injective :
    Function.Injective cl11StageOneRepresentedOperator := by
  intro A B hAB
  apply cl11StageOneGNSVectorToColimit_injective
  have hEval := congrArg
    (fun T : CuntzMatrixTraceHilbertColimit →L[ℂ]
        CuntzMatrixTraceHilbertColimit =>
      T (cl11StageOneGNSVectorToColimit 1)) hAB
  change cl11StageOneRepresentedOperator A
      (cl11StageOneGNSVectorToColimit 1) =
    cl11StageOneRepresentedOperator B
      (cl11StageOneGNSVectorToColimit 1) at hEval
  rw [cl11StageOneRepresentedOperator_apply_unit,
    cl11StageOneRepresentedOperator_apply_unit] at hEval
  exact hEval

/-- The concrete global GNS representation carries multiplication of
stage-one Clifford observables to composition in the bounded-operator algebra.
This records the multiplicative map on the actual global Hilbert carrier. -/
theorem cl11StageOneRepresentedOperator_mul (A B : MatStage 1) :
    cl11StageOneRepresentedOperator (A * B) =
      cl11StageOneRepresentedOperator A *
        cl11StageOneRepresentedOperator B := by
  apply ContinuousLinearMap.ext
  intro z
  have h_mat : cl11StageOneToCStarMatrix (A * B) =
      cl11StageOneToCStarMatrix A * cl11StageOneToCStarMatrix B :=
    map_mul cl11StageOneToCStarMatrixRingHom A B
  dsimp only [cl11StageOneRepresentedOperator]
  rw [h_mat]
  rw [globalStageRepresentation_mul_apply]
  rfl

theorem cl11StageOneRepresentedOperator_zero :
    cl11StageOneRepresentedOperator 0 = 0 := by
  apply ContinuousLinearMap.ext
  intro z
  have h_mat : cl11StageOneToCStarMatrix 0 = 0 :=
    map_zero cl11StageOneToCStarMatrixRingHom
  dsimp only [cl11StageOneRepresentedOperator]
  rw [h_mat]
  rw [globalStageRepresentation_zero_apply]
  rfl

theorem cl11StageOneRepresentedOperator_one :
    cl11StageOneRepresentedOperator 1 = 1 := by
  apply ContinuousLinearMap.ext
  intro z
  have h_mat : cl11StageOneToCStarMatrix 1 = 1 :=
    map_one cl11StageOneToCStarMatrixRingHom
  dsimp only [cl11StageOneRepresentedOperator]
  rw [h_mat]
  rw [globalStageRepresentation_one_apply]
  rfl

theorem cl11StageOneRepresentedOperator_add (A B : MatStage 1) :
    cl11StageOneRepresentedOperator (A + B) =
      cl11StageOneRepresentedOperator A +
        cl11StageOneRepresentedOperator B := by
  apply ContinuousLinearMap.ext
  intro z
  have h_mat : cl11StageOneToCStarMatrix (A + B) =
      cl11StageOneToCStarMatrix A + cl11StageOneToCStarMatrix B :=
    map_add cl11StageOneToCStarMatrixRingHom A B
  dsimp only [cl11StageOneRepresentedOperator]
  rw [h_mat]
  rw [globalStageRepresentation_add_apply]
  rfl

/-- Square-zero root transport through coherent complexification and
Mathlib's `CStarMatrix` equivalence. -/
theorem cl11StageOneToCStarMatrix_sq_zero_of_sq_zero
    (A : MatStage 1) (hA : A * A = 0) :
    cl11StageOneToCStarMatrix A * cl11StageOneToCStarMatrix A = 0 := by
  let φ : MatStage 1 →ₐ[ℝ] CoherentComplexStage 1 :=
    coherentComplexifyClStage 1
  let ι : CoherentComplexStage 1 ≃⋆ₐ[ℂ] CStarMatrixStage 1 :=
    CStarMatrix.ofMatrixStarAlgEquiv
  change ι (φ A) * ι (φ A) = 0
  calc
    ι (φ A) * ι (φ A) = ι (φ (A * A)) :=
      (ι.map_mul (φ A) (φ A)).symm.trans
        (congrArg ι ((φ.map_mul A A).symm))
    _ = ι (φ 0) := congrArg (fun X : MatStage 1 => ι (φ X)) hA
    _ = ι 0 := congrArg ι φ.map_zero
    _ = 0 := ι.map_zero

/-- Multiplication in the native global representation preserves square-zero
elements of the finite Clifford stage. -/
theorem cl11StageOneRepresentedOperator_sq_zero_of_sq_zero
    (A : MatStage 1) (hA : A * A = 0) :
    cl11StageOneRepresentedOperator A ^ 2 = 0 := by
  calc
    cl11StageOneRepresentedOperator A ^ 2 =
        cl11StageOneRepresentedOperator A *
          cl11StageOneRepresentedOperator A := by rw [pow_two]
    _ = cl11StageOneRepresentedOperator (A * A) :=
      (cl11StageOneRepresentedOperator_mul A A).symm
    _ = cl11StageOneRepresentedOperator 0 :=
      congrArg cl11StageOneRepresentedOperator hA
    _ = 0 := cl11StageOneRepresentedOperator_zero

/-- The split-quaternion raising root remains square-zero after transport to
the global bounded-operator representation. -/
theorem representedRootPlus_sq_zero :
    cl11StageOneRepresentedOperator (matrixToCl11StageOne rootPlus) ^ 2 = 0 := by
  apply cl11StageOneRepresentedOperator_sq_zero_of_sq_zero
  rw [← map_mul, rootPlus_sq_zero, map_zero]

/-- The split-quaternion lowering root remains square-zero after transport to
the global bounded-operator representation. -/
theorem representedRootMinus_sq_zero :
    cl11StageOneRepresentedOperator (matrixToCl11StageOne rootMinus) ^ 2 = 0 := by
  apply cl11StageOneRepresentedOperator_sq_zero_of_sq_zero
  rw [← map_mul, rootMinus_sq_zero, map_zero]

/-- The raising and lowering split-quaternion roots satisfy CAR as bounded
operators on the global GNS Hilbert colimit. -/
theorem cl11StageOneRepresentedOperator_CAR
    (A B : MatStage 1) (hCAR : A * B + B * A = 1) :
    cl11StageOneRepresentedOperator A *
        cl11StageOneRepresentedOperator B +
      cl11StageOneRepresentedOperator B *
        cl11StageOneRepresentedOperator A = 1 := by
  calc
    cl11StageOneRepresentedOperator A *
        cl11StageOneRepresentedOperator B +
      cl11StageOneRepresentedOperator B *
        cl11StageOneRepresentedOperator A =
      cl11StageOneRepresentedOperator (A * B) +
        cl11StageOneRepresentedOperator (B * A) := by
      rw [← cl11StageOneRepresentedOperator_mul A B,
        ← cl11StageOneRepresentedOperator_mul B A]
    _ = cl11StageOneRepresentedOperator (A * B + B * A) :=
      (cl11StageOneRepresentedOperator_add (A * B) (B * A)).symm
    _ = cl11StageOneRepresentedOperator 1 :=
      congrArg cl11StageOneRepresentedOperator hCAR
    _ = 1 := cl11StageOneRepresentedOperator_one

/-- The raising and lowering split-quaternion roots satisfy CAR as bounded
operators on the global GNS Hilbert colimit. -/
theorem representedRoots_anticommutator_eq_one :
    cl11StageOneRepresentedOperator (matrixToCl11StageOne rootPlus) *
        cl11StageOneRepresentedOperator (matrixToCl11StageOne rootMinus) +
      cl11StageOneRepresentedOperator (matrixToCl11StageOne rootMinus) *
        cl11StageOneRepresentedOperator (matrixToCl11StageOne rootPlus) = 1 := by
  apply cl11StageOneRepresentedOperator_CAR
  rw [← map_mul, ← map_mul, ← map_add, root_anticommutator, map_one]

end InfoGeometry.Canonical.Cl11TraceGNSHilbertColimitBridge
