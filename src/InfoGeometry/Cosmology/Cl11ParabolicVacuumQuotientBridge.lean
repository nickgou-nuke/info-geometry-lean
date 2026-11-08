import InfoGeometry.Cosmology.SpacetimeParabolicQuotient
import InfoGeometry.Cosmology.KreinBogoliubovCausalPoset
import InfoGeometry.Clifford.SolderingCl11MatrixBridge
import InfoGeometry.Canonical.StateRadicalGNSIdealBridge
import InfoGeometry.Canonical.Cl11FiniteNormalizedTraceState
import InfoGeometry.Canonical.Cl11FiniteTraceGNSAction

/-!
# The `Cl(1,1)` roots in the finite parabolic vacuum quotient

This file transports the explicit Clifford roots through their native
`Cl(1,1) ≃ₐ[ℝ] Mat₂(ℝ)` representation into the finite vacuum-column
quotient. The quotient and its projectivization are those of
`SpacetimeParabolicQuotient`; this is not the filtered trace-state C⋆-GNS
Hilbert space constructed in the gauge-colimit modules.
-/

noncomputable section

namespace InfoGeometry.Cosmology.Cl11ParabolicVacuumQuotientBridge

open InfoGeometry.Clifford.SolderingCl11MatrixBridge
open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Clifford.Soldering
open InfoGeometry.Clifford.SolderingIsomorphism
open InfoGeometry.Projective.SplitQuaternionRankOneProjective
open InfoGeometry.Cosmology.SpacetimeParabolicQuotient
open InfoGeometry.Cosmology.KreinBogoliubov
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.TowerMatrix
open InfoGeometry.Canonical.Cl11FiniteNormalizedTraceState
open InfoGeometry.Canonical.Cl11FiniteTraceGNSAction
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Prequantum.GNSBridge.AbstractGNSState
open scoped LinearAlgebra.Projectivization

abbrev RealMatrix2 := Matrix (Fin 2) (Fin 2) ℝ

/-- The native first matrix stage of the repository's `Cl(1,1)` tower,
transported to the standard `2 × 2` matrix carrier by Mathlib's reindexing
algebra equivalence. -/
noncomputable def matrixToCl11StageOne :
    RealMatrix2 ≃ₐ[ℝ] MatStage 1 :=
  (InfoGeometry.Clifford.TowerMatrix.matEquivFinPowTwo 1).symm

/-- The tower's normalized trace at stage one agrees with half the ordinary
trace after the canonical finite-index reindexing. -/
theorem normalizedTrace_stageOne_matrixToCl11 (A : RealMatrix2) :
    normalizedTrace 1 (matrixToCl11StageOne A) = Matrix.trace A / 2 := by
  change Matrix.trace ((InfoGeometry.Clifford.TowerMatrix.matEquivFinPowTwo 1).symm A) /
      (2 : ℝ) ^ 1 = Matrix.trace A / 2
  have htrace := trace_reindex
    (InfoGeometry.Clifford.TowerMatrix.idxEquivFinPowTwo 1).symm A
  change Matrix.trace ((InfoGeometry.Clifford.TowerMatrix.matEquivFinPowTwo 1).symm A) =
    Matrix.trace A at htrace
  rw [htrace]
  norm_num

/-- The normalized `RealAlgebraicState` already owned by the `Cl(1,1)` tower
reads the reindexed first-stage matrix as its normalized trace. -/
theorem normalizedTraceState_stageOne_matrixToCl11 (A : RealMatrix2) :
    (normalizedTraceState 1).eval (matrixToCl11StageOne A) =
      Matrix.trace A / 2 := by
  rw [normalizedTraceState_eval, normalizedTrace_stageOne_matrixToCl11]

/-- The finite vacuum state as an additive map to the scalar field. -/
def vacuumStateAddHom : RealMatrix2 →+ ℝ where
  toFun := vacuumState
  map_zero' := by simp [vacuumState]
  map_add' A B := by simp [vacuumState]

/-- View the scalar vacuum evaluation as a matrix-valued additive map by the
canonical central scalar embedding. This lets the finite model instantiate
the repository's abstract star-ring radical without changing its carrier. -/
def vacuumStateMatrixHom : RealMatrix2 →+ RealMatrix2 :=
  (algebraMap ℝ RealMatrix2).toAddMonoidHom.comp vacuumStateAddHom

@[simp] theorem vacuumStateMatrixHom_apply (A : RealMatrix2) :
    vacuumStateMatrixHom A = algebraMap ℝ RealMatrix2 (vacuumState A) := rfl

/-- The finite vacuum evaluation is the sum of the scalar trace and the
Krein-weighted trace, each with coefficient `1/2`. This explicitly connects
the state readout to the existing Krein fundamental symmetry. -/
theorem vacuumState_eq_trace_add_krein_trace (A : RealMatrix2) :
    vacuumState A =
      (Matrix.trace A + Matrix.trace (kreinMetric * A)) / 2 := by
  simp [vacuumState, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    kreinMetric, Fin.sum_univ_two]
  ; ring

/-- The finite vacuum functional is the native first-stage normalized trace
state plus the Krein-weighted trace correction. -/
theorem vacuumState_eq_stageOne_state_add_krein_correction (A : RealMatrix2) :
    vacuumState A =
      (normalizedTraceState 1).eval (matrixToCl11StageOne A) +
        Matrix.trace (kreinMetric * A) / 2 := by
  rw [normalizedTraceState_stageOne_matrixToCl11,
    vacuumState_eq_trace_add_krein_trace]
  ring

/-- The scalar embedding into `M₂(ℝ)` is injective on the `(0,0)` entry. -/
theorem algebraMap_realMatrix2_eq_zero_iff (r : ℝ) :
    algebraMap ℝ RealMatrix2 r = 0 ↔ r = 0 := by
  constructor
  · intro h
    have h00 := congrArg (fun M : RealMatrix2 => M 0 0) h
    simpa [Matrix.algebraMap_matrix_apply] using h00
  · rintro rfl
    simp

/-- For real matrices, the star pairing used by the abstract state radical is
the transpose pairing used in the explicit vacuum annihilator. -/
theorem vacuumState_star_mul_eq_transpose (B A : RealMatrix2) :
    vacuumState (star B * A) = vacuumState (B.transpose * A) := by
  rw [Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial]

/-- The vacuum quadratic form on a matrix is the sum of squares in its first
column, equivalently the Euclidean squared norm of the vacuum orbit vector. -/
theorem vacuumState_star_mul_self_eq_column_sq (A : RealMatrix2) :
    vacuumState (star A * A) = (A 0 0) ^ 2 + (A 1 0) ^ 2 := by
  rw [vacuumState_star_mul_eq_transpose]
  simp [vacuumState, Matrix.mul_apply, Matrix.transpose_apply,
    Fin.sum_univ_two]
  ; ring

/-- The finite vacuum functional is nonnegative on elements of the form
`star A * A`; this is the positivity statement underlying its null quotient. -/
theorem vacuumState_star_mul_self_nonneg (A : RealMatrix2) :
    0 ≤ vacuumState (star A * A) := by
  rw [vacuumState_star_mul_self_eq_column_sq]
  positivity

/-- Vanishing of the finite vacuum quadratic form is exactly membership in
the explicitly defined GNS null radical. -/
theorem InGNSNull_iff_vacuumState_star_mul_self_eq_zero (A : RealMatrix2) :
    InGNSNull A ↔ vacuumState (star A * A) = 0 := by
  rw [vacuumState_star_mul_self_eq_column_sq,
    inGNSNull_iff_mulVec_vacuum, mulVec_cyclicVacuum_eq_zero]
  constructor
  · rintro ⟨h₀, h₁⟩
    simp [h₀, h₁]
  · intro h
    constructor <;> nlinarith [sq_nonneg (A 0 0), sq_nonneg (A 1 0)]

/-- The finite vacuum annihilator is exactly the abstract star-ring radical
for the scalar vacuum evaluation embedded centrally in the matrix algebra. -/
theorem mem_vacuumStateMatrixRadical_iff_InGNSNull (A : RealMatrix2) :
    A ∈ InfoGeometry.Canonical.StateRadicalGNSIdealBridge.gnsRadical
      vacuumStateMatrixHom ↔ InGNSNull A := by
  rw [InfoGeometry.Canonical.StateRadicalGNSIdealBridge.mem_gnsRadical_iff]
  constructor
  · intro h B
    have hzero : vacuumStateMatrixHom (star B * A) = 0 := by
      exact h B
    rw [vacuumStateMatrixHom_apply,
      algebraMap_realMatrix2_eq_zero_iff] at hzero
    calc
      vacuumState (B.transpose * A) = vacuumState (star B * A) :=
        (vacuumState_star_mul_eq_transpose B A).symm
      _ = 0 := hzero
  · intro h B
    change vacuumStateMatrixHom (star B * A) = 0
    rw [vacuumStateMatrixHom_apply]
    apply (algebraMap_realMatrix2_eq_zero_iff _).2
    rw [vacuumState_star_mul_eq_transpose]
    exact h B

/-- The finite vacuum evaluation is not tracial: it distinguishes the two
opposite CAR root products. -/
theorem vacuumStateMatrixHom_not_tracial :
    ¬ InfoGeometry.Canonical.StateRadicalGNSIdealBridge.IsTracial
      vacuumStateMatrixHom := by
  intro htrace
  have h := htrace rootPlus rootMinus
  have hplus : vacuumState (rootPlus * rootMinus) = 1 := by
    rw [rootPlus_eq_matrix, rootMinus_eq_matrix]
    norm_num [vacuumState, Matrix.mul_apply, Fin.sum_univ_two]
  have hminus : vacuumState (rootMinus * rootPlus) = 0 := by
    rw [rootPlus_eq_matrix, rootMinus_eq_matrix]
    norm_num [vacuumState, Matrix.mul_apply, Fin.sum_univ_two]
  simp [hplus, hminus] at h

/-- In the concrete vacuum radical the raising root is present, but multiplying
it on the right by the lowering root leaves the radical. Thus this radical is
left-sided and not a two-sided ideal for this nontracial state. -/
theorem vacuumStateMatrixRadical_rootPlus_not_right_stable :
    rootPlus ∈ InfoGeometry.Canonical.StateRadicalGNSIdealBridge.gnsRadical
        vacuumStateMatrixHom ∧
      rootPlus * rootMinus ∉
        InfoGeometry.Canonical.StateRadicalGNSIdealBridge.gnsRadical
          vacuumStateMatrixHom := by
  constructor
  · exact (mem_vacuumStateMatrixRadical_iff_InGNSNull rootPlus).2
      solderingRootPlus_mem_InGNSNull
  · intro hmem
    have hnull :=
      (mem_vacuumStateMatrixRadical_iff_InGNSNull
        (rootPlus * rootMinus)).1 hmem
    have hquad :=
      (InGNSNull_iff_vacuumState_star_mul_self_eq_zero
        (rootPlus * rootMinus)).1 hnull
    have hproduct : rootPlus * rootMinus =
        (!![(1 : ℝ), 0; 0, 0] : RealMatrix2) := by
      rw [rootPlus_eq_matrix, rootMinus_eq_matrix]
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [Matrix.mul_apply, Fin.sum_univ_two]
    rw [hproduct] at hquad
    norm_num [vacuumState, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_apply,
      Matrix.mul_apply, Fin.sum_univ_two] at hquad

/-- The same raising root is null for the finite vacuum state but survives in
the native first-stage trace GNS quotient. This compares the two existing
state-dependent null constructions after transporting the matrix to `MatStage 1`.
-/
theorem cl11RootPlus_vacuumNull_but_traceNonNull :
    InGNSNull rootPlus ∧
      matrixToCl11StageOne rootPlus ∉
        (cl11RepresentationState 1).state.gnsNullSet := by
  refine ⟨solderingRootPlus_mem_InGNSNull, ?_⟩
  intro hnull
  have hquad : normalizedTrace 1
      (star (matrixToCl11StageOne rootPlus) * matrixToCl11StageOne rootPlus) = 0 := by
    have h := (InfoGeometry.Prequantum.GNSBridge.AbstractGNSState.mem_gnsNullSet_iff
      (cl11RepresentationState 1).state (matrixToCl11StageOne rootPlus)).mp hnull
    change (InfoGeometry.Canonical.Cl11FiniteTraceGNSReadout.cl11AbstractGNSState 1).eval
      (star (matrixToCl11StageOne rootPlus) * matrixToCl11StageOne rootPlus) = 0 at h
    rw [InfoGeometry.Canonical.Cl11FiniteTraceGNSReadout.cl11AbstractGNSState_eval] at h
    exact h
  have hzero :=
    (normalizedTrace_star_mul_self_eq_zero_iff 1
      (matrixToCl11StageOne rootPlus)).mp hquad
  have hroot : rootPlus = 0 := (matrixToCl11StageOne).injective hzero
  rw [rootPlus_eq_matrix] at hroot
  have hentry := congrArg (fun M : RealMatrix2 => M 0 1) hroot
  norm_num at hentry

/-- The normalized-trace state at the first matrix stage is faithful, so its
algebraic GNS equivalence relation identifies only equal representatives. -/
theorem cl11TraceGNS_stageOne_setoid_eq {X Y : MatStage 1}
    (hXY : InfoGeometry.Prequantum.GNSBridge.AbstractGNSState.gnsSetoid
      (cl11RepresentationState 1).state X Y) : X = Y := by
  change (cl11RepresentationState 1).state.state.gnsEquiv X Y at hXY
  change X - Y ∈ (cl11RepresentationState 1).state.state.gnsNullSet at hXY
  have hquad : normalizedTrace 1 (star (X - Y) * (X - Y)) = 0 := by
    have h := (InfoGeometry.Prequantum.GNSBridge.AbstractGNSState.mem_gnsNullSet_iff
      (cl11RepresentationState 1).state (X - Y)).mp hXY
    change (InfoGeometry.Canonical.Cl11FiniteTraceGNSReadout.cl11AbstractGNSState 1).eval
      (star (X - Y) * (X - Y)) = 0 at h
    rw [InfoGeometry.Canonical.Cl11FiniteTraceGNSReadout.cl11AbstractGNSState_eval] at h
    exact h
  have hzero := (normalizedTrace_star_mul_self_eq_zero_iff 1 (X - Y)).mp hquad
  exact sub_eq_zero.mp hzero

/-- Read the finite trace GNS quotient at stage one as the first column of its
unique matrix representative. This is a map of carriers; the source remains
the native algebraic GNS quotient, and the target is the vacuum spinor space. -/
noncomputable def cl11TraceGNS_to_vacuumSpinor :
    cl11RepresentationQuotient 1 → (Fin 2 → ℝ) :=
  Quotient.lift
    (fun X : MatStage 1 => vacuumColumnMap (matrixToCl11StageOne.symm X))
    (by
      intro X Y hXY
      have hEq := cl11TraceGNS_stageOne_setoid_eq hXY
      rw [hEq]
      )

@[simp] theorem cl11TraceGNS_to_vacuumSpinor_mk (X : MatStage 1) :
    cl11TraceGNS_to_vacuumSpinor
      (Quotient.mk (InfoGeometry.Prequantum.GNSBridge.AbstractGNSState.gnsSetoid
        (cl11RepresentationState 1).state) X) =
      vacuumColumnMap (matrixToCl11StageOne.symm X) := rfl

/-- Every vacuum spinor is the image of a class in the native trace GNS
quotient, via the first-column map on the reindexed matrix stage. -/
theorem cl11TraceGNS_to_vacuumSpinor_surjective :
    Function.Surjective cl11TraceGNS_to_vacuumSpinor := by
  intro v
  obtain ⟨A, hA⟩ := vacuumColumnMap_surjective v
  refine ⟨Quotient.mk (InfoGeometry.Prequantum.GNSBridge.AbstractGNSState.gnsSetoid
    (cl11RepresentationState 1).state) (matrixToCl11StageOne A), ?_⟩
  rw [cl11TraceGNS_to_vacuumSpinor_mk]
  simpa only [AlgEquiv.symm_apply_apply] using hA

/-- The readout intertwines the native finite trace GNS left action with the
standard matrix action on the vacuum spinor. -/
theorem cl11TraceGNS_to_vacuumSpinor_intertwines
    (A : RealMatrix2) (X : MatStage 1) :
    cl11TraceGNS_to_vacuumSpinor
      (cl11Action 1 (matrixToCl11StageOne A)
        (Quotient.mk (InfoGeometry.Prequantum.GNSBridge.AbstractGNSState.gnsSetoid
          (cl11RepresentationState 1).state) X)) =
      Matrix.mulVec A
        (cl11TraceGNS_to_vacuumSpinor
          (Quotient.mk (InfoGeometry.Prequantum.GNSBridge.AbstractGNSState.gnsSetoid
            (cl11RepresentationState 1).state) X)) := by
  rw [cl11Action_mk, cl11TraceGNS_to_vacuumSpinor_mk,
    cl11TraceGNS_to_vacuumSpinor_mk]
  rw [map_mul]
  simp only [AlgEquiv.symm_apply_apply]
  change Matrix.mulVec (A * matrixToCl11StageOne.symm X) cyclicVacuum =
    Matrix.mulVec A (Matrix.mulVec (matrixToCl11StageOne.symm X) cyclicVacuum)
  simp only [← Matrix.mulVec_mulVec]

/-- The native trace-GNS quotient maps onto the already-owned finite
vacuum-column quotient. This is the quotient map induced by the identity on
the reindexed matrix representatives; its target is the vacuum-state quotient,
not an algebra quotient. -/
noncomputable def cl11TraceGNS_to_vacuumNullQuotient :
    cl11RepresentationQuotient 1 →
      RealMatrix2 ⧸ LinearMap.ker vacuumColumnMap :=
  Quotient.lift
    (fun X : MatStage 1 =>
      Submodule.Quotient.mk (matrixToCl11StageOne.symm X))
    (by
      intro X Y hXY
      have hEq := cl11TraceGNS_stageOne_setoid_eq hXY
      rw [hEq])

@[simp] theorem cl11TraceGNS_to_vacuumNullQuotient_mk (X : MatStage 1) :
    cl11TraceGNS_to_vacuumNullQuotient
      (Quotient.mk (InfoGeometry.Prequantum.GNSBridge.AbstractGNSState.gnsSetoid
        (cl11RepresentationState 1).state) X) =
      Submodule.Quotient.mk (matrixToCl11StageOne.symm X) := rfl

/-- The quotient-to-quotient map is exactly the first-column spinor readout
followed by the native first-isomorphism equivalence of the vacuum quotient. -/
theorem vacuumNullQuotientEquiv_cl11TraceGNS_to_vacuumNullQuotient
    (q : cl11RepresentationQuotient 1) :
    vacuumNullQuotientEquiv (cl11TraceGNS_to_vacuumNullQuotient q) =
      cl11TraceGNS_to_vacuumSpinor q := by
  refine Quotient.inductionOn q ?_
  intro X
  rw [cl11TraceGNS_to_vacuumNullQuotient_mk,
    vacuumNullQuotientEquiv_mk,
    cl11TraceGNS_to_vacuumSpinor_mk]
  change (fun i : Fin 2 => matrixToCl11StageOne.symm X i 0) =
    Matrix.mulVec (matrixToCl11StageOne.symm X) cyclicVacuum
  rw [mulVec_cyclicVacuum]
  ext i
  fin_cases i <;> rfl

/-- The kernel of the trace-GNS-to-vacuum-quotient map consists exactly of
classes whose first-column spinor readout vanishes. -/
theorem cl11TraceGNS_to_vacuumNullQuotient_eq_zero_iff
    (q : cl11RepresentationQuotient 1) :
    cl11TraceGNS_to_vacuumNullQuotient q = 0 ↔
      cl11TraceGNS_to_vacuumSpinor q = 0 := by
  constructor
  · intro h
    have hread := congrArg vacuumNullQuotientEquiv h
    rw [map_zero,
      vacuumNullQuotientEquiv_cl11TraceGNS_to_vacuumNullQuotient] at hread
    exact hread
  · intro h
    apply vacuumNullQuotientEquiv.injective
    rw [vacuumNullQuotientEquiv_cl11TraceGNS_to_vacuumNullQuotient,
      h, map_zero]

/-- On a trace-GNS representative, the kernel criterion reduces to the
existing concrete first-column kernel in `SpacetimeParabolicQuotient`. -/
theorem cl11TraceGNS_to_vacuumNullQuotient_mk_eq_zero_iff
    (X : MatStage 1) :
    cl11TraceGNS_to_vacuumNullQuotient
      (Quotient.mk (InfoGeometry.Prequantum.GNSBridge.AbstractGNSState.gnsSetoid
        (cl11RepresentationState 1).state) X) = 0 ↔
      matrixToCl11StageOne.symm X ∈ LinearMap.ker vacuumColumnMap := by
  rw [cl11TraceGNS_to_vacuumNullQuotient_mk,
    Submodule.Quotient.mk_eq_zero]

/-- Every class of the finite vacuum-column quotient is the image of a class
in the faithful finite trace-GNS quotient. -/
theorem cl11TraceGNS_to_vacuumNullQuotient_surjective :
    Function.Surjective cl11TraceGNS_to_vacuumNullQuotient := by
  intro q
  refine Quotient.inductionOn q ?_
  intro A
  refine ⟨Quotient.mk (InfoGeometry.Prequantum.GNSBridge.AbstractGNSState.gnsSetoid
    (cl11RepresentationState 1).state) (matrixToCl11StageOne A), ?_⟩
  rw [cl11TraceGNS_to_vacuumNullQuotient_mk]
  change Submodule.Quotient.mk
      (matrixToCl11StageOne.symm (matrixToCl11StageOne A)) =
    Submodule.Quotient.mk A
  rw [AlgEquiv.symm_apply_apply]

/-- On representatives, the quotient-to-quotient map commutes with left
matrix multiplication. This is the concrete operator-action leg of the
surjection from the trace-GNS quotient to the vacuum-state quotient. -/
theorem cl11TraceGNS_to_vacuumNullQuotient_left_action_mk
    (A : RealMatrix2) (X : MatStage 1) :
    cl11TraceGNS_to_vacuumNullQuotient
      (cl11Action 1 (matrixToCl11StageOne A)
        (Quotient.mk (InfoGeometry.Prequantum.GNSBridge.AbstractGNSState.gnsSetoid
          (cl11RepresentationState 1).state) X)) =
      Submodule.Quotient.mk
        (A * matrixToCl11StageOne.symm X) := by
  rw [cl11Action_mk, cl11TraceGNS_to_vacuumNullQuotient_mk]
  have hmul := map_mul matrixToCl11StageOne.symm
    (matrixToCl11StageOne A) X
  rw [AlgEquiv.symm_apply_apply] at hmul
  exact congrArg Submodule.Quotient.mk hmul

/-- The raising root is killed by the vacuum-column quotient map, as required
by its vacuum nullity. -/
theorem cl11TraceGNS_rootPlus_maps_to_zero :
    cl11TraceGNS_to_vacuumNullQuotient
      (Quotient.mk (InfoGeometry.Prequantum.GNSBridge.AbstractGNSState.gnsSetoid
        (cl11RepresentationState 1).state)
        (matrixToCl11StageOne rootPlus)) = 0 := by
  rw [cl11TraceGNS_to_vacuumNullQuotient_mk,
    AlgEquiv.symm_apply_apply]
  apply (Submodule.Quotient.mk_eq_zero _).2
  rw [mem_vacuumColumnMap_ker_iff]
  exact solderingRootPlus_mem_InGNSNull

/-- Although its image in the vacuum-state quotient is zero, the raising-root
class is nonzero in the faithful trace-GNS quotient. Thus this bridge map is
surjective but has a genuine kernel; it is not an identification of the two
GNS quotients. -/
theorem cl11TraceGNS_rootPlus_nonzero_in_kernel :
    (Quotient.mk (InfoGeometry.Prequantum.GNSBridge.AbstractGNSState.gnsSetoid
      (cl11RepresentationState 1).state)
      (matrixToCl11StageOne rootPlus) : cl11RepresentationQuotient 1) ≠
    Quotient.mk (InfoGeometry.Prequantum.GNSBridge.AbstractGNSState.gnsSetoid
      (cl11RepresentationState 1).state) (0 : MatStage 1) ∧
    cl11TraceGNS_to_vacuumNullQuotient
      (Quotient.mk (InfoGeometry.Prequantum.GNSBridge.AbstractGNSState.gnsSetoid
        (cl11RepresentationState 1).state)
        (matrixToCl11StageOne rootPlus)) = 0 := by
  constructor
  · intro hzero
    have hrel := Quotient.exact hzero
    change matrixToCl11StageOne rootPlus - 0 ∈
      (cl11RepresentationState 1).state.state.gnsNullSet at hrel
    have hnull : matrixToCl11StageOne rootPlus ∈
        (cl11RepresentationState 1).state.gnsNullSet := by
      simpa using hrel
    exact cl11RootPlus_vacuumNull_but_traceNonNull.2 hnull
  · exact cl11TraceGNS_rootPlus_maps_to_zero

/-- The nonzero part of the finite trace GNS carrier on which projectivization
of the vacuum-spinor readout is defined. -/
abbrev Cl11TraceGNSProjectiveCarrier :=
  {q : cl11RepresentationQuotient 1 // cl11TraceGNS_to_vacuumSpinor q ≠ 0}

/-- Project a nonzero trace-GNS class to its vacuum-spinor ray and then use the
native orbit-stabilizer equivalence to obtain its `SL₂(ℝ)/P` coset. -/
noncomputable def cl11TraceGNS_to_parabolicCoset :
    Cl11TraceGNSProjectiveCarrier → RealSL2 ⧸ vacuumRayStabilizer :=
  fun q => vacuumRayCosetEquivProjectiveLine.symm
    (Projectivization.mk ℝ (cl11TraceGNS_to_vacuumSpinor q.1) q.2)

/-- The parabolic-coset readout recovers precisely the projective ray of the
first column of a trace-GNS representative. -/
theorem cl11TraceGNS_to_parabolicCoset_image
    (q : Cl11TraceGNSProjectiveCarrier) :
    vacuumRayCosetEquivProjectiveLine
      (cl11TraceGNS_to_parabolicCoset q) =
      Projectivization.mk ℝ (cl11TraceGNS_to_vacuumSpinor q.1) q.2 := by
  simp [cl11TraceGNS_to_parabolicCoset]

/-- Every parabolic coset is represented by a projectivized class in the
finite trace GNS carrier after taking the first-column readout. This is a
surjectivity statement for that readout construction; it does not identify
the faithful trace-GNS quotient itself with the two-dimensional vacuum space. -/
theorem cl11TraceGNS_to_parabolicCoset_surjective :
    Function.Surjective cl11TraceGNS_to_parabolicCoset := by
  intro c
  have hrep : ∃ v : Fin 2 → ℝ, ∃ hv : v ≠ 0,
      Projectivization.mk ℝ v hv = vacuumRayCosetEquivProjectiveLine c := by
    induction vacuumRayCosetEquivProjectiveLine c using Projectivization.ind with
    | h v hv => exact ⟨v, hv, rfl⟩
  obtain ⟨v, hv, hrep⟩ := hrep
  obtain ⟨q, hq⟩ := cl11TraceGNS_to_vacuumSpinor_surjective v
  have hq0 : cl11TraceGNS_to_vacuumSpinor q ≠ 0 := by
    rw [hq]
    exact hv
  refine ⟨⟨q, hq0⟩, ?_⟩
  apply vacuumRayCosetEquivProjectiveLine.injective
  calc
    vacuumRayCosetEquivProjectiveLine
        (cl11TraceGNS_to_parabolicCoset ⟨q, hq0⟩) =
      Projectivization.mk ℝ (cl11TraceGNS_to_vacuumSpinor q) hq0 := by
        simp only [cl11TraceGNS_to_parabolicCoset, Equiv.apply_symm_apply]
    _ = Projectivization.mk ℝ v hv := by
      apply (Projectivization.mk_eq_mk_iff ℝ _ _ _ _).2
      refine ⟨1, ?_⟩
      simp only [one_smul]
      exact hq.symm
    _ = vacuumRayCosetEquivProjectiveLine c := hrep

/-- The native trace-GNS class of the Clifford lowering root has the second
standard spinor as its vacuum readout. -/
theorem cl11TraceGNS_rootMinus_readout :
    cl11TraceGNS_to_vacuumSpinor
      (Quotient.mk (InfoGeometry.Prequantum.GNSBridge.AbstractGNSState.gnsSetoid
        (cl11RepresentationState 1).state)
        (matrixToCl11StageOne rootMinus)) = ![0, 1] := by
  rw [cl11TraceGNS_to_vacuumSpinor_mk]
  simp only [AlgEquiv.symm_apply_apply]
  change Matrix.mulVec rootMinus cyclicVacuum = ![0, 1]
  rw [rootMinus_eq_matrix]
  ext i
  fin_cases i <;> norm_num [Matrix.mulVec, dotProduct, cyclicVacuum,
    Fin.sum_univ_two]

/-- The Clifford lowering-root representative defines a nonzero projective
class in the trace-GNS carrier after taking its vacuum-spinor readout. -/
noncomputable def cl11TraceGNSRootMinusProjectiveCarrier :
    Cl11TraceGNSProjectiveCarrier :=
  ⟨Quotient.mk (InfoGeometry.Prequantum.GNSBridge.AbstractGNSState.gnsSetoid
      (cl11RepresentationState 1).state)
      (matrixToCl11StageOne rootMinus), by
    rw [cl11TraceGNS_rootMinus_readout]
    norm_num⟩

/-- The explicit finite GNS radical inherits left stability from the abstract
star-ring radical theorem. -/
theorem inGNSNull_left_mul (A X : RealMatrix2) (hX : InGNSNull X) :
    InGNSNull (A * X) := by
  apply (mem_vacuumStateMatrixRadical_iff_InGNSNull _).1
  apply InfoGeometry.Canonical.StateRadicalGNSIdealBridge.gnsRadical_is_left_ideal
    vacuumStateMatrixHom A
  exact (mem_vacuumStateMatrixRadical_iff_InGNSNull X).2 hX

/-- Equivalently, the kernel defining the finite vacuum quotient is a left
ideal under matrix multiplication, by transport from the canonical radical. -/
theorem vacuumColumnMap_ker_left_mul (A X : RealMatrix2)
    (hX : X ∈ LinearMap.ker vacuumColumnMap) :
    A * X ∈ LinearMap.ker vacuumColumnMap := by
  rw [mem_vacuumColumnMap_ker_iff] at hX ⊢
  exact inGNSNull_left_mul A X hX

/-- The native Bogoliubov hyperbolic matrix has determinant one, so it belongs
to the same matrix `SL₂(ℝ)` carrier used by the vacuum-ray parabolic quotient. -/
theorem bogoliubovTransform_isSL2 (θ : ℝ) :
    IsSL2 (bogoliubovTransform θ) := by
  change Matrix.det (bogoliubovTransform θ) = 1
  rw [Matrix.det_fin_two]
  change Real.cosh θ * Real.cosh θ - Real.sinh θ * Real.sinh θ = 1
  simpa only [pow_two] using Real.cosh_sq_sub_sinh_sq θ

/-- The Bogoliubov boost viewed as an element of the native special linear
group. -/
noncomputable def bogoliubovAsRealSL2 (θ : ℝ) : RealSL2 :=
  ⟨bogoliubovTransform θ, bogoliubovTransform_isSL2 θ⟩

@[simp] theorem coe_bogoliubovAsRealSL2 (θ : ℝ) :
    (bogoliubovAsRealSL2 θ : Matrix (Fin 2) (Fin 2) ℝ) =
      bogoliubovTransform θ := rfl

/-- The boosted vacuum ray has a canonical point in the native quotient by its
ray stabilizer. This uses the actual Bogoliubov element in `SL₂(ℝ)` and the
existing orbit/stabilizer equivalence. -/
noncomputable def bogoliubovVacuumRayCoset (θ : ℝ) :
    RealSL2 ⧸ vacuumRayStabilizer :=
  vacuumRayCosetEquivProjectiveLine.symm
    (bogoliubovAsRealSL2 θ • vacuumProjectivePoint)

/-- The native parabolic quotient sends the constructed boost coset to the
projective action of the Bogoliubov matrix on the cyclic vacuum ray. -/
theorem bogoliubovVacuumRayCoset_image (θ : ℝ) :
    vacuumRayCosetEquivProjectiveLine (bogoliubovVacuumRayCoset θ) =
      bogoliubovAsRealSL2 θ • vacuumProjectivePoint :=
  Equiv.apply_symm_apply _ _

/-- The vector action of the special-linear-group element is the existing
Bogoliubov matrix action on spinors. -/
theorem bogoliubovAsRealSL2_smul_cyclicVacuum (θ : ℝ) :
    bogoliubovAsRealSL2 θ • cyclicVacuum =
      boostVec θ cyclicVacuum := by
  rw [Matrix.SpecialLinearGroup.smul_def]
  rfl

/-- The coset image has the concrete spinor representative obtained by
boosting the vacuum. -/
theorem bogoliubovVacuumRayCoset_projective_rep (θ : ℝ) :
    vacuumRayCosetEquivProjectiveLine (bogoliubovVacuumRayCoset θ) =
      Projectivization.mk ℝ (boostVec θ cyclicVacuum) (by
        intro hzero
        have hcoord := congrFun hzero 0
        have hcosh : Real.cosh θ = 0 := by
          simpa [boostVec, Matrix.mulVec, dotProduct, bogoliubovTransform,
            cyclicVacuum, Fin.sum_univ_two] using hcoord
        exact (ne_of_gt (Real.cosh_pos θ)) hcosh) := by
  rw [bogoliubovVacuumRayCoset_image]
  have hv : cyclicVacuum ≠ 0 := by norm_num [cyclicVacuum]
  change bogoliubovAsRealSL2 θ • Projectivization.mk ℝ cyclicVacuum hv = _
  rw [Projectivization.smul_mk]
  apply (Projectivization.mk_eq_mk_iff ℝ _ _ _ _).2
  refine ⟨1, ?_⟩
  simp only [one_smul]
  exact bogoliubovAsRealSL2_smul_cyclicVacuum θ

/-- The trace-GNS class represented by the unit reads out as the chosen
vacuum spinor. -/
theorem cl11TraceGNS_unit_readout :
    cl11TraceGNS_to_vacuumSpinor
      (Quotient.mk (InfoGeometry.Prequantum.GNSBridge.AbstractGNSState.gnsSetoid
        (cl11RepresentationState 1).state)
        (matrixToCl11StageOne (1 : RealMatrix2))) = cyclicVacuum := by
  rw [← vacuumNullQuotientEquiv_cl11TraceGNS_to_vacuumNullQuotient]
  rw [cl11TraceGNS_to_vacuumNullQuotient_mk,
    vacuumNullQuotientEquiv_mk]
  ext i
  fin_cases i <;> simp [cyclicVacuum]

/-- Acting on the trace-GNS vacuum class by the stage-one Bogoliubov matrix
reads out to the same boosted vacuum vector as the existing spinor/Krein
flow. -/
theorem cl11TraceGNS_bogoliubov_action_readout (θ : ℝ) :
    cl11TraceGNS_to_vacuumSpinor
      (cl11Action 1 (matrixToCl11StageOne (bogoliubovTransform θ))
        (Quotient.mk (InfoGeometry.Prequantum.GNSBridge.AbstractGNSState.gnsSetoid
          (cl11RepresentationState 1).state)
          (matrixToCl11StageOne (1 : RealMatrix2)))) =
      boostVec θ cyclicVacuum := by
  rw [cl11TraceGNS_to_vacuumSpinor_intertwines,
    cl11TraceGNS_unit_readout]
  rfl

/-- The boosted vacuum class is in the projective carrier: its first
spinor-coordinate is `cosh θ`, which is strictly positive. -/
noncomputable def cl11TraceGNSBogoliubovProjectiveCarrier (θ : ℝ) :
    Cl11TraceGNSProjectiveCarrier :=
  ⟨cl11Action 1 (matrixToCl11StageOne (bogoliubovTransform θ))
      (Quotient.mk (InfoGeometry.Prequantum.GNSBridge.AbstractGNSState.gnsSetoid
        (cl11RepresentationState 1).state)
        (matrixToCl11StageOne (1 : RealMatrix2))), by
    rw [cl11TraceGNS_bogoliubov_action_readout]
    intro hzero
    have hcoord := congrFun hzero 0
    have hcosh : Real.cosh θ = 0 := by
      simpa [boostVec, Matrix.mulVec, dotProduct, bogoliubovTransform,
        cyclicVacuum, Fin.sum_univ_two] using hcoord
    exact (ne_of_gt (Real.cosh_pos θ)) hcosh⟩

/-- The parabolic coset of the Bogoliubov-transformed trace-GNS vacuum class
is exactly the coset already assigned to the Bogoliubov spinor flow. This
closes the finite GNS-action, spinor, Krein-flow, and `SL₂/P` lanes in one
commuting comparison. -/
theorem cl11TraceGNS_bogoliubov_coset_eq (θ : ℝ) :
    cl11TraceGNS_to_parabolicCoset
        (cl11TraceGNSBogoliubovProjectiveCarrier θ) =
      bogoliubovVacuumRayCoset θ := by
  apply vacuumRayCosetEquivProjectiveLine.injective
  simp only [cl11TraceGNS_to_parabolicCoset_image,
    cl11TraceGNSBogoliubovProjectiveCarrier,
    cl11TraceGNS_bogoliubov_action_readout,
    bogoliubovVacuumRayCoset_projective_rep]

/-- The projective representative of the boost coset remains timelike for
the split Krein form: its quadratic value is the vacuum value, namely `1`. -/
theorem bogoliubovVacuum_kreinQuadForm (θ : ℝ) :
    kreinQuadForm (boostVec θ cyclicVacuum) = 1 := by
  rw [kreinQuadForm_boost]
  simp [kreinQuadForm, cyclicVacuum]

/-- Thus the vacuum orbit used in the parabolic quotient is not on the Krein
null cone. This records the precise relation between the two geometries. -/
theorem bogoliubovVacuum_not_kreinNull (θ : ℝ) :
    ¬ IsKreinNull (boostVec θ cyclicVacuum) := by
  rw [IsKreinNull, bogoliubovVacuum_kreinQuadForm]
  norm_num

/-- The Clifford raising root maps to zero in the finite quotient determined
by the chosen vacuum column. -/
theorem cl11_rootPlus_vanishes_in_vacuum_quotient :
    vacuumNullQuotientEquiv
      (Submodule.Quotient.mk (cl11EquivMat rootPlusCl11)) = 0 := by
  apply (vacuumNullQuotientEquiv_mk_eq_zero_iff _).2
  rw [cl11EquivMat_rootPlusCl11]
  exact solderingRootPlus_mem_InGNSNull

/-- The Clifford lowering root survives in the finite vacuum quotient as the
second standard spinor. -/
theorem cl11_rootMinus_vacuum_quotient_eq_second_basis :
    vacuumNullQuotientEquiv
      (Submodule.Quotient.mk (cl11EquivMat rootMinusCl11)) = ![0, 1] := by
  rw [cl11EquivMat_rootMinusCl11]
  exact solderingRootMinus_quotient_eq_second_basis

/-- Consequently, the lowering root has nonzero class in the finite vacuum
quotient, even though both Clifford roots are null for the soldering form. -/
theorem cl11_rootMinus_class_ne_zero :
    (Submodule.Quotient.mk (cl11EquivMat rootMinusCl11) :
      Matrix (Fin 2) (Fin 2) ℝ ⧸ LinearMap.ker vacuumColumnMap) ≠ 0 := by
  intro hzero
  have hmap := congrArg vacuumNullQuotientEquiv hzero
  rw [cl11_rootMinus_vacuum_quotient_eq_second_basis] at hmap
  rw [map_zero] at hmap
  have hcoord := congrFun hmap 1
  norm_num at hcoord

/-- The Clifford raising root is null for the finite vacuum quadratic form. -/
theorem cl11_rootPlus_vacuum_quadratic_eq_zero :
    vacuumState (star (cl11EquivMat rootPlusCl11) *
      cl11EquivMat rootPlusCl11) = 0 := by
  rw [cl11EquivMat_rootPlusCl11]
  rw [rootPlus_eq_matrix]
  norm_num [vacuumState, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_apply,
    Matrix.mul_apply, Fin.sum_univ_two]

/-- The Clifford lowering root is spacetime-null but has unit squared size
for the chosen finite vacuum functional. -/
theorem cl11_rootMinus_vacuum_quadratic_eq_one :
    vacuumState (star (cl11EquivMat rootMinusCl11) *
      cl11EquivMat rootMinusCl11) = 1 := by
  rw [cl11EquivMat_rootMinusCl11]
  rw [rootMinus_eq_matrix]
  norm_num [vacuumState, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_apply,
    Matrix.mul_apply, Fin.sum_univ_two]

/-- Soldering-nullity and vacuum-state nullity are distinct: both Clifford
roots have zero spacetime quadratic form, while their finite vacuum quadratic
values are respectively zero and one. -/
theorem cl11_soldering_nullity_vs_vacuum_quadratic :
    q22 (solderingInv (cl11EquivMat rootPlusCl11)) = 0 ∧
    q22 (solderingInv (cl11EquivMat rootMinusCl11)) = 0 ∧
    vacuumState (star (cl11EquivMat rootPlusCl11) *
      cl11EquivMat rootPlusCl11) = 0 ∧
    vacuumState (star (cl11EquivMat rootMinusCl11) *
      cl11EquivMat rootMinusCl11) = 1 := by
  exact ⟨rootPlusCl11_solderedVector_null,
    rootMinusCl11_solderedVector_null,
    cl11_rootPlus_vacuum_quadratic_eq_zero,
    cl11_rootMinus_vacuum_quadratic_eq_one⟩

/-- The nonzero projective class of the Clifford lowering root in the finite
vacuum-column quotient. -/
noncomputable def cl11RootMinusProjective : VacuumNullProjectiveLine :=
  Projectivization.mk ℝ
    (Submodule.Quotient.mk (cl11EquivMat rootMinusCl11))
    cl11_rootMinus_class_ne_zero

/-- Under the finite quotient's canonical projectivization, the Clifford
lowering root determines the ray of the second standard spinor. -/
theorem cl11RootMinusProjective_image :
    vacuumNullProjectiveEquiv cl11RootMinusProjective =
      Projectivization.mk ℝ (![0, 1] : Fin 2 → ℝ) (by norm_num) := by
  change vacuumNullProjectiveMap cl11RootMinusProjective = _
  rw [cl11RootMinusProjective, vacuumNullProjectiveMap_mk]
  apply (Projectivization.mk_eq_mk_iff ℝ _ _ _ _).2
  refine ⟨1, ?_⟩
  simp only [one_smul]
  exact cl11_rootMinus_vacuum_quotient_eq_second_basis.symm

/-- The parabolic coset assigned to the Clifford lowering-root ray by the
existing native `SL₂(ℝ)/P` equivalence. -/
noncomputable def cl11RootMinusParabolicCoset :
    RealSL2 ⧸ vacuumRayStabilizer :=
  vacuumRayCosetEquivProjectiveNullQuotient.symm cl11RootMinusProjective

/-- Explicitly, the canonical `SL₂(ℝ)/P` point maps back to the projective
second-spinor ray represented by the Clifford lowering root. -/
theorem cl11RootMinusParabolicCoset_image :
    vacuumNullProjectiveEquiv
      (vacuumRayCosetEquivProjectiveNullQuotient
        cl11RootMinusParabolicCoset) =
      Projectivization.mk ℝ (![0, 1] : Fin 2 → ℝ) (by norm_num) := by
  rw [cl11RootMinusParabolicCoset, Equiv.apply_symm_apply,
    cl11RootMinusProjective_image]

/-- A determinant-one Weyl matrix exchanges the two coordinate rays. -/
noncomputable def cl11RootWeyl : RealSL2 :=
  ⟨!![(0 : ℝ), -1; 1, 0], by norm_num [IsSL2, Matrix.det_fin_two_of]⟩

/-- The Weyl representative sends the chosen vacuum spinor to the second
standard spinor, which is the class of the Clifford lowering root. -/
theorem cl11RootWeyl_smul_vacuum :
    cl11RootWeyl • cyclicVacuum = ![0, 1] := by
  rw [Matrix.SpecialLinearGroup.smul_def]
  ext i
  fin_cases i <;> simp [cl11RootWeyl, cyclicVacuum, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two]

/-- The orbit-stabilizer equivalence sends the quotient class of a group
element to its action on the vacuum projective point. -/
theorem vacuumRayCosetEquivProjectiveLine_mk (g : RealSL2) :
    vacuumRayCosetEquivProjectiveLine (QuotientGroup.mk g) =
      g • vacuumProjectivePoint := by
  change ((MulAction.orbitEquivQuotientStabilizer RealSL2 vacuumProjectivePoint).symm
    (QuotientGroup.mk g) : ℙ ℝ (Fin 2 → ℝ)) = _
  exact MulAction.orbitEquivQuotientStabilizer_symm_apply
    (G := RealSL2) (b := vacuumProjectivePoint) g

/-- The Weyl matrix's projective action is the ray represented by the
Clifford lowering-root quotient class. -/
theorem cl11RootWeyl_projective_image :
    cl11RootWeyl • vacuumProjectivePoint =
      Projectivization.mk ℝ (![0, 1] : Fin 2 → ℝ) (by norm_num) := by
  have hv : cyclicVacuum ≠ 0 := by norm_num [cyclicVacuum]
  change cl11RootWeyl • Projectivization.mk ℝ cyclicVacuum hv = _
  rw [Projectivization.smul_mk]
  apply (Projectivization.mk_eq_mk_iff ℝ _ _ _ _).2
  refine ⟨1, ?_⟩
  simp only [one_smul]
  exact cl11RootWeyl_smul_vacuum.symm

/-- Under the projective readout from the native trace-GNS carrier, the
Clifford lowering root determines the Weyl coset in `SL₂(ℝ)/P`. -/
theorem cl11TraceGNS_rootMinus_parabolicCoset_eq_weyl :
    cl11TraceGNS_to_parabolicCoset cl11TraceGNSRootMinusProjectiveCarrier =
      QuotientGroup.mk cl11RootWeyl := by
  apply vacuumRayCosetEquivProjectiveLine.injective
  calc
    vacuumRayCosetEquivProjectiveLine
        (cl11TraceGNS_to_parabolicCoset cl11TraceGNSRootMinusProjectiveCarrier) =
      Projectivization.mk ℝ (![0, 1] : Fin 2 → ℝ) (by norm_num) := by
        rw [cl11TraceGNS_to_parabolicCoset_image]
        apply (Projectivization.mk_eq_mk_iff ℝ _ _ _ _).2
        refine ⟨1, ?_⟩
        simp only [one_smul]
        exact cl11TraceGNS_rootMinus_readout.symm
    _ = cl11RootWeyl • vacuumProjectivePoint :=
      cl11RootWeyl_projective_image.symm
    _ = vacuumRayCosetEquivProjectiveLine (QuotientGroup.mk cl11RootWeyl) :=
      (vacuumRayCosetEquivProjectiveLine_mk cl11RootWeyl).symm

/-- The Clifford lowering-root coset is explicitly the class of the Weyl
matrix in `SL₂(ℝ)/P`. -/
theorem cl11RootMinusParabolicCoset_eq_weyl :
    cl11RootMinusParabolicCoset = QuotientGroup.mk cl11RootWeyl := by
  apply vacuumRayCosetEquivProjectiveLine.injective
  calc
    vacuumRayCosetEquivProjectiveLine cl11RootMinusParabolicCoset =
        vacuumNullProjectiveEquiv cl11RootMinusProjective := by
      simp [cl11RootMinusParabolicCoset,
        vacuumRayCosetEquivProjectiveNullQuotient]
    _ = Projectivization.mk ℝ (![0, 1] : Fin 2 → ℝ) (by norm_num) :=
      cl11RootMinusProjective_image
    _ = cl11RootWeyl • vacuumProjectivePoint :=
      cl11RootWeyl_projective_image.symm
    _ = vacuumRayCosetEquivProjectiveLine (QuotientGroup.mk cl11RootWeyl) :=
      (vacuumRayCosetEquivProjectiveLine_mk cl11RootWeyl).symm

/-- The Clifford roots exhibit the state-dependent quotient split: both are
spacetime-null, the raising root is killed by the chosen vacuum, and the
lowering root survives as the second spinor. The existing equivalence
`vacuumRayCosetEquivProjectiveNullQuotient` identifies the projectivization of
this finite quotient with the native `SL₂(ℝ)` vacuum-ray coset. -/
theorem cl11_roots_soldering_and_vacuum_quotient :
    q22 (solderingInv (cl11EquivMat rootPlusCl11)) = 0 ∧
    q22 (solderingInv (cl11EquivMat rootMinusCl11)) = 0 ∧
    vacuumNullQuotientEquiv
      (Submodule.Quotient.mk (cl11EquivMat rootPlusCl11)) = 0 ∧
    vacuumNullQuotientEquiv
      (Submodule.Quotient.mk (cl11EquivMat rootMinusCl11)) = ![0, 1] ∧
    (Submodule.Quotient.mk (cl11EquivMat rootMinusCl11) :
      Matrix (Fin 2) (Fin 2) ℝ ⧸ LinearMap.ker vacuumColumnMap) ≠ 0 := by
  exact ⟨rootPlusCl11_solderedVector_null,
    rootMinusCl11_solderedVector_null,
    cl11_rootPlus_vanishes_in_vacuum_quotient,
    cl11_rootMinus_vacuum_quotient_eq_second_basis,
    cl11_rootMinus_class_ne_zero⟩

end InfoGeometry.Cosmology.Cl11ParabolicVacuumQuotientBridge

end
