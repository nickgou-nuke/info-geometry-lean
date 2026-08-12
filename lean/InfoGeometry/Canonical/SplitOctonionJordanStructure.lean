import InfoGeometry.Canonical.SplitOctonionJordanCore
import InfoGeometry.Canonical.SplitOctonionSkew28
import Mathlib.LinearAlgebra.Basis.Basic

set_option maxHeartbeats 5000000

/-!
# Operator layer for the explicit spin-factor Jordan core

This owner defines the native left-multiplication and inner-commutator
operators.  The later identification with an orthogonal structure algebra is
deliberately not folded into these definitions.
-/

namespace InfoGeometry.Canonical.SplitOctonionJordanStructure

open SplitOctonionJordanForm
open SplitOctonionJordanCore
open SplitOctonionSkew28

abbrev Orthogonal44 := SplitOctonionSkew28.Orthogonal44
abbrev Orthogonal44Lie :=
  skewAdjointMatricesLieSubalgebra SplitOctonionSkew28.eta44

abbrev Carrier := SpinCarrier

def leftJordanMul (x : Carrier) : Module.End ℝ Carrier where
  toFun y := x * y
  map_add' y z := by
    ext <;> simp [jordanMul] <;> ring
  map_smul' r y := by
    ext <;> simp [jordanMul] <;> ring

@[simp] theorem leftJordanMul_apply (x y : Carrier) :
    leftJordanMul x y = x * y := rfl

def innerJordanDerivation (x y : Carrier) : Module.End ℝ Carrier :=
  leftJordanMul x * leftJordanMul y - leftJordanMul y * leftJordanMul x

@[simp] theorem innerJordanDerivation_apply (x y z : Carrier) :
    innerJordanDerivation x y z = x * (y * z) - y * (x * z) := by
  rfl

theorem jordan_structure_jordan_identity (x y : Carrier) :
    (x * y) * (x * x) = x * (y * (x * x)) :=
  jordanMul_jordan_identity x y

theorem innerJordanDerivation_zero_self (x : Carrier) :
    innerJordanDerivation x x = 0 := by
  apply LinearMap.ext
  intro z
  simp [innerJordanDerivation]

theorem innerJordanDerivation_traceFree_apply
    (xi eta z : MiddleCarrier) (s : ℝ) :
    innerJordanDerivation (0, xi) (0, eta) (s, z) =
      (0, W xi eta z) := by
  ext i <;>
    simp [innerJordanDerivation, leftJordanMul, jordanMul, W,
      smul_eq_mul] ;
    ring

theorem innerJordanDerivation_traceFree_form_skew
    (xi eta z w : MiddleCarrier) :
    beta44 ((innerJordanDerivation (0, xi) (0, eta) (0, z)).2) w +
      beta44 z ((innerJordanDerivation (0, xi) (0, eta) (0, w)).2) = 0 := by
  rw [innerJordanDerivation_traceFree_apply,
    innerJordanDerivation_traceFree_apply]
  exact W_skew xi eta z w

/-! ## Rank-two orthogonal generators on the trace-free carrier -/

def rankTwoOperator (xi eta : MiddleCarrier) : Module.End ℝ MiddleCarrier where
  toFun z := beta44 eta z • xi - beta44 xi z • eta
  map_add' z w := by
    change beta44 eta (z + w) • xi - beta44 xi (z + w) • eta =
      (beta44 eta z • xi - beta44 xi z • eta) +
        (beta44 eta w • xi - beta44 xi w • eta)
    rw [beta44_add_right, beta44_add_right]
    module
  map_smul' r z := by
    change beta44 eta (r • z) • xi - beta44 xi (r • z) • eta =
      r • (beta44 eta z • xi - beta44 xi z • eta)
    rw [beta44_smul_right, beta44_smul_right]
    module

@[simp] theorem rankTwoOperator_apply (xi eta z : MiddleCarrier) :
    rankTwoOperator xi eta z = W xi eta z := rfl

theorem rankTwoOperator_skew (xi eta z w : MiddleCarrier) :
    beta44 (rankTwoOperator xi eta z) w +
      beta44 z (rankTwoOperator xi eta w) = 0 := by
  exact W_skew xi eta z w

theorem rankTwoOperator_swap (xi eta : MiddleCarrier) :
    rankTwoOperator eta xi = -rankTwoOperator xi eta := by
  apply LinearMap.ext
  intro z
  simp [rankTwoOperator, sub_eq_add_neg, add_comm]

/-! The coordinate generators are the genuine skew-basis generators. -/

def coordinateVector (i : Fin 8) : MiddleCarrier := Pi.single i 1

def etaSign (i : Fin 8) : ℝ := if i.val < 4 then 1 else -1

def rankTwoBasisOperator (p : SplitOctonionSkew28.Index) :
    Module.End ℝ MiddleCarrier :=
  rankTwoOperator (coordinateVector p.1.1)
    ((etaSign p.1.1 * etaSign p.1.2) • coordinateVector p.1.2)

theorem beta44_coordinateVector (i j : Fin 8) :
    beta44 (coordinateVector i) (coordinateVector j) =
      if i.val < 4 then (if i = j then 1 else 0)
      else (if i = j then -1 else 0) := by
  fin_cases i <;> fin_cases j <;>
    simp [beta44, coordinateVector, Pi.single_apply, Fin.sum_univ_succ]

theorem skewMatrix_single_mulVec
    (p : SplitOctonionSkew28.Index) (z : MiddleCarrier) :
    (skewMatrix (Pi.single p 1)).mulVec z =
      z p.1.2 • coordinateVector p.1.1 -
        z p.1.1 • coordinateVector p.1.2 := by
  rcases p with ⟨⟨i, j⟩, hij⟩
  change i < j at hij
  have hji : ¬ j < i := by omega
  have hijne : i ≠ j := by omega
  have hjine : j ≠ i := Ne.symm hijne
  funext l
  change (∑ k : Fin 8, skewMatrix (Pi.single ⟨(i, j), hij⟩ 1) l k * z k) = _
  have hentry (k : Fin 8) :
      skewMatrix (Pi.single ⟨(i, j), hij⟩ 1) l k =
        (if l = i then (if k = j then 1 else 0)
         else if l = j then (if k = i then -1 else 0) else 0) := by
    by_cases hli : l = i
    · subst l
      by_cases hkj : k = j
      · subst k
        simp [skewMatrix, hij]
      · by_cases hki : k = i
        · subst k
          simp [skewMatrix, hijne]
        · simp [skewMatrix, hijne, hkj, hki]
    · by_cases hlj : l = j
      · subst l
        by_cases hki : k = i
        · subst k
          simp [skewMatrix, hij, hji, hjine]
        · simp [skewMatrix, hjine, hki]
      · simp [skewMatrix, hli, hlj]
  simp_rw [hentry]
  by_cases hli : l = i <;> by_cases hlj : l = j <;>
    simp [Finset.sum_ite_eq', coordinateVector,
      hijne, hjine, hli, hlj]

theorem eta44_skewMatrix_single_mulVec
    (p : SplitOctonionSkew28.Index) (z : MiddleCarrier) :
    (eta44 * skewMatrix (Pi.single p 1)).mulVec z =
      eta44.mulVec
        (z p.1.2 • coordinateVector p.1.1 -
          z p.1.1 • coordinateVector p.1.2) := by
  rw [← Matrix.mulVec_mulVec, skewMatrix_single_mulVec]

theorem eta44_skewMatrix_single_eq_rankTwo
    (p : SplitOctonionSkew28.Index) (z : MiddleCarrier) :
    (eta44 * skewMatrix (Pi.single p 1)).mulVec z =
      rankTwoBasisOperator p z := by
  rw [eta44_skewMatrix_single_mulVec]
  rcases p with ⟨⟨i, j⟩, hij⟩
  ext l
  fin_cases i <;> fin_cases j <;> fin_cases l <;>
    simp [rankTwoBasisOperator, rankTwoOperator, coordinateVector,
      eta44, etaSign, Matrix.mulVec]

def orthogonalAction : Orthogonal44 →ₗ[ℝ] Module.End ℝ MiddleCarrier where
  toFun D :=
    { toFun := D.1.mulVec
      map_add' := by
        intro x y
        exact Matrix.mulVec_add D.1 x y
      map_smul' r x := by
        exact Matrix.mulVec_smul D.1 r x }
  map_add' D E := by
    apply LinearMap.ext
    intro z
    simp [Matrix.add_mulVec]
  map_smul' r D := by
    apply LinearMap.ext
    intro z
    simp [Matrix.smul_mulVec]

@[simp] theorem orthogonalAction_apply (D : Orthogonal44) (z : MiddleCarrier) :
    orthogonalAction D z = D.1.mulVec z := rfl

theorem orthogonal44Basis_action (p : SplitOctonionSkew28.Index)
    (z : MiddleCarrier) :
    (orthogonal44Basis p).1.mulVec z =
      rankTwoBasisOperator p z := by
  have hbasis : (orthogonal44Basis p).1 =
      eta44 * skewMatrix (Pi.single p 1) := by
    change
      (orthogonal44Equiv
        (skewCoordinateEquiv (Pi.basisFun ℝ SplitOctonionSkew28.Index p))).1 =
        eta44 * skewMatrix (Pi.single p 1)
    rw [Pi.basisFun_apply]
    rfl
  rw [hbasis, eta44_skewMatrix_single_eq_rankTwo]

theorem orthogonalAction_injective : Function.Injective orthogonalAction := by
  intro D E h
  apply Subtype.ext
  ext i j
  have hj := congrArg (fun T : Module.End ℝ MiddleCarrier => T (Pi.single j 1)) h
  have hi := congrArg (fun z : MiddleCarrier => z i) hj
  simpa [orthogonalAction, Matrix.mulVec, Pi.single_apply] using hi

noncomputable def orthogonalActionEquiv :
    Orthogonal44 ≃ₗ[ℝ] LinearMap.range orthogonalAction :=
  LinearEquiv.ofInjective orthogonalAction orthogonalAction_injective

theorem orthogonalActionEquiv_apply (D : Orthogonal44) :
    orthogonalActionEquiv D = ⟨orthogonalAction D, ⟨D, rfl⟩⟩ := rfl

noncomputable def orthogonal44LieEquiv :
    Orthogonal44 ≃ₗ⁅ℝ⁆ Orthogonal44Lie := by
  let e : Orthogonal44 ≃ₗ[ℝ] Orthogonal44Lie :=
    { toFun := fun A => ⟨A.1, A.2⟩
      invFun := fun A => ⟨A.1, A.2⟩
      left_inv := by intro A; rfl
      right_inv := by intro A; rfl
      map_add' := by intro A B; rfl
      map_smul' := by intro r A; rfl }
  refine LieEquiv.mk (LieHom.mk e ?_) e.symm ?_ ?_
  · intro A B
    apply Subtype.ext
    rfl
  · intro A
    exact e.left_inv A
  · intro A
    exact e.right_inv A

theorem orthogonal44Lie_finrank :
    Module.finrank ℝ Orthogonal44Lie = 28 := by
  calc
    Module.finrank ℝ Orthogonal44Lie = Module.finrank ℝ Orthogonal44 :=
      (orthogonal44LieEquiv.toLinearEquiv.finrank_eq).symm
    _ = 28 := SplitOctonionSkew28.finrank_orthogonal44

theorem orthogonalAction_range_finrank :
    Module.finrank ℝ (LinearMap.range orthogonalAction) = 28 := by
  let e : Orthogonal44 ≃ₗ[ℝ] LinearMap.range orthogonalAction :=
    LinearEquiv.ofInjective orthogonalAction orthogonalAction_injective
  calc
    Module.finrank ℝ (LinearMap.range orthogonalAction) =
        Module.finrank ℝ Orthogonal44 := (LinearEquiv.finrank_eq e).symm
    _ = 28 := SplitOctonionSkew28.finrank_orthogonal44

theorem rankTwoBasisOperator_eq_orthogonalAction (p : SplitOctonionSkew28.Index)
    (z : MiddleCarrier) :
    rankTwoBasisOperator p z = orthogonalAction (orthogonal44Basis p) z := by
  rw [orthogonalAction_apply]
  exact (orthogonal44Basis_action p z).symm

theorem rankTwoOperator_span_eq_orthogonalAction_range :
    Submodule.span ℝ (Set.range rankTwoBasisOperator) =
      LinearMap.range orthogonalAction := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro y ⟨p, rfl⟩
    refine ⟨orthogonal44Basis p, ?_⟩
    apply LinearMap.ext
    intro z
    exact (rankTwoBasisOperator_eq_orthogonalAction p z).symm
  · rintro y ⟨D, rfl⟩
    have hD := orthogonal44Basis_coordinate_decomposition D
    rw [← hD]
    simp only [map_sum, map_smul]
    refine (Submodule.span ℝ (Set.range rankTwoBasisOperator)).sum_mem ?_
    intro p hp
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    refine ⟨p, ?_⟩
    apply LinearMap.ext
    intro z
    exact rankTwoBasisOperator_eq_orthogonalAction p z

theorem rankTwoOperator_span_finrank :
    Module.finrank ℝ (Submodule.span ℝ (Set.range rankTwoBasisOperator)) = 28 := by
  rw [rankTwoOperator_span_eq_orthogonalAction_range]
  exact orthogonalAction_range_finrank

/-! The rank-two generators identify the full reduced structure algebra with
    the native orthogonal Lie subalgebra through an actual linear equivalence. -/
noncomputable def rankTwoOperatorSpanOrthogonalEquiv :
    (Submodule.span ℝ (Set.range rankTwoBasisOperator)) ≃ₗ[ℝ] Orthogonal44Lie := by
  let eRange :
      (Submodule.span ℝ (Set.range rankTwoBasisOperator)) ≃ₗ[ℝ]
        LinearMap.range orthogonalAction :=
    LinearEquiv.ofEq _ _ rankTwoOperator_span_eq_orthogonalAction_range
  exact eRange.trans
    (orthogonalActionEquiv.symm.trans orthogonal44LieEquiv.toLinearEquiv)

theorem rankTwoOperatorSpanOrthogonalEquiv_finrank :
    Module.finrank ℝ
        (Submodule.span ℝ (Set.range rankTwoBasisOperator)) =
      Module.finrank ℝ Orthogonal44Lie := by
  exact rankTwoOperatorSpanOrthogonalEquiv.finrank_eq

/-! ## The scalar-plus-orthogonal structure carrier -/

abbrev StructureCarrier := ℝ × Orthogonal44

noncomputable def structureBracket (p q : StructureCarrier) : StructureCarrier :=
  (0, ⁅p.2, q.2⁆)

noncomputable instance : LieRing StructureCarrier where
  bracket := structureBracket
  add_lie := by
    intro p q r
    apply Prod.ext
    · change (0 : ℝ) = 0 + 0
      simp
    · exact add_lie p.2 q.2 r.2
  lie_add := by
    intro p q r
    apply Prod.ext
    · change (0 : ℝ) = 0 + 0
      simp
    · exact lie_add p.2 q.2 r.2
  lie_self := by
    intro p
    apply Prod.ext
    · change (0 : ℝ) = 0
      rfl
    · exact lie_self p.2
  leibniz_lie := by
    intro p q r
    apply Prod.ext
    · change (0 : ℝ) = 0 + 0
      simp
    · exact leibniz_lie p.2 q.2 r.2

noncomputable instance : LieAlgebra ℝ StructureCarrier where
  lie_smul := by
    intro r p q
    apply Prod.ext
    · change (0 : ℝ) = r * 0
      simp
    · exact LieAlgebra.lie_smul r p.2 q.2

theorem structureCarrier_finrank :
    Module.finrank ℝ StructureCarrier = 29 := by
  simp [StructureCarrier, SplitOctonionSkew28.finrank_orthogonal44]

def structureAction (a : ℝ) (D : Orthogonal44) : Module.End ℝ Carrier where
  toFun x := (a * x.1, D.1.mulVec x.2)
  map_add' x y := by
    rcases x with ⟨x₁, x₂⟩
    rcases y with ⟨y₁, y₂⟩
    ext
    all_goals simp [Matrix.mulVec_add]
    all_goals ring
  map_smul' r x := by
    rcases x with ⟨x₁, x₂⟩
    ext
    all_goals simp [Matrix.mulVec_smul]
    all_goals ring

@[simp] theorem structureAction_apply (a : ℝ) (D : Orthogonal44)
    (x : Carrier) :
    structureAction a D x = (a * x.1, D.1.mulVec x.2) := rfl

def structureActionLinear : StructureCarrier →ₗ[ℝ] Module.End ℝ Carrier where
  toFun p := structureAction p.1 p.2
  map_add' p q := by
    apply LinearMap.ext
    intro x
    rcases p with ⟨a, D⟩
    rcases q with ⟨b, E⟩
    simp [structureAction, Matrix.add_mulVec, add_mul]
  map_smul' r p := by
    apply LinearMap.ext
    intro x
    rcases p with ⟨a, D⟩
    simp [structureAction, Matrix.smul_mulVec, mul_assoc]

theorem structureActionLinear_bracket (p q : StructureCarrier) :
    structureActionLinear ⁅p, q⁆ =
      structureActionLinear p * structureActionLinear q -
        structureActionLinear q * structureActionLinear p := by
  apply LinearMap.ext
  intro x
  rcases p with ⟨a, D⟩
  rcases q with ⟨b, E⟩
  rcases x with ⟨s, u⟩
  apply Prod.ext
  · simp [structureActionLinear, structureAction,
      Module.End.mul_apply]
    change (0 : ℝ) * s = a * (b * s) - b * (a * s)
    ring
  · change (⁅D, E⁆ : Orthogonal44).1.mulVec u =
      D.1.mulVec (E.1.mulVec u) - E.1.mulVec (D.1.mulVec u)
    change (D.1 * E.1 - E.1 * D.1).mulVec u =
      D.1.mulVec (E.1.mulVec u) - E.1.mulVec (D.1.mulVec u)
    rw [Matrix.sub_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

noncomputable def structureActionLieSubalgebra :
    LieSubalgebra ℝ (Module.End ℝ Carrier) :=
  { structureActionLinear.range with
    lie_mem' := by
      intro A B hA hB
      rcases hA with ⟨p, rfl⟩
      rcases hB with ⟨q, rfl⟩
      refine ⟨⁅p, q⁆, ?_⟩
      exact structureActionLinear_bracket p q }

theorem structureAction_injective :
    Function.Injective (fun p : StructureCarrier => structureAction p.1 p.2) := by
  intro p q h
  rcases p with ⟨a, D⟩
  rcases q with ⟨b, E⟩
  have h0 := congrArg (fun T : Module.End ℝ Carrier => T (1, 0)) h
  have hD : D.1 = E.1 := by
    ext i j
    have hj := congrArg (fun T : Module.End ℝ Carrier => T (0, Pi.single j 1)) h
    have hi := congrArg (fun z : Carrier => z.2 i) hj
    simpa [structureAction, Matrix.mulVec, Finset.mul_sum, Pi.single_apply] using hi
  have hab : a = b := by
    simpa [structureAction] using congrArg Prod.fst h0
  subst hab
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    exact hD

theorem structureActionLinear_injective :
    Function.Injective structureActionLinear := by
  exact structureAction_injective

noncomputable def structureActionLieEquiv :
    StructureCarrier ≃ₗ⁅ℝ⁆ structureActionLieSubalgebra := by
  let e : StructureCarrier ≃ₗ[ℝ] structureActionLieSubalgebra :=
    LinearEquiv.ofInjective structureActionLinear structureActionLinear_injective
  refine LieEquiv.mk (LieHom.mk e ?_) e.symm ?_ ?_
  · intro p q
    apply Subtype.ext
    exact structureActionLinear_bracket p q
  · intro p
    exact e.left_inv p
  · intro p
    exact e.right_inv p

noncomputable def structureActionEquiv :
    StructureCarrier ≃ₗ[ℝ] structureActionLinear.range :=
  LinearEquiv.ofInjective structureActionLinear structureActionLinear_injective

theorem structureActionRange_finrank :
    Module.finrank ℝ structureActionLinear.range = 29 := by
  calc
    Module.finrank ℝ structureActionLinear.range =
        Module.finrank ℝ StructureCarrier :=
      (LinearEquiv.finrank_eq structureActionEquiv).symm
    _ = 29 := structureCarrier_finrank

end InfoGeometry.Canonical.SplitOctonionJordanStructure
