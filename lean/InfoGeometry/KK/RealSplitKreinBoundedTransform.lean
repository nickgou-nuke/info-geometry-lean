/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.KK.RealSplitKreinUnboundedCycle
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.KK.CompactOperatorBridge
import InfoGeometry.KK.KasparovCycle
import InfoGeometry.KK.RealSplitKreinHilbertizationBridge
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Matrix.Order

open scoped InnerProductSpace

namespace InfoGeometry.KK

open InfoGeometry.Krein

/-!
# Real Split Krein Bounded Transform

Bounded-transform bridges from the primitive unbounded split-Krein cycle.

### Evidence Boundaries (`BUCKET 2` vs `BUCKET 3`)
- **`BUCKET 3` (Infinite-dimensional unbounded functional calculus)**: On a general
  infinite-dimensional `[CompleteSpace H]`, the full unbounded functional
  calculus for the canonical phase `D (1 + D²)^(-1/2)` is not yet formalized.
  `RealSplitKreinBoundedTransform` uses the concrete compact `X.resolvent`
  representative packaged in `RealSplitKreinResolventData` as its phase and
  makes oddness, Krein skew-adjointness, and compactness of `F² - 1` explicit.
- **`BUCKET 2` (Finite-dimensional `CFC.sqrt` bounded transform)**: When
  `[FiniteDimensional ℝ H]`, `section FiniteDimFunctionalCalculus` constructs the
  exact bounded transform `F := D (1 + D²)^(-1/2)` by transporting `D` via
  `LinearMap.toMatrixOrthonormal (stdOrthonormalBasis ℝ H)` into `Matrix _ _ ℝ`,
  taking `CFC.sqrt (1 + M_D * M_D)` (requiring both `IsSelfAdjoint D` and
  `IsKreinSkewAdjoint D` so `1 + M_D * M_D` is `PosDef`), and proving `IsOdd F`,
  `IsKreinSkewAdjoint F`, `1 - F² = (1 + D²)⁻¹`, and compactness of `F² - 1`
  and `[F, π(a)]`.
-/

variable {A B H : Type*}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [KreinSpace H] [KreinGradedModule H]

omit [CompleteSpace H] [KreinSpace H] [KreinGradedModule H] in
/-- Compact endomorphisms are closed under negation. -/
lemma isCompactEnd_neg {T : EndH H}
    (hT : IsCompactEnd H T) :
    IsCompactEnd H (-T) := by
  simpa [IsCompactEnd] using (IsCompactOperator.neg hT)

omit [CompleteSpace H] [KreinSpace H] [KreinGradedModule H] in
/-- Compact endomorphisms are closed under subtraction. -/
lemma isCompactEnd_sub {S T : EndH H}
    (hS : IsCompactEnd H S) (hT : IsCompactEnd H T) :
    IsCompactEnd H (S - T) := by
  simpa [IsCompactEnd] using (IsCompactOperator.sub hS hT)

omit [CompleteSpace H] [KreinSpace H] [KreinGradedModule H] in
/-- Postcomposition of a compact endomorphism by a bounded endomorphism stays compact. -/
lemma isCompactEnd_comp_right {S T : EndH H}
    (hS : IsCompactEnd H S) :
    IsCompactEnd H (S.comp T) := by
  simpa [IsCompactEnd, ContinuousLinearMap.coe_comp] using
    IsCompactOperator.comp_clm (hf := hS) (g := T)

omit [CompleteSpace H] [KreinSpace H] [KreinGradedModule H] in
/-- Precomposition of a compact endomorphism by a bounded endomorphism stays compact. -/
lemma isCompactEnd_comp_left {S T : EndH H}
    (hT : IsCompactEnd H T) :
    IsCompactEnd H (S.comp T) := by
  simpa [IsCompactEnd, ContinuousLinearMap.coe_comp] using
    IsCompactOperator.clm_comp (hf := hT) (g := S)

/-- Grading conjugation preserves compactness of bounded endomorphisms. -/
lemma gradeConj_compact {T : EndH H}
    (hT : IsCompactEnd H T) :
    IsCompactEnd H (KreinGradedModule.gradeConj (H := H) T) := by
  unfold KreinGradedModule.gradeConj
  exact isCompactEnd_comp_left
    (S := KreinGradedModule.gradeCLM (H := H))
    (isCompactEnd_comp_right
      (T := KreinGradedModule.gradeCLM (H := H))
      hT)

/-- The grading-even part of a compact endomorphism is compact. -/
lemma evenPart_compact {T : EndH H}
    (hT : IsCompactEnd H T) :
    IsCompactEnd H (KreinGradedModule.evenPart (H := H) T) := by
  unfold KreinGradedModule.evenPart
  exact isCompactEnd_smul (2 : ℝ)⁻¹
    (isCompactEnd_add hT (gradeConj_compact hT))

/-- The grading-odd part of a compact endomorphism is compact. -/
lemma oddPart_compact {T : EndH H}
    (hT : IsCompactEnd H T) :
    IsCompactEnd H (KreinGradedModule.oddPart (H := H) T) := by
  unfold KreinGradedModule.oddPart
  exact isCompactEnd_smul (2 : ℝ)⁻¹
    (isCompactEnd_sub hT (gradeConj_compact hT))

omit [CompleteSpace H] [KreinSpace H] [KreinGradedModule H] in
/-- If the left factor is compact, the ordinary commutator is compact. -/
lemma comm_isCompactEnd_of_left_compact {S T : EndH H}
    (hS : IsCompactEnd H S) :
    IsCompactEnd H (KreinGradedModule.comm (H := H) S T) := by
  unfold KreinGradedModule.comm
  exact isCompactEnd_sub
    (isCompactEnd_comp_right (T := T) hS)
    (isCompactEnd_comp_left (S := T) hS)

omit [CompleteSpace H] [KreinSpace H] [KreinGradedModule H] in
/-- If the left factor is compact, the ordinary anticommutator is compact. -/
lemma anticomm_isCompactEnd_of_left_compact {S T : EndH H}
    (hS : IsCompactEnd H S) :
    IsCompactEnd H (KreinGradedModule.anticomm (H := H) S T) := by
  unfold KreinGradedModule.anticomm
  exact isCompactEnd_add
    (isCompactEnd_comp_right (T := T) hS)
    (isCompactEnd_comp_left (S := T) hS)

/-- If the left factor is compact, the graded commutator is compact. -/
lemma superComm_isCompactEnd_of_left_compact {S T : EndH H}
    (hS : IsCompactEnd H S) :
    IsCompactEnd H (KreinGradedModule.superComm (H := H) S T) := by
  unfold KreinGradedModule.superComm
  have hEven : IsCompactEnd H (KreinGradedModule.evenPart (H := H) S) :=
    evenPart_compact hS
  have hOdd : IsCompactEnd H (KreinGradedModule.oddPart (H := H) S) :=
    oddPart_compact hS
  exact isCompactEnd_add
    (isCompactEnd_add
      (isCompactEnd_add
        (comm_isCompactEnd_of_left_compact (T := KreinGradedModule.evenPart (H := H) T) hEven)
        (comm_isCompactEnd_of_left_compact (T := KreinGradedModule.oddPart (H := H) T) hEven))
      (comm_isCompactEnd_of_left_compact (T := KreinGradedModule.evenPart (H := H) T) hOdd))
    (anticomm_isCompactEnd_of_left_compact (T := KreinGradedModule.oddPart (H := H) T) hOdd)

/--
Primitive bounded-transform bridge data over the unbounded split-Krein cycle.

The bounded phase is canonically chosen to be the concrete resolvent carried by
the unbounded cycle. The bridge records exactly the remaining phase properties
that are not yet derivable from the present resolvent packet alone.
-/
structure RealSplitKreinBoundedTransform
    (X : RealSplitKreinUnboundedCycle A B H) where
  phase_odd :
    KreinGradedModule.IsOdd (H := H) X.resolvent
  phase_krein_skewAdj :
    KreinSpace.IsKreinSkewAdjoint (H := H) X.resolvent
  phase_sq_one_compact :
    IsCompactEnd H (X.resolvent * X.resolvent - (1 : EndH H))

namespace RealSplitKreinBoundedTransform

variable {X : RealSplitKreinUnboundedCycle A B H}
variable (T : RealSplitKreinBoundedTransform X)

/-- The canonical bounded phase associated to the unbounded cycle. -/
abbrev phase (_T : RealSplitKreinBoundedTransform X) : EndH H :=
  X.resolvent

@[simp] theorem phase_eq_resolvent :
    phase T = X.resolvent := rfl

/-- The canonical bounded phase is compact because it is the chosen resolvent. -/
theorem phase_compact :
    IsCompactEnd H (phase T) :=
  RealSplitKreinUnboundedCycle.resolvent_compact X

/-- The canonical bounded phase is odd. -/
theorem phase_isOdd :
    KreinGradedModule.IsOdd (H := H) (phase T) :=
  RealSplitKreinBoundedTransform.phase_odd T

/-- The canonical bounded phase is Krein-skew-adjoint. -/
theorem phase_isKreinSkewAdjoint :
    KreinSpace.IsKreinSkewAdjoint (H := H) (phase T) :=
  RealSplitKreinBoundedTransform.phase_krein_skewAdj T

/-- The canonical bounded phase satisfies the primitive `F² - 1` compactness law. -/
theorem phase_sq_one_isCompact :
    IsCompactEnd H (phase T * phase T - (1 : EndH H)) :=
  RealSplitKreinBoundedTransform.phase_sq_one_compact T

/-- The bounded-phase commutator with the `A`-action is compact. -/
theorem phase_commutator_compact (a : A) :
    IsCompactEnd H (phase T * (X.π a) - (X.π a) * phase T) := by
  exact isCompactEnd_sub
    (isCompactEnd_comp_right (T := X.π a) (phase_compact T))
    (isCompactEnd_comp_left (S := X.π a) (phase_compact T))

/-- The bounded-phase graded commutator with `ε` is compact. -/
theorem phase_superComm_eps_compact :
    IsCompactEnd H (KreinGradedModule.superComm (H := H) (phase T) X.cl11.eps) :=
  superComm_isCompactEnd_of_left_compact (phase_compact T)

/-- The bounded-phase graded commutator with `J` is compact. -/
theorem phase_superComm_J_compact :
    IsCompactEnd H (KreinGradedModule.superComm (H := H) (phase T) X.cl11.J) :=
  superComm_isCompactEnd_of_left_compact (phase_compact T)

/--
Package the unbounded primitive cycle and its bounded-transform bridge as a
primitive bounded real split-Krein Kasparov cycle.
-/
noncomputable def toRealSplitKreinKasparovCycle :
    RealSplitKreinKasparovCycle A B H where
  cl11 := X.cl11
  π := X.π
  ρ := X.ρ
  π_even := X.π_even
  ρ_even := X.ρ_even
  F := phase T
  F_odd := phase_isOdd T
  F_skewAdj := phase_isKreinSkewAdjoint T
  F_sq_one_compact := phase_sq_one_isCompact T
  comm_compact := phase_commutator_compact T
  superComm_eps_compact := phase_superComm_eps_compact T
  superComm_J_compact := phase_superComm_J_compact T

/-- Forget the split-`Cl(1,1)` data and keep the bounded KK compatibility surface. -/
noncomputable def toKasparovCycle :
    KasparovCycle A B H :=
  RealSplitKreinKasparovCycle.toKasparovCycle
    (toRealSplitKreinKasparovCycle T)

@[simp] theorem toRealSplitKreinKasparovCycle_F :
    (toRealSplitKreinKasparovCycle T).F = X.resolvent := rfl

@[simp] theorem toKasparovCycle_F :
    (toKasparovCycle T).F = X.resolvent := rfl

end RealSplitKreinBoundedTransform

section FiniteDimFunctionalCalculus

open scoped MatrixOrder

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [KreinSpace H] [KreinGradedModule H] [FiniteDimensional ℝ H]

private noncomputable def finiteDimMatrixEquiv (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] :
    (H →ₗ[ℝ] H) ≃⋆ₐ[ℝ] Matrix (Fin (Module.finrank ℝ H)) (Fin (Module.finrank ℝ H)) ℝ :=
  LinearMap.toMatrixOrthonormal (stdOrthonormalBasis ℝ H)

/-- Matrix representation of `1 + D²` in `stdOrthonormalBasis ℝ H`. -/
noncomputable def finiteDimOneAddSqMatrix (D : EndH H) :
    Matrix (Fin (Module.finrank ℝ H)) (Fin (Module.finrank ℝ H)) ℝ :=
  1 + finiteDimMatrixEquiv H D.toLinearMap * finiteDimMatrixEquiv H D.toLinearMap

omit [KreinSpace H] [KreinGradedModule H] in
lemma finiteDimOneAddSqMatrix_posDef (D : EndH H) (hD_self : IsSelfAdjoint D) :
    (finiteDimOneAddSqMatrix D).PosDef := by
  let Φ := finiteDimMatrixEquiv H
  have hLinSelf : IsSelfAdjoint D.toLinearMap :=
    (ContinuousLinearMap.isSelfAdjoint_toLinearMap_iff D).2 hD_self
  have hMatStar : star (Φ D.toLinearMap) = Φ D.toLinearMap := by
    rw [← map_star Φ, hLinSelf.star_eq]
  have hConj : Matrix.conjTranspose (Φ D.toLinearMap) = Φ D.toLinearMap := by
    simpa [Matrix.star_eq_conjTranspose] using hMatStar
  have hPosSemidef : (Φ D.toLinearMap * Φ D.toLinearMap).PosSemidef := by
    have h0 := Matrix.posSemidef_conjTranspose_mul_self (Φ D.toLinearMap)
    rwa [hConj] at h0
  exact Matrix.PosDef.one.add_posSemidef hPosSemidef

omit [KreinSpace H] [KreinGradedModule H] in
lemma finiteDimOneAddSqMatrix_posSemidef (D : EndH H) (hD_self : IsSelfAdjoint D) :
    (finiteDimOneAddSqMatrix D).PosSemidef :=
  (finiteDimOneAddSqMatrix_posDef D hD_self).posSemidef

omit [KreinSpace H] [KreinGradedModule H] in
private lemma finiteDimSqrt_isUnit (D : EndH H) (hD_self : IsSelfAdjoint D) :
    IsUnit (CFC.sqrt (finiteDimOneAddSqMatrix D)) := by
  have hPos : (finiteDimOneAddSqMatrix D).PosDef :=
    finiteDimOneAddSqMatrix_posDef D hD_self
  have hSq :
      CFC.sqrt (finiteDimOneAddSqMatrix D) * CFC.sqrt (finiteDimOneAddSqMatrix D) =
        finiteDimOneAddSqMatrix D :=
    CFC.sqrt_mul_sqrt_self (finiteDimOneAddSqMatrix D) hPos.posSemidef.nonneg
  have hUnitSq : IsUnit (CFC.sqrt (finiteDimOneAddSqMatrix D) *
      CFC.sqrt (finiteDimOneAddSqMatrix D)) := by
    rw [hSq]
    exact hPos.isUnit
  exact isUnit_of_mul_isUnit_left hUnitSq

/--
`BUCKET 2` finite-dimensional inverse square root `(1 + D²)⁻¹/²`, constructed via
`CFC.sqrt` on `Matrix (Fin (Module.finrank ℝ H)) (Fin (Module.finrank ℝ H)) ℝ`
under `stdOrthonormalBasis ℝ H` (contrasting with the `BUCKET 3` infinite-dimensional
`X.resolvent` surrogate in `RealSplitKreinBoundedTransform`).
-/
noncomputable def finiteDimInvSqrt (D : EndH H) : EndH H :=
  ((finiteDimMatrixEquiv H).symm (CFC.sqrt (finiteDimOneAddSqMatrix D))⁻¹).toContinuousLinearMap

/--
`BUCKET 2` finite-dimensional bounded transform `D (1 + D²)⁻¹/²` via `CFC.sqrt`.
-/
noncomputable def finiteDimPhase (D : EndH H) : EndH H :=
  D.comp (finiteDimInvSqrt D)

omit [CompleteSpace H] [KreinSpace H] [KreinGradedModule H] in
private lemma toLinearMap_finiteDimInvSqrt (D : EndH H) :
    (finiteDimInvSqrt D).toLinearMap =
      (finiteDimMatrixEquiv H).symm (CFC.sqrt (finiteDimOneAddSqMatrix D))⁻¹ := rfl

omit [KreinSpace H] [KreinGradedModule H] in
lemma finiteDimInvSqrt_isSelfAdjoint (D : EndH H) :
    IsSelfAdjoint (finiteDimInvSqrt D) := by
  let Φ := finiteDimMatrixEquiv H
  have hSqrtNonneg : 0 ≤ CFC.sqrt (finiteDimOneAddSqMatrix D) :=
    CFC.sqrt_nonneg (finiteDimOneAddSqMatrix D)
  have hSqrtStar : star (CFC.sqrt (finiteDimOneAddSqMatrix D)) =
      CFC.sqrt (finiteDimOneAddSqMatrix D) :=
    hSqrtNonneg.star_eq
  have hInvStar : star (CFC.sqrt (finiteDimOneAddSqMatrix D))⁻¹ =
      (CFC.sqrt (finiteDimOneAddSqMatrix D))⁻¹ := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_nonsing_inv]
    simpa [Matrix.star_eq_conjTranspose] using congrArg Inv.inv hSqrtStar
  have hLin : IsSelfAdjoint (Φ.symm (CFC.sqrt (finiteDimOneAddSqMatrix D))⁻¹) := by
    change star (Φ.symm _) = Φ.symm _
    rw [← map_star Φ.symm, hInvStar]
  exact (LinearMap.isSelfAdjoint_toContinuousLinearMap_iff _).2 hLin

omit [KreinSpace H] [KreinGradedModule H] in
lemma finiteDimInvSqrt_commute_of_commute_sq
    {D T : EndH H} (hD_self : IsSelfAdjoint D)
    (hcomm : Commute T (D * D)) :
    Commute T (finiteDimInvSqrt D) := by
  let Φ := finiteDimMatrixEquiv H
  have hS_unit := finiteDimSqrt_isUnit D hD_self
  have hDetS : IsUnit (CFC.sqrt (finiteDimOneAddSqMatrix D)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hS_unit
  have hMulInv :
      CFC.sqrt (finiteDimOneAddSqMatrix D) * (CFC.sqrt (finiteDimOneAddSqMatrix D))⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hDetS
  have hInvMul :
      (CFC.sqrt (finiteDimOneAddSqMatrix D))⁻¹ * CFC.sqrt (finiteDimOneAddSqMatrix D) = 1 :=
    Matrix.nonsing_inv_mul _ hDetS
  have hcommLin : Commute T.toLinearMap (D.toLinearMap * D.toLinearMap) := by
    change T.toLinearMap * (D.toLinearMap * D.toLinearMap) =
      (D.toLinearMap * D.toLinearMap) * T.toLinearMap
    have h1 : (T * (D * D)).toLinearMap = ((D * D) * T).toLinearMap := congrArg (·.toLinearMap) hcomm
    exact h1
  have hcommP : Commute (finiteDimOneAddSqMatrix D) (Φ T.toLinearMap) := by
    have hMatSq : Φ T.toLinearMap * (Φ D.toLinearMap * Φ D.toLinearMap) =
        (Φ D.toLinearMap * Φ D.toLinearMap) * Φ T.toLinearMap := by
      simp only [← map_mul]
      exact congrArg Φ hcommLin
    change (1 + Φ D.toLinearMap * Φ D.toLinearMap) * Φ T.toLinearMap =
      Φ T.toLinearMap * (1 + Φ D.toLinearMap * Φ D.toLinearMap)
    rw [add_mul, one_mul, mul_add, mul_one, hMatSq]
  have hcommS : Commute (CFC.sqrt (finiteDimOneAddSqMatrix D)) (Φ T.toLinearMap) := by
    change Commute (cfcₙ NNReal.sqrt (finiteDimOneAddSqMatrix D)) (Φ T.toLinearMap)
    exact hcommP.cfcₙ_nnreal NNReal.sqrt
  have hcommInv : Commute (Φ T.toLinearMap) (CFC.sqrt (finiteDimOneAddSqMatrix D))⁻¹ := by
    change Φ T.toLinearMap * (CFC.sqrt (finiteDimOneAddSqMatrix D))⁻¹ =
      (CFC.sqrt (finiteDimOneAddSqMatrix D))⁻¹ * Φ T.toLinearMap
    calc
      Φ T.toLinearMap * (CFC.sqrt (finiteDimOneAddSqMatrix D))⁻¹
          = ((CFC.sqrt (finiteDimOneAddSqMatrix D))⁻¹ * CFC.sqrt (finiteDimOneAddSqMatrix D)) *
              (Φ T.toLinearMap * (CFC.sqrt (finiteDimOneAddSqMatrix D))⁻¹) := by
            rw [hInvMul, one_mul]
      _ = (CFC.sqrt (finiteDimOneAddSqMatrix D))⁻¹ *
            ((CFC.sqrt (finiteDimOneAddSqMatrix D) * Φ T.toLinearMap) *
              (CFC.sqrt (finiteDimOneAddSqMatrix D))⁻¹) := by
            simp only [mul_assoc]
      _ = (CFC.sqrt (finiteDimOneAddSqMatrix D))⁻¹ *
            ((Φ T.toLinearMap * CFC.sqrt (finiteDimOneAddSqMatrix D)) *
              (CFC.sqrt (finiteDimOneAddSqMatrix D))⁻¹) := by
            rw [hcommS]
      _ = (CFC.sqrt (finiteDimOneAddSqMatrix D))⁻¹ * Φ T.toLinearMap := by
            rw [mul_assoc (Φ T.toLinearMap), hMulInv, mul_one]
  have hcommSymm : Commute T.toLinearMap (finiteDimInvSqrt D).toLinearMap := by
    rw [toLinearMap_finiteDimInvSqrt]
    change T.toLinearMap * Φ.symm _ = Φ.symm _ * T.toLinearMap
    apply Φ.injective
    change Φ (T.toLinearMap * Φ.symm (CFC.sqrt (finiteDimOneAddSqMatrix D))⁻¹) =
      Φ (Φ.symm (CFC.sqrt (finiteDimOneAddSqMatrix D))⁻¹ * T.toLinearMap)
    rw [map_mul, map_mul, Φ.apply_symm_apply]
    exact hcommInv
  ext x
  have hx := congrArg (fun f : H →ₗ[ℝ] H => f x) hcommSymm
  simpa [ContinuousLinearMap.mul_def] using hx

omit [KreinSpace H] [KreinGradedModule H] in
lemma finiteDimInvSqrt_sq (D : EndH H) (hD_self : IsSelfAdjoint D) :
    (1 + D * D) * (finiteDimInvSqrt D * finiteDimInvSqrt D) = 1 ∧
      (finiteDimInvSqrt D * finiteDimInvSqrt D) * (1 + D * D) = 1 := by
  let Φ := finiteDimMatrixEquiv H
  have hP : (finiteDimOneAddSqMatrix D).PosDef := finiteDimOneAddSqMatrix_posDef D hD_self
  have hS_unit := finiteDimSqrt_isUnit D hD_self
  have hDetS : IsUnit (CFC.sqrt (finiteDimOneAddSqMatrix D)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hS_unit
  set S := CFC.sqrt (finiteDimOneAddSqMatrix D)
  have hMulInv : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S hDetS
  have hInvMul : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hDetS
  have hSS : S * S = finiteDimOneAddSqMatrix D :=
    CFC.sqrt_mul_sqrt_self (finiteDimOneAddSqMatrix D) hP.posSemidef.nonneg
  have hMatLeft : finiteDimOneAddSqMatrix D * (S⁻¹ * S⁻¹) = 1 := by
    nth_rw 1 [← hSS]
    calc
      (S * S) * (S⁻¹ * S⁻¹) = S * (S * S⁻¹) * S⁻¹ := by simp only [mul_assoc]
      _ = S * 1 * S⁻¹ := by nth_rw 1 [hMulInv]
      _ = S * S⁻¹ := by rw [mul_one]
      _ = 1 := hMulInv
  have hMatRight : (S⁻¹ * S⁻¹) * finiteDimOneAddSqMatrix D = 1 := by
    nth_rw 1 [← hSS]
    calc
      (S⁻¹ * S⁻¹) * (S * S) = S⁻¹ * (S⁻¹ * S) * S := by simp only [mul_assoc]
      _ = S⁻¹ * 1 * S := by nth_rw 1 [hInvMul]
      _ = S⁻¹ * S := by rw [mul_one]
      _ = 1 := hInvMul
  have hPhiOneAdd : Φ ((1 + D * D).toLinearMap) = finiteDimOneAddSqMatrix D := by
    change Φ (1 + D.toLinearMap * D.toLinearMap) =
      1 + Φ D.toLinearMap * Φ D.toLinearMap
    rw [map_add, map_one, map_mul]
  constructor
  · apply ContinuousLinearMap.coe_inj.mp
    ext x
    have hLin :
        ((1 + D * D).toLinearMap *
          ((finiteDimInvSqrt D).toLinearMap * (finiteDimInvSqrt D).toLinearMap)) = 1 := by
      apply Φ.injective
      change Φ ((1 + D * D).toLinearMap *
          ((finiteDimInvSqrt D).toLinearMap * (finiteDimInvSqrt D).toLinearMap)) = Φ 1
      rw [map_mul, map_mul, hPhiOneAdd, toLinearMap_finiteDimInvSqrt,
        Φ.apply_symm_apply, map_one]
      exact hMatLeft
    simpa [ContinuousLinearMap.mul_def] using congrArg (fun f : H →ₗ[ℝ] H => f x) hLin
  · apply ContinuousLinearMap.coe_inj.mp
    ext x
    have hLin :
        ((finiteDimInvSqrt D).toLinearMap * (finiteDimInvSqrt D).toLinearMap) *
          (1 + D * D).toLinearMap = 1 := by
      apply Φ.injective
      change Φ (((finiteDimInvSqrt D).toLinearMap * (finiteDimInvSqrt D).toLinearMap) *
          (1 + D * D).toLinearMap) = Φ 1
      rw [map_mul, map_mul, hPhiOneAdd, toLinearMap_finiteDimInvSqrt,
        Φ.apply_symm_apply, map_one]
      exact hMatRight
    simpa [ContinuousLinearMap.mul_def] using congrArg (fun f : H →ₗ[ℝ] H => f x) hLin

theorem finiteDimPhase_odd
    {D : EndH H} (hD_self : IsSelfAdjoint D) (hD_odd : KreinGradedModule.IsOdd (H := H) D) :
    KreinGradedModule.IsOdd (H := H) (finiteDimPhase D) := by
  let Γ : EndH H := KreinGradedModule.gradeCLM (H := H)
  have hGammaD : Γ * D = -(D * Γ) := by
    have h := congrArg (fun T : EndH H => T.comp Γ) hD_odd
    simpa [KreinGradedModule.gradeConj, Γ, ContinuousLinearMap.comp_assoc,
      ContinuousLinearMap.mul_def] using h
  have hGammaSq : Commute Γ (D * D) := by
    change Γ * (D * D) = (D * D) * Γ
    calc
      Γ * (D * D) = (Γ * D) * D := by rw [mul_assoc]
      _ = (-(D * Γ)) * D := by rw [hGammaD]
      _ = -(D * (Γ * D)) := by simp [mul_assoc]
      _ = -(D * (-(D * Γ))) := by rw [hGammaD]
      _ = (D * D) * Γ := by simp [mul_assoc]
  have hGammaInv : Commute Γ (finiteDimInvSqrt D) :=
    finiteDimInvSqrt_commute_of_commute_sq hD_self hGammaSq
  unfold KreinGradedModule.IsOdd KreinGradedModule.gradeConj finiteDimPhase
  change Γ * (D * finiteDimInvSqrt D) * Γ = -(D * finiteDimInvSqrt D)
  calc
    Γ * (D * finiteDimInvSqrt D) * Γ
        = (Γ * D) * (finiteDimInvSqrt D * Γ) := by simp only [mul_assoc]
    _ = (-(D * Γ)) * (Γ * finiteDimInvSqrt D) := by rw [hGammaD, hGammaInv.eq]
    _ = -(D * ((Γ * Γ) * finiteDimInvSqrt D)) := by simp only [neg_mul, mul_assoc]
    _ = -(D * finiteDimInvSqrt D) := by
          have hG2 : Γ * Γ = 1 := KreinGradedModule.gradeCLM_comp_self (H := H)
          rw [hG2, one_mul]

omit [KreinGradedModule H] in
theorem finiteDimPhase_krein_skewAdj
    {D : EndH H}
    (hD_self : IsSelfAdjoint D)
    (hD_krein : KreinSpace.IsKreinSkewAdjoint (H := H) D) :
    KreinSpace.IsKreinSkewAdjoint (H := H) (finiteDimPhase D) := by
  let J : EndH H := KreinSpace.jCLM (H := H)
  have hJ_anti_D : J * D = -(D * J) := by
    rw [KreinSpace.isKreinSkewAdjoint_iff_eq_neg] at hD_krein
    have hD_adj : ContinuousLinearMap.adjoint D = D :=
      ContinuousLinearMap.isSelfAdjoint_iff'.mp hD_self
    have h1 := congrArg (fun T : EndH H => J.comp T) hD_krein
    have h2 : D.comp J = -(J.comp D) := by
      simpa [KreinSpace.kreinAdjoint, J, hD_adj, ContinuousLinearMap.comp_assoc] using h1
    have h3 : J.comp D = -(D.comp J) := by
      rw [h2, neg_neg]
    exact h3
  have hJSq : Commute J (D * D) := by
    change J * (D * D) = (D * D) * J
    calc
      J * (D * D) = (J * D) * D := by rw [mul_assoc]
      _ = (-(D * J)) * D := by rw [hJ_anti_D]
      _ = -(D * (J * D)) := by simp [mul_assoc]
      _ = -(D * (-(D * J))) := by rw [hJ_anti_D]
      _ = (D * D) * J := by simp [mul_assoc]
  have hJInv : Commute J (finiteDimInvSqrt D) :=
    finiteDimInvSqrt_commute_of_commute_sq hD_self hJSq
  have hDInv : Commute D (finiteDimInvSqrt D) :=
    finiteDimInvSqrt_commute_of_commute_sq hD_self ((Commute.refl D).mul_right (Commute.refl D))
  have hPhaseSelf : IsSelfAdjoint (finiteDimPhase D) := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff']
    have hD_adj : ContinuousLinearMap.adjoint D = D :=
      ContinuousLinearMap.isSelfAdjoint_iff'.mp hD_self
    have hInv_adj : ContinuousLinearMap.adjoint (finiteDimInvSqrt D) = finiteDimInvSqrt D :=
      ContinuousLinearMap.isSelfAdjoint_iff'.mp (finiteDimInvSqrt_isSelfAdjoint D)
    change ContinuousLinearMap.adjoint (D.comp (finiteDimInvSqrt D)) = D.comp (finiteDimInvSqrt D)
    rw [ContinuousLinearMap.adjoint_comp, hD_adj, hInv_adj]
    exact hDInv.eq.symm
  have hJ_anti_phase : J.comp (finiteDimPhase D) = -((finiteDimPhase D).comp J) := by
    change J * (D * finiteDimInvSqrt D) = -((D * finiteDimInvSqrt D) * J)
    calc
      J * (D * finiteDimInvSqrt D)
          = (J * D) * finiteDimInvSqrt D := by rw [mul_assoc]
      _ = (-(D * J)) * finiteDimInvSqrt D := by rw [hJ_anti_D]
      _ = -(D * (J * finiteDimInvSqrt D)) := by simp [mul_assoc]
      _ = -(D * (finiteDimInvSqrt D * J)) := by rw [hJInv.eq]
      _ = -((D * finiteDimInvSqrt D) * J) := by simp [mul_assoc]
  exact (RealSplitKreinHilbertizationBridge.isKreinSkewAdjoint_of_anticommute_j
    (finiteDimPhase D) hJ_anti_phase).2 hPhaseSelf

omit [KreinSpace H] [KreinGradedModule H] in
/-- Exact defect identity `(1 + D²) * (1 - F²) = 1` and `(1 - F²) * (1 + D²) = 1`
for `F = finiteDimPhase D` (so `1 - F² = (1 + D²)⁻¹`). -/
theorem finiteDimPhase_sq_add_inv_one_add_sq
    {D : EndH H} (hD_self : IsSelfAdjoint D) :
    (1 + D * D) * (1 - finiteDimPhase D * finiteDimPhase D) = 1 ∧
      (1 - finiteDimPhase D * finiteDimPhase D) * (1 + D * D) = 1 := by
  have hDInv : Commute D (finiteDimInvSqrt D) :=
    finiteDimInvSqrt_commute_of_commute_sq hD_self ((Commute.refl D).mul_right (Commute.refl D))
  have hSq : finiteDimPhase D * finiteDimPhase D =
      (D * D) * (finiteDimInvSqrt D * finiteDimInvSqrt D) := by
    change (D * finiteDimInvSqrt D) * (D * finiteDimInvSqrt D) =
      (D * D) * (finiteDimInvSqrt D * finiteDimInvSqrt D)
    calc
      (D * finiteDimInvSqrt D) * (D * finiteDimInvSqrt D)
          = D * (finiteDimInvSqrt D * D) * finiteDimInvSqrt D := by simp only [mul_assoc]
      _ = D * (D * finiteDimInvSqrt D) * finiteDimInvSqrt D := by rw [hDInv.eq]
      _ = (D * D) * (finiteDimInvSqrt D * finiteDimInvSqrt D) := by simp only [mul_assoc]
  obtain ⟨hL, hR⟩ := finiteDimInvSqrt_sq D hD_self
  have hDefect :
      1 - finiteDimPhase D * finiteDimPhase D = finiteDimInvSqrt D * finiteDimInvSqrt D := by
    have hL' : (D * D) * (finiteDimInvSqrt D * finiteDimInvSqrt D) +
        finiteDimInvSqrt D * finiteDimInvSqrt D = 1 := by
      simpa [add_mul, add_comm] using hL
    rw [hSq]
    exact sub_eq_of_eq_add' hL'.symm
  rw [hDefect]
  exact ⟨hL, hR⟩

omit [KreinSpace H] [KreinGradedModule H] in
theorem finiteDimPhase_sq_one_compact (D : EndH H) :
    IsCompactEnd H (finiteDimPhase D * finiteDimPhase D - (1 : EndH H)) :=
  isCompactEnd_of_finiteDimensional (H := H) _

omit [KreinSpace H] [KreinGradedModule H] in
theorem finiteDimPhase_comm_compact {A : Type*} [Ring A] [Algebra ℝ A] (π : A →ₐ[ℝ] EndH H)
    (D : EndH H) (a : A) :
    IsCompactEnd H (finiteDimPhase D * π a - π a * finiteDimPhase D) :=
  isCompactEnd_of_finiteDimensional (H := H) _

/--
Build a `RealSplitKreinKasparovCycle A B H` via the `BUCKET 2` finite-dimensional
`CFC.sqrt` bounded transform `finiteDimPhase D = D (1 + D²)⁻¹/²`.
-/
noncomputable def finiteDimToRealSplitKreinKasparovCycle
    {A B : Type*}
    [NormedRing A] [NormedRing B] [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
    (cl11 : InfoGeometry.Quantum.RealSplitCl11Action H)
    (π : A →ₐ[ℝ] EndH H) (ρ : B →ₐ[ℝ] EndH H)
    (hpi_even : ∀ a : A, KreinGradedModule.IsEven (H := H) (π a))
    (hrho_even : ∀ b : B, KreinGradedModule.IsEven (H := H) (ρ b))
    (D : EndH H)
    (hD_self : IsSelfAdjoint D)
    (hD_odd : KreinGradedModule.IsOdd (H := H) D)
    (hD_krein : KreinSpace.IsKreinSkewAdjoint (H := H) D) :
    RealSplitKreinKasparovCycle A B H where
  cl11 := cl11
  π := π
  ρ := ρ
  π_even := hpi_even
  ρ_even := hrho_even
  F := finiteDimPhase D
  F_odd := finiteDimPhase_odd hD_self hD_odd
  F_skewAdj := finiteDimPhase_krein_skewAdj hD_self hD_krein
  F_sq_one_compact := finiteDimPhase_sq_one_compact D
  comm_compact := fun a => finiteDimPhase_comm_compact π D a
  superComm_eps_compact := isCompactEnd_of_finiteDimensional (H := H) _
  superComm_J_compact := isCompactEnd_of_finiteDimensional (H := H) _

/--
Lift an unbounded cycle `X : RealSplitKreinUnboundedCycle A B H` on a
finite-dimensional carrier, given a Hilbert-self-adjoint continuous extension
`D_op : EndH H` of `X.D`, to a `RealSplitKreinKasparovCycle A B H` using the
`BUCKET 2` `CFC.sqrt` bounded transform (`finiteDimPhase D_op`).

`X.D_odd` and `X.D_krein_skewAdj` extend from `X.domain` to all of `H` via
`X.dense_domain`.
-/
noncomputable def finiteDimToRealSplitKreinKasparovCycle_of_unbounded
    {A B : Type*}
    [NormedRing A] [NormedRing B] [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
    (X : RealSplitKreinUnboundedCycle A B H)
    (D_op : EndH H)
    (hD_ext : ∀ x : {x // x ∈ X.domain}, D_op x.1 = X.D x)
    (hD_self : IsSelfAdjoint D_op) :
    RealSplitKreinKasparovCycle A B H :=
  finiteDimToRealSplitKreinKasparovCycle
    X.cl11 X.π X.ρ X.π_even X.ρ_even D_op hD_self
    (by
      have hFun :
          (fun x : H => KreinGradedModule.gradeCLM (H := H)
            (D_op (KreinGradedModule.gradeCLM (H := H) x))) =
          (fun x : H => -(D_op x)) := by
        refine X.dense_domain.denseRange_val.equalizer ?_ ?_ (funext fun ⟨x, hx⟩ => ?_)
        · exact (KreinGradedModule.gradeCLM (H := H)).continuous.comp
            (D_op.continuous.comp (KreinGradedModule.gradeCLM (H := H)).continuous)
        · exact D_op.continuous.neg
        · have hx' : KreinGradedModule.gradeCLM (H := H) x ∈ X.domain :=
            X.grade_preserves_domain hx
          change KreinGradedModule.gradeCLM (H := H)
              (D_op (KreinGradedModule.gradeCLM (H := H) x)) = -(D_op x)
          rw [hD_ext ⟨KreinGradedModule.gradeCLM (H := H) x, hx'⟩, X.D_odd ⟨x, hx⟩,
            ← hD_ext ⟨x, hx⟩]
          have hgg :
              KreinGradedModule.gradeCLM (H := H) (KreinGradedModule.gradeCLM (H := H) (D_op x)) =
                D_op x := by
            simpa using KreinGradedModule.grade_invol (H := H) (D_op x)
          rw [map_neg, hgg]
      ext x
      exact congrFun hFun x)
    (by
      rw [KreinSpace.isKreinSkewAdjoint_iff]
      have hLeft : ∀ u : H, u ∈ X.domain →
          ∀ v : H, KreinSpace.kreinInner (D_op u) v + KreinSpace.kreinInner u (D_op v) = 0 := by
        intro u hu v
        have hFunV :
            (fun y : H => KreinSpace.kreinInner (D_op u) y + KreinSpace.kreinInner u (D_op y)) =
            (fun _ : H => (0 : ℝ)) := by
          refine X.dense_domain.denseRange_val.equalizer ?_ continuous_const
            (funext fun ⟨y, hy⟩ => ?_)
          · exact (KreinSpace.continuous_kreinInner.comp
              (continuous_const.prodMk continuous_id)).add
              (KreinSpace.continuous_kreinInner.comp
                (continuous_const.prodMk D_op.continuous))
          · change KreinSpace.kreinInner (D_op u) y + KreinSpace.kreinInner u (D_op y) = 0
            rw [hD_ext ⟨u, hu⟩, hD_ext ⟨y, hy⟩]
            exact X.D_krein_skewAdj ⟨u, hu⟩ ⟨y, hy⟩
        exact congrFun hFunV v
      intro u v
      have hFunU :
          (fun x : H => KreinSpace.kreinInner (D_op x) v + KreinSpace.kreinInner x (D_op v)) =
          (fun _ : H => (0 : ℝ)) := by
        refine X.dense_domain.denseRange_val.equalizer ?_ continuous_const
          (funext fun ⟨x, hx⟩ => ?_)
        · exact (KreinSpace.continuous_kreinInner.comp
            (D_op.continuous.prodMk continuous_const)).add
            (KreinSpace.continuous_kreinInner.comp
              (continuous_id.prodMk continuous_const))
        · exact hLeft x hx v
      exact congrFun hFunU u)

end FiniteDimFunctionalCalculus

end InfoGeometry.KK
