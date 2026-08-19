import Mathlib.Data.Matrix.Block
import Mathlib.Tactic
import InfoGeometry.Lie.SplitOctonionWittPairingTransportBridge

noncomputable section
set_option maxHeartbeats 800000

namespace InfoGeometry.Lie.SplitOctonionDerivationWittBlockRealization

open Matrix
open InfoGeometry.Lie.SplitOctonionDerivationWittOrthogonalBridge
open InfoGeometry.Lie.SplitOctonionWittEndomorphismBlockBridge
open InfoGeometry.Lie.SplitOctonionWittPairingTransportBridge

abbrev CanonicalZorn :=
  InfoGeometry.Canonical.SplitOctonionGogberashviliCanonicalBridge.CanonicalZorn
abbrev Derivation := SplitOctonionDerivationWittOrthogonalBridge.Derivation

def wittIndex : Fin 4 ⊕ Fin 4 → Fin 8
  | Sum.inl i => ⟨i.val, by omega⟩
  | Sum.inr i => ⟨i.val + 4, by omega⟩

abbrev wittEquiv : Fin 4 ⊕ Fin 4 ≃ Fin 8 := @finSumFinEquiv 4 4

@[simp] theorem wittIndex_eq_finSumFinEquiv :
    wittIndex = wittEquiv := by
  funext i
  cases i with
  | inl i => rfl
  | inr i =>
      apply Fin.ext
      simp [wittIndex, wittEquiv, finSumFinEquiv]

@[simp] theorem wittIndex_finSumFinEquiv_symm (i : Fin 8) :
    wittIndex (wittEquiv.symm i) = i := by
  rw [wittIndex_eq_finSumFinEquiv]
  exact wittEquiv.apply_symm_apply i

def transportedDerivation (D : Derivation) : Coord8 →ₗ[ℝ] Coord8 :=
  neutralCanonicalToCoord.toLinearMap.comp (D.1.comp neutralCanonicalToCoord.symm.toLinearMap)

noncomputable def transportedDerivationLinear :
    Derivation →ₗ[ℝ] Module.End ℝ Coord8 where
  toFun := transportedDerivation
  map_add' D E := by
    apply LinearMap.ext
    intro x
    change neutralCanonicalToCoord
        (D.1 (neutralCanonicalToCoord.symm x) +
          E.1 (neutralCanonicalToCoord.symm x)) = _
    exact neutralCanonicalToCoord.map_add _ _
  map_smul' r D := by
    apply LinearMap.ext
    intro x
    change neutralCanonicalToCoord
        (r • D.1 (neutralCanonicalToCoord.symm x)) = _
    exact neutralCanonicalToCoord.map_smul _ _

theorem transportedDerivation_map_lie (D E : Derivation) :
    transportedDerivation ⁅D, E⁆ =
      ⁅transportedDerivation D, transportedDerivation E⁆ := by
  apply LinearMap.ext
  intro x
  simp [transportedDerivation, LieRing.of_associative_ring_bracket]
  change neutralCanonicalToCoord
      (D.1 (E.1 (neutralCanonicalToCoord.symm x)) -
        E.1 (D.1 (neutralCanonicalToCoord.symm x))) = _
  exact neutralCanonicalToCoord.map_sub _ _

noncomputable def transportedDerivationLieHom :
    Derivation →ₗ⁅ℝ⁆ Module.End ℝ Coord8 where
  __ := transportedDerivationLinear
  map_lie' := by
    intro D E
    exact transportedDerivation_map_lie D E

theorem transportedDerivationLieHom_apply (D : Derivation) :
    transportedDerivationLieHom D = transportedDerivation D := rfl

theorem transportedDerivationLieHom_injective :
    Function.Injective transportedDerivationLieHom := by
  intro D E h
  apply Subtype.ext
  apply LinearMap.ext
  intro X
  have h' := congrArg (fun F : Module.End ℝ Coord8 =>
    F (neutralCanonicalToCoord X)) h
  change transportedDerivation D (neutralCanonicalToCoord X) =
    transportedDerivation E (neutralCanonicalToCoord X) at h'
  have h'' : neutralCanonicalToCoord (D.1 X) =
      neutralCanonicalToCoord (E.1 X) := by
    simpa [transportedDerivation] using h'
  exact neutralCanonicalToCoord.injective h''

noncomputable def transportedDerivationLieEquiv :
    Derivation ≃ₗ⁅ℝ⁆ (transportedDerivationLieHom).range :=
  LieEquiv.ofInjective transportedDerivationLieHom
    transportedDerivationLieHom_injective

abbrev transportedDerivationLieSubalgebra :
    LieSubalgebra ℝ (Module.End ℝ Coord8) :=
  transportedDerivationLieHom.range

theorem finrank_transportedDerivation_range :
    Module.finrank ℝ (transportedDerivationLieHom).range = 14 := by
  rw [← transportedDerivationLieEquiv.toLinearEquiv.finrank_eq]
  exact CanonicalZornDerivationDimension.finrank_canonicalZornDerivations

noncomputable abbrev FinMatrix8 := Matrix (Fin 8) (Fin 8) ℝ

noncomputable def canonicalDerivationFinMatrix (D : Derivation) : FinMatrix8 :=
  LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8))
    (transportedDerivation D)

theorem canonicalDerivationFinMatrix_map_lie (D E : Derivation) :
    canonicalDerivationFinMatrix ⁅D, E⁆ =
      canonicalDerivationFinMatrix D * canonicalDerivationFinMatrix E -
        canonicalDerivationFinMatrix E * canonicalDerivationFinMatrix D := by
  change LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8))
      (transportedDerivation ⁅D, E⁆) = _
  rw [transportedDerivation_map_lie D E]
  change LinearMap.toMatrixAlgEquiv (Pi.basisFun ℝ (Fin 8))
      (transportedDerivation D * transportedDerivation E -
        transportedDerivation E * transportedDerivation D) =
      LinearMap.toMatrixAlgEquiv (Pi.basisFun ℝ (Fin 8)) (transportedDerivation D) *
        LinearMap.toMatrixAlgEquiv (Pi.basisFun ℝ (Fin 8)) (transportedDerivation E) -
      LinearMap.toMatrixAlgEquiv (Pi.basisFun ℝ (Fin 8)) (transportedDerivation E) *
        LinearMap.toMatrixAlgEquiv (Pi.basisFun ℝ (Fin 8)) (transportedDerivation D)
  simp only [map_sub, LinearMap.toMatrixAlgEquiv_mul]

theorem canonicalDerivationFinMatrix_injective :
    Function.Injective canonicalDerivationFinMatrix := by
  intro D E h
  apply transportedDerivationLieHom_injective
  exact (LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8))
    (Pi.basisFun ℝ (Fin 8))).injective h

def canonicalDerivationMatrix (D : Derivation) : Mat8 :=
  fun i j =>
    LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8))
      (transportedDerivation D) (wittIndex i) (wittIndex j)

theorem canonicalDerivationMatrix_apply_general
    (D : Derivation) (i j : Fin 4 ⊕ Fin 4) :
    canonicalDerivationMatrix D i j =
      (transportedDerivation D
        (Pi.basisFun ℝ (Fin 8) (wittIndex j))) (wittIndex i) := by
  simp [canonicalDerivationMatrix]

theorem canonicalDerivationMatrix_apply
    (D : Derivation) (i j : Fin 4) :
    canonicalDerivationMatrix D (Sum.inl i) (Sum.inr j) =
      (transportedDerivation D
        (Pi.basisFun ℝ (Fin 8) (wittIndex (Sum.inr j))))
        (wittIndex (Sum.inl i)) := by
  simp [canonicalDerivationMatrix]

theorem canonicalDerivationMatrix_apply_lowerLeft
    (D : Derivation) (i j : Fin 4) :
    canonicalDerivationMatrix D (Sum.inr i) (Sum.inl j) =
      (transportedDerivation D
        (Pi.basisFun ℝ (Fin 8) (wittIndex (Sum.inl j))))
        (wittIndex (Sum.inr i)) := by
  simp [canonicalDerivationMatrix]

def canonicalDerivationBlock (D : Derivation) : WittBlockMatrix where
  A i j := canonicalDerivationMatrix D (Sum.inl i) (Sum.inl j)
  B i j := canonicalDerivationMatrix D (Sum.inl i) (Sum.inr j)
  C i j := canonicalDerivationMatrix D (Sum.inr i) (Sum.inl j)
  D i j := canonicalDerivationMatrix D (Sum.inr i) (Sum.inr j)

theorem canonicalDerivationBlock_toMat8 (D : Derivation) :
    toMat8 (canonicalDerivationBlock D) = canonicalDerivationMatrix D := by
  ext i j
  cases i <;> cases j <;> rfl

def smulWittBlock (r : ℝ) (M : WittBlockMatrix) : WittBlockMatrix where
  A := r • M.A
  B := r • M.B
  C := r • M.C
  D := r • M.D

theorem wittBlock_ext {M N : WittBlockMatrix}
    (hA : M.A = N.A) (hB : M.B = N.B)
    (hC : M.C = N.C) (hD : M.D = N.D) : M = N := by
  cases M
  cases N
  simp_all

theorem canonicalDerivationBlock_smul (r : ℝ) (D : Derivation) :
    canonicalDerivationBlock (r • D) = smulWittBlock r (canonicalDerivationBlock D) := by
  apply wittBlock_ext
  · ext i j
    simp [canonicalDerivationBlock, smulWittBlock, canonicalDerivationMatrix,
      transportedDerivation, wittIndex]
  · ext i j
    simp [canonicalDerivationBlock, smulWittBlock, canonicalDerivationMatrix,
      transportedDerivation, wittIndex]
  · ext i j
    simp [canonicalDerivationBlock, smulWittBlock, canonicalDerivationMatrix,
      transportedDerivation, wittIndex]
  · ext i j
    simp [canonicalDerivationBlock, smulWittBlock, canonicalDerivationMatrix,
      transportedDerivation, wittIndex]

theorem neutral_canonical_derivation_eta_skew (D : Derivation) (X Y : CanonicalZorn) :
    neutralEtaPairing (neutralCanonicalToCoord (D.1 X))
        (neutralCanonicalToCoord Y) +
      neutralEtaPairing (neutralCanonicalToCoord X)
        (neutralCanonicalToCoord (D.1 Y)) = 0 := by
  calc
    _ = etaPairing (canonicalToCoord (D.1 X)) (canonicalToCoord Y) +
        etaPairing (canonicalToCoord X) (canonicalToCoord (D.1 Y)) := by
          rw [show neutralCanonicalToCoord (D.1 X) =
            neutralize (canonicalToCoord (D.1 X)) by rfl,
            show neutralCanonicalToCoord Y = neutralize (canonicalToCoord Y) by rfl,
            show neutralCanonicalToCoord X = neutralize (canonicalToCoord X) by rfl,
            show neutralCanonicalToCoord (D.1 Y) =
              neutralize (canonicalToCoord (D.1 Y)) by rfl,
            neutralEtaPairing_neutralize, neutralEtaPairing_neutralize]
    _ = 0 := canonical_derivation_eta_skew D X Y

theorem canonicalDerivationMatrix_eta_skew (D : Derivation) :
    (canonicalDerivationMatrix D)ᵀ * etaW + etaW * canonicalDerivationMatrix D = 0 := by
  ext i j
  have h := neutral_canonical_derivation_eta_skew D
    (neutralCanonicalToCoord.symm (Pi.basisFun ℝ (Fin 8) (wittIndex i)))
    (neutralCanonicalToCoord.symm (Pi.basisFun ℝ (Fin 8) (wittIndex j)))
  fin_cases i <;> fin_cases j
  all_goals
    simp [canonicalDerivationMatrix, transportedDerivation, wittIndex, etaW,
      Matrix.mul_apply, Fin.sum_univ_four,
      neutralEtaPairing] at h ⊢
    linarith

theorem canonicalDerivationBlock_isWittSkew (D : Derivation) :
    IsWittSkew (canonicalDerivationBlock D) := by
  change (toMat8 (canonicalDerivationBlock D))ᵀ * etaW +
    etaW * toMat8 (canonicalDerivationBlock D) = 0
  rw [canonicalDerivationBlock_toMat8 D]
  exact canonicalDerivationMatrix_eta_skew D

/-! The native derivation-to-block transport is now packaged as the datum
consumed by the cross-tower owner.  This constructor prevents the derivation
and its Witt block from being supplied as unrelated fields. -/

noncomputable def canonicalWittOrthogonalDatum (D : Derivation) :
    WittOrthogonalDatum :=
  { derivation := D
    block := canonicalDerivationBlock D
    block_is_witt_skew := canonicalDerivationBlock_isWittSkew D }

@[simp] theorem canonicalWittOrthogonalDatum_derivation (D : Derivation) :
    (canonicalWittOrthogonalDatum D).derivation = D := rfl

@[simp] theorem canonicalWittOrthogonalDatum_block (D : Derivation) :
    (canonicalWittOrthogonalDatum D).block = canonicalDerivationBlock D := rfl

/-! Canonical derivation-to-Witt API.  These names deliberately expose the
transported native theorem without reproving any block equations by
coordinates. -/

theorem derivation_witt_skew (D : Derivation) :
    IsWittSkew (canonicalDerivationBlock D) :=
  canonicalDerivationBlock_isWittSkew D

theorem canonicalDerivationBlock_equations (D : Derivation) :
    IsWittOrthogonalLie (canonicalDerivationBlock D) :=
  (isWittSkew_iff_isWittOrthogonalLie _).mp (canonicalDerivationBlock_isWittSkew D)

theorem canonicalDerivationBlock_lowerRight_eq_negTranspose (D : Derivation) :
    (canonicalDerivationBlock D).D = - (canonicalDerivationBlock D).Aᵀ :=
  (canonicalDerivationBlock_equations D).1

theorem derivation_lowerRight_eq_negTranspose (D : Derivation) :
    (canonicalDerivationBlock D).D = -(canonicalDerivationBlock D).Aᵀ :=
  canonicalDerivationBlock_lowerRight_eq_negTranspose D

theorem canonicalDerivationBlock_upperRight_skew (D : Derivation) :
    (canonicalDerivationBlock D).Bᵀ = - (canonicalDerivationBlock D).B :=
  (canonicalDerivationBlock_equations D).2.1

theorem derivation_upperRight_skew (D : Derivation) :
    (canonicalDerivationBlock D).Bᵀ = -(canonicalDerivationBlock D).B :=
  canonicalDerivationBlock_upperRight_skew D

theorem canonicalDerivationBlock_lowerLeft_skew (D : Derivation) :
    (canonicalDerivationBlock D).Cᵀ = - (canonicalDerivationBlock D).C :=
  (canonicalDerivationBlock_equations D).2.2

theorem derivation_lowerLeft_skew (D : Derivation) :
    (canonicalDerivationBlock D).Cᵀ = -(canonicalDerivationBlock D).C :=
  canonicalDerivationBlock_lowerLeft_skew D

theorem trace_canonicalDerivationFinMatrix (D : Derivation) :
    Matrix.trace (canonicalDerivationFinMatrix D) = 0 := by
  have hblock := canonicalDerivationBlock_equations D
  have htrace :
      Matrix.trace (canonicalDerivationFinMatrix D) =
        Matrix.trace (canonicalDerivationBlock D).A +
          Matrix.trace (canonicalDerivationBlock D).D := by
    have hreindex :
        canonicalDerivationFinMatrix D =
          Matrix.reindexAlgEquiv ℝ ℝ wittEquiv
            (canonicalDerivationMatrix D) := by
      ext i j
      change
        (transportedDerivation D) (Pi.single j 1) i =
          (transportedDerivation D)
            (Pi.single (wittIndex (wittEquiv.symm j)) 1)
            (wittIndex (wittEquiv.symm i))
      rw [wittIndex_finSumFinEquiv_symm, wittIndex_finSumFinEquiv_symm]
    rw [hreindex]
    change
      (∑ i : Fin 8,
        canonicalDerivationMatrix D (wittEquiv.symm i)
          (wittEquiv.symm i)) = _
    calc
      _ = ∑ i : Fin 4 ⊕ Fin 4, canonicalDerivationMatrix D i i := by
        symm
        exact Equiv.sum_comp wittEquiv
          (fun i : Fin 8 =>
            canonicalDerivationMatrix D (wittEquiv.symm i) (wittEquiv.symm i))
      _ = Matrix.trace (canonicalDerivationBlock D).A +
          Matrix.trace (canonicalDerivationBlock D).D := by
        rw [← canonicalDerivationBlock_toMat8 D]
        simp [Matrix.trace, toMat8]
  rw [htrace, hblock.1, Matrix.trace_neg, Matrix.trace_transpose]
  ring

theorem transportedDerivation_trace_zero (D : Derivation) :
    LinearMap.trace ℝ Coord8 (transportedDerivation D) = 0 := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (Pi.basisFun ℝ (Fin 8))]
  exact trace_canonicalDerivationFinMatrix D

theorem canonicalDerivation_trace_zero (D : Derivation) :
    LinearMap.trace ℝ CanonicalZorn D.1 = 0 := by
  have h := transportedDerivation_trace_zero D
  calc
    LinearMap.trace ℝ CanonicalZorn D.1 =
        LinearMap.trace ℝ Coord8
          (neutralCanonicalToCoord.conj D.1) :=
      (LinearMap.trace_conj' D.1 neutralCanonicalToCoord).symm
    _ = 0 := by
      simpa [transportedDerivation, LinearEquiv.conj] using h

end InfoGeometry.Lie.SplitOctonionDerivationWittBlockRealization
