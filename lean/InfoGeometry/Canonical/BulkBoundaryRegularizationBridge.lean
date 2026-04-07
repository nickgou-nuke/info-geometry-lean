import InfoGeometry.Canonical.Singular
import InfoGeometry.Meta.Architecture
import InfoGeometry.Quantum.BulkBoundary

/-!
# Bulk-Boundary Regularization Bridge

Nontrivial generalized-inverse package for polarization-odd boundary operators.

The key point is that the first honest nonidentity Drazin/Moore-Penrose
projectors do not come from the fully invertible modular owner, but from an odd
boundary/supercharge operator with a genuine zero mode.

If the chosen polarization has plus/minus sectors of different finite
dimension, then any polarization-odd operator has nontrivial kernel. Finite-
dimensional global existence of Moore-Penrose and Drazin inverses then upgrades
that zero-mode statement to a nontrivial regularization package: the resulting
projectors cannot be the identity.
-/

namespace InfoGeometry.Canonical.BulkBoundaryRegularizationBridge

open InfoGeometry.Canonical
open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.MoorePenrose
open InfoGeometry.Quantum.BulkBoundary
open InfoGeometry.Quantum.KitaevChain
open InfoGeometry.Quantum.RealMajorana

section Core

variable {S : Type*}
variable [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
variable [FiniteDimensional ℝ S]

/--
Canonical structure-valued generalized-inverse package for a nontrivial
boundary regularization.
-/
@[rep_depth operator]
structure NontrivialRegularizationPackage
    (Q : S →L[ℝ] S) where
  Q_MP : S →L[ℝ] S
  Q_D : S →L[ℝ] S
  k : ℕ
  hMP : IsMoorePenroseInverse Q Q_MP
  hD : IsDrazinInverse Q Q_D k
  rightProjector_ne_one :
    IsMoorePenroseInverse.rightProjector Q Q_MP ≠ (1 : S →L[ℝ] S)
  leftProjector_ne_one :
    IsMoorePenroseInverse.leftProjector Q Q_MP ≠ (1 : S →L[ℝ] S)
  drazinProjection_ne_one :
    IsDrazinInverse.projection Q Q_D ≠ (1 : S →L[ℝ] S)

/--
Canonical package combining a concrete zero-mode witness with a nontrivial
generalized-inverse regularization package for the same operator.
-/
@[rep_depth operator]
structure ZeroModeRegularizationPackage
    (Q : S →L[ℝ] S) where
  v : S
  v_zeroMode : Q v = 0
  v_ne_zero : v ≠ 0
  reg : NontrivialRegularizationPackage (S := S) Q

omit [CompleteSpace S] [FiniteDimensional ℝ S] in
private theorem surjective_of_mul_eq_one
    {A B : S →L[ℝ] S} (h : A * B = (1 : S →L[ℝ] S)) :
    Function.Surjective A.toLinearMap := by
  intro x
  refine ⟨B x, ?_⟩
  have hEval := congrArg (fun T : S →L[ℝ] S => T x) h
  simpa using hEval

/-- A zero mode forces the MP range projector to be nonidentity. -/
theorem moorePenroseRightProjector_ne_one_of_hasZeroMode
    {A B : S →L[ℝ] S}
    (_hMP : IsMoorePenroseInverse A B)
    (hZero : HasZeroMode (S := S) A) :
    IsMoorePenroseInverse.rightProjector A B ≠ (1 : S →L[ℝ] S) := by
  intro hProj
  have hSurj : Function.Surjective A.toLinearMap := by
    unfold IsMoorePenroseInverse.rightProjector at hProj
    exact surjective_of_mul_eq_one hProj
  have hInj : Function.Injective A.toLinearMap :=
    (LinearMap.injective_iff_surjective).2 hSurj
  have hKer : A.toLinearMap.ker = ⊥ := LinearMap.ker_eq_bot.2 hInj
  exact hZero hKer

/-- A zero mode forces the MP co-range projector to be nonidentity. -/
theorem moorePenroseLeftProjector_ne_one_of_hasZeroMode
    {S : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
    {A B : S →L[ℝ] S}
    (_hMP : IsMoorePenroseInverse A B)
    (hZero : HasZeroMode (S := S) A) :
    IsMoorePenroseInverse.leftProjector A B ≠ (1 : S →L[ℝ] S) := by
  intro hProj
  rcases exists_zeroMode_of_hasZeroMode (S := S) (H := A) hZero with ⟨v, hv, hvne⟩
  have hEval := congrArg (fun T : S →L[ℝ] S => T v) hProj
  unfold IsMoorePenroseInverse.leftProjector at hEval
  simp [hv] at hEval
  exact hvne hEval.symm

/-- A zero mode forces the Drazin spectral projector to be nonidentity. -/
theorem drazinProjection_ne_one_of_hasZeroMode
    {S : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]
    {A B : S →L[ℝ] S} {k : ℕ}
    (_hD : IsDrazinInverse A B k)
    (hZero : HasZeroMode (S := S) A) :
    IsDrazinInverse.projection A B ≠ (1 : S →L[ℝ] S) := by
  intro hProj
  have hSurj : Function.Surjective A.toLinearMap := by
    unfold IsDrazinInverse.projection at hProj
    exact surjective_of_mul_eq_one hProj
  have hInj : Function.Injective A.toLinearMap :=
    (LinearMap.injective_iff_surjective).2 hSurj
  have hKer : A.toLinearMap.ker = ⊥ := LinearMap.ker_eq_bot.2 hInj
  exact hZero hKer

/--
Nontrivial generalized-inverse package for a polarization-odd boundary
operator/supercharge.

The plus/minus dimension mismatch forces a zero mode. Global finite-dimensional
existence of Moore-Penrose and Drazin inverses then yields actual generalized
inverse witnesses whose projectors are provably nonidentity.
-/
@[rep_depth operator]
theorem exists_nontrivial_regularization_pair_of_dim_mismatch
    (M : RealMajoranaDatum (S := S))
    (P0 : KPolarization (S := S) M)
    (Q : S →L[ℝ] S)
    (hodd : PolarizationOdd (M := M) P0 Q)
    (hdim :
      Module.finrank ℝ P0.plus
        ≠ Module.finrank ℝ P0.minus) :
    ∃ (Q_MP Q_D : S →L[ℝ] S) (k : ℕ),
      IsMoorePenroseInverse Q Q_MP ∧
      IsDrazinInverse Q Q_D k ∧
      IsMoorePenroseInverse.rightProjector Q Q_MP ≠ (1 : S →L[ℝ] S) ∧
      IsMoorePenroseInverse.leftProjector Q Q_MP ≠ (1 : S →L[ℝ] S) ∧
      IsDrazinInverse.projection Q Q_D ≠ (1 : S →L[ℝ] S) := by
  have hZero : HasZeroMode (S := S) Q :=
    hasZeroMode_of_dim_mismatch (M := M) P0 Q hodd hdim
  rcases exists_moorePenroseInverse_global (A := Q) with ⟨Q_MP, hMP⟩
  rcases exists_drazinInverse_global (A := Q) with ⟨k, Q_D, hD⟩
  refine ⟨Q_MP, Q_D, k, hMP, hD, ?_, ?_, ?_⟩
  · exact moorePenroseRightProjector_ne_one_of_hasZeroMode hMP hZero
  · exact moorePenroseLeftProjector_ne_one_of_hasZeroMode hMP hZero
  · exact drazinProjection_ne_one_of_hasZeroMode hD hZero

/--
Structure-valued nontrivial regularization package extracted from the
dimension-mismatch argument.
-/
@[rep_depth operator]
noncomputable def nontrivialRegularizationPackage_of_dim_mismatch
    (M : RealMajoranaDatum (S := S))
    (P0 : KPolarization (S := S) M)
    (Q : S →L[ℝ] S)
    (hodd : PolarizationOdd (M := M) P0 Q)
    (hdim :
      Module.finrank ℝ P0.plus
        ≠ Module.finrank ℝ P0.minus) :
    NontrivialRegularizationPackage (S := S) Q := by
  classical
  let hReg :=
    exists_nontrivial_regularization_pair_of_dim_mismatch
      (S := S) (M := M) P0 Q hodd hdim
  let Q_MP := Classical.choose hReg
  let hReg1 := Classical.choose_spec hReg
  let Q_D := Classical.choose hReg1
  let hReg2 := Classical.choose_spec hReg1
  let k := Classical.choose hReg2
  let hReg3 := Classical.choose_spec hReg2
  exact
    { Q_MP := Q_MP
      Q_D := Q_D
      k := k
      hMP := hReg3.1
      hD := hReg3.2.1
      rightProjector_ne_one := hReg3.2.2.1
      leftProjector_ne_one := hReg3.2.2.2.1
      drazinProjection_ne_one := hReg3.2.2.2.2 }

/--
Structure-valued zero-mode plus nontrivial regularization package extracted from
the dimension-mismatch argument.
-/
@[rep_depth operator]
noncomputable def zeroModeRegularizationPackage_of_dim_mismatch
    (M : RealMajoranaDatum (S := S))
    (P0 : KPolarization (S := S) M)
    (Q : S →L[ℝ] S)
    (hodd : PolarizationOdd (M := M) P0 Q)
    (hdim :
      Module.finrank ℝ P0.plus
        ≠ Module.finrank ℝ P0.minus) :
    ZeroModeRegularizationPackage (S := S) Q := by
  classical
  let hZero := exists_zeroMode_of_dim_mismatch (M := M) P0 Q hodd hdim
  let v := Classical.choose hZero
  let hZeroSpec := Classical.choose_spec hZero
  let reg :=
    nontrivialRegularizationPackage_of_dim_mismatch
      (S := S) (M := M) P0 Q hodd hdim
  exact
    { v := v
      v_zeroMode := hZeroSpec.1
      v_ne_zero := hZeroSpec.2
      reg := reg }

/--
Explicit witness version of the nontrivial regularization package.
-/
@[rep_depth operator]
theorem exists_zeroMode_and_nontrivial_regularization_pair_of_dim_mismatch
    (M : RealMajoranaDatum (S := S))
    (P0 : KPolarization (S := S) M)
    (Q : S →L[ℝ] S)
    (hodd : PolarizationOdd (M := M) P0 Q)
    (hdim :
      Module.finrank ℝ P0.plus
        ≠ Module.finrank ℝ P0.minus) :
    ∃ v : S, Q v = 0 ∧ v ≠ 0
      ∧ ∃ (Q_MP Q_D : S →L[ℝ] S) (k : ℕ),
          IsMoorePenroseInverse Q Q_MP ∧
          IsDrazinInverse Q Q_D k ∧
          IsMoorePenroseInverse.rightProjector Q Q_MP ≠ (1 : S →L[ℝ] S) ∧
          IsMoorePenroseInverse.leftProjector Q Q_MP ≠ (1 : S →L[ℝ] S) ∧
          IsDrazinInverse.projection Q Q_D ≠ (1 : S →L[ℝ] S) := by
  let pkg :=
    zeroModeRegularizationPackage_of_dim_mismatch
      (S := S) (M := M) P0 Q hodd hdim
  exact
    ⟨pkg.v, pkg.v_zeroMode, pkg.v_ne_zero,
      pkg.reg.Q_MP, pkg.reg.Q_D, pkg.reg.k,
      pkg.reg.hMP, pkg.reg.hD,
      pkg.reg.rightProjector_ne_one,
      pkg.reg.leftProjector_ne_one,
      pkg.reg.drazinProjection_ne_one⟩

/--
Turnkey existential regularization package for the concrete open-chain operator
coming from a simplified boundary model in the `topologicalIndexZ2 = 1` phase.
-/
@[rep_depth operator]
theorem exists_nontrivial_regularization_pair_of_topologicalIndexZ2_eq_one_of_simplifiedBoundaryModel
    (M : RealMajoranaDatum (S := S))
    (P0 : KPolarization (S := S) M)
    (localOp : KitaevCell → S →L[ℝ] S)
    (chain : List KitaevCell)
    (hTopo : topologicalIndexZ2 chain = 1)
    (hPHS : ∀ c : KitaevCell,
      ParticleHoleSymmetric (M := M) (P0 := P0) (localOp c))
    (hSimple : SimplifiedBoundaryModel (M := M) (P0 := P0) localOp chain) :
    ∃ (Q_MP Q_D : S →L[ℝ] S) (k : ℕ),
      IsMoorePenroseInverse
        (globalChainOperatorFromOpenChain (S := S) localOp chain) Q_MP ∧
      IsDrazinInverse
        (globalChainOperatorFromOpenChain (S := S) localOp chain) Q_D k ∧
      IsMoorePenroseInverse.rightProjector
          (globalChainOperatorFromOpenChain (S := S) localOp chain) Q_MP
          ≠ (1 : S →L[ℝ] S) ∧
      IsMoorePenroseInverse.leftProjector
          (globalChainOperatorFromOpenChain (S := S) localOp chain) Q_MP
          ≠ (1 : S →L[ℝ] S) ∧
      IsDrazinInverse.projection
          (globalChainOperatorFromOpenChain (S := S) localOp chain) Q_D
          ≠ (1 : S →L[ℝ] S) := by
  let Q := globalChainOperatorFromOpenChain (S := S) localOp chain
  have hodd :
      PolarizationOdd (M := M) P0 Q :=
    polarizationOdd_globalChainOperatorFromOpenChain
      (M := M) (P0 := P0) (localOp := localOp) hPHS chain
  have hLoc :
      BoundaryLocalizationBridge
        (M := M) (P0 := P0) localOp chain :=
    boundaryLocalizationBridge_of_simplifiedBoundaryModel
      (M := M) (P0 := P0) (localOp := localOp) (chain := chain) hSimple
  have hdim :
      Module.finrank ℝ P0.plus
        ≠ Module.finrank ℝ P0.minus :=
    dim_mismatch_of_topologicalIndexZ2_eq_one
      (M := M) (P0 := P0) chain hTopo
      (hNegPhaseDimMismatch_of_boundaryLocalizationBridge
        (M := M) (P0 := P0) (localOp := localOp) (chain := chain) hLoc)
  simpa [Q] using
    exists_nontrivial_regularization_pair_of_dim_mismatch
      (S := S) (M := M) (P0 := P0) Q hodd hdim

/--
Structure-valued turnkey regularization package for the concrete open-chain
operator coming from a simplified boundary model in the `topologicalIndexZ2 = 1`
phase.
-/
@[rep_depth operator]
noncomputable def nontrivialRegularizationPackage_of_topologicalIndexZ2_eq_one_of_simplifiedBoundaryModel
    (M : RealMajoranaDatum (S := S))
    (P0 : KPolarization (S := S) M)
    (localOp : KitaevCell → S →L[ℝ] S)
    (chain : List KitaevCell)
    (hTopo : topologicalIndexZ2 chain = 1)
    (hPHS : ∀ c : KitaevCell,
      ParticleHoleSymmetric (M := M) (P0 := P0) (localOp c))
    (hSimple : SimplifiedBoundaryModel (M := M) (P0 := P0) localOp chain) :
    NontrivialRegularizationPackage
      (S := S) (globalChainOperatorFromOpenChain (S := S) localOp chain) := by
  let Q := globalChainOperatorFromOpenChain (S := S) localOp chain
  have hodd :
      PolarizationOdd (M := M) P0 Q :=
    polarizationOdd_globalChainOperatorFromOpenChain
      (M := M) (P0 := P0) (localOp := localOp) hPHS chain
  have hLoc :
      BoundaryLocalizationBridge
        (M := M) (P0 := P0) localOp chain :=
    boundaryLocalizationBridge_of_simplifiedBoundaryModel
      (M := M) (P0 := P0) (localOp := localOp) (chain := chain) hSimple
  have hdim :
      Module.finrank ℝ P0.plus
        ≠ Module.finrank ℝ P0.minus :=
    dim_mismatch_of_topologicalIndexZ2_eq_one
      (M := M) (P0 := P0) chain hTopo
      (hNegPhaseDimMismatch_of_boundaryLocalizationBridge
        (M := M) (P0 := P0) (localOp := localOp) (chain := chain) hLoc)
  simpa [Q] using
    nontrivialRegularizationPackage_of_dim_mismatch
      (S := S) (M := M) (P0 := P0) Q hodd hdim

/--
Structure-valued zero-mode plus nontrivial regularization package for the
concrete open-chain operator coming from a simplified boundary model in the
`topologicalIndexZ2 = 1` phase.
-/
@[rep_depth operator]
noncomputable def zeroModeRegularizationPackage_of_topologicalIndexZ2_eq_one_of_simplifiedBoundaryModel
    (M : RealMajoranaDatum (S := S))
    (P0 : KPolarization (S := S) M)
    (localOp : KitaevCell → S →L[ℝ] S)
    (chain : List KitaevCell)
    (hTopo : topologicalIndexZ2 chain = 1)
    (hPHS : ∀ c : KitaevCell,
      ParticleHoleSymmetric (M := M) (P0 := P0) (localOp c))
    (hSimple : SimplifiedBoundaryModel (M := M) (P0 := P0) localOp chain) :
    ZeroModeRegularizationPackage
      (S := S) (globalChainOperatorFromOpenChain (S := S) localOp chain) := by
  let Q := globalChainOperatorFromOpenChain (S := S) localOp chain
  have hodd :
      PolarizationOdd (M := M) P0 Q :=
    polarizationOdd_globalChainOperatorFromOpenChain
      (M := M) (P0 := P0) (localOp := localOp) hPHS chain
  have hLoc :
      BoundaryLocalizationBridge
        (M := M) (P0 := P0) localOp chain :=
    boundaryLocalizationBridge_of_simplifiedBoundaryModel
      (M := M) (P0 := P0) (localOp := localOp) (chain := chain) hSimple
  have hdim :
      Module.finrank ℝ P0.plus
        ≠ Module.finrank ℝ P0.minus :=
    dim_mismatch_of_topologicalIndexZ2_eq_one
      (M := M) (P0 := P0) chain hTopo
      (hNegPhaseDimMismatch_of_boundaryLocalizationBridge
        (M := M) (P0 := P0) (localOp := localOp) (chain := chain) hLoc)
  simpa [Q] using
    zeroModeRegularizationPackage_of_dim_mismatch
      (S := S) (M := M) (P0 := P0) Q hodd hdim

end Core

end InfoGeometry.Canonical.BulkBoundaryRegularizationBridge
