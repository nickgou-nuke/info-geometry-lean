import InfoGeometry.Canonical.BulkBoundaryRegularizationBridge
import InfoGeometry.Meta.Architecture
import InfoGeometry.Quantum.BulkBoundary

/-!
# Majorana Kitaev Spinor Bridge

Canonical bridge from the stable real Majorana/Kitaev bulk-boundary corridor to
Weyl-spinor boundary modes and a nontrivial generalized-inverse package.

This file is intentionally built on the landed owner surfaces:

- `Quantum.RealMajorana`
- `Quantum.KitaevChain`
- `Quantum.BulkBoundary`
- `Canonical.BulkBoundaryRegularizationBridge`

It does not depend on the sorry-equivalent modular spinor layer.
-/

namespace InfoGeometry.Canonical.MajoranaKitaevSpinorBridge

open InfoGeometry.Canonical.BulkBoundaryRegularizationBridge
open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.MoorePenrose
open InfoGeometry.KK
open InfoGeometry.Quantum.BulkBoundary
open InfoGeometry.Quantum.KitaevChain
open InfoGeometry.Quantum.RealMajorana

section Core

variable {S : Type*}
variable [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
variable [FiniteDimensional ℝ S]

/-- Weyl boundary zero-mode pair for a fixed global chain operator. -/
@[rep_depth krein]
structure WeylBoundarySpinorPair
    (M : RealMajoranaDatum (S := S))
    (Q : S →L[ℝ] S) where
  psiPlus : S
  psiMinus : S
  psiPlus_ne_zero : psiPlus ≠ 0
  psiMinus_ne_zero : psiMinus ≠ 0
  psiPlus_weyl : M.J psiPlus = psiPlus
  psiMinus_weyl : M.J psiMinus = -psiMinus
  psiPlus_zeroMode : Q psiPlus = 0
  psiMinus_zeroMode : Q psiMinus = 0

/--
Unified package: Weyl boundary spinors together with a nonidentity Moore-Penrose
and Drazin regularization package for the same chain operator.
-/
@[rep_depth krein]
structure MajoranaKitaevSpinorRegularizationPackage
    (M : RealMajoranaDatum (S := S))
    (Q : S →L[ℝ] S) where
  spinors : WeylBoundarySpinorPair (S := S) M Q
  Q_MP : S →L[ℝ] S
  Q_D : S →L[ℝ] S
  k : ℕ
  hMP : IsMoorePenroseInverse Q Q_MP
  hD : IsDrazinInverse Q Q_D k
  rightProjector_ne_one :
    MoorePenrose.IsMoorePenroseInverse.rightProjector Q Q_MP ≠ (1 : S →L[ℝ] S)
  leftProjector_ne_one :
    MoorePenrose.IsMoorePenroseInverse.leftProjector Q Q_MP ≠ (1 : S →L[ℝ] S)
  drazinProjection_ne_one :
    Drazin.IsDrazinInverse.projection Q Q_D ≠ (1 : S →L[ℝ] S)

section IndexResidue

variable {A B : Type*}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [InfoGeometry.Krein.KreinSpace S]
variable [InfoGeometry.Krein.KreinGradedModule S]

omit [FiniteDimensional ℝ S] in
/--
If the Majorana chirality operator is identified with the KK grading involution,
then the bounded KK phase is polarization-odd for the canonical chirality
polarization.
-/
@[rep_depth krein]
theorem polarizationOdd_F_of_chiralityPolarization_eq_kkChirality
    (X : KasparovCycle A B S)
    (M : RealMajoranaDatum (S := S))
    (hJ : M.J = InfoGeometry.Krein.KreinGradedModule.gradeCLM (H := S)) :
    PolarizationOdd (M := M) M.chiralityPolarization X.F := by
  unfold PolarizationOdd
  rw [RealMajoranaDatum.chiralityPolarization_P, hJ]
  simpa [InfoGeometry.KK.RealSplitKreinKasparovCycle.diracOperator,
    InfoGeometry.KK.RealSplitKreinKasparovCycle.chirality] using
    X.dirac_anticommutes_chirality

omit [FiniteDimensional ℝ S] in
/--
If both chiral kernel slices are explicitly identified with the canonical
Majorana chirality polarization and are both nontrivial, then the bounded KK
phase carries an explicit Weyl-plus/Weyl-minus zero-mode pair.
-/
@[rep_depth krein]
theorem exists_weyl_boundary_spinor_pair_of_nontrivial_chiralKernelSlices_of_identifiedChirality
    (X : KasparovCycle A B S)
    (M : RealMajoranaDatum (S := S))
    (hplus : M.chiralityPolarization.plus = KasparovCycle.chiralKernelSlicePlus X)
    (hminus : M.chiralityPolarization.minus = KasparovCycle.chiralKernelSliceMinus X)
    (hplus_ne : KasparovCycle.chiralKernelSlicePlus X ≠ ⊥)
    (hminus_ne : KasparovCycle.chiralKernelSliceMinus X ≠ ⊥) :
    ∃ spinors : WeylBoundarySpinorPair (S := S) M X.F,
      spinors.psiPlus ≠ 0 ∧
      spinors.psiMinus ≠ 0 ∧
      M.J spinors.psiPlus = spinors.psiPlus ∧
      M.J spinors.psiMinus = -spinors.psiMinus ∧
      X.F spinors.psiPlus = 0 ∧
      X.F spinors.psiMinus = 0 := by
  have hplus_ne' : M.chiralityPolarization.plus ≠ ⊥ := by
    rw [hplus]
    exact hplus_ne
  have hminus_ne' : M.chiralityPolarization.minus ≠ ⊥ := by
    rw [hminus]
    exact hminus_ne
  rcases (M.chiralityPolarization.plus).ne_bot_iff.mp hplus_ne' with
    ⟨ψplus, hψplus_mem, hψplus_ne⟩
  rcases (M.chiralityPolarization.minus).ne_bot_iff.mp hminus_ne' with
    ⟨ψminus, hψminus_mem, hψminus_ne⟩
  have hψplus_slice : ψplus ∈ KasparovCycle.chiralKernelSlicePlus X := by
    rw [← hplus]
    exact hψplus_mem
  have hψminus_slice : ψminus ∈ KasparovCycle.chiralKernelSliceMinus X := by
    rw [← hminus]
    exact hψminus_mem
  have hψplus_zero : X.F ψplus = 0 := by
    exact (Submodule.mem_inf.mp hψplus_slice).1
  have hψminus_zero : X.F ψminus = 0 := by
    exact (Submodule.mem_inf.mp hψminus_slice).1
  have hψplus_mem_weyl : ψplus ∈ M.weylPlus := by
    simpa using hψplus_mem
  have hψminus_mem_weyl : ψminus ∈ M.weylMinus := by
    simpa using hψminus_mem
  have hψplus_weyl :
      M.J ψplus = ψplus := by
    simpa using (M.mem_weylPlus_iff ψplus).mp hψplus_mem_weyl
  have hψminus_weyl :
      M.J ψminus = -ψminus := by
    simpa using (M.mem_weylMinus_iff ψminus).mp hψminus_mem_weyl
  let spinors : WeylBoundarySpinorPair (S := S) M X.F :=
    { psiPlus := ψplus
      psiMinus := ψminus
      psiPlus_ne_zero := hψplus_ne
      psiMinus_ne_zero := hψminus_ne
      psiPlus_weyl := hψplus_weyl
      psiMinus_weyl := hψminus_weyl
      psiPlus_zeroMode := hψplus_zero
      psiMinus_zeroMode := hψminus_zero }
  exact
    ⟨spinors,
      hψplus_ne, hψminus_ne, hψplus_weyl, hψminus_weyl,
      hψplus_zero, hψminus_zero⟩

/--
Nonzero analytical index, together with explicit identification of the
chirality polarization and nontriviality of both chiral slices, yields existence
of a Weyl boundary spinor plus nontrivial regularization package for the bounded
KK phase.
-/
@[rep_depth krein]
theorem exists_majorana_kitaev_spinor_regularization_package_of_nonzero_analyticalIndex_of_identifiedChiralKernelSlices
    (X : KasparovCycle A B S)
    (M : RealMajoranaDatum (S := S))
    (hJ : M.J = InfoGeometry.Krein.KreinGradedModule.gradeCLM (H := S))
    (hplus : M.chiralityPolarization.plus = KasparovCycle.chiralKernelSlicePlus X)
    (hminus : M.chiralityPolarization.minus = KasparovCycle.chiralKernelSliceMinus X)
    (hplus_ne : KasparovCycle.chiralKernelSlicePlus X ≠ ⊥)
    (hminus_ne : KasparovCycle.chiralKernelSliceMinus X ≠ ⊥)
    (hNonzero : X.analyticalIndex ≠ 0) :
    ∃ pkg : MajoranaKitaevSpinorRegularizationPackage (S := S) M X.F,
      IsMoorePenroseInverse X.F pkg.Q_MP ∧
      IsDrazinInverse X.F pkg.Q_D pkg.k ∧
      MoorePenrose.IsMoorePenroseInverse.rightProjector X.F pkg.Q_MP
        ≠ (1 : S →L[ℝ] S) ∧
      MoorePenrose.IsMoorePenroseInverse.leftProjector X.F pkg.Q_MP
        ≠ (1 : S →L[ℝ] S) ∧
      Drazin.IsDrazinInverse.projection X.F pkg.Q_D
        ≠ (1 : S →L[ℝ] S) := by
  rcases
    exists_weyl_boundary_spinor_pair_of_nontrivial_chiralKernelSlices_of_identifiedChirality
      (X := X) (M := M) hplus hminus hplus_ne hminus_ne with
    ⟨spinors, _hψplus_ne, _hψminus_ne, _hψplus_weyl, _hψminus_weyl,
      _hψplus_zero, _hψminus_zero⟩
  rcases
    exists_zero_mode_regularization_package_of_nonzero_analyticalIndex_of_identifiedPolarization
      (X := X) (M := M) (P0 := M.chiralityPolarization)
      hplus hminus
      (polarizationOdd_F_of_chiralityPolarization_eq_kkChirality
        (X := X) (M := M) hJ)
      hNonzero with
    ⟨reg, _hZero, _hNonzero, hMP, hD, hRight, hLeft, hDrazin⟩
  let pkg : MajoranaKitaevSpinorRegularizationPackage (S := S) M X.F :=
    { spinors := spinors
      Q_MP := reg.reg.Q_MP
      Q_D := reg.reg.Q_D
      k := reg.reg.k
      hMP := reg.reg.hMP
      hD := reg.reg.hD
      rightProjector_ne_one := reg.reg.rightProjector_ne_one
      leftProjector_ne_one := reg.reg.leftProjector_ne_one
      drazinProjection_ne_one := reg.reg.drazinProjection_ne_one }
  exact ⟨pkg, hMP, hD, hRight, hLeft, hDrazin⟩

end IndexResidue

omit [FiniteDimensional ℝ S] in
/--
Topological Kitaev phase plus a simplified boundary model in the chirality
polarization yields an explicit Weyl boundary spinor pair for the global
open-chain operator.
-/
@[rep_depth krein]
noncomputable def weylBoundarySpinorPair_of_simplifiedBoundaryModel
    (M : RealMajoranaDatum (S := S))
    (localOp : KitaevCell → S →L[ℝ] S)
    (chain : List KitaevCell)
    (hTopo : topologicalIndexZ2 chain = 1)
    (_hPHS : ∀ c : KitaevCell,
      ParticleHoleSymmetric (M := M) (P0 := M.chiralityPolarization) (localOp c))
    (hSimple :
      SimplifiedBoundaryModel (M := M) (P0 := M.chiralityPolarization) localOp chain) :
    WeylBoundarySpinorPair
      (S := S) M (globalChainOperatorFromOpenChain (S := S) localOp chain) := by
  let hPair :=
    boundaryLocalizedZeroModeWitness_of_topologicalIndexZ2_eq_one_of_simplifiedBoundaryModel
      (M := M) (P0 := M.chiralityPolarization) localOp chain hTopo hSimple
  have hPlusWeyl :
      M.J hPair.psiPlus = hPair.psiPlus := by
    simpa using (M.mem_weylPlus_iff hPair.psiPlus).mp hPair.psiPlus_mem
  have hMinusWeyl :
      M.J hPair.psiMinus = -hPair.psiMinus := by
    simpa using (M.mem_weylMinus_iff hPair.psiMinus).mp hPair.psiMinus_mem
  exact
    { psiPlus := hPair.psiPlus
      psiMinus := hPair.psiMinus
      psiPlus_ne_zero := hPair.psiPlus_ne_zero
      psiMinus_ne_zero := hPair.psiMinus_ne_zero
      psiPlus_weyl := hPlusWeyl
      psiMinus_weyl := hMinusWeyl
      psiPlus_zeroMode := hPair.psiPlus_zeroMode
      psiMinus_zeroMode := hPair.psiMinus_zeroMode }

omit [FiniteDimensional ℝ S] in
/--
Topological Kitaev phase plus a simplified boundary model in the chirality
polarization yields explicit Weyl boundary spinor zero modes.
-/
@[rep_depth krein]
theorem exists_weyl_boundary_spinor_pair_of_simplifiedBoundaryModel
    (M : RealMajoranaDatum (S := S))
    (localOp : KitaevCell → S →L[ℝ] S)
    (chain : List KitaevCell)
    (hTopo : topologicalIndexZ2 chain = 1)
    (_hPHS : ∀ c : KitaevCell,
      ParticleHoleSymmetric (M := M) (P0 := M.chiralityPolarization) (localOp c))
    (hSimple :
      SimplifiedBoundaryModel (M := M) (P0 := M.chiralityPolarization) localOp chain) :
    ∃ spinors : WeylBoundarySpinorPair
        (S := S) M (globalChainOperatorFromOpenChain (S := S) localOp chain),
      spinors.psiPlus ≠ 0 ∧
      spinors.psiMinus ≠ 0 ∧
      M.J spinors.psiPlus = spinors.psiPlus ∧
      M.J spinors.psiMinus = -spinors.psiMinus ∧
      (globalChainOperatorFromOpenChain (S := S) localOp chain) spinors.psiPlus = 0 ∧
      (globalChainOperatorFromOpenChain (S := S) localOp chain) spinors.psiMinus = 0 := by
  let hPair :=
    boundaryLocalizedZeroModeWitness_of_topologicalIndexZ2_eq_one_of_simplifiedBoundaryModel
      (M := M) (P0 := M.chiralityPolarization) localOp chain hTopo hSimple
  have hPlusWeyl :
      M.J hPair.psiPlus = hPair.psiPlus := by
    simpa using (M.mem_weylPlus_iff hPair.psiPlus).mp hPair.psiPlus_mem
  have hMinusWeyl :
      M.J hPair.psiMinus = -hPair.psiMinus := by
    simpa using (M.mem_weylMinus_iff hPair.psiMinus).mp hPair.psiMinus_mem
  let spinors :
      WeylBoundarySpinorPair
        (S := S) M (globalChainOperatorFromOpenChain (S := S) localOp chain) :=
    { psiPlus := hPair.psiPlus
      psiMinus := hPair.psiMinus
      psiPlus_ne_zero := hPair.psiPlus_ne_zero
      psiMinus_ne_zero := hPair.psiMinus_ne_zero
      psiPlus_weyl := hPlusWeyl
      psiMinus_weyl := hMinusWeyl
      psiPlus_zeroMode := hPair.psiPlus_zeroMode
      psiMinus_zeroMode := hPair.psiMinus_zeroMode }
  exact
    ⟨spinors,
      hPair.psiPlus_ne_zero, hPair.psiMinus_ne_zero,
      hPlusWeyl, hMinusWeyl,
      hPair.psiPlus_zeroMode, hPair.psiMinus_zeroMode⟩

/--
The same topological/simplified-boundary hypotheses yield a genuinely
nonidentity Moore-Penrose/Drazin package for the global open-chain operator.
-/
@[rep_depth operator]
theorem exists_nontrivial_regularization_pair_of_simplifiedBoundaryModel
    (M : RealMajoranaDatum (S := S))
    (localOp : KitaevCell → S →L[ℝ] S)
    (chain : List KitaevCell)
    (hTopo : topologicalIndexZ2 chain = 1)
    (hPHS : ∀ c : KitaevCell,
      ParticleHoleSymmetric (M := M) (P0 := M.chiralityPolarization) (localOp c))
    (hSimple :
      SimplifiedBoundaryModel (M := M) (P0 := M.chiralityPolarization) localOp chain) :
    ∃ (Q_MP Q_D : S →L[ℝ] S) (k : ℕ),
      IsMoorePenroseInverse
        (globalChainOperatorFromOpenChain (S := S) localOp chain) Q_MP ∧
      IsDrazinInverse
        (globalChainOperatorFromOpenChain (S := S) localOp chain) Q_D k ∧
      MoorePenrose.IsMoorePenroseInverse.rightProjector
          (globalChainOperatorFromOpenChain (S := S) localOp chain) Q_MP
          ≠ (1 : S →L[ℝ] S) ∧
      MoorePenrose.IsMoorePenroseInverse.leftProjector
          (globalChainOperatorFromOpenChain (S := S) localOp chain) Q_MP
          ≠ (1 : S →L[ℝ] S) ∧
      Drazin.IsDrazinInverse.projection
          (globalChainOperatorFromOpenChain (S := S) localOp chain) Q_D
          ≠ (1 : S →L[ℝ] S) := by
  simpa using
    exists_nontrivial_regularization_pair_of_topologicalIndexZ2_eq_one_of_simplifiedBoundaryModel
      (S := S) (M := M) (P0 := M.chiralityPolarization)
      localOp chain hTopo hPHS hSimple

/--
Existence of the stable Majorana/Kitaev/Weyl corridor package: topological phase
data yields Weyl boundary spinors and a nonidentity generalized-inverse package
for the same global chain operator.
-/
@[rep_depth krein]
theorem exists_majorana_kitaev_spinor_regularization_package_of_simplifiedBoundaryModel
    (M : RealMajoranaDatum (S := S))
    (localOp : KitaevCell → S →L[ℝ] S)
    (chain : List KitaevCell)
    (hTopo : topologicalIndexZ2 chain = 1)
    (hPHS : ∀ c : KitaevCell,
      ParticleHoleSymmetric (M := M) (P0 := M.chiralityPolarization) (localOp c))
    (hSimple :
      SimplifiedBoundaryModel (M := M) (P0 := M.chiralityPolarization) localOp chain) :
    ∃ pkg : MajoranaKitaevSpinorRegularizationPackage
        (S := S) M (globalChainOperatorFromOpenChain (S := S) localOp chain),
      IsMoorePenroseInverse
        (globalChainOperatorFromOpenChain (S := S) localOp chain) pkg.Q_MP ∧
      IsDrazinInverse
        (globalChainOperatorFromOpenChain (S := S) localOp chain) pkg.Q_D pkg.k ∧
      MoorePenrose.IsMoorePenroseInverse.rightProjector
          (globalChainOperatorFromOpenChain (S := S) localOp chain) pkg.Q_MP
          ≠ (1 : S →L[ℝ] S) ∧
      MoorePenrose.IsMoorePenroseInverse.leftProjector
          (globalChainOperatorFromOpenChain (S := S) localOp chain) pkg.Q_MP
          ≠ (1 : S →L[ℝ] S) ∧
      Drazin.IsDrazinInverse.projection
          (globalChainOperatorFromOpenChain (S := S) localOp chain) pkg.Q_D
          ≠ (1 : S →L[ℝ] S) := by
  let Q := globalChainOperatorFromOpenChain (S := S) localOp chain
  rcases
    exists_weyl_boundary_spinor_pair_of_simplifiedBoundaryModel
      (S := S) M localOp chain hTopo hPHS hSimple
    with
    ⟨spinors, _hψplus_ne, _hψminus_ne, _hψplus_weyl, _hψminus_weyl,
      _hψplus_zero, _hψminus_zero⟩
  rcases
    exists_nontrivial_regularization_package_of_topologicalIndexZ2_eq_one_of_simplifiedBoundaryModel
      (S := S) (M := M) (P0 := M.chiralityPolarization)
      localOp chain hTopo hPHS hSimple with
    ⟨reg, hMP, hD, hRight, hLeft, hDrazin⟩
  let pkg :
      MajoranaKitaevSpinorRegularizationPackage
        (S := S) M (globalChainOperatorFromOpenChain (S := S) localOp chain) :=
    { spinors := by simpa [Q] using spinors
      Q_MP := reg.Q_MP
      Q_D := reg.Q_D
      k := reg.k
      hMP := reg.hMP
      hD := reg.hD
      rightProjector_ne_one := reg.rightProjector_ne_one
      leftProjector_ne_one := reg.leftProjector_ne_one
      drazinProjection_ne_one := reg.drazinProjection_ne_one }
  exact ⟨pkg, hMP, hD, hRight, hLeft, hDrazin⟩

end Core

end InfoGeometry.Canonical.MajoranaKitaevSpinorBridge
