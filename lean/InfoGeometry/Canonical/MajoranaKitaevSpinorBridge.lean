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

/--
Topological Kitaev phase plus a simplified boundary model in the chirality
polarization yields explicit Weyl boundary spinor zero modes.
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
  refine
    { psiPlus := hPair.psiPlus
      psiMinus := hPair.psiMinus
      psiPlus_ne_zero := hPair.psiPlus_ne_zero
      psiMinus_ne_zero := hPair.psiMinus_ne_zero
      psiPlus_weyl := ?_
      psiMinus_weyl := ?_
      psiPlus_zeroMode := hPair.psiPlus_zeroMode
      psiMinus_zeroMode := hPair.psiMinus_zeroMode }
  · simpa using (M.mem_weylPlus_iff hPair.psiPlus).mp hPair.psiPlus_mem
  · simpa using (M.mem_weylMinus_iff hPair.psiMinus).mp hPair.psiMinus_mem

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
Canonical unification package for the stable Majorana/Kitaev/Weyl corridor:
topological phase data yields Weyl boundary spinors and a nonidentity
generalized-inverse package for the same global chain operator.
-/
@[rep_depth krein]
noncomputable def majoranaKitaevSpinorRegularizationPackage_of_simplifiedBoundaryModel
    (M : RealMajoranaDatum (S := S))
    (localOp : KitaevCell → S →L[ℝ] S)
    (chain : List KitaevCell)
    (hTopo : topologicalIndexZ2 chain = 1)
    (hPHS : ∀ c : KitaevCell,
      ParticleHoleSymmetric (M := M) (P0 := M.chiralityPolarization) (localOp c))
    (hSimple :
      SimplifiedBoundaryModel (M := M) (P0 := M.chiralityPolarization) localOp chain) :
    MajoranaKitaevSpinorRegularizationPackage
      (S := S) M (globalChainOperatorFromOpenChain (S := S) localOp chain) := by
  let Q := globalChainOperatorFromOpenChain (S := S) localOp chain
  let spinors :=
    weylBoundarySpinorPair_of_simplifiedBoundaryModel
      (S := S) M localOp chain hTopo hPHS hSimple
  let reg :=
    nontrivialRegularizationPackage_of_topologicalIndexZ2_eq_one_of_simplifiedBoundaryModel
      (S := S) (M := M) (P0 := M.chiralityPolarization)
      localOp chain hTopo hPHS hSimple
  exact
    { spinors := by simpa [Q] using spinors
      Q_MP := reg.Q_MP
      Q_D := reg.Q_D
      k := reg.k
      hMP := reg.hMP
      hD := reg.hD
      rightProjector_ne_one := reg.rightProjector_ne_one
      leftProjector_ne_one := reg.leftProjector_ne_one
      drazinProjection_ne_one := reg.drazinProjection_ne_one }

end Core

end InfoGeometry.Canonical.MajoranaKitaevSpinorBridge
