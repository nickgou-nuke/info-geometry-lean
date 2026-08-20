import InfoGeometry.Lie.SplitOctonionDerivationWittOrthogonalBridge
import InfoGeometry.Lie.SplitOctonionDerivationSO55Bridge
import InfoGeometry.Canonical.G2Cl55ChiralHodgeEquivarianceBridge
import InfoGeometry.Clifford.Cl55SpinBivectorLieBridge
import InfoGeometry.Canonical.RealUHFFiniteMatrixNormedCarrier
import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# Split-octonion derivations through a supplied `Cl(5,5)` spinor lift

This owner is the theorem-safe composition layer between the existing native
derivation matrix realization and the master spinor carrier.  It does not
invent a map from `Mat10` to spinor matrices.  Instead, a future concrete
Clifford construction supplies a Lie lift together with its chirality and
Hodge commutation proofs; all transport consequences are then automatic.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitOctonionDerivationSpinorLiftBridge

open InfoGeometry.Lie.SplitOctonionDerivationWittOrthogonalBridge
open InfoGeometry.Lie.SplitOctonionDerivationSO55Bridge
open InfoGeometry.Canonical.G2Cl55ChiralHodgeEquivarianceBridge
open InfoGeometry.Canonical.Cl55MasterWittSpinorEnvelopeBridge
open InfoGeometry.Canonical.Cl55MasterParityOddnessBridge
open InfoGeometry.Canonical.Cl55MasterChiralHodgeBlockBridge
open InfoGeometry.Clifford.Cl55SpinBivectorImage
open InfoGeometry.Clifford.Cl55SpinBivectorLieBridge
open InfoGeometry.Clifford.TowerMatrix

abbrev Mat10 := InfoGeometry.Lie.SplitOctonionDerivationSO55Bridge.Mat10
abbrev Mat32 := InfoGeometry.Canonical.G2Cl55ChiralHodgeEquivarianceBridge.Mat32
abbrev Derivation := InfoGeometry.Lie.SplitOctonionDerivationSO55Bridge.Derivation
abbrev SpinBivector55 := InfoGeometry.Clifford.Cl55SpinBivectorImage.SpinBivector55

noncomputable def spinorMatrixToMat32 :
    InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5 ≃ₐ[ℝ] Mat32 :=
  (matEquivFinPowTwo 5).symm

/-- Data required from a concrete `so(5,5)` spinor realization. -/
structure SpinorLiftDatum where
  rho : Mat10 →ₗ⁅ℝ⁆ Mat32
  commutes_chirality : ∀ A, rho A * MasterChirality = MasterChirality * rho A
  commutes_hodge : ∀ A,
    rho A * embeddedSplitOctonionHodgeDirac =
      embeddedSplitOctonionHodgeDirac * rho A

variable (L : SpinorLiftDatum)

/-- The induced action of a split-octonion derivation on the master spinor carrier. -/
def derivationSpinorAction (D : Derivation) : Mat32 :=
  L.rho (derivationToSO55 D)

@[simp] theorem derivationSpinorAction_apply (D : Derivation) :
    derivationSpinorAction L D = L.rho (derivationToSO55 D) := rfl

theorem derivationSpinorAction_map_lie (D E : Derivation) :
    derivationSpinorAction L ⁅D, E⁆ =
      derivationSpinorAction L D * derivationSpinorAction L E -
        derivationSpinorAction L E * derivationSpinorAction L D := by
  dsimp [derivationSpinorAction]
  rw [derivationToSO55_map_lie]
  exact L.rho.map_lie (derivationToSO55 D) (derivationToSO55 E)

theorem derivationSpinorAction_commutes_chirality (D : Derivation) :
    derivationSpinorAction L D * MasterChirality =
      MasterChirality * derivationSpinorAction L D :=
  L.commutes_chirality (derivationToSO55 D)

theorem derivationSpinorAction_commutes_hodge (D : Derivation) :
    derivationSpinorAction L D * embeddedSplitOctonionHodgeDirac =
      embeddedSplitOctonionHodgeDirac * derivationSpinorAction L D :=
  L.commutes_hodge (derivationToSO55 D)

/-- Every supplied lift packages the induced action as the existing equivariance datum. -/
def derivationSpinorRepresentation (D : Derivation) : G2SpinorRepresentation where
  rho := derivationSpinorAction L D
  even_parity := derivationSpinorAction_commutes_chirality L D
  commutes_hodge := derivationSpinorAction_commutes_hodge L D

@[simp] theorem derivationSpinorRepresentation_rho (D : Derivation) :
    (derivationSpinorRepresentation L D).rho = derivationSpinorAction L D := rfl

theorem derivationSpinorAction_preserves_chiralPlus (D : Derivation) :
    derivationSpinorAction L D * masterChiralProjectorPlus =
      masterChiralProjectorPlus * derivationSpinorAction L D := by
  have h := g2Spin_preserves_chiralPlus (derivationSpinorRepresentation L D)
  exact h

theorem derivationSpinorAction_preserves_chiralMinus (D : Derivation) :
    derivationSpinorAction L D * masterChiralProjectorMinus =
      masterChiralProjectorMinus * derivationSpinorAction L D := by
  have h := g2Spin_preserves_chiralMinus (derivationSpinorRepresentation L D)
  exact h

theorem derivationSpinorAction_commutes_chiralDiracPlus (D : Derivation) :
    derivationSpinorAction L D * chiralDiracPlusOp =
      chiralDiracPlusOp * derivationSpinorAction L D := by
  have h := g2Spin_commutes_chiralDiracPlus (derivationSpinorRepresentation L D)
  exact h

theorem derivationSpinorAction_commutes_chiralDiracMinus (D : Derivation) :
    derivationSpinorAction L D * chiralDiracMinusOp =
      chiralDiracMinusOp * derivationSpinorAction L D := by
  have h := g2Spin_commutes_chiralDiracMinus (derivationSpinorRepresentation L D)
  exact h

/-! A native variant of the interface.  Here the missing composition is
explicitly a Lie lift into the Clifford bivector subalgebra, after which the
existing bivector-to-spinor algebra equivalence supplies the action. -/

structure NativeSpinorLiftDatum where
  toBivector : Derivation →ₗ⁅ℝ⁆ SpinBivector55
  commutes_chirality : ∀ D,
    spinorMatrixToMat32 (spinBivectorMatrixLinear (toBivector D)) * MasterChirality =
      MasterChirality * spinorMatrixToMat32 (spinBivectorMatrixLinear (toBivector D))
  commutes_hodge : ∀ D,
    spinorMatrixToMat32 (spinBivectorMatrixLinear (toBivector D)) *
        embeddedSplitOctonionHodgeDirac =
      embeddedSplitOctonionHodgeDirac *
        spinorMatrixToMat32 (spinBivectorMatrixLinear (toBivector D))

def nativeDerivationSpinorAction (N : NativeSpinorLiftDatum) (D : Derivation) : Mat32 :=
  spinorMatrixToMat32 (spinBivectorMatrixLinear (N.toBivector D))

@[simp] theorem nativeDerivationSpinorAction_apply
    (N : NativeSpinorLiftDatum) (D : Derivation) :
    nativeDerivationSpinorAction N D =
      spinorMatrixToMat32 (spinBivectorMatrixLinear (N.toBivector D)) := rfl

/-- Every supplied native lift remains in the strict Clifford bivector image. -/
theorem nativeDerivationSpinorAction_mem_nativeImage
    (N : NativeSpinorLiftDatum) (D : Derivation) :
    ∃ X : SpinBivector55,
      nativeDerivationSpinorAction N D =
        spinorMatrixToMat32 (spinBivectorMatrixLinear X) := by
  exact ⟨N.toBivector D, rfl⟩

/-- The inverse matrix equivalence recovers a bivector preimage for every native action. -/
theorem nativeDerivationSpinorAction_preimage_mem_range
    (N : NativeSpinorLiftDatum) (D : Derivation) :
    spinorMatrixToMat32.symm (nativeDerivationSpinorAction N D) ∈
      LinearMap.range spinBivectorMatrixLinear := by
  refine ⟨N.toBivector D, ?_⟩
  simp [nativeDerivationSpinorAction]

/-- Injectivity of the native spinor action reduces to injectivity of the supplied lift. -/
theorem nativeDerivationSpinorAction_injective
    (N : NativeSpinorLiftDatum)
    (hN : Function.Injective N.toBivector) :
    Function.Injective (nativeDerivationSpinorAction N) := by
  intro D E h
  apply hN
  apply spinBivectorMatrixLinear_injective
  apply spinorMatrixToMat32.injective
  exact h

theorem nativeDerivationSpinorAction_map_lie
    (N : NativeSpinorLiftDatum) (D E : Derivation) :
    nativeDerivationSpinorAction N ⁅D, E⁆ =
      nativeDerivationSpinorAction N D * nativeDerivationSpinorAction N E -
        nativeDerivationSpinorAction N E * nativeDerivationSpinorAction N D := by
  dsimp [nativeDerivationSpinorAction]
  rw [N.toBivector.map_lie]
  rw [spinBivectorMatrixLinear_map_lie]
  change spinorMatrixToMat32 ⁅
      spinBivectorMatrixLinear (N.toBivector D),
      spinBivectorMatrixLinear (N.toBivector E)⁆ = _
  simp [Ring.lie_def]

/-! The native action is a genuine Lie-homomorphism once the supplied
`Derivation → SpinBivector55` lift is viewed as the source map.  No
injectivity is built into `NativeSpinorLiftDatum`; it is exposed separately
as an explicit hypothesis below. -/

noncomputable def nativeDerivationSpinorLieHom
    (N : NativeSpinorLiftDatum) : Derivation →ₗ⁅ℝ⁆ Mat32 where
  toFun := nativeDerivationSpinorAction N
  map_add' := by
    intro D E
    dsimp [nativeDerivationSpinorAction]
    simp
  map_smul' := by
    intro r D
    dsimp [nativeDerivationSpinorAction]
    simp
  map_lie' := by
    intro D E
    exact nativeDerivationSpinorAction_map_lie N D E

@[simp] theorem nativeDerivationSpinorLieHom_apply
    (N : NativeSpinorLiftDatum) (D : Derivation) :
    nativeDerivationSpinorLieHom N D = nativeDerivationSpinorAction N D := rfl

theorem nativeDerivationSpinorLieHom_injective
    (N : NativeSpinorLiftDatum)
    (hN : Function.Injective N.toBivector) :
    Function.Injective (nativeDerivationSpinorLieHom N) := by
  intro D E h
  apply hN
  apply spinBivectorMatrixLinear_injective
  apply spinorMatrixToMat32.injective
  exact h

theorem nativeDerivationSpinorAction_commutes_chirality
    (N : NativeSpinorLiftDatum) (D : Derivation) :
    nativeDerivationSpinorAction N D * MasterChirality =
      MasterChirality * nativeDerivationSpinorAction N D :=
  N.commutes_chirality D

theorem nativeDerivationSpinorAction_commutes_hodge
    (N : NativeSpinorLiftDatum) (D : Derivation) :
    nativeDerivationSpinorAction N D * embeddedSplitOctonionHodgeDirac =
      embeddedSplitOctonionHodgeDirac * nativeDerivationSpinorAction N D :=
  N.commutes_hodge D

def nativeDerivationSpinorRepresentation
    (N : NativeSpinorLiftDatum) (D : Derivation) :
    G2SpinorRepresentation where
  rho := nativeDerivationSpinorAction N D
  even_parity := nativeDerivationSpinorAction_commutes_chirality N D
  commutes_hodge := nativeDerivationSpinorAction_commutes_hodge N D

theorem nativeDerivationSpinorAction_commutes_chiralDiracPlus
    (N : NativeSpinorLiftDatum) (D : Derivation) :
    nativeDerivationSpinorAction N D * chiralDiracPlusOp =
      chiralDiracPlusOp * nativeDerivationSpinorAction N D := by
  exact g2Spin_commutes_chiralDiracPlus (nativeDerivationSpinorRepresentation N D)

theorem nativeDerivationSpinorAction_commutes_chiralDiracMinus
    (N : NativeSpinorLiftDatum) (D : Derivation) :
    nativeDerivationSpinorAction N D * chiralDiracMinusOp =
      chiralDiracMinusOp * nativeDerivationSpinorAction N D := by
  exact g2Spin_commutes_chiralDiracMinus (nativeDerivationSpinorRepresentation N D)

/-! Finite exponential consequences of a supplied native lift. -/
noncomputable def nativeDerivationSpinorFlow
    (N : NativeSpinorLiftDatum) (D : Derivation) (t : ℝ) : Mat32 :=
  NormedSpace.exp (t • nativeDerivationSpinorAction N D)

theorem nativeDerivationSpinorFlow_commutes_chirality
    (N : NativeSpinorLiftDatum) (D : Derivation) (t : ℝ) :
    nativeDerivationSpinorFlow N D t * MasterChirality =
      MasterChirality * nativeDerivationSpinorFlow N D t := by
  have hbase : Commute (nativeDerivationSpinorAction N D) MasterChirality :=
    nativeDerivationSpinorAction_commutes_chirality N D
  have hscaled : Commute (t • nativeDerivationSpinorAction N D) MasterChirality :=
    hbase.smul_left t
  exact (hscaled.exp_left).eq

theorem nativeDerivationSpinorFlow_commutes_hodge
    (N : NativeSpinorLiftDatum) (D : Derivation) (t : ℝ) :
    nativeDerivationSpinorFlow N D t * embeddedSplitOctonionHodgeDirac =
      embeddedSplitOctonionHodgeDirac * nativeDerivationSpinorFlow N D t := by
  have hbase :
      Commute (nativeDerivationSpinorAction N D)
        embeddedSplitOctonionHodgeDirac :=
    nativeDerivationSpinorAction_commutes_hodge N D
  have hscaled :
      Commute (t • nativeDerivationSpinorAction N D)
        embeddedSplitOctonionHodgeDirac :=
    hbase.smul_left t
  exact (hscaled.exp_left).eq

end InfoGeometry.Canonical.SplitOctonionDerivationSpinorLiftBridge
