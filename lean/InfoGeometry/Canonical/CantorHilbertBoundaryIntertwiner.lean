/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.CantorGoldenMeanBitwordBridge
import InfoGeometry.Canonical.ConcreteHilbertSewnAnomaly
import Mathlib.Analysis.Normed.Lp.lpSpace

noncomputable section

/-!
# Boolean and Hilbert Cantor boundary intertwiners

Identify the Boolean boundary used by finite-prefix and cylinder owners with
the plus/minus boundary indexing the sewn Hilbert carrier.  The equivalence
preserves prefixing.  This is an index-carrier equivalence; it does not assert
that cylinder observables, Hilbert states, or modular flows are intertwined.
-/

namespace InfoGeometry.Canonical.CantorHilbertBoundaryIntertwiner

open InfoGeometry.Canonical.CantorGoldenMeanBitwordBridge
open InfoGeometry.OperatorAlgebra.ErlangenNet
open InfoGeometry.Topology
open InfoGeometry.Canonical.ConcreteHilbertCommutation

/-- The binary sequence carrier used by the Boolean Cantor models. -/
abbrev BooleanBoundary := CantorGoldenMeanBitwordBridge.CantorBoundary

/-- The plus/minus alphabet indexing the sewn-Hilbert boundary. -/
abbrev HilbertSector := InfoGeometry.OperatorAlgebra.ErlangenNet.BinarySector

/-- The distinct plus/minus alphabet used by the L2 Cantor commutation owner. -/
abbrev L2Sector := InfoGeometry.Analysis.L2CantorCommutation.BinarySector

/-- The boundary index type of the sewn Hilbert space. -/
abbrev HilbertBoundary := InfoGeometry.Topology.BinaryCantorBoundary

/-- Convert Boolean branches to the plus/minus Hilbert boundary alphabet. -/
def sectorOfBool : Bool → HilbertSector
  | false => BinarySector.plus
  | true => BinarySector.minus

/-- Read a Boolean branch from the plus/minus Hilbert boundary alphabet. -/
def boolOfSector : HilbertSector → Bool
  | BinarySector.plus => false
  | BinarySector.minus => true

@[simp] theorem boolOfSector_sectorOfBool (b : Bool) :
    boolOfSector (sectorOfBool b) = b := by
  cases b <;> rfl

@[simp] theorem sectorOfBool_boolOfSector (s : HilbertSector) :
    sectorOfBool (boolOfSector s) = s := by
  cases s <;> rfl

/-- Convert the L2 Cantor `plus/minus` alphabet to the Erlangen Hilbert alphabet. -/
def l2SectorToHilbert : L2Sector → HilbertSector
  | InfoGeometry.Analysis.L2CantorCommutation.BinarySector.plus => BinarySector.plus
  | InfoGeometry.Analysis.L2CantorCommutation.BinarySector.minus => BinarySector.minus

/-- Decode an Erlangen Hilbert sector into the L2 Cantor alphabet. -/
def hilbertSectorToL2 : HilbertSector → L2Sector
  | BinarySector.plus => InfoGeometry.Analysis.L2CantorCommutation.BinarySector.plus
  | BinarySector.minus => InfoGeometry.Analysis.L2CantorCommutation.BinarySector.minus

@[simp] theorem hilbertSectorToL2_l2SectorToHilbert (s : L2Sector) :
    hilbertSectorToL2 (l2SectorToHilbert s) = s := by
  cases s <;> rfl

@[simp] theorem l2SectorToHilbert_hilbertSectorToL2 (s : HilbertSector) :
    l2SectorToHilbert (hilbertSectorToL2 s) = s := by
  cases s <;> rfl

@[simp] theorem l2SectorToHilbert_plus :
    l2SectorToHilbert InfoGeometry.Analysis.L2CantorCommutation.BinarySector.plus =
      BinarySector.plus := rfl

@[simp] theorem l2SectorToHilbert_minus :
    l2SectorToHilbert InfoGeometry.Analysis.L2CantorCommutation.BinarySector.minus =
      BinarySector.minus := rfl

/-- Equivalence between the repository's two independently defined sector types. -/
def l2SectorEquivHilbert : L2Sector ≃ HilbertSector where
  toFun := l2SectorToHilbert
  invFun := hilbertSectorToL2
  left_inv := hilbertSectorToL2_l2SectorToHilbert
  right_inv := l2SectorToHilbert_hilbertSectorToL2

@[simp] theorem l2SectorEquivHilbert_apply (s : L2Sector) :
    l2SectorEquivHilbert s = l2SectorToHilbert s := rfl

/-- Reindex a Boolean Cantor boundary by the Hilbert plus/minus alphabet. -/
def toHilbertBoundary (x : BooleanBoundary) : HilbertBoundary :=
  fun n => sectorOfBool (x n)

/-- Decode a Hilbert boundary back to Boolean coordinates. -/
def ofHilbertBoundary (x : HilbertBoundary) : BooleanBoundary :=
  fun n => boolOfSector (x n)

@[simp] theorem of_toHilbertBoundary (x : BooleanBoundary) :
    ofHilbertBoundary (toHilbertBoundary x) = x := by
  funext n
  simp [ofHilbertBoundary, toHilbertBoundary]

@[simp] theorem to_ofHilbertBoundary (x : HilbertBoundary) :
    toHilbertBoundary (ofHilbertBoundary x) = x := by
  funext n
  simp [ofHilbertBoundary, toHilbertBoundary]

/-- Explicit equivalence of the Boolean and sewn-Hilbert boundary indices. -/
def booleanBoundaryEquivHilbert : BooleanBoundary ≃ HilbertBoundary where
  toFun := toHilbertBoundary
  invFun := ofHilbertBoundary
  left_inv := of_toHilbertBoundary
  right_inv := to_ofHilbertBoundary

/-- Boolean prefixing is transported to the Hilbert boundary's prefix map. -/
theorem toHilbertBoundary_consBit (b : Bool) (x : BooleanBoundary) :
    toHilbertBoundary (CantorGoldenMeanBitwordBridge.consBit b x) =
      InfoGeometry.Topology.prefixBoundary (sectorOfBool b)
        (toHilbertBoundary x) := by
  funext n
  cases n <;> rfl

/-- Convert the existing L2 plus/minus boundary index into the sewn-Hilbert
boundary index. -/
def l2BoundaryToHilbert
    (x : CantorGoldenMeanBitwordBridge.L2BaseIndex) : HilbertBoundary :=
  fun n => l2SectorEquivHilbert (x n)

/-- The Boolean-to-L2 and Boolean-to-Hilbert maps commute after alphabet
conversion. -/
theorem boolean_to_l2_to_hilbert (x : BooleanBoundary) :
    l2BoundaryToHilbert
        (CantorGoldenMeanBitwordBridge.toBaseIndex x) = toHilbertBoundary x := by
  funext n
  cases h : x n <;>
    simp [l2BoundaryToHilbert, l2SectorEquivHilbert, l2SectorToHilbert,
      CantorGoldenMeanBitwordBridge.toBaseIndex,
      CantorGoldenMeanBitwordBridge.sectorOfBool, toHilbertBoundary, sectorOfBool, h]

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- The Boolean-indexed version of the doubled Hilbert fiber used by `H_lp`. -/
abbrev BooleanHilbertLp :=
  lp (fun _ : BooleanBoundary => InfoGeometry.Krein.DoubledSpace E) 2

/-- Reindex an `L²` field from Boolean addresses to the actual `H_lp` boundary. -/
def reindexToHilbert (ψ : BooleanHilbertLp (E := E)) :
    InfoGeometry.Canonical.ConcreteHilbertCommutation.H_lp E := by
  refine ⟨fun x => ψ (ofHilbertBoundary x), ?_⟩
  apply memℓp_gen
  have hψ : Summable (fun x : BooleanBoundary =>
      ‖ψ x‖ ^ ENNReal.toReal (2 : ENNReal)) :=
    (lp.memℓp ψ).summable (by norm_num)
  exact (Equiv.summable_iff booleanBoundaryEquivHilbert.symm).mpr hψ

/-- Pull an `H_lp` field back to Boolean address coordinates. -/
def reindexToBoolean
    (ψ : InfoGeometry.Canonical.ConcreteHilbertCommutation.H_lp E) :
    BooleanHilbertLp (E := E) := by
  refine ⟨fun x => ψ (toHilbertBoundary x), ?_⟩
  apply memℓp_gen
  have hψ : Summable (fun x : HilbertBoundary =>
      ‖ψ x‖ ^ ENNReal.toReal (2 : ENNReal)) :=
    (lp.memℓp ψ).summable (by norm_num)
  exact (Equiv.summable_iff booleanBoundaryEquivHilbert).mpr hψ

@[simp] theorem reindexToBoolean_reindexToHilbert
    (ψ : BooleanHilbertLp (E := E)) :
    reindexToBoolean (reindexToHilbert ψ) = ψ := by
  apply Subtype.ext
  funext x
  change ψ (ofHilbertBoundary (toHilbertBoundary x)) = ψ x
  rw [of_toHilbertBoundary]

@[simp] theorem reindexToHilbert_reindexToBoolean
    (ψ : InfoGeometry.Canonical.ConcreteHilbertCommutation.H_lp E) :
    reindexToHilbert (reindexToBoolean ψ) = ψ := by
  apply Subtype.ext
  funext x
  change ψ (toHilbertBoundary (ofHilbertBoundary x)) = ψ x
  rw [to_ofHilbertBoundary]

/-- Reindexing is linear because it only changes the address index. -/
def reindexLinear : BooleanHilbertLp (E := E) →ₗ[ℝ]
    InfoGeometry.Canonical.ConcreteHilbertCommutation.H_lp E where
  toFun := reindexToHilbert
  map_add' ψ φ := by
    apply Subtype.ext
    funext x
    rfl
  map_smul' c ψ := by
    apply Subtype.ext
    funext x
    rfl

/-- Reindexing back to Boolean addresses is linear. -/
def reindexLinearSymm : InfoGeometry.Canonical.ConcreteHilbertCommutation.H_lp E →ₗ[ℝ]
    BooleanHilbertLp (E := E) where
  toFun := reindexToBoolean
  map_add' ψ φ := by
    apply Subtype.ext
    funext x
    rfl
  map_smul' c ψ := by
    apply Subtype.ext
    funext x
    rfl

/-- The two linear reindexing maps are inverse. -/
theorem reindexLinear_left_inverse :
    reindexLinearSymm.comp reindexLinear =
      (LinearMap.id : BooleanHilbertLp (E := E) →ₗ[ℝ]
        BooleanHilbertLp (E := E)) := by
  apply LinearMap.ext
  intro ψ
  apply Subtype.ext
  funext x
  change ψ (ofHilbertBoundary (toHilbertBoundary x)) = ψ x
  rw [of_toHilbertBoundary]

/-- The two linear reindexing maps are inverse in the other direction. -/
theorem reindexLinear_right_inverse :
    reindexLinear.comp reindexLinearSymm =
      (LinearMap.id : InfoGeometry.Canonical.ConcreteHilbertCommutation.H_lp E →ₗ[ℝ]
        InfoGeometry.Canonical.ConcreteHilbertCommutation.H_lp E) := by
  apply LinearMap.ext
  intro ψ
  apply Subtype.ext
  funext x
  change ψ (toHilbertBoundary (ofHilbertBoundary x)) = ψ x
  rw [to_ofHilbertBoundary]

/-- Pointwise modular swap on Boolean-indexed `L²` fields. -/
noncomputable def booleanModularSwap (ψ : BooleanHilbertLp (E := E)) :
    BooleanHilbertLp (E := E) := by
  refine ⟨fun x => InfoGeometry.Krein.modular_j (E := E) (ψ x), ?_⟩
  apply memℓp_gen
  have hψ : Summable (fun x : BooleanBoundary =>
      ‖ψ x‖ ^ ENNReal.toReal (2 : ENNReal)) := (lp.memℓp ψ).summable (by norm_num)
  simpa only [InfoGeometry.Canonical.ConcreteHilbertSewnAnomaly.modular_j_norm]
    using hψ

/-- Pointwise fundamental symmetry on Boolean-indexed `L²` fields. -/
noncomputable def booleanFundamentalSymmetry (ψ : BooleanHilbertLp (E := E)) :
    BooleanHilbertLp (E := E) := by
  refine ⟨fun x => InfoGeometry.Krein.spectral_epsilon (E := E) (ψ x), ?_⟩
  apply memℓp_gen
  have hψ : Summable (fun x : BooleanBoundary =>
      ‖ψ x‖ ^ ENNReal.toReal (2 : ENNReal)) := (lp.memℓp ψ).summable (by norm_num)
  simpa only [InfoGeometry.Canonical.ConcreteHilbertSewnAnomaly.spectral_epsilon_norm]
    using hψ

/-- Reindexing intertwines the modular swap on the Boolean and Hilbert carriers. -/
theorem reindex_modularSwap_intertwines (ψ : BooleanHilbertLp (E := E)) :
    reindexLinear (booleanModularSwap ψ) =
      InfoGeometry.Canonical.ConcreteHilbertSewnAnomaly.J_lp_clm
        (E := E) (reindexToHilbert ψ) := by
  apply Subtype.ext
  funext x
  rfl

/-- Reindexing intertwines the fundamental symmetry on the Boolean and Hilbert
carriers. -/
theorem reindex_fundamentalSymmetry_intertwines
    (ψ : BooleanHilbertLp (E := E)) :
    reindexLinear (booleanFundamentalSymmetry ψ) =
      InfoGeometry.Canonical.ConcreteHilbertSewnAnomaly.epsilon_lp_clm
        (E := E) (reindexToHilbert ψ) := by
  apply Subtype.ext
  funext x
  rfl

end InfoGeometry.Canonical.CantorHilbertBoundaryIntertwiner
