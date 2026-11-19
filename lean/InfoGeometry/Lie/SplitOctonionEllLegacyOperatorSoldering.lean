/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Lie.SplitOctonionCircularBasisTransition
import InfoGeometry.Lie.SplitOctonionEllCircularKreinOperatorBridge

/-!
# Soldering the two circular operator-sector decompositions

The `uPlus/uMinus` Ell frame and the `zornPlus/zornMinus` legacy frame have
different coordinates on the same native Zorn carrier.  This module identifies
the legacy within/cross operator sectors with native regular-`J` centralizer
and double-commutator range using the established coordinate equivalences.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionEllLegacyOperatorSoldering

open InfoGeometry.Lie.SplitOctonionCircularBasisTransition
open InfoGeometry.Lie.SplitOctonionEllCircularKreinOperatorBridge
open InfoGeometry.Lie.SplitOctonionEllCrossChannel
open InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance

abbrev NativeEnd := EndCZ
abbrev LegacyCoord := InfoGeometry.Algebra.FiniteSpin.Vec8R

def nativeJ : NativeEnd := regularJ uPlus uMinus

def legacyReadout (T : NativeEnd) : Module.End ℝ LegacyCoord :=
  InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout T

/-- The concrete circular-basis readout as a linear equivalence of operator
carriers.  This is the map used below to transport the two operator sectors. -/
def legacyReadoutEquiv : NativeEnd ≃ₗ[ℝ] Module.End ℝ LegacyCoord :=
  InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout.toLinearEquiv

def nativeJCentralizer : Submodule ℝ NativeEnd where
  carrier := {T | nativeJ * T = T * nativeJ}
  zero_mem' := by simp
  add_mem' := by
    intro X Y hX hY
    change nativeJ * (X + Y) = (X + Y) * nativeJ
    rw [mul_add, add_mul, hX, hY]
  smul_mem' := by
    intro c X hX
    change nativeJ * (c • X) = (c • X) * nativeJ
    rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, hX]

def nativeJDoubleCommRange : Submodule ℝ NativeEnd :=
  LinearMap.range nativeRegularJDoubleCommMap

private theorem legacyReadout_injective : Function.Injective legacyReadout := by
  intro X Y h
  change (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis.equivFun.conjAlgEquiv ℝ) X =
    (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis.equivFun.conjAlgEquiv ℝ) Y at h
  exact (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis.equivFun.conjAlgEquiv ℝ).injective h

private theorem legacyReadout_zero_iff (T : NativeEnd) :
    legacyReadout T = 0 ↔ T = 0 := by
  constructor
  · intro h
    apply legacyReadout_injective
    simpa [legacyReadout] using h
  · rintro rfl
    simp [legacyReadout]

private theorem legacyReadout_smul_iff (c : ℝ) (X Y : NativeEnd) :
    legacyReadout X = c • legacyReadout Y ↔ X = c • Y := by
  constructor
  · intro h
    apply legacyReadout_injective
    simpa [legacyReadout] using h
  · intro h
    rw [h]
    simp [legacyReadout]

/-- The legacy within-sector block is exactly the readout of the native
regular-`J` centralizer. -/
theorem legacyWithin_iff_nativeJCentralizer (T : NativeEnd) :
    legacyReadout T ∈ legacyWithinSectorOperatorSubspace ↔
      T ∈ nativeJCentralizer := by
  have hlegacy := (legacyRegularJ_doubleComm_eigenspaces (legacyReadout T)).1
  have hsector : legacyReadout T ∈ legacyWithinSectorOperatorSubspace ↔
      legacyCoordinateDoubleComm legacyRegularJOperator (legacyReadout T) = 0 := by
    simpa [legacyRegularJOperator] using hlegacy.symm
  calc
    legacyReadout T ∈ legacyWithinSectorOperatorSubspace
        ↔ legacyCoordinateDoubleComm legacyRegularJOperator (legacyReadout T) = 0 := hsector
    _ ↔ T ∈ nativeJCentralizer := by
      have hsolder : legacyCoordinateDoubleComm (legacyReadout nativeJ) (legacyReadout T) =
          legacyReadout (doubleComm nativeJ T) := by
        simpa [legacyReadout] using legacyCoordinateDoubleComm_soldering nativeJ T
      rw [show legacyRegularJOperator = legacyReadout nativeJ from rfl, hsolder]
      change legacyReadout (doubleComm nativeJ T) = 0 ↔ nativeJ * T = T * nativeJ
      rw [legacyReadout_zero_iff]
      change doubleComm (regularJ uPlus uMinus) T = 0 ↔ _
      rw [← nativeRegularJDoubleCommMap_apply]
      exact nativeRegularJ_doubleComm_eq_zero_iff_commutes T

private theorem nativeJ_doubleComm_eq_four_iff_antiInvariant (T : NativeEnd) :
    doubleComm nativeJ T = (4 : ℝ) • T ↔ nativeJ * T * nativeJ = -T := by
  have hJ : nativeJ * nativeJ = 1 :=
    InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates.regularJ_uPlus_uMinus_sq
  have hform : doubleComm nativeJ T = (2 : ℝ) • (T - nativeJ * T * nativeJ) := by
    dsimp [doubleComm, operatorComm]
    calc
      nativeJ * (nativeJ * T - T * nativeJ) - (nativeJ * T - T * nativeJ) * nativeJ
          = (nativeJ * nativeJ) * T - 2 • (nativeJ * T * nativeJ) + T * (nativeJ * nativeJ) := by
              noncomm_ring
      _ = (2 : ℝ) • (T - nativeJ * T * nativeJ) := by rw [hJ]; module
  rw [hform]
  constructor
  · intro h
    have hsub : T - nativeJ * T * nativeJ = (2 : ℝ) • T := by
      have h' := congrArg (fun X : NativeEnd => (1 / 2 : ℝ) • X) h
      norm_num [smul_smul] at h'
      exact h'
    have hanti : nativeJ * T * nativeJ = -T := by
      calc
        nativeJ * T * nativeJ = T - (T - nativeJ * T * nativeJ) := by noncomm_ring
        _ = T - (2 : ℝ) • T := by rw [hsub]
        _ = -T := by module
    exact hanti
  · intro h
    rw [h]
    module

/-- The legacy cross-sector block is exactly the readout of the native
regular-`J` double-commutator range. -/
theorem legacyCross_iff_nativeJDoubleCommRange (T : NativeEnd) :
    legacyReadout T ∈ legacyCrossSectorOperatorSubspace ↔
      T ∈ nativeJDoubleCommRange := by
  have hlegacy := (legacyRegularJ_doubleComm_eigenspaces (legacyReadout T)).2
  have hsector : legacyReadout T ∈ legacyCrossSectorOperatorSubspace ↔
      legacyCoordinateDoubleComm legacyRegularJOperator (legacyReadout T) =
        (↑(4 : ℕ) : ℝ) • legacyReadout T := by
    simpa only [legacyRegularJOperator, Nat.cast_smul_eq_nsmul] using hlegacy.symm
  calc
    legacyReadout T ∈ legacyCrossSectorOperatorSubspace
        ↔ legacyCoordinateDoubleComm legacyRegularJOperator (legacyReadout T) =
          (4 : ℝ) • legacyReadout T := hsector
    _ ↔ T ∈ nativeJDoubleCommRange := by
      have hsolder : legacyCoordinateDoubleComm (legacyReadout nativeJ) (legacyReadout T) =
          legacyReadout (doubleComm nativeJ T) := by
        simpa [legacyReadout] using legacyCoordinateDoubleComm_soldering nativeJ T
      rw [show legacyRegularJOperator = legacyReadout nativeJ from rfl, hsolder,
        legacyReadout_smul_iff, nativeJ_doubleComm_eq_four_iff_antiInvariant]
      change nativeJ * T * nativeJ = -T ↔
        T ∈ LinearMap.range nativeRegularJDoubleCommMap
      rw [nativeJ]
      exact (nativeRegularJ_doubleComm_mem_range_iff_anti_conjugate T).symm

/-- The image of the native regular-`J` centralizer under the explicit
Ell-to-legacy circular operator readout is exactly the legacy within sector. -/
theorem nativeJCentralizer_map_eq_legacyWithin :
    nativeJCentralizer.map legacyReadoutEquiv.toLinearMap =
      legacyWithinSectorOperatorSubspace := by
  ext X
  constructor
  · rintro ⟨T, hT, rfl⟩
    exact (legacyWithin_iff_nativeJCentralizer T).2 hT
  · intro hX
    refine ⟨legacyReadoutEquiv.symm X, ?_, ?_⟩
    · exact (legacyWithin_iff_nativeJCentralizer (legacyReadoutEquiv.symm X)).1 (by
        simpa [legacyReadout, legacyReadoutEquiv] using hX)
    · simp [legacyReadoutEquiv]

/-- The image of the native double-commutator range under circular readout is
exactly the legacy cross sector. -/
theorem nativeJDoubleCommRange_map_eq_legacyCross :
    nativeJDoubleCommRange.map legacyReadoutEquiv.toLinearMap =
      legacyCrossSectorOperatorSubspace := by
  ext X
  constructor
  · rintro ⟨T, hT, rfl⟩
    exact (legacyCross_iff_nativeJDoubleCommRange T).2 hT
  · intro hX
    refine ⟨legacyReadoutEquiv.symm X, ?_, ?_⟩
    · exact (legacyCross_iff_nativeJDoubleCommRange (legacyReadoutEquiv.symm X)).1 (by
        simpa [legacyReadout, legacyReadoutEquiv] using hX)
    · simp [legacyReadoutEquiv]

/-- The sector correspondences are actual linear equivalences, rather than
only pointwise membership criteria. -/
def legacyWithin_nativeJCentralizer_equiv :
    nativeJCentralizer ≃ₗ[ℝ] legacyWithinSectorOperatorSubspace :=
  (legacyReadoutEquiv.submoduleMap nativeJCentralizer).trans
    (LinearEquiv.ofEq _ _ nativeJCentralizer_map_eq_legacyWithin)

def legacyCross_nativeJDoubleCommRange_equiv :
    nativeJDoubleCommRange ≃ₗ[ℝ] legacyCrossSectorOperatorSubspace :=
  (legacyReadoutEquiv.submoduleMap nativeJDoubleCommRange).trans
    (LinearEquiv.ofEq _ _ nativeJDoubleCommRange_map_eq_legacyCross)

/-- The centralizer submodule is exactly the kernel of the native
double-commutator map. -/
theorem nativeJCentralizer_eq_doubleComm_ker :
    nativeJCentralizer = LinearMap.ker nativeRegularJDoubleCommMap := by
  ext T
  change nativeJ * T = T * nativeJ ↔ nativeRegularJDoubleCommMap T = 0
  rw [nativeRegularJDoubleCommMap_apply, nativeJ]
  exact (nativeRegularJ_doubleComm_eq_zero_iff_commutes T).symm

/-- The actual native signed eigenmode spans, rather than only abstract
centralizer/range subspaces, transport to the two legacy Peirce blocks. -/
theorem nativeSignedModeSpans_map_eq_legacySectors :
    nativeRegularJZeroModeSpan.map legacyReadoutEquiv.toLinearMap =
        legacyWithinSectorOperatorSubspace ∧
      nativeRegularJFourModeSpan.map legacyReadoutEquiv.toLinearMap =
        legacyCrossSectorOperatorSubspace := by
  constructor
  · rw [nativeRegularJ_modes_are_exact_kernel_and_range.1,
      ← nativeJCentralizer_eq_doubleComm_ker]
    exact nativeJCentralizer_map_eq_legacyWithin
  · rw [nativeRegularJ_modes_are_exact_kernel_and_range.2]
    exact nativeJDoubleCommRange_map_eq_legacyCross

/-- The transported zero/four eigenmode spans are linearly equivalent to the
legacy within/cross blocks through the explicit circular readout. -/
def legacyWithin_nativeZeroMode_equiv :
    nativeRegularJZeroModeSpan ≃ₗ[ℝ] legacyWithinSectorOperatorSubspace :=
  (legacyReadoutEquiv.submoduleMap nativeRegularJZeroModeSpan).trans
    (LinearEquiv.ofEq _ _ nativeSignedModeSpans_map_eq_legacySectors.1)

def legacyCross_nativeFourMode_equiv :
    nativeRegularJFourModeSpan ≃ₗ[ℝ] legacyCrossSectorOperatorSubspace :=
  (legacyReadoutEquiv.submoduleMap nativeRegularJFourModeSpan).trans
    (LinearEquiv.ofEq _ _ nativeSignedModeSpans_map_eq_legacySectors.2)

/-- Both legacy operator sectors have the exact dimensions of their native
counterparts after soldering through the explicit circular-basis map. -/
theorem soldered_operator_sector_dimensions :
    Module.finrank ℝ legacyWithinSectorOperatorSubspace = 32 ∧
      Module.finrank ℝ legacyCrossSectorOperatorSubspace = 32 := by
  constructor
  · rw [← legacyWithin_nativeJCentralizer_equiv.finrank_eq,
    nativeJCentralizer_eq_doubleComm_ker]
    exact nativeRegularJ_doubleComm_rank_kernel_dimensions.2
  · rw [← legacyCross_nativeJDoubleCommRange_equiv.finrank_eq]
    exact nativeRegularJ_doubleComm_rank_kernel_dimensions.1

/-- Multiplication respects the native within/cross decomposition: the
centralizer is a subalgebra, mixed products are anti-invariant, and the
product of two anti-invariants returns to the centralizer.  This is the
operator-sector multiplication law behind the legacy block multiplication
table. -/
theorem native_operator_sector_product_rules (X Y : NativeEnd) :
    (X ∈ nativeJCentralizer → Y ∈ nativeJCentralizer → X * Y ∈ nativeJCentralizer) ∧
    (X ∈ nativeJCentralizer → Y ∈ nativeJDoubleCommRange →
      X * Y ∈ nativeJDoubleCommRange) ∧
    (X ∈ nativeJDoubleCommRange → Y ∈ nativeJCentralizer →
      X * Y ∈ nativeJDoubleCommRange) ∧
    (X ∈ nativeJDoubleCommRange → Y ∈ nativeJDoubleCommRange →
      X * Y ∈ nativeJCentralizer) := by
  have hJ : nativeJ * nativeJ = 1 :=
    InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates.regularJ_uPlus_uMinus_sq
  have hanti (T : NativeEnd) (hT : T ∈ nativeJDoubleCommRange) :
      nativeJ * T * nativeJ = -T :=
    (nativeRegularJ_doubleComm_mem_range_iff_anti_conjugate T).mp hT
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hX hY
    change nativeJ * X = X * nativeJ at hX
    change nativeJ * Y = Y * nativeJ at hY
    change nativeJ * (X * Y) = (X * Y) * nativeJ
    calc
      nativeJ * (X * Y) = (nativeJ * X) * Y := by simp [mul_assoc]
      _ = (X * nativeJ) * Y := by rw [hX]
      _ = X * (nativeJ * Y) := by simp [mul_assoc]
      _ = X * (Y * nativeJ) := by rw [hY]
      _ = (X * Y) * nativeJ := by simp [mul_assoc]
  · intro hX hY
    change nativeJ * X = X * nativeJ at hX
    have hy := hanti Y hY
    apply (nativeRegularJ_doubleComm_mem_range_iff_anti_conjugate (X * Y)).mpr
    calc
      nativeJ * (X * Y) * nativeJ = (nativeJ * X) * (Y * nativeJ) := by
        noncomm_ring
      _ = (X * nativeJ) * (Y * nativeJ) := by rw [hX]
      _ = X * (nativeJ * Y * nativeJ) := by noncomm_ring
      _ = -(X * Y) := by rw [hy]; noncomm_ring
  · intro hX hY
    change nativeJ * Y = Y * nativeJ at hY
    have hx := hanti X hX
    apply (nativeRegularJ_doubleComm_mem_range_iff_anti_conjugate (X * Y)).mpr
    calc
      nativeJ * (X * Y) * nativeJ = (nativeJ * X) * (Y * nativeJ) := by
        noncomm_ring
      _ = (nativeJ * X) * (nativeJ * Y) := by rw [← hY]
      _ = (nativeJ * X * nativeJ) * Y := by noncomm_ring
      _ = -(X * Y) := by rw [hx]; noncomm_ring
  · intro hX hY
    have hx := hanti X hX
    have hy := hanti Y hY
    have hXY : nativeJ * (X * Y) * nativeJ = X * Y := by
      calc
        nativeJ * (X * Y) * nativeJ =
            (nativeJ * X * nativeJ) * (nativeJ * Y * nativeJ) := by
              calc
                nativeJ * (X * Y) * nativeJ =
                    nativeJ * X * 1 * Y * nativeJ := by simp [mul_assoc]
                _ = nativeJ * X * (nativeJ * nativeJ) * Y * nativeJ := by rw [hJ]
                _ = (nativeJ * X * nativeJ) * (nativeJ * Y * nativeJ) := by
                      simp [mul_assoc]
        _ = (-X) * (-Y) := by rw [hx, hy]
        _ = X * Y := by noncomm_ring
    change nativeJ * (X * Y) = (X * Y) * nativeJ
    calc
      nativeJ * (X * Y) = nativeJ * (X * Y) * (nativeJ * nativeJ) := by rw [hJ, mul_one]
      _ = (nativeJ * (X * Y) * nativeJ) * nativeJ := by noncomm_ring
      _ = (X * Y) * nativeJ := by rw [hXY]

/-- The native within and cross sectors span the entire endomorphism algebra.
This transports the legacy basis decomposition back through the circular
readout equivalence. -/
theorem nativeJCentralizer_sup_doubleCommRange_eq_top :
    nativeJCentralizer ⊔ nativeJDoubleCommRange = ⊤ := by
  apply le_antisymm le_top
  intro T _
  have hlegacy : legacyReadoutEquiv T ∈
      legacyWithinSectorOperatorSubspace ⊔ legacyCrossSectorOperatorSubspace := by
    rw [legacyWithin_sup_crossSector_eq_top]
    exact Submodule.mem_top
  rcases Submodule.mem_sup.mp hlegacy with ⟨X, hX, Y, hY, hsum⟩
  have hXnative : legacyReadoutEquiv.symm X ∈ nativeJCentralizer := by
    apply (legacyWithin_iff_nativeJCentralizer _).1
    simpa [legacyReadout, legacyReadoutEquiv] using hX
  have hYnative : legacyReadoutEquiv.symm Y ∈ nativeJDoubleCommRange := by
    apply (legacyCross_iff_nativeJDoubleCommRange _).1
    simpa [legacyReadout, legacyReadoutEquiv] using hY
  apply Submodule.mem_sup.mpr
  refine ⟨legacyReadoutEquiv.symm X, hXnative,
    legacyReadoutEquiv.symm Y, hYnative, ?_⟩
  apply legacyReadoutEquiv.injective
  simpa using hsum

/-- The native within and cross sectors have zero intersection, so together
with the spanning theorem they form a direct-sum decomposition. -/
theorem nativeJCentralizer_inf_doubleCommRange_eq_bot :
    nativeJCentralizer ⊓ nativeJDoubleCommRange = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro T hT
  have hwithin := (legacyWithin_iff_nativeJCentralizer T).2 hT.1
  have hcross := (legacyCross_iff_nativeJDoubleCommRange T).2 hT.2
  have hmem : legacyReadout T ∈
      legacyWithinSectorOperatorSubspace ⊓ legacyCrossSectorOperatorSubspace :=
    ⟨hwithin, hcross⟩
  rw [legacyWithin_inf_crossSector_eq_bot] at hmem
  exact (legacyReadout_zero_iff T).mp (by simpa using hmem)

end InfoGeometry.Lie.SplitOctonionEllLegacyOperatorSoldering
