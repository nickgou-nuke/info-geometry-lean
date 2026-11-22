/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.KreinProjectorLattice
import InfoGeometry.Krein.Representation
import InfoGeometry.Krein.PositiveSectorMetric

/-!
# Positive Sector–Projector Equivalence Bridge

Proves the missing equivalence between the `Cl(1,1)` positive projector in
`KreinProjectorLattice` / `Krein.Representation` and the positive fundamental
subspace `KreinSpace.posSubspace` used by `PositiveSectorMetric`:

1. For any real `KreinSpace H`,
   `x ∈ KreinSpace.posSubspace H ↔ KreinSpace.P_plus x = x`
   and symmetrically
   `x ∈ KreinSpace.negSubspace H ↔ KreinSpace.P_minus x = x`.
2. On the doubled real Krein carrier `DoubledSpace E` with representation `cl11Rep`,
   `x ∈ KreinSpace.posSubspace (DoubledSpace E) ↔ cl11Rep (KreinSector.toAlg .plus) x = x`.
3. Positive-sector strict positivity of `kreinInner` and `sectorMetric` is read back
   as a theorem directly from the `Cl(1,1)` projector fixed-point characterization.
-/

noncomputable section

namespace InfoGeometry.Krein.PositiveSectorProjectorBridge

open InfoGeometry.Krein
open InfoGeometry.Krein.PositiveSectorMetric
open InfoGeometry.Canonical.KreinProjectorLattice

section GeneralKreinSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [KreinSpace H]

/-- A vector belongs to `KreinSpace.posSubspace H` iff it is fixed by `P_plus`. -/
theorem mem_posSubspace_iff_P_plus_eq (x : H) :
    x ∈ KreinSpace.posSubspace H ↔ KreinSpace.P_plus (H := H) x = x := by
  rw [KreinSpace.mem_posSubspace_iff]
  have hadd : KreinSpace.P_plus (H := H) x + KreinSpace.P_minus (H := H) x = x :=
    KreinSpace.P_plus_add_P_minus_apply x
  have hsub : KreinSpace.P_plus (H := H) x - KreinSpace.P_minus (H := H) x =
      (KreinSpace.J : H ≃ₗᵢ[ℝ] H) x := by
    have h := congrArg (fun T : H →L[ℝ] H => T x) (KreinSpace.P_plus_sub_P_minus (H := H))
    simpa [KreinSpace.jCLM_apply] using h
  constructor
  · intro hJ
    have h2 : (2 : ℝ) • KreinSpace.P_plus (H := H) x = (2 : ℝ) • x := by
      calc
        (2 : ℝ) • KreinSpace.P_plus (H := H) x
            = (KreinSpace.P_plus (H := H) x + KreinSpace.P_minus (H := H) x) +
                (KreinSpace.P_plus (H := H) x - KreinSpace.P_minus (H := H) x) := by
              rw [two_smul]
              abel
        _ = x + (KreinSpace.J : H ≃ₗᵢ[ℝ] H) x := by rw [hadd, hsub]
        _ = x + x := by rw [hJ]
        _ = (2 : ℝ) • x := (two_smul ℝ x).symm
    exact smul_right_injective H (by norm_num : (2 : ℝ) ≠ 0) h2
  · intro hP
    have hPm : KreinSpace.P_minus (H := H) x = 0 := by
      have : x + KreinSpace.P_minus (H := H) x = x + 0 := by
        simpa [hP] using hadd
      exact add_left_cancel this
    rw [← hsub, hP, hPm, sub_zero]

/-- A vector belongs to `KreinSpace.negSubspace H` iff it is fixed by `P_minus`. -/
theorem mem_negSubspace_iff_P_minus_eq (x : H) :
    x ∈ KreinSpace.negSubspace H ↔ KreinSpace.P_minus (H := H) x = x := by
  rw [KreinSpace.mem_negSubspace_iff]
  have hadd : KreinSpace.P_plus (H := H) x + KreinSpace.P_minus (H := H) x = x :=
    KreinSpace.P_plus_add_P_minus_apply x
  have hsub : KreinSpace.P_plus (H := H) x - KreinSpace.P_minus (H := H) x =
      (KreinSpace.J : H ≃ₗᵢ[ℝ] H) x := by
    have h := congrArg (fun T : H →L[ℝ] H => T x) (KreinSpace.P_plus_sub_P_minus (H := H))
    simpa [KreinSpace.jCLM_apply] using h
  constructor
  · intro hJ
    have h2 : (2 : ℝ) • KreinSpace.P_minus (H := H) x = (2 : ℝ) • x := by
      calc
        (2 : ℝ) • KreinSpace.P_minus (H := H) x
            = (KreinSpace.P_plus (H := H) x + KreinSpace.P_minus (H := H) x) -
                (KreinSpace.P_plus (H := H) x - KreinSpace.P_minus (H := H) x) := by
              rw [two_smul]
              abel
        _ = x - (KreinSpace.J : H ≃ₗᵢ[ℝ] H) x := by rw [hadd, hsub]
        _ = x - (-x) := by rw [hJ]
        _ = (2 : ℝ) • x := by rw [sub_neg_eq_add, two_smul]
    exact smul_right_injective H (by norm_num : (2 : ℝ) ≠ 0) h2
  · intro hPm
    have hPp : KreinSpace.P_plus (H := H) x = 0 := by
      have : KreinSpace.P_plus (H := H) x + x = 0 + x := by
        simpa [hPm] using hadd
      exact add_right_cancel this
    rw [← hsub, hPp, hPm, zero_sub]

end GeneralKreinSpace

section DoubledSpaceCl11

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Equivalence between `posSubspace (DoubledSpace E)` and the fixed-point space of the
`Cl(1,1)` positive lattice projector `cl11Rep (KreinSector.toAlg .plus)`. -/
theorem mem_posSubspace_iff_cl11Rep_plus_eq (x : DoubledSpace E) :
    x ∈ KreinSpace.posSubspace (DoubledSpace E) ↔
      cl11Rep (E := E) (KreinSector.toAlg KreinSector.plus) x = x := by
  rw [cl11Rep_kreinSectorPlus_eq_P_plus (E := E)]
  exact mem_posSubspace_iff_P_plus_eq x

/-- Any nonzero fixed point of the `Cl(1,1)` positive projector has strictly positive
Krein inner product. -/
theorem kreinInner_pos_of_cl11Rep_plus_fixed {x : DoubledSpace E}
    (hx : cl11Rep (E := E) (KreinSector.toAlg KreinSector.plus) x = x)
    (hx0 : x ≠ 0) :
    0 < KreinSpace.kreinInner x x :=
  KreinSpace.kreinInner_pos_on_posSubspace
    ((mem_posSubspace_iff_cl11Rep_plus_eq x).mpr hx) hx0

/-- On nonzero fixed points of the `Cl(1,1)` positive projector, `sectorMetric` is
strictly positive. -/
theorem sectorMetric_self_pos_of_cl11Rep_plus_fixed {x v : DoubledSpace E}
    (hx : cl11Rep (E := E) (KreinSector.toAlg KreinSector.plus) x = x) (hx0 : x ≠ 0)
    (hv : cl11Rep (E := E) (KreinSector.toAlg KreinSector.plus) v = v) (hv0 : v ≠ 0) :
    0 < sectorMetric x v v :=
  sectorMetric_self_pos
    ((mem_posSubspace_iff_cl11Rep_plus_eq x).mpr hx) hx0
    ((mem_posSubspace_iff_cl11Rep_plus_eq v).mpr hv) hv0

end DoubledSpaceCl11

end InfoGeometry.Krein.PositiveSectorProjectorBridge
