import InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction
import InfoGeometry.Lie.CanonicalZornG2CartanSouriauCharacterBridge
import InfoGeometry.Lie.CanonicalZornG2CartanWeylEquivariant

/-!
# The coordinate-root finite Souriau datum

This file supplies the concrete finite datum obtained from the signed
coordinate-root carrier.  It is only an algebraic finite-state construction:
no continuum, positivity, or modular-flow statement is introduced here.
-/

namespace InfoGeometry.Lie.CanonicalZornG2CoordinateRootSouriauBridge

open InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction
open InfoGeometry.Algebra.Zorn.G2Roots
open InfoGeometry.Algebra.Zorn.G2PositiveRootCoordinateBridge
open InfoGeometry.Lie.CanonicalZornG2CartanSouriauCharacterBridge
open InfoGeometry.Lie
open InfoGeometry.Lie.CanonicalZornG2CartanWeylEquivariant

def coordinateRootMomentMap (x : G2CoordinateRoot) : Fin 2 → ℝ := fun i =>
  if i = 0 then (x.1.1 : ℝ) else (x.1.2 : ℝ)

noncomputable def g2CoordinateRootSouriauDatum :
    CartanSouriauDatum G2CoordinateRoot where
  momentMap := coordinateRootMomentMap
  beta := fun _ => 0

@[simp] theorem g2CoordinateRootSouriauDatum_momentMap
    (x : G2CoordinateRoot) (i : Fin 2) :
    (g2CoordinateRootSouriauDatum : CartanSouriauDatum G2CoordinateRoot).momentMap x i =
      coordinateRootMomentMap x i := rfl

@[simp] theorem g2CoordinateRootSouriauDatum_beta (i : Fin 2) :
    (g2CoordinateRootSouriauDatum : CartanSouriauDatum G2CoordinateRoot).beta i = 0 := rfl

theorem coordinateRootMomentMap_s1 (x : G2CoordinateRoot) :
    coordinateRootMomentMap (s1Root x) =
      ![(-((x.1.1 : ℝ)) + 3 * (x.1.2 : ℝ)), (x.1.2 : ℝ)] := by
  funext i
  fin_cases i <;>
    simp [coordinateRootMomentMap, s1Root, s1]

theorem coordinateRootMomentMap_s2 (x : G2CoordinateRoot) :
    coordinateRootMomentMap (s2Root x) =
      ![(x.1.1 : ℝ), (x.1.1 : ℝ) - (x.1.2 : ℝ)] := by
  funext i
  fin_cases i <;>
    simp [coordinateRootMomentMap, s2Root, s2]

theorem coordinateRootMomentMap_not_canonicalShort_covariant :
    ¬ (∀ x : G2CoordinateRoot, ∀ i : Fin 2,
      coordinateRootMomentMap (s1Root x) i =
        canonicalShortReflectionChargeReal (coordinateRootMomentMap x) i) := by
  intro h
  have hx := h (positiveRootInFullCarrier .alpha) 1
  norm_num [coordinateRootMomentMap, s1Root, s1,
    canonicalShortReflectionChargeReal, positiveRootInFullCarrier,
    rootCoordinates] at hx

theorem coordinateRootMomentMap_not_canonicalLong_covariant :
    ¬ (∀ x : G2CoordinateRoot, ∀ i : Fin 2,
      coordinateRootMomentMap (s2Root x) i =
        canonicalLongReflectionChargeReal (coordinateRootMomentMap x) i) := by
  intro h
  have hx := h (positiveRootInFullCarrier .alpha) 1
  norm_num [coordinateRootMomentMap, s2Root, s2,
    canonicalLongReflectionChargeReal, positiveRootInFullCarrier,
    rootCoordinates] at hx

theorem coordinateRoot_pairing_s1 (beta : Fin 2 → ℝ) (x : G2CoordinateRoot) :
    (∑ i : Fin 2, beta i * coordinateRootMomentMap (s1Root x) i) =
      ∑ i : Fin 2,
        canonicalShortReflectionChargeReal beta i * coordinateRootMomentMap x i := by
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  simp [coordinateRootMomentMap, s1Root, s1,
    canonicalShortReflectionChargeReal]
  ring

theorem coordinateRoot_pairing_s2 (beta : Fin 2 → ℝ) (x : G2CoordinateRoot) :
    (∑ i : Fin 2, beta i * coordinateRootMomentMap (s2Root x) i) =
      ∑ i : Fin 2,
        canonicalLongReflectionChargeReal beta i * coordinateRootMomentMap x i := by
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  simp [coordinateRootMomentMap, s2Root, s2,
    canonicalLongReflectionChargeReal]
  ring

theorem coordinateRoot_realGibbsKernel_s1 (beta : Fin 2 → ℝ) (x : G2CoordinateRoot) :
    realGibbsKernel g2CoordinateRootSouriauDatum beta (s1Root x) =
      realGibbsKernel g2CoordinateRootSouriauDatum
        (canonicalShortReflectionChargeReal beta) x := by
  unfold realGibbsKernel realPairingEnergy
  change Real.exp (-(∑ i : Fin 2,
    beta i * coordinateRootMomentMap (s1Root x) i)) =
      Real.exp (-(∑ i : Fin 2,
        canonicalShortReflectionChargeReal beta i * coordinateRootMomentMap x i))
  rw [coordinateRoot_pairing_s1]

theorem coordinateRoot_realGibbsKernel_s2 (beta : Fin 2 → ℝ) (x : G2CoordinateRoot) :
    realGibbsKernel g2CoordinateRootSouriauDatum beta (s2Root x) =
      realGibbsKernel g2CoordinateRootSouriauDatum
        (canonicalLongReflectionChargeReal beta) x := by
  unfold realGibbsKernel realPairingEnergy
  change Real.exp (-(∑ i : Fin 2,
    beta i * coordinateRootMomentMap (s2Root x) i)) =
      Real.exp (-(∑ i : Fin 2,
        canonicalLongReflectionChargeReal beta i * coordinateRootMomentMap x i))
  rw [coordinateRoot_pairing_s2]

theorem coordinateRoot_realGibbsPartition_s1 (beta : Fin 2 → ℝ) :
    realGibbsPartition g2CoordinateRootSouriauDatum
        (canonicalShortReflectionChargeReal beta) =
      realGibbsPartition g2CoordinateRootSouriauDatum beta := by
  unfold realGibbsPartition
  have h := Equiv.sum_comp s1Root
    (realGibbsKernel g2CoordinateRootSouriauDatum beta)
  change (∑ x, realGibbsKernel g2CoordinateRootSouriauDatum beta (s1Root x)) = _ at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro x _
  exact (coordinateRoot_realGibbsKernel_s1 beta x).symm

theorem coordinateRoot_realGibbsPartition_s2 (beta : Fin 2 → ℝ) :
    realGibbsPartition g2CoordinateRootSouriauDatum
        (canonicalLongReflectionChargeReal beta) =
      realGibbsPartition g2CoordinateRootSouriauDatum beta := by
  unfold realGibbsPartition
  have h := Equiv.sum_comp s2Root
    (realGibbsKernel g2CoordinateRootSouriauDatum beta)
  change (∑ x, realGibbsKernel g2CoordinateRootSouriauDatum beta (s2Root x)) = _ at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro x _
  exact (coordinateRoot_realGibbsKernel_s2 beta x).symm

theorem coordinateRoot_realGibbsWeight_s1 (beta : Fin 2 → ℝ) (x : G2CoordinateRoot) :
    realGibbsWeight g2CoordinateRootSouriauDatum beta (s1Root x) =
      realGibbsWeight g2CoordinateRootSouriauDatum
        (canonicalShortReflectionChargeReal beta) x := by
  unfold realGibbsWeight
  rw [coordinateRoot_realGibbsKernel_s1,
    coordinateRoot_realGibbsPartition_s1]

theorem coordinateRoot_realGibbsWeight_s2 (beta : Fin 2 → ℝ) (x : G2CoordinateRoot) :
    realGibbsWeight g2CoordinateRootSouriauDatum beta (s2Root x) =
      realGibbsWeight g2CoordinateRootSouriauDatum
        (canonicalLongReflectionChargeReal beta) x := by
  unfold realGibbsWeight
  rw [coordinateRoot_realGibbsKernel_s2,
    coordinateRoot_realGibbsPartition_s2]

theorem coordinateRoot_souriauMassieu_s1 (beta : Fin 2 → ℝ) :
    souriauMassieu g2CoordinateRootSouriauDatum
        (canonicalShortReflectionChargeReal beta) =
      souriauMassieu g2CoordinateRootSouriauDatum beta := by
  letI : Nonempty G2CoordinateRoot :=
    ⟨positiveRootInFullCarrier .alpha⟩
  unfold souriauMassieu
  rw [coordinateRoot_realGibbsPartition_s1]

theorem coordinateRoot_souriauMassieu_s2 (beta : Fin 2 → ℝ) :
    souriauMassieu g2CoordinateRootSouriauDatum
        (canonicalLongReflectionChargeReal beta) =
      souriauMassieu g2CoordinateRootSouriauDatum beta := by
  letI : Nonempty G2CoordinateRoot :=
    ⟨positiveRootInFullCarrier .alpha⟩
  unfold souriauMassieu
  rw [coordinateRoot_realGibbsPartition_s2]

theorem g2CoordinateRootSouriauDatum_partition_pos
    (beta : Fin 2 → ℝ) :
    0 < realGibbsPartition g2CoordinateRootSouriauDatum beta := by
  letI : Nonempty G2CoordinateRoot :=
    ⟨positiveRootInFullCarrier .alpha⟩
  exact realGibbsPartition_pos g2CoordinateRootSouriauDatum beta

theorem g2CoordinateRootSouriauDatum_weights_normalized
    (beta : Fin 2 → ℝ) :
    (∑ x : G2CoordinateRoot,
      realGibbsWeight g2CoordinateRootSouriauDatum beta x) = 1 := by
  letI : Nonempty G2CoordinateRoot :=
    ⟨positiveRootInFullCarrier .alpha⟩
  exact realGibbsWeight_sum_eq_one g2CoordinateRootSouriauDatum beta

end InfoGeometry.Lie.CanonicalZornG2CoordinateRootSouriauBridge
