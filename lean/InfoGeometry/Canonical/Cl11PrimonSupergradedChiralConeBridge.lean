import InfoGeometry.Canonical.Cl11BitWordCuntzCantorBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# `Cl(1,1)` colimit CAR readout and the chiral-cone projectors

The source is the native algebraic tensor-tower colimit and the target is the
chosen compatible Cuntz representation.  This owner packages the existing
creation/annihilation readout into the local Witt/CAR cone.  It does not claim
an equivalence with a Fock space, nor does it construct the independent
bosonic CCR sector.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl11PrimonSupergradedChiralConeBridge

open InfoGeometry.Canonical.Cl11BitWordCuntzCantorBridge
open InfoGeometry.Canonical.Cl11CuntzCantorChiralFramework
open InfoGeometry.Canonical.GNSCARColimit

variable {Op : Type} [Ring Op] [StarRing Op]
variable (R : CompatibleCuntzRepresentation (Op := Op))

def creationReadout (k : ℕ) : Op :=
  CompatibleCuntzRepresentation.representation R (limit_u k)

def annihilationReadout (k : ℕ) : Op :=
  CompatibleCuntzRepresentation.representation R (limit_v k)

def plusSheetProjector (k : ℕ) : Op :=
  creationReadout R k * annihilationReadout R k

def minusSheetProjector (k : ℕ) : Op :=
  annihilationReadout R k * creationReadout R k

theorem creationReadout_sq_zero (k : ℕ) :
    creationReadout R k * creationReadout R k = 0 := by
  exact representation_limit_creation_sq_zero R k

theorem annihilationReadout_sq_zero (k : ℕ) :
    annihilationReadout R k * annihilationReadout R k = 0 := by
  exact representation_limit_annihilation_sq_zero R k

theorem readout_car (k : ℕ) :
    creationReadout R k * annihilationReadout R k +
        annihilationReadout R k * creationReadout R k = 1 := by
  exact representation_limit_car_anticommutator R k

theorem plusSheetProjector_idempotent (k : ℕ) :
    plusSheetProjector R k * plusSheetProjector R k = plusSheetProjector R k := by
  unfold plusSheetProjector
  have hcar := readout_car R k
  have hc := creationReadout_sq_zero R k
  have ha := annihilationReadout_sq_zero R k
  have hba : annihilationReadout R k * creationReadout R k =
      1 - creationReadout R k * annihilationReadout R k := by
    calc
      annihilationReadout R k * creationReadout R k =
          (creationReadout R k * annihilationReadout R k +
            annihilationReadout R k * creationReadout R k) -
              creationReadout R k * annihilationReadout R k := by noncomm_ring
      _ = 1 - creationReadout R k * annihilationReadout R k := by rw [hcar]
  calc
    creationReadout R k * annihilationReadout R k *
          (creationReadout R k * annihilationReadout R k) =
        creationReadout R k *
          (annihilationReadout R k * creationReadout R k) *
            annihilationReadout R k := by noncomm_ring
    _ = creationReadout R k *
          (1 - creationReadout R k * annihilationReadout R k) *
            annihilationReadout R k := by rw [← hba]
    _ = creationReadout R k * annihilationReadout R k := by
      calc
        creationReadout R k *
            (1 - creationReadout R k * annihilationReadout R k) *
              annihilationReadout R k =
          (creationReadout R k -
            creationReadout R k *
              (creationReadout R k * annihilationReadout R k)) *
                annihilationReadout R k := by
          rw [mul_sub, mul_one]
        _ = creationReadout R k * annihilationReadout R k := by
          rw [sub_mul]
          have hzero : creationReadout R k *
              (creationReadout R k * annihilationReadout R k) *
                annihilationReadout R k = 0 := by
            calc
              creationReadout R k *
                  (creationReadout R k * annihilationReadout R k) *
                    annihilationReadout R k =
                (creationReadout R k * creationReadout R k) *
                  (annihilationReadout R k * annihilationReadout R k) := by
                noncomm_ring
              _ = 0 := by rw [hc, zero_mul]
          rw [hzero, sub_zero]

theorem minusSheetProjector_idempotent (k : ℕ) :
    minusSheetProjector R k * minusSheetProjector R k = minusSheetProjector R k := by
  unfold minusSheetProjector
  have hcar := readout_car R k
  have hc := creationReadout_sq_zero R k
  have ha := annihilationReadout_sq_zero R k
  have hab : creationReadout R k * annihilationReadout R k =
      1 - annihilationReadout R k * creationReadout R k := by
    calc
      creationReadout R k * annihilationReadout R k =
          (creationReadout R k * annihilationReadout R k +
            annihilationReadout R k * creationReadout R k) -
              annihilationReadout R k * creationReadout R k := by noncomm_ring
      _ = 1 - annihilationReadout R k * creationReadout R k := by rw [hcar]
  calc
    annihilationReadout R k * creationReadout R k *
          (annihilationReadout R k * creationReadout R k) =
        annihilationReadout R k *
          (creationReadout R k * annihilationReadout R k) *
            creationReadout R k := by noncomm_ring
    _ = annihilationReadout R k *
          (1 - annihilationReadout R k * creationReadout R k) *
            creationReadout R k := by
      rw [← hab]
    _ = annihilationReadout R k * creationReadout R k := by
      calc
        annihilationReadout R k *
            (1 - annihilationReadout R k * creationReadout R k) *
              creationReadout R k =
          (annihilationReadout R k -
            annihilationReadout R k *
              (annihilationReadout R k * creationReadout R k)) *
                creationReadout R k := by
          rw [mul_sub, mul_one]
        _ = annihilationReadout R k * creationReadout R k := by
          rw [sub_mul]
          have hzero : annihilationReadout R k *
              (annihilationReadout R k * creationReadout R k) *
                creationReadout R k = 0 := by
            calc
              annihilationReadout R k *
                  (annihilationReadout R k * creationReadout R k) *
                    creationReadout R k =
                (annihilationReadout R k * annihilationReadout R k) *
                  (creationReadout R k * creationReadout R k) := by
                noncomm_ring
              _ = 0 := by rw [ha, zero_mul]
          rw [hzero, sub_zero]

theorem sheetProjectors_resolve (k : ℕ) :
    plusSheetProjector R k + minusSheetProjector R k = 1 :=
  readout_car R k

theorem chiralConeCARPacket (k : ℕ) :
    creationReadout R k * creationReadout R k = 0 ∧
    annihilationReadout R k * annihilationReadout R k = 0 ∧
    creationReadout R k * annihilationReadout R k +
        annihilationReadout R k * creationReadout R k = 1 ∧
    plusSheetProjector R k * plusSheetProjector R k = plusSheetProjector R k ∧
    minusSheetProjector R k * minusSheetProjector R k = minusSheetProjector R k ∧
    plusSheetProjector R k + minusSheetProjector R k = 1 := by
  exact ⟨creationReadout_sq_zero R k,
    annihilationReadout_sq_zero R k,
    readout_car R k,
    plusSheetProjector_idempotent R k,
    minusSheetProjector_idempotent R k,
    sheetProjectors_resolve R k⟩

end InfoGeometry.Canonical.Cl11PrimonSupergradedChiralConeBridge
