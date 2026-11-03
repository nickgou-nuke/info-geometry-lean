/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.AlbertCayleyDickson
import InfoGeometry.Canonical.CARProjectorRingEquiv

/-!
# CAR occupation idempotents inside the noncommutative cyclotomic carrier

The CAR relation constructs the occupation idempotent in the coefficient ring.
The canonical coefficient embedding into `OpCyclotomic3` preserves that
idempotent, and the defined cyclotomic conjugation fixes the embedded
coefficient subring. This records an explicit link between the CAR and
cyclotomic carriers without claiming that Galois conjugation creates the
idempotent.
-/

namespace InfoGeometry.Canonical.CyclotomicCARIdempotentBridge

open InfoGeometry.Canonical.CarrierMasterLemmas
open InfoGeometry.Canonical.CARProjectorRingEquiv

variable {A : Type*} [Ring A]

/-- The cyclotomic embedding preserves products from the noncommutative
coefficient ring. -/
theorem cyclotomic3_embed_mul (x y : A) :
    InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpCyclotomic3.embed (x * y) =
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpCyclotomic3.embed x *
        InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpCyclotomic3.embed y := by
  apply InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpCyclotomic3.ext <;>
    simp [InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpCyclotomic3.embed,
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpCyclotomic3.mul_c0,
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpCyclotomic3.mul_c1]

/-- The cyclotomic conjugation fixes every element in the embedded
coefficient carrier. -/
@[simp] theorem cyclotomic3_galoisConj_embed (x : A) :
    InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpCyclotomic3.galoisConj
        (InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpCyclotomic3.embed x) =
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpCyclotomic3.embed x := by
  apply InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpCyclotomic3.ext <;>
    simp [InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpCyclotomic3.galoisConj,
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpCyclotomic3.embed]

/-- A CAR occupation operator remains idempotent after embedding into the
third cyclotomic carrier. -/
theorem cyclotomic3_embed_CAR_occupation_idempotent
    (C : CARCarrierPair A) :
    (InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpCyclotomic3.embed
        (C.c_dag * C.c)) *
        (InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpCyclotomic3.embed
          (C.c_dag * C.c)) =
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpCyclotomic3.embed
        (C.c_dag * C.c) := by
  rw [← cyclotomic3_embed_mul, car_number_operator_idempotent]

/-- The embedded CAR occupation idempotent is fixed by the cyclotomic
conjugation because that conjugation fixes the embedded coefficient ring. -/
theorem cyclotomic3_galoisConj_CAR_occupation
    (C : CARCarrierPair A) :
    InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpCyclotomic3.galoisConj
        (InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpCyclotomic3.embed
          (C.c_dag * C.c)) =
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpCyclotomic3.embed
        (C.c_dag * C.c) := by
  exact cyclotomic3_galoisConj_embed (C.c_dag * C.c)

/-- At every finite split-Clifford stage, the isotropic head pair's occupation
operator embeds as a Galois-fixed idempotent in `OpCyclotomic3`. -/
theorem isotropic_head_occupation_cyclotomic_fixed (n : ℕ) :
    (InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpCyclotomic3.embed
      (headNullOccupation n)) *
        (InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpCyclotomic3.embed
          (headNullOccupation n)) =
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpCyclotomic3.embed
        (headNullOccupation n) ∧
    InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpCyclotomic3.galoisConj
      (InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpCyclotomic3.embed
        (headNullOccupation n)) =
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpCyclotomic3.embed
        (headNullOccupation n) := by
  have hIdem : headNullOccupation n * headNullOccupation n =
      headNullOccupation n :=
    (isotropic_head_pair_generates_occupation_idempotent n).2.2.2.2.2
  constructor
  · rw [← cyclotomic3_embed_mul, hIdem]
  · exact cyclotomic3_galoisConj_embed (headNullOccupation n)

end InfoGeometry.Canonical.CyclotomicCARIdempotentBridge
