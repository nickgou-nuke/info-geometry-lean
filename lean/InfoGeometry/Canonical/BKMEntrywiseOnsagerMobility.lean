/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Tactic
import InfoGeometry.InformationGeometry.BKMMetricModularBridge

/-!
# Entrywise finite BKM Onsager mobility

This owner records the spectral-basis logarithmic-mean multiplier.  It is a
finite matrix construction distinct from the operator-transport mobility in
`BKMOnsagerMobilityBridge`; no equality between those carriers is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.EntrywiseBKMOnsagerMobility

open Matrix
open InfoGeometry.InformationGeometry.BKM

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev EntrywiseMat (ι : Type*) := Matrix ι ι ℂ

/-- The logarithmic-mean multiplier in a fixed spectral matrix basis. -/
def bkmOnsager (energies : ι → ℝ) :
    EntrywiseMat ι →ₗ[ℂ] EntrywiseMat ι where
  toFun X := fun i j =>
    (bkmWeightScalar (energies i) (energies j) : ℂ) * X i j
  map_add' X Y := by
    ext i j
    change
      (bkmWeightScalar (energies i) (energies j) : ℂ) * (X i j + Y i j) =
        (bkmWeightScalar (energies i) (energies j) : ℂ) * X i j +
          (bkmWeightScalar (energies i) (energies j) : ℂ) * Y i j
    rw [mul_add]
  map_smul' c X := by
    ext i j
    change
      (bkmWeightScalar (energies i) (energies j) : ℂ) * (c * X i j) =
        c * ((bkmWeightScalar (energies i) (energies j) : ℂ) * X i j)
    ring

@[simp] theorem bkmOnsager_apply (energies : ι → ℝ)
    (X : EntrywiseMat ι) (i j : ι) :
    bkmOnsager energies X i j =
      (bkmWeightScalar (energies i) (energies j) : ℂ) * X i j := rfl

/-- The trace pairing of the entrywise mobility is the native finite BKM
inner product. -/
theorem trace_star_bkmOnsager (energies : ι → ℝ)
    (X Y : EntrywiseMat ι) :
    trace (star X * bkmOnsager energies Y) =
      bkmInnerProduct energies X Y := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.star_apply, bkmOnsager_apply, bkmInnerProduct]
  simp only [starRingEnd_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [bkmWeightScalar_symm]
  ring

/-- Positivity of the entrywise mobility follows from positivity of the BKM
inner product. -/
theorem bkmOnsager_positive (energies : ι → ℝ) (X : EntrywiseMat ι) :
    0 ≤ (trace (star X * bkmOnsager energies X)).re := by
  rw [trace_star_bkmOnsager]
  exact bkmInnerProduct_self_nonneg energies X

end InfoGeometry.Canonical.EntrywiseBKMOnsagerMobility
