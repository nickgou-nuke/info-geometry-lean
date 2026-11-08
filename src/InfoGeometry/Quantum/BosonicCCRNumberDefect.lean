/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.NuclearPhononRPAAlgebra

/-!
# Bosonic CCR number operators are not CAR occupation projectors by default

For a bosonic mode satisfying `[a, a†] = 1`, its number operator `n = a† a`
has exact idempotency defect `n² - n = a†² a²`.  Thus a bosonic mode has a
projector number operator only under the additional annihilation relation
`a†² a² = 0`.  This algebraic identity does not itself assert Bose–Einstein
condensation, which requires state or limiting data beyond the CCR relations.
-/

namespace InfoGeometry.Quantum.BosonicCCRNumberDefect

open InfoGeometry.Physics.NuclearPhononRPA

variable {ι : Type*} [DecidableEq ι]
variable {A : Type*} [Ring A]

/-- The canonical bosonic CCR expresses `a * a†` as `1 + a† * a`. -/
private theorem annihilation_mul_creation
    (rpa : PhononRPA ι A) (i : ι) :
    rpa.Q i * rpa.Qdag i = 1 + rpa.Qdag i * rpa.Q i := by
  have h := rpa.comm_Q_Qdag i i
  simp [InfoGeometry.Physics.NuclearPhononRPA.comm] at h
  exact (sub_eq_iff_eq_add).mp h

/-- Exact bosonic number-operator defect under the CCR. -/
theorem numberOp_idempotency_defect (rpa : PhononRPA ι A) (i : ι) :
    rpa.numberOp i * rpa.numberOp i - rpa.numberOp i =
      rpa.Qdag i * rpa.Qdag i * (rpa.Q i * rpa.Q i) := by
  dsimp [PhononRPA.numberOp]
  calc
    rpa.Qdag i * rpa.Q i * (rpa.Qdag i * rpa.Q i) -
        rpa.Qdag i * rpa.Q i =
      rpa.Qdag i * (rpa.Q i * rpa.Qdag i) * rpa.Q i -
        rpa.Qdag i * rpa.Q i := by noncomm_ring
    _ = rpa.Qdag i * (1 + rpa.Qdag i * rpa.Q i) * rpa.Q i -
        rpa.Qdag i * rpa.Q i := by
          rw [annihilation_mul_creation rpa i]
    _ = rpa.Qdag i * rpa.Qdag i * (rpa.Q i * rpa.Q i) := by
          noncomm_ring

/-- The bosonic number operator is idempotent exactly when its two-particle
raising/lowering product vanishes.  The CCR alone does not provide that extra
vanishing premise. -/
theorem numberOp_idempotent_iff (rpa : PhononRPA ι A) (i : ι) :
    rpa.numberOp i * rpa.numberOp i = rpa.numberOp i ↔
      rpa.Qdag i * rpa.Qdag i * (rpa.Q i * rpa.Q i) = 0 := by
  rw [← sub_eq_zero, numberOp_idempotency_defect]

end InfoGeometry.Quantum.BosonicCCRNumberDefect
