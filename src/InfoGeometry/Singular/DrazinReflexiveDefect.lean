/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Singular.SchurDrazinMoorePenrose
import InfoGeometry.Canonical.Drazin
import InfoGeometry.Physics.ZornTkkAlgebraicClosure

/-!
# Reflexive inverse defect, Drazin residue, and triple normalization

The sandwich defect `a - a*d*a` is the existing Schur/Drazin residue, not
the Kantor operator `K(x,y)z = T(x,z,y) - T(y,z,x)`. For a Drazin witness,
its vanishing is equivalent to the same candidate satisfying the index-one
equations. The symmetric associative triple has diagonal `2 • (a*d*a)`;
no division by two or new triple-system carrier is needed.
-/

namespace InfoGeometry.Singular.SchurDrazinMoorePenrose

open InfoGeometry.Canonical.Drazin
open InfoGeometry.Physics.ZornTkkAlgebraicClosure

variable {R : Type*} [Ring R] {a d : R} {k : ℕ}

/-- Drazin commutation identifies the sandwich residue with the native nilpotent part. -/
theorem residue_eq_nilpotent (h : IsDrazinInverse a d k) :
    drazinResidueBlock a d = IsDrazinInverse.nilpotent a d := by
  unfold drazinResidueBlock drazinRegularBlock IsDrazinInverse.nilpotent
    IsDrazinInverse.core
  rw [mul_assoc, ← h.comm, ← mul_assoc]

/-- The residue vanishes exactly when the same inverse satisfies the group-inverse
equations. The exponent one here is a witness, not a minimality claim. -/
theorem residue_eq_zero_iff_indexOne (h : IsDrazinInverse a d k) :
    drazinResidueBlock a d = 0 ↔ IsDrazinInverse a d 1 := by
  have hswitch : a * d * a = a * a * d := by
    rw [mul_assoc, ← h.comm, ← mul_assoc]
  constructor
  · intro hz
    have ha : a * d * a = a := by
      exact (sub_eq_zero.mp hz).symm
    refine ⟨h.comm, h.idempotent, ?_⟩
    simpa [pow_two, hswitch] using ha
  · intro hg
    have ha : a * a * d = a := by simpa [pow_two] using hg.power
    simp only [drazinResidueBlock, drazinRegularBlock, hswitch, ha, sub_self]

/-- The unnormalized symmetric triple retains twice the nilpotent defect. -/
theorem triple_add_twice_nilpotent (h : IsDrazinInverse a d k) :
    jordanTriple a d a + 2 • IsDrazinInverse.nilpotent a d = 2 • a := by
  rw [← residue_eq_nilpotent h]
  simp only [jordanTriple, drazinResidueBlock, drazinRegularBlock, two_nsmul]
  abel

end InfoGeometry.Singular.SchurDrazinMoorePenrose
