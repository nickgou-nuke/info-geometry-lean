/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.Cl55InfinitySourceSinkGrading
import InfoGeometry.Clifford.Cl55ChiralGrandCanonical

/-!
# Chiral charge of the native infinity source/sink words

The existing chiral charge is the difference of the centered number operators
of modes `0` and `1`.  The infinity/origin CAR endpoints occupy mode `4`, so
they are neutral under this charge.  A source or sink word acquires the charge
of its second factor.  Thus both chiral signs occur inside either number-degree
sector `+2` or `-2`.

These are commutator identities in `Cl55`.  Number degree, chiral charge, and
Clifford involution parity are separate quantities; no state or modular-flow
identification is assumed here.
-/

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Canonical.Cl55InfinityChiralCharge

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Canonical.Cl55InfinityWittBoundary
open InfoGeometry.Canonical.Cl55InfinitySourceSinkGrading
open InfoGeometry.OperatorAlgebra

/-- The charge eigenvalue of a native creation mode for `chiralCharge55`. -/
def chiralModeWeight55 (i : Fin 5) : ℤ :=
  (if i = 0 then 1 else 0) - (if i = 1 then 1 else 0)

theorem creation55_has_chiralCharge_grade (i : Fin 5) :
    HasOperatorGrade chiralCharge55 (creation55 i) (chiralModeWeight55 i) := by
  unfold HasOperatorGrade chiralCharge55 chiralPlusNumber55 chiralMinusNumber55
  calc
    (mixedGenerator55 0 0 - mixedGenerator55 1 1) * creation55 i -
        creation55 i * (mixedGenerator55 0 0 - mixedGenerator55 1 1) =
      (mixedGenerator55 0 0 * creation55 i - creation55 i * mixedGenerator55 0 0) -
        (mixedGenerator55 1 1 * creation55 i -
          creation55 i * mixedGenerator55 1 1) := by noncomm_ring
    _ = (if (0 : Fin 5) = i then creation55 0 else 0) -
        (if (1 : Fin 5) = i then creation55 1 else 0) := by
      rw [mixedGenerator55_commutator_creation,
        mixedGenerator55_commutator_creation]
    _ = (chiralModeWeight55 i : ℝ) • creation55 i := by
      by_cases h0 : i = 0
      · subst i
        norm_num [chiralModeWeight55]
      · by_cases h1 : i = 1
        · subst i
          norm_num [chiralModeWeight55]
        · simp [chiralModeWeight55, h0, h1, Ne.symm h0, Ne.symm h1]

theorem annihilation55_has_chiralCharge_grade (i : Fin 5) :
    HasOperatorGrade chiralCharge55 (annihilation55 i) (-chiralModeWeight55 i) := by
  unfold HasOperatorGrade chiralCharge55 chiralPlusNumber55 chiralMinusNumber55
  calc
    (mixedGenerator55 0 0 - mixedGenerator55 1 1) * annihilation55 i -
        annihilation55 i * (mixedGenerator55 0 0 - mixedGenerator55 1 1) =
      (mixedGenerator55 0 0 * annihilation55 i -
        annihilation55 i * mixedGenerator55 0 0) -
      (mixedGenerator55 1 1 * annihilation55 i -
        annihilation55 i * mixedGenerator55 1 1) := by noncomm_ring
    _ = (if (0 : Fin 5) = i then -(annihilation55 0) else 0) -
        (if (1 : Fin 5) = i then -(annihilation55 1) else 0) := by
      rw [mixedGenerator55_commutator_annihilation,
        mixedGenerator55_commutator_annihilation]
    _ = ((-chiralModeWeight55 i : ℤ) : ℝ) • annihilation55 i := by
      by_cases h0 : i = 0
      · subst i
        norm_num [chiralModeWeight55]
      · by_cases h1 : i = 1
        · subst i
          norm_num [chiralModeWeight55]
        · simp [chiralModeWeight55, h0, h1, Ne.symm h0, Ne.symm h1]

theorem infinityClifford55_has_chiralCharge_grade_zero :
    HasOperatorGrade chiralCharge55 infinityClifford55 0 := by
  rw [infinityClifford55_eq_creation55]
  simpa [chiralModeWeight55] using creation55_has_chiralCharge_grade 4

theorem originClifford55_has_chiralCharge_grade_zero :
    HasOperatorGrade chiralCharge55 originClifford55 0 := by
  rw [originClifford55_eq_annihilation55]
  simpa [chiralModeWeight55] using annihilation55_has_chiralCharge_grade 4

theorem chiralCharge55_commutator_infinityClifford55 :
    chiralCharge55 * infinityClifford55 -
      infinityClifford55 * chiralCharge55 = 0 := by
  simpa [HasOperatorGrade] using infinityClifford55_has_chiralCharge_grade_zero

theorem chiralCharge55_commutator_originClifford55 :
    chiralCharge55 * originClifford55 -
      originClifford55 * chiralCharge55 = 0 := by
  simpa [HasOperatorGrade] using originClifford55_has_chiralCharge_grade_zero

theorem infinityProjector55_has_chiralCharge_grade_zero :
    HasOperatorGrade chiralCharge55 infinityProjector55 0 := by
  exact grade_mul infinityClifford55_has_chiralCharge_grade_zero
    originClifford55_has_chiralCharge_grade_zero

theorem originProjector55_has_chiralCharge_grade_zero :
    HasOperatorGrade chiralCharge55 originProjector55 0 := by
  exact grade_mul originClifford55_has_chiralCharge_grade_zero
    infinityClifford55_has_chiralCharge_grade_zero

theorem infinityGrading55_has_chiralCharge_grade_zero :
    HasOperatorGrade chiralCharge55 infinityGrading55 0 := by
  exact grade_sub infinityProjector55_has_chiralCharge_grade_zero
    originProjector55_has_chiralCharge_grade_zero

theorem sourcePair55_has_chiralCharge_grade (i : Fin 5) :
    HasOperatorGrade chiralCharge55 (sourcePair55 i) (chiralModeWeight55 i) := by
  simpa only [sourcePair55, zero_add] using grade_mul
    infinityClifford55_has_chiralCharge_grade_zero
    (creation55_has_chiralCharge_grade i)

theorem sinkPair55_has_chiralCharge_grade (i : Fin 5) :
    HasOperatorGrade chiralCharge55 (sinkPair55 i) (-chiralModeWeight55 i) := by
  simpa only [sinkPair55, zero_add] using grade_mul
    originClifford55_has_chiralCharge_grade_zero
    (annihilation55_has_chiralCharge_grade i)

theorem sourcePair55_mode_zero_charge_pos_one :
    chiralCharge55 * sourcePair55 0 - sourcePair55 0 * chiralCharge55 =
      sourcePair55 0 := by
  simpa [HasOperatorGrade, chiralModeWeight55] using
    sourcePair55_has_chiralCharge_grade 0

theorem sourcePair55_mode_one_charge_neg_one :
    chiralCharge55 * sourcePair55 1 - sourcePair55 1 * chiralCharge55 =
      -(sourcePair55 1) := by
  simpa [HasOperatorGrade, chiralModeWeight55] using
    sourcePair55_has_chiralCharge_grade 1

theorem sinkPair55_mode_zero_charge_neg_one :
    chiralCharge55 * sinkPair55 0 - sinkPair55 0 * chiralCharge55 =
      -(sinkPair55 0) := by
  simpa [HasOperatorGrade, chiralModeWeight55] using
    sinkPair55_has_chiralCharge_grade 0

theorem sinkPair55_mode_one_charge_pos_one :
    chiralCharge55 * sinkPair55 1 - sinkPair55 1 * chiralCharge55 =
      sinkPair55 1 := by
  simpa [HasOperatorGrade, chiralModeWeight55] using
    sinkPair55_has_chiralCharge_grade 1

end InfoGeometry.Canonical.Cl55InfinityChiralCharge
