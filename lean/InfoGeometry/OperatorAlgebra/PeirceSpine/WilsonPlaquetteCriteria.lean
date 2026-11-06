/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.WilsonPlaquette
import InfoGeometry.OperatorAlgebra.PeirceDefectBridge

/-!
# Exact vanishing and quadratic truncation criteria for a Peirce plaquette

The ordered group-commutator word and its quartic expansion are owned by
`WilsonPlaquette`. This file characterizes when that word is the identity
and when its expansion equals `1 + Σ` exactly. The proofs separate opposite
Peirce corners, so they require no characteristic or division hypothesis.

All results concern the existing associative-ring word. No braiding,
balanced category, conformal net, or Connes fusion is constructed here.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B] {P : B} (hP : P * P = P)

include hP

/-- The multiplicative plaquette is trivial exactly when the two corner
directions commute. The reverse gate order cancels its unit factors. -/
theorem wilsonPlaquette_eq_one_iff_genSig_eq_zero (A C : B) :
    wilsonPlaquette P A C = 1 ↔ genSig P A C = 0 := by
  constructor
  · intro h
    have hread :
        (wilsonPlaquette P A C - 1) * (1 + coneMinus P C) *
          (1 + conePlus P A) = genSig P A C := by
      unfold wilsonPlaquette
      peirce_nf hP
    rw [h, sub_self, zero_mul, zero_mul] at hread
    exact hread.symm
  · intro h
    have hfactor : wilsonPlaquette P A C - 1 =
        genSig P A C * (1 - conePlus P A) * (1 - coneMinus P C) := by
      unfold wilsonPlaquette
      peirce_nf hP
    rw [h, zero_mul, zero_mul] at hfactor
    exact sub_eq_zero.mp hfactor

/-- Trivial plaquette and zero Jordan interaction are equivalent for opposite
Peirce corners, by the existing interaction/commutator criterion. -/
theorem wilsonPlaquette_eq_one_iff_genV_eq_zero (A C : B) :
    wilsonPlaquette P A C = 1 ↔ genV P A C = 0 :=
  (wilsonPlaquette_eq_one_iff_genSig_eq_zero hP A C).trans
    (tetraktys_interaction_iff_chiral_obstruction hP A C).symm

/-- The plaquette is the identity exactly when both ordered mixed products
vanish. Nonzero individual corner directions alone do not force monodromy. -/
theorem wilsonPlaquette_eq_one_iff_qgt_eq_zero (A C : B) :
    wilsonPlaquette P A C = 1 ↔
      qgtPlus P A C = 0 ∧ qgtMinus P A C = 0 :=
  (wilsonPlaquette_eq_one_iff_genV_eq_zero hP A C).trans
    (InfoGeometry.OperatorAlgebra.PeirceDefectBridge.genV_eq_zero_iff_qgt_zero
      P A C hP)

/-- The quadratic expression `1 + Σ` is exact precisely when the odd cubic
term vanishes. That condition also forces the upper quartic term to vanish. -/
theorem wilsonPlaquette_eq_one_add_genSig_iff (A C : B) :
    wilsonPlaquette P A C = 1 + genSig P A C ↔
      genV P A C * genJ P A C = 0 := by
  have hW := (wilsonPlaquette_ordered_expansions hP A C).1
  constructor
  · intro h
    have hodd :
        oddGrade P (wilsonPlaquette P A C - (1 + genSig P A C)) =
          -(genV P A C * genJ P A C) := by
      rw [hW]
      simp only [qgtPlus]
      peirce_nf hP
    rw [h, sub_self] at hodd
    have hz : -(genV P A C * genJ P A C) = 0 := by
      simpa only [oddGrade, mul_zero, zero_mul, add_zero] using hodd.symm
    exact neg_eq_zero.mp hz
  · intro h
    have hquartic : qgtPlus P A C * qgtPlus P A C = 0 := by
      calc
        qgtPlus P A C * qgtPlus P A C =
            P * (genV P A C * genJ P A C) * coneMinus P C := by
          simp only [qgtPlus]
          peirce_nf hP
        _ = 0 := by rw [h, mul_zero, zero_mul]
    rw [hW, h, hquartic, sub_zero, add_zero]

/-- Exact quadratic truncation is equivalent to vanishing of both directed
cubic round trips; neither direction can cancel the other across the cut. -/
theorem wilsonPlaquette_eq_one_add_genSig_iff_cubic_round_trips (A C : B) :
    wilsonPlaquette P A C = 1 + genSig P A C ↔
      conePlus P A * coneMinus P C * conePlus P A = 0 ∧
      coneMinus P C * conePlus P A * coneMinus P C = 0 := by
  rw [wilsonPlaquette_eq_one_add_genSig_iff hP A C]
  constructor
  · intro h
    have hplus : P * (genV P A C * genJ P A C) =
        conePlus P A * coneMinus P C * conePlus P A := by
      peirce_nf hP
    have hminus : (1 - P) * (genV P A C * genJ P A C) =
        -(coneMinus P C * conePlus P A * coneMinus P C) := by
      peirce_nf hP
    rw [h, mul_zero] at hplus hminus
    exact ⟨hplus.symm, neg_eq_zero.mp hminus.symm⟩
  · rintro ⟨hplus, hminus⟩
    have hread : genV P A C * genJ P A C =
        conePlus P A * coneMinus P C * conePlus P A -
          coneMinus P C * conePlus P A * coneMinus P C := by
      peirce_nf hP
    rw [hread, hplus, hminus, sub_self]

end InfoGeometry.OperatorAlgebra.PeirceSpine
