/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic
import InfoGeometry.Canonical.MoorePenrose

namespace InfoGeometry.Physics.MoorePenroseHodgeDrazinGhostBridge

section Pseudoinverses

variable {R : Type*} [Ring R] [StarRing R]

abbrev IsMoorePenrose (A A_plus : R) : Prop :=
  InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse A A_plus

abbrev IsDrazinIndexOne (A A_D : R) : Prop :=
  InfoGeometry.Canonical.Drazin.IsDrazinInverse A A_D 1

omit [StarRing R] in
lemma index_one_aab {A A_D : R} (h : IsDrazinIndexOne A A_D) :
    A * A * A_D = A := by
  simpa [pow_two, pow_one] using h.power

def defect_ghost (A_plus A_D : R) : R := A_plus - A_D

omit [StarRing R] in
theorem zero_ghost_implies_metric_commutation
    (A A_plus A_D : R)
    (h_drazin : IsDrazinIndexOne A A_D)
    (h_ghost : defect_ghost A_plus A_D = 0) :
    A * A_plus = A_plus * A := by
  have h_eq : A_plus = A_D := sub_eq_zero.mp h_ghost
  rw [h_eq]
  exact h_drazin.comm

omit [StarRing R] in
theorem operator_ghost_commutator
    (A A_plus A_D : R)
    (h_drazin : IsDrazinIndexOne A A_D) :
    A * (defect_ghost A_plus A_D) - (defect_ghost A_plus A_D) * A =
    A * A_plus - A_plus * A := by
  dsimp [defect_ghost]
  have h_comm : A * A_D = A_D * A := h_drazin.comm
  calc
    A * (A_plus - A_D) - (A_plus - A_D) * A
      = A * A_plus - A * A_D - (A_plus * A - A_D * A) := by simp only [mul_sub, sub_mul]
    _ = A * A_plus - A_plus * A - A * A_D + A_D * A := by abel
    _ = A * A_plus - A_plus * A - A * A_D + A * A_D := by rw [h_comm]
    _ = A * A_plus - A_plus * A := by abel

omit [StarRing R] in
/-- Under the Drazin commutation law, vanishing of the ghost commutator is
    equivalent to commutation of the Moore–Penrose candidate itself. -/
theorem ghost_commutator_eq_zero_iff
    (A A_plus A_D : R)
    (h_drazin : IsDrazinIndexOne A A_D) :
    A * (defect_ghost A_plus A_D) - (defect_ghost A_plus A_D) * A = 0 ↔
      A * A_plus = A_plus * A := by
  rw [operator_ghost_commutator A A_plus A_D h_drazin]
  exact sub_eq_zero

/-!
## Index-one sector geometry

The index-one Drazin laws split `A` into a regular core and an algebraic
(null-volume) complement.  The two names above are abbreviations for the
canonical Drazin and Moore--Penrose owner predicates; no parallel predicate is
introduced here.  All statements remain over an arbitrary ring, with the
star-ring structure used only by the Moore--Penrose laws.
-/

/-- The regular (core) projector `E_C = A A_D`. -/
def regularProjector (A A_D : R) : R := A * A_D

/-- The algebraic complementary (null-volume) projector `E_N = 1 - A A_D`.
The legacy name does not assert a Hodge differential or Laplacian. -/
def harmonicProjector (A A_D : R) : R := 1 - A * A_D

/-- The regular core `C = A E_C`. -/
def regularPart (A A_D : R) : R := A * regularProjector A A_D

/-- The algebraic complementary part `N = A E_N` (legacy name retained). -/
def harmonicPart (A A_D : R) : R := A * harmonicProjector A A_D

/-- The local Moore--Penrose predicate is the owner predicate. -/
theorem toIsMoorePenroseInverse {A A_plus : R} (h : IsMoorePenrose A A_plus) :
    InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse A A_plus :=
  h

omit [StarRing R] in
/-- The local index-one predicate is the `k = 1` case of the Drazin owner. -/
theorem toIsDrazinInverse {A A_D : R} (h : IsDrazinIndexOne A A_D) :
    InfoGeometry.Canonical.Drazin.IsDrazinInverse A A_D 1 := by
  exact h

omit [StarRing R] in
/-- **`regular_add_harmonic_id`.**  The regular and harmonic projectors are
complementary for every Drazin pair. -/
theorem regular_add_harmonic_id (A A_D : R) :
    regularProjector A A_D + harmonicProjector A A_D = 1 := by
  unfold regularProjector harmonicProjector
  abel

omit [StarRing R] in
/-- The operator-level core/harmonic decomposition `A = C + N`. -/
theorem regularPart_add_harmonicPart (A A_D : R) :
    regularPart A A_D + harmonicPart A A_D = A := by
  unfold regularPart harmonicPart harmonicProjector regularProjector
  rw [mul_sub, mul_one]
  abel

omit [StarRing R] in
/-- **`regular_projector_idempotent`.** -/
theorem regular_projector_idempotent {A A_D : R} (h : IsDrazinIndexOne A A_D) :
    regularProjector A A_D * regularProjector A A_D = regularProjector A A_D := by
  have hEA : (A * A_D) * A = A := by
    rw [mul_assoc, ← h.comm, ← mul_assoc, index_one_aab h]
  unfold regularProjector
  rw [← mul_assoc, hEA]

omit [StarRing R] in
/-- **`harmonic_projector_idempotent`.** -/
theorem harmonic_projector_idempotent {A A_D : R} (h : IsDrazinIndexOne A A_D) :
    harmonicProjector A A_D * harmonicProjector A A_D = harmonicProjector A A_D := by
  have hE : (A * A_D) * (A * A_D) = A * A_D := regular_projector_idempotent h
  unfold harmonicProjector
  rw [sub_mul, one_mul, mul_sub, mul_one, hE, sub_self, sub_zero]

omit [StarRing R] in
/-- **`harmonic_projector_in_kernel`.**  The harmonic projector is annihilated
by `A`, so it is the null-volume sector. -/
theorem harmonic_projector_in_kernel {A A_D : R} (h : IsDrazinIndexOne A A_D) :
    A * harmonicProjector A A_D = 0 := by
  unfold harmonicProjector
  rw [mul_sub, mul_one, ← mul_assoc, index_one_aab h, sub_self]

omit [StarRing R] in
/-- **`drazin_annihilates_null`.**  The Drazin inverse kills the harmonic
sector. -/
theorem drazin_annihilates_null {A A_D : R} (h : IsDrazinIndexOne A A_D) :
    A_D * harmonicProjector A A_D = 0 := by
  unfold harmonicProjector
  rw [mul_sub, mul_one, ← mul_assoc, h.idempotent, sub_self]

omit [StarRing R] in
/-- **`regular_sector_exact_inversion`.**  Replacing the null-volume operator on
the harmonic sector by its projector makes the Drazin inverse exact:
`(C + E_N) (A_D + E_N) = 1` and conversely. -/
theorem regular_sector_exact_inversion {A A_D : R} (h : IsDrazinIndexOne A A_D) :
    (regularPart A A_D + harmonicProjector A A_D) *
        (A_D + harmonicProjector A A_D) = 1 ∧
      (A_D + harmonicProjector A A_D) *
        (regularPart A A_D + harmonicProjector A A_D) = 1 := by
  have hR : regularPart A A_D = A := by
    unfold regularPart regularProjector
    rw [← mul_assoc, index_one_aab h]
  have hN : (1 - A * A_D) * (1 - A * A_D) = 1 - A * A_D := by
    simpa [harmonicProjector] using harmonic_projector_idempotent h
  have hAN : A * (1 - A * A_D) = 0 := by
    simpa [harmonicProjector] using harmonic_projector_in_kernel h
  have hDN : A_D * (1 - A * A_D) = 0 := by
    simpa [harmonicProjector] using drazin_annihilates_null h
  have hND : (1 - A * A_D) * A_D = 0 := by
    rw [sub_mul, one_mul, h.comm, h.idempotent, sub_self]
  have hEA : (A * A_D) * A = A := by
    rw [mul_assoc, ← h.comm, ← mul_assoc, index_one_aab h]
  have hDA : A_D * A = A * A_D := h.comm.symm
  have hNE : (1 - A * A_D) * A = 0 := by
    rw [sub_mul, one_mul, hEA, sub_self]
  constructor
  · rw [hR]
    unfold harmonicProjector
    calc
      (A + (1 - A * A_D)) * (A_D + (1 - A * A_D))
          = A * A_D + A * (1 - A * A_D) + (1 - A * A_D) * A_D +
              (1 - A * A_D) * (1 - A * A_D) := by noncomm_ring
      _ = A * A_D + 0 + 0 + (1 - A * A_D) := by rw [hAN, hND, hN]
      _ = 1 := by abel
  · rw [hR]
    unfold harmonicProjector
    calc
      (A_D + (1 - A * A_D)) * (A + (1 - A * A_D))
          = A_D * A + A_D * (1 - A * A_D) + (1 - A * A_D) * A +
              (1 - A * A_D) * (1 - A * A_D) := by noncomm_ring
      _ = A * A_D + 0 + 0 + (1 - A * A_D) := by rw [hDA, hDN, hNE, hN]
      _ = 1 := by abel

/-- **`moore_penrose_is_drazin_index_one`.**  Under the EP hypothesis the
Moore--Penrose inverse is a Drazin index-one inverse.  The hypothesis cannot be
dropped: for the nilpotent shift `A = !![0, 1; 0, 0]` the Moore--Penrose laws
hold while `A * A * A† = 0 ≠ A`. -/
theorem moore_penrose_is_drazin_index_one {A A_plus : R}
    (h : IsMoorePenrose A A_plus) (hEP : A * A_plus = A_plus * A) :
    IsDrazinIndexOne A A_plus := by
  refine ⟨hEP, h.bab_eq_b, ?_⟩
  simpa [pow_two, pow_one] using (by
    rw [mul_assoc, hEP, ← mul_assoc, h.aba_eq_a] : A * A * A_plus = A)

/-- Capstone certificate: the Moore--Penrose and Drazin index-one laws are
recorded together and induce the exact algebraic regular/complementary split.
It does not assert equality of the supplied inverse candidates or a Hodge
complex. -/
structure CertifiedMPHodgeDrazinGhostSynthesis (A A_plus A_D : R) : Prop where
  mp : IsMoorePenrose A A_plus
  drazin : IsDrazinIndexOne A A_D
  ep : A * A_plus = A_plus * A
  projectors_sum_one : regularProjector A A_D + harmonicProjector A A_D = 1
  regular_idempotent :
    regularProjector A A_D * regularProjector A A_D = regularProjector A A_D
  harmonic_idempotent :
    harmonicProjector A A_D * harmonicProjector A A_D = harmonicProjector A A_D
  harmonic_in_kernel : A * harmonicProjector A A_D = 0
  drazin_annihilates_harmonic : A_D * harmonicProjector A A_D = 0
  gauge_inverse_left :
    (regularPart A A_D + harmonicProjector A A_D) *
        (A_D + harmonicProjector A A_D) = 1
  gauge_inverse_right :
    (A_D + harmonicProjector A A_D) *
        (regularPart A A_D + harmonicProjector A A_D) = 1
  mp_is_drazin : IsDrazinIndexOne A A_plus

/-- **`certified_mp_hodge_drazin_ghost_synthesis`.** -/
theorem certified_mp_hodge_drazin_ghost_synthesis {A A_plus A_D : R}
    (hMP : IsMoorePenrose A A_plus) (hD : IsDrazinIndexOne A A_D)
    (hEP : A * A_plus = A_plus * A) :
    CertifiedMPHodgeDrazinGhostSynthesis A A_plus A_D where
  mp := hMP
  drazin := hD
  ep := hEP
  projectors_sum_one := regular_add_harmonic_id A A_D
  regular_idempotent := regular_projector_idempotent hD
  harmonic_idempotent := harmonic_projector_idempotent hD
  harmonic_in_kernel := harmonic_projector_in_kernel hD
  drazin_annihilates_harmonic := drazin_annihilates_null hD
  gauge_inverse_left := (regular_sector_exact_inversion hD).1
  gauge_inverse_right := (regular_sector_exact_inversion hD).2
  mp_is_drazin := moore_penrose_is_drazin_index_one hMP hEP

end Pseudoinverses

end InfoGeometry.Physics.MoorePenroseHodgeDrazinGhostBridge
