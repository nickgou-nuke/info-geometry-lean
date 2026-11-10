/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic.NoncommRing
import InfoGeometry.Arithmetic.HoradamIonBinetSlice
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Horadam `2^k`-ion Catalan/Cassini Binet slice

This module formalizes both the non-commutative `[Ring B]` Binet Catalan/Cassini
cross-term identity and the commutative-coordinate `[CommRing R]` shadow of the
Catalan/Cassini identity family in `preprints201906.0303.v1`, *Horadam 2^k-ions*.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.HoradamIonCatalanSlice

open InfoGeometry.Arithmetic.HoradamIonMatrixMethods
open InfoGeometry.Arithmetic.HoradamIonBinetSlice
open InfoGeometry.Algebra.FiniteSpin

/-- Non-commutativity witness for the finite spin algebra carrier. -/
theorem exists_noncomm_pair :
    ∃ x y : Mat2C, x * y ≠ y * x :=
  ⟨J_plus, J_minus, j_plus_j_minus_ne⟩

section NonCommRingBinetCatalan

variable {B : Type*} [Ring B]

/-- Pure Binet sequence `α ^ n - β ^ n` in an arbitrary non-commutative ring `[Ring B]`. -/
def ringPureBinet (α β : B) (n : ℕ) : B :=
  α ^ n - β ^ n

/-- Over any non-commutative ring `[Ring B]`, the diagonal powers `α ^ m * α ^ (m + 2 * r)`
and `β ^ m * β ^ (m + 2 * r)` cancel against `α ^ (m + r) * α ^ (m + r)` and
`β ^ (m + r) * β ^ (m + r)` without any commutativity assumption between `α` and `β`. -/
theorem ringPureBinet_catalan_cross_identity (α β : B) (m r : ℕ) :
    ringPureBinet α β m * ringPureBinet α β (m + 2 * r) -
      ringPureBinet α β (m + r) * ringPureBinet α β (m + r) =
        α ^ (m + r) * β ^ (m + r) + β ^ (m + r) * α ^ (m + r) -
          α ^ m * β ^ (m + 2 * r) - β ^ m * α ^ (m + 2 * r) := by
  unfold ringPureBinet
  have hα : α ^ m * α ^ (m + 2 * r) = α ^ (m + r) * α ^ (m + r) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have hβ : β ^ m * β ^ (m + 2 * r) = β ^ (m + r) * β ^ (m + r) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  calc
    (α ^ m - β ^ m) * (α ^ (m + 2 * r) - β ^ (m + 2 * r)) -
        (α ^ (m + r) - β ^ (m + r)) * (α ^ (m + r) - β ^ (m + r))
      = (α ^ m * α ^ (m + 2 * r) - α ^ (m + r) * α ^ (m + r)) +
          (β ^ m * β ^ (m + 2 * r) - β ^ (m + r) * β ^ (m + r)) +
          (α ^ (m + r) * β ^ (m + r) + β ^ (m + r) * α ^ (m + r) -
            α ^ m * β ^ (m + 2 * r) - β ^ m * α ^ (m + 2 * r)) := by
      noncomm_ring
    _ = α ^ (m + r) * β ^ (m + r) + β ^ (m + r) * α ^ (m + r) -
          α ^ m * β ^ (m + 2 * r) - β ^ m * α ^ (m + 2 * r) := by
      rw [hα, hβ]
      noncomm_ring

end NonCommRingBinetCatalan

variable {R : Type*} [CommRing R]

/-- Catalan/Cassini-style finite identity for the commutative Binet core. -/
theorem binetCore_catalan_shadow
    (A B α β : R) (m r : ℕ) :
    binetCore A B α β m * binetCore A B α β (m + 2 * r) -
      binetCore A B α β (m + r) ^ 2 =
        -(A * B) * (α * β) ^ m * (α ^ r - β ^ r) ^ 2 := by
  unfold binetCore
  rw [pow_add α m (2 * r), pow_add β m (2 * r), pow_add α m r, pow_add β m r]
  rw [show α ^ (2 * r) = (α ^ r) ^ 2 by
    rw [show 2 * r = r + r by omega, pow_add]
    ring]
  rw [show β ^ (2 * r) = (β ^ r) ^ 2 by
    rw [show 2 * r = r + r by omega, pow_add]
    ring]
  rw [mul_pow]
  ring

/-- Componentwise Catalan/Cassini shadow for the coordinate Binet lift. -/
theorem binetIon_catalan_shadow {N : ℕ}
    (A B α β : R) (m r : ℕ) :
    (fun s : Fin N =>
        binetIon (N := N) A B α β m s *
            binetIon (N := N) A B α β (m + 2 * r) s -
          binetIon (N := N) A B α β (m + r) s ^ 2) =
      fun s : Fin N =>
        -(A * B) * (α * β) ^ (m + s.val) * (α ^ r - β ^ r) ^ 2 := by
  ext s
  simp [binetIon]
  simpa [add_assoc, add_comm, add_left_comm] using
    binetCore_catalan_shadow A B α β (m + s.val) r

/-- Cassini specialization `r=1`. -/
theorem binetCore_cassini_shadow
    (A B α β : R) (m : ℕ) :
    binetCore A B α β m * binetCore A B α β (m + 2) -
      binetCore A B α β (m + 1) ^ 2 =
        -(A * B) * (α * β) ^ m * (α - β) ^ 2 := by
  simpa using binetCore_catalan_shadow A B α β m 1

/-- Consolidated finite Catalan/Cassini coordinate packet. -/
theorem horadam_ion_catalan_slice_packet {N : ℕ}
    (A B α β : R) :
    (∀ m r : ℕ,
      binetCore A B α β m * binetCore A B α β (m + 2 * r) -
        binetCore A B α β (m + r) ^ 2 =
          -(A * B) * (α * β) ^ m * (α ^ r - β ^ r) ^ 2) ∧
    (∀ m r : ℕ,
      (fun s : Fin N =>
          binetIon (N := N) A B α β m s *
              binetIon (N := N) A B α β (m + 2 * r) s -
            binetIon (N := N) A B α β (m + r) s ^ 2) =
        fun s : Fin N =>
          -(A * B) * (α * β) ^ (m + s.val) * (α ^ r - β ^ r) ^ 2) := by
  exact ⟨binetCore_catalan_shadow A B α β,
    binetIon_catalan_shadow A B α β⟩

end InfoGeometry.Arithmetic.HoradamIonCatalanSlice

end noncomputable section
