import InfoGeometry.Arithmetic.HoradamIonBinetSlice
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Horadam `2^k`-ion Catalan/Cassini Binet slice

This module formalizes a theorem-safe commutative-coordinate shadow of the
Catalan/Cassini identity family in `preprints201906.0303.v1`, *Horadam 2^k-ions*.

For the Binet core `C_n = A α^n - B β^n`, it proves

`C_m C_{m+2r} - C_{m+r}^2 = - A B (αβ)^m (α^r - β^r)^2`.

The coordinate-lift theorem applies the same identity componentwise to the
finite `2^k`-ion coordinate packet.

This deliberately does **not** assert the paper's noncommutative
Cayley-Dickson-product Catalan/Cassini identities.  Those require a separate
owner for the relevant Cayley-Dickson multiplication and associativity scope.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.HoradamIonCatalanSlice

open InfoGeometry.Arithmetic.HoradamIonMatrixMethods
open InfoGeometry.Arithmetic.HoradamIonBinetSlice

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
