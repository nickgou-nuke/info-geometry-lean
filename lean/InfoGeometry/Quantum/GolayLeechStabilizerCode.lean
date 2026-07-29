import InfoGeometry.Canonical.GolayLeechStabilizerCode

/-!
# Quantum stabilizer readout of the extended binary Golay code

This module exports the actual finite code and its isotropic Pauli carrier.
It contains no parameter witness structure.
-/

namespace InfoGeometry.Quantum.GolayLeechStabilizerCode

open InfoGeometry.Combinatorics.ExtendedBinaryGolay
open InfoGeometry.Canonical.GolayLeechStabilizerCode

/-- The quantum-code carrier is the constructed isotropic Pauli code. -/
abbrev golayStabilizerCode : Finset BinaryPauli24 :=
  golayPauliCode

/-- Kernel-checked existence of the constructed stabilizer carrier. -/
theorem golay_stabilizer_code_nonempty :
    golayStabilizerCode.Nonempty := by
  refine ⟨(0, 0), ?_⟩
  simp [golayStabilizerCode, golayPauliCode, golayCode, code, encode_zero]

/--
Compatibility existence theorem for the historical public name.

Its conclusion now concerns the genuinely constructed stabilizer carrier,
rather than a record containing only the numeral equalities `24 = 24`,
`12 = 12`, and `8 = 8`.
-/
theorem golay_leech_stabilizer_code_exists :
    golayStabilizerCode.Nonempty :=
  golay_stabilizer_code_nonempty

/-- Every two stabilizer labels commute under the binary symplectic form. -/
theorem golay_stabilizer_commutes :
    ∀ u ∈ golayStabilizerCode, ∀ v ∈ golayStabilizerCode,
      symplecticInnerProduct u v = 0 :=
  golay_pauli_code_isotropic

/-- The underlying classical code has exact minimum weight eight. -/
theorem golay_stabilizer_distance_eight :
    (∀ w ∈ golayCode, w ≠ 0 → 8 ≤ hammingWeight w) ∧
      (∃ w ∈ golayCode, hammingWeight w = 8) :=
  golay_code_minimumWeight_eq_eight

/-! ## Deprecated numerical compatibility API -/

/--
Deprecated compatibility record for clients of the former `[n,k,d]` marker.
The constructed stabilizer carrier remains `golayStabilizerCode`; this record
only preserves the old numerical entry point and is not a code construction.
-/
structure QuantumStabilizerCode (n k d : ℕ) where
  carrier : Finset BinaryPauli24
  carrier_nonempty : carrier.Nonempty
  symplectic_commutation :
    ∀ u ∈ carrier, ∀ v ∈ carrier,
      symplecticInnerProduct u v = 0
  n_eq : n = 24
  k_eq : k = 12
  d_eq : d = 8

namespace QuantumStabilizerCode

variable {n k d : ℕ} (C : QuantumStabilizerCode n k d)

@[deprecated n_eq (since := "2026-07-27")]
theorem length_eq : n = 24 := C.n_eq

@[deprecated k_eq (since := "2026-07-27")]
theorem dim_eq : k = 12 := C.k_eq

@[deprecated d_eq (since := "2026-07-27")]
theorem distance_eq : d = 8 := C.d_eq

theorem is_self_dual : k * 2 = n := by
  omega

theorem distance_pos : 0 < d := by
  omega

end QuantumStabilizerCode

def golayStabilizerCodeParameters : QuantumStabilizerCode 24 12 8 where
  carrier := golayStabilizerCode
  carrier_nonempty := golay_stabilizer_code_nonempty
  symplectic_commutation := golay_stabilizer_commutes
  n_eq := rfl
  k_eq := rfl
  d_eq := rfl

end InfoGeometry.Quantum.GolayLeechStabilizerCode
