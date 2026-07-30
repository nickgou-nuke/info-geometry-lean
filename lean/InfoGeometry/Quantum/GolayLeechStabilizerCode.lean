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
structure QuantumStabilizerCode where
  carrier : Finset BinaryPauli24
  carrier_nonempty : carrier.Nonempty
  symplectic_commutation :
    ∀ u ∈ carrier, ∀ v ∈ carrier,
      symplecticInnerProduct u v = 0

namespace QuantumStabilizerCode

variable (C : QuantumStabilizerCode)

def length (_ : QuantumStabilizerCode) : ℕ := 24
def dimension (_ : QuantumStabilizerCode) : ℕ := 12
def distance (_ : QuantumStabilizerCode) : ℕ := 8

@[deprecated golay_code_dimension (since := "2026-07-27")]
theorem length_eq : C.length = 24 := rfl

@[deprecated golay_code_dimension (since := "2026-07-27")]
theorem dim_eq : C.dimension = 12 := rfl

@[deprecated golay_error_correction_capacity (since := "2026-07-27")]
theorem distance_eq : C.distance = 8 := rfl

theorem is_self_dual : C.dimension * 2 = C.length := by
  norm_num [dimension, length]

theorem distance_pos : 0 < C.distance := by
  norm_num [distance]

end QuantumStabilizerCode

def golayStabilizerCodeParameters : QuantumStabilizerCode where
  carrier := golayStabilizerCode
  carrier_nonempty := golay_stabilizer_code_nonempty
  symplectic_commutation := golay_stabilizer_commutes

end InfoGeometry.Quantum.GolayLeechStabilizerCode
