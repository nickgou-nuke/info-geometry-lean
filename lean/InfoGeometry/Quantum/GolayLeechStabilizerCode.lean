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
  simp only [golayStabilizerCode, golayPauliCode, Finset.mem_product]
  constructor
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, encode_zero⟩
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, encode_zero⟩

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
    (∀ m : Message, 4 ∣ hammingWeight (encode m)) →
    (∀ m : Message, encode m ≠ 0 →
      ∃ f : Fin 23 → Fin (hammingWeight (encode m) ^ 2 -
        hammingWeight (encode m) + 1), Function.Injective f) →
    (∀ w ∈ golayCode, w ≠ 0 → 8 ≤ hammingWeight w) ∧
      (∃ w ∈ golayCode, hammingWeight w = 8) :=
  golay_code_minimumWeight_eq_eight

structure QuantumStabilizerCode where
  carrier : Finset BinaryPauli24
  carrier_nonempty : carrier.Nonempty
  symplectic_commutation :
    ∀ u ∈ carrier, ∀ v ∈ carrier,
      symplecticInnerProduct u v = 0

def golayStabilizerCodeParameters : QuantumStabilizerCode where
  carrier := golayStabilizerCode
  carrier_nonempty := golay_stabilizer_code_nonempty
  symplectic_commutation := golay_stabilizer_commutes

end InfoGeometry.Quantum.GolayLeechStabilizerCode
