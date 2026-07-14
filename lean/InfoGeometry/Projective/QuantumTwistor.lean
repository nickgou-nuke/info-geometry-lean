import InfoGeometry.Projective.QuantumGrassmannian
import InfoGeometry.Projective.KleinQuadricPlucker

/-!
# Quantum Twistors

This module maps the formal quantum minors of the `QuantumGrassmannian` coordinate ring
into the `QuantumPluckerGenerator` structure, explicitly identifying the FRT minors
with the physical twistor products $p_{ij} = \langle Z_i Z_j \rangle$.
-/

namespace InfoGeometry.Projective.QuantumTwistor

open InfoGeometry.Projective.QuantumGrassmannian
open InfoGeometry.Projective.KleinQuadricPlucker

universe u
variable (R : Type u) [Field R]

/-- Structure representing the 6 quantum Plucker generators. -/
structure QuantumPluckerGenerator (A : Type*) where
  p01 : A
  p02 : A
  p03 : A
  p12 : A
  p13 : A
  p23 : A

/--
Explicit map from the `QuantumGrassmannian` coordinate ring (the FRT minors)
to the physical `QuantumPluckerGenerator` coordinates.
-/
def quantumPluckerMap (q : R) :
    QuantumPluckerGenerator (coordinateRing R q) where
  p01 := ⟨quantumMinor R q ⟨(0, 1), by decide⟩, quantumMinor_mem_coordinateRing R q _⟩
  p02 := ⟨quantumMinor R q ⟨(0, 2), by decide⟩, quantumMinor_mem_coordinateRing R q _⟩
  p03 := ⟨quantumMinor R q ⟨(0, 3), by decide⟩, quantumMinor_mem_coordinateRing R q _⟩
  p12 := ⟨quantumMinor R q ⟨(1, 2), by decide⟩, quantumMinor_mem_coordinateRing R q _⟩
  p13 := ⟨quantumMinor R q ⟨(1, 3), by decide⟩, quantumMinor_mem_coordinateRing R q _⟩
  p23 := ⟨quantumMinor R q ⟨(2, 3), by decide⟩, quantumMinor_mem_coordinateRing R q _⟩

/-- The six production twistor coordinates satisfy the q-Plücker relation in
`O_q(Gr(2,4))`. -/
theorem quantumPluckerMap_relation (q : R) :
    let P := quantumPluckerMap R q
    P.p01 * P.p23 - q • (P.p02 * P.p13) + q ^ 2 • (P.p03 * P.p12) = 0 := by
  apply Subtype.ext
  exact quantumPlucker R q

/-! ## Homogeneous scalar gauge readback -/

/-- Evaluate a quantum minor after scaling every matrix entry by `u`. -/
noncomputable def scaledQuantumMinor (u q : R) (p : QuantumMinorIndex) :
    QuantumMatrixAlgebra R q :=
  (u • entry R q 0 p.1.1) * (u • entry R q 1 p.1.2) -
    q • ((u • entry R q 0 p.1.2) * (u • entry R q 1 p.1.1))

/-- Scaling both rows by `u` gives every `2 × 2` quantum minor weight two. -/
theorem scaledQuantumMinor_eq_weight_two (u q : R) (p : QuantumMinorIndex) :
    scaledQuantumMinor R u q p = (u ^ 2) • quantumMinor R q p := by
  simp only [scaledQuantumMinor, quantumMinor, smul_mul_smul, pow_two,
    smul_sub, smul_smul]
  rw [mul_comm q (u * u)]

/-- A scaled quantum minor remains in the quantum Grassmannian coordinate ring. -/
theorem scaledQuantumMinor_mem_coordinateRing (u q : R) (p : QuantumMinorIndex) :
    scaledQuantumMinor R u q p ∈ coordinateRing R q := by
  rw [scaledQuantumMinor_eq_weight_two]
  exact (coordinateRing R q).smul_mem (quantumMinor_mem_coordinateRing R q p) (u ^ 2)

/-- The scaled minor as an element of `O_q(Gr(2,4))`. -/
noncomputable def scaledQuantumMinorCoordinate (u q : R) (p : QuantumMinorIndex) :
    coordinateRing R q :=
  ⟨scaledQuantumMinor R u q p, scaledQuantumMinor_mem_coordinateRing R u q p⟩

@[simp]
theorem coe_scaledQuantumMinorCoordinate (u q : R) (p : QuantumMinorIndex) :
    (scaledQuantumMinorCoordinate R u q p : QuantumMatrixAlgebra R q) =
      (u ^ 2) • quantumMinor R q p :=
  scaledQuantumMinor_eq_weight_two R u q p

end InfoGeometry.Projective.QuantumTwistor
