import InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
import InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms

namespace InfoGeometry.Algebra.Zorn.G2TwoPCConjugation

open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup

/- CAS export: PCCONJ 6 2 = (0,1,0,0,0,0). -/
theorem pc2Aut_comm_pc6Aut :
    pc2Aut * pc6Aut = pc6Aut * pc2Aut := by
  apply Subtype.ext
  apply Equiv.ext
  intro X
  rw [aut_mul_apply, aut_mul_apply]
  exact (pc2_pc6 X).symm

theorem pc6Aut_conj_pc2Aut :
    pc6Aut⁻¹ * pc2Aut * pc6Aut = pc2Aut := by
  rw [pc6Aut_inv_eq]
  have hsq : pc6Aut * pc6Aut = 1 := by
    rw [← pc6Aut_inv_eq]
    exact inv_mul_cancel pc6Aut
  calc
    pc6Aut * pc2Aut * pc6Aut = pc2Aut * pc6Aut * pc6Aut := by
      rw [pc2Aut_comm_pc6Aut]
    _ = pc2Aut := by
      rw [mul_assoc, hsq, mul_one]

/- CAS export: PCCONJ 6 3 = (0,0,1,0,0,0). -/
theorem pc3Aut_comm_pc6Aut :
    pc3Aut * pc6Aut = pc6Aut * pc3Aut := by
  apply Subtype.ext
  apply Equiv.ext
  intro X
  rw [aut_mul_apply, aut_mul_apply]
  exact (pc3_pc6 X).symm

theorem pc6Aut_conj_pc3Aut :
    pc6Aut⁻¹ * pc3Aut * pc6Aut = pc3Aut := by
  rw [pc6Aut_inv_eq]
  have hsq : pc6Aut * pc6Aut = 1 := by
    rw [← pc6Aut_inv_eq]
    exact inv_mul_cancel pc6Aut
  calc
    pc6Aut * pc3Aut * pc6Aut = pc3Aut * pc6Aut * pc6Aut := by
      rw [pc3Aut_comm_pc6Aut]
    _ = pc3Aut := by rw [mul_assoc, hsq, mul_one]

/- CAS export: PCCONJ 6 4 = (0,0,0,1,0,0). -/
theorem pc4Aut_comm_pc6Aut :
    pc4Aut * pc6Aut = pc6Aut * pc4Aut := by
  apply Subtype.ext
  apply Equiv.ext
  intro X
  rw [aut_mul_apply, aut_mul_apply]
  change G2TwoSylowPCGenerators.pc6Fun
      (G2TwoSylowPCGenerators.pc4Fun X) =
    G2TwoSylowPCGenerators.pc4Fun
      (G2TwoSylowPCGenerators.pc6Fun X)
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  ext <;> dsimp [G2TwoSylowPCGenerators.pc4Fun,
    G2TwoSylowPCGenerators.pc6Fun,
    InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add2]
  all_goals simp [Bool.xor_left_comm]

/- CAS export: PCCONJ 6 5 = (0,0,0,0,1,0). -/
theorem pc5Aut_comm_pc6Aut :
    pc5Aut * pc6Aut = pc6Aut * pc5Aut := by
  apply Subtype.ext
  apply Equiv.ext
  intro X
  rw [aut_mul_apply, aut_mul_apply]
  change G2TwoSylowPCGenerators.pc6Fun
      (G2TwoSylowPCGenerators.pc5Fun X) =
    G2TwoSylowPCGenerators.pc5Fun
      (G2TwoSylowPCGenerators.pc6Fun X)
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  ext <;> dsimp [G2TwoSylowPCGenerators.pc5Fun,
    G2TwoSylowPCGenerators.pc6Fun,
    InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add2]
  all_goals simp [Bool.xor_left_comm, Bool.xor_comm]

/- CAS export: PCCONJ 6 1 = (1,0,0,0,0,0). -/
theorem pc1Aut_comm_pc6Aut :
    pc1Aut * pc6Aut = pc6Aut * pc1Aut := by
  apply Subtype.ext
  apply Equiv.ext
  intro X
  rw [aut_mul_apply, aut_mul_apply]
  change G2TwoSylowPCGenerators.pc6Fun
      (G2TwoSylowPCGenerators.pc1Fun X) =
    G2TwoSylowPCGenerators.pc1Fun
      (G2TwoSylowPCGenerators.pc6Fun X)
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  ext <;> dsimp [G2TwoSylowPCGenerators.pc1Fun,
    G2TwoSylowPCGenerators.pc6Fun,
    InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add2]
  all_goals simp [Bool.xor_left_comm, Bool.xor_comm]

/- CAS export: PCCONJ 5 4 = (0,0,0,1,0,0). -/
theorem pc4Aut_comm_pc5Aut :
    pc4Aut * pc5Aut = pc5Aut * pc4Aut := by
  apply Subtype.ext
  apply Equiv.ext
  intro X
  rw [aut_mul_apply, aut_mul_apply]
  change G2TwoSylowPCGenerators.pc5Fun
      (G2TwoSylowPCGenerators.pc4Fun X) =
    G2TwoSylowPCGenerators.pc4Fun
      (G2TwoSylowPCGenerators.pc5Fun X)
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  ext <;> dsimp [G2TwoSylowPCGenerators.pc4Fun,
    G2TwoSylowPCGenerators.pc5Fun,
    InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add2]
  all_goals simp [Bool.xor_left_comm, Bool.xor_comm]

/- CAS export: PCCONJ 5 3 = (0,0,1,0,0,1). -/
theorem pc5Aut_conj_pc3Aut :
    pc5Aut⁻¹ * pc3Aut * pc5Aut = pc3Aut * pc6Aut := by
  rw [pc5Aut_inv_eq]
  apply Subtype.ext
  apply Equiv.ext
  intro X
  rw [aut_mul_apply, aut_mul_apply, aut_mul_apply]
  change G2TwoSylowPCGenerators.pc5Fun
      (G2TwoSylowPCGenerators.pc3Fun
        (G2TwoSylowPCGenerators.pc5Fun X)) =
    G2TwoSylowPCGenerators.pc6Fun
      (G2TwoSylowPCGenerators.pc3Fun X)
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  ext <;> dsimp [G2TwoSylowPCGenerators.pc3Fun,
    G2TwoSylowPCGenerators.pc5Fun,
    G2TwoSylowPCGenerators.pc6Fun,
    InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add2]
  all_goals simp [Bool.xor_left_comm, Bool.xor_comm]

/- CAS export: PCCONJ 5 2 = (0,1,0,0,0,1). -/
theorem pc5Aut_conj_pc2Aut :
    pc5Aut⁻¹ * pc2Aut * pc5Aut = pc2Aut * pc6Aut := by
  rw [pc5Aut_inv_eq]
  apply Subtype.ext
  apply Equiv.ext
  intro X
  rw [aut_mul_apply, aut_mul_apply, aut_mul_apply]
  change G2TwoSylowPCGenerators.pc5Fun
      (G2TwoSylowPCGenerators.pc2Fun
        (G2TwoSylowPCGenerators.pc5Fun X)) =
    G2TwoSylowPCGenerators.pc6Fun
      (G2TwoSylowPCGenerators.pc2Fun X)
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  ext <;> dsimp [G2TwoSylowPCGenerators.pc2Fun,
    G2TwoSylowPCGenerators.pc5Fun,
    G2TwoSylowPCGenerators.pc6Fun,
    InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add2]
  all_goals simp [Bool.xor_left_comm, Bool.xor_comm]

/- CAS export: PCCONJ 5 1 = (1,0,0,1,0,0). -/
theorem pc5Aut_conj_pc1Aut :
    pc5Aut⁻¹ * pc1Aut * pc5Aut = pc1Aut * pc4Aut := by
  rw [pc5Aut_inv_eq]
  apply Subtype.ext
  apply Equiv.ext
  intro X
  rw [aut_mul_apply, aut_mul_apply, aut_mul_apply]
  change G2TwoSylowPCGenerators.pc5Fun
      (G2TwoSylowPCGenerators.pc1Fun
        (G2TwoSylowPCGenerators.pc5Fun X)) =
    G2TwoSylowPCGenerators.pc4Fun
      (G2TwoSylowPCGenerators.pc1Fun X)
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  ext <;> dsimp [G2TwoSylowPCGenerators.pc1Fun,
    G2TwoSylowPCGenerators.pc4Fun,
    G2TwoSylowPCGenerators.pc5Fun,
    InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add2]
  all_goals simp [Bool.xor_left_comm, Bool.xor_comm]

/- CAS export: PCCONJ 4 3 = (0,0,1,0,0,0). -/
theorem pc3Aut_comm_pc4Aut :
    pc3Aut * pc4Aut = pc4Aut * pc3Aut := by
  apply Subtype.ext
  apply Equiv.ext
  intro X
  rw [aut_mul_apply, aut_mul_apply]
  change G2TwoSylowPCGenerators.pc4Fun
      (G2TwoSylowPCGenerators.pc3Fun X) =
    G2TwoSylowPCGenerators.pc3Fun
      (G2TwoSylowPCGenerators.pc4Fun X)
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  ext <;> dsimp [G2TwoSylowPCGenerators.pc3Fun,
    G2TwoSylowPCGenerators.pc4Fun,
    InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add2]
  all_goals simp [Bool.xor_left_comm, Bool.xor_comm]

/- CAS export: PCCONJ 4 1 = (1,0,0,0,0,0). -/
theorem pc1Aut_comm_pc4Aut :
    pc1Aut * pc4Aut = pc4Aut * pc1Aut := by
  apply Subtype.ext
  apply Equiv.ext
  intro X
  rw [aut_mul_apply, aut_mul_apply]
  change G2TwoSylowPCGenerators.pc4Fun
      (G2TwoSylowPCGenerators.pc1Fun X) =
    G2TwoSylowPCGenerators.pc1Fun
      (G2TwoSylowPCGenerators.pc4Fun X)
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  ext <;> dsimp [G2TwoSylowPCGenerators.pc1Fun,
    G2TwoSylowPCGenerators.pc4Fun,
    InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add2]
  all_goals simp [Bool.xor_left_comm, Bool.xor_comm]

/- CAS export: PCCONJ 4 2 = (0,1,0,0,0,1). -/
theorem pc4Aut_conj_pc2Aut :
    pc4Aut⁻¹ * pc2Aut * pc4Aut = pc2Aut * pc6Aut := by
  rw [pc4Aut_inv_eq]
  apply Subtype.ext
  apply Equiv.ext
  intro X
  rw [aut_mul_apply, aut_mul_apply, aut_mul_apply]
  change G2TwoSylowPCGenerators.pc4Fun
      (G2TwoSylowPCGenerators.pc2Fun
        (G2TwoSylowPCGenerators.pc4Fun X)) =
    G2TwoSylowPCGenerators.pc6Fun
      (G2TwoSylowPCGenerators.pc2Fun X)
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  ext <;> dsimp [G2TwoSylowPCGenerators.pc2Fun,
    G2TwoSylowPCGenerators.pc4Fun,
    G2TwoSylowPCGenerators.pc6Fun,
    InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add2]
  all_goals simp [Bool.xor_left_comm, Bool.xor_comm]

/- CAS export: PCCONJ 3 2 = (0,1,0,0,0,0). -/
theorem pc2Aut_comm_pc3Aut :
    pc2Aut * pc3Aut = pc3Aut * pc2Aut := by
  apply Subtype.ext
  apply Equiv.ext
  intro X
  rw [aut_mul_apply, aut_mul_apply]
  change G2TwoSylowPCGenerators.pc3Fun
      (G2TwoSylowPCGenerators.pc2Fun X) =
    G2TwoSylowPCGenerators.pc2Fun
      (G2TwoSylowPCGenerators.pc3Fun X)
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  ext <;> dsimp [G2TwoSylowPCGenerators.pc2Fun,
    G2TwoSylowPCGenerators.pc3Fun,
    InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add2]
  all_goals simp [Bool.xor_left_comm, Bool.xor_comm]

/- CAS export: PCCONJ 3 1 = (1,0,0,0,0,1). -/
theorem pc3Aut_conj_pc1Aut :
    pc3Aut⁻¹ * pc1Aut * pc3Aut = pc1Aut * pc6Aut := by
  rw [pc3Aut_inv_eq]
  apply Subtype.ext
  apply Equiv.ext
  intro X
  rw [aut_mul_apply, aut_mul_apply, aut_mul_apply, aut_mul_apply]
  change G2TwoSylowPCGenerators.pc3Fun
      (G2TwoSylowPCGenerators.pc1Fun
        (G2TwoSylowPCGenerators.pc3Fun
          (G2TwoSylowPCGenerators.pc6Fun X))) =
    G2TwoSylowPCGenerators.pc6Fun
      (G2TwoSylowPCGenerators.pc1Fun X)
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  ext <;> dsimp [G2TwoSylowPCGenerators.pc1Fun,
    G2TwoSylowPCGenerators.pc3Fun,
    G2TwoSylowPCGenerators.pc6Fun,
    InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add2]
  all_goals simp [Bool.xor_left_comm, Bool.xor_comm]

/- CAS export: PCCONJ 2 1 = (1,0,1,1,0,1). -/
theorem pc2Aut_conj_pc1Aut :
    pc2Aut⁻¹ * pc1Aut * pc2Aut = pc6Aut * pc4Aut * pc3Aut * pc1Aut := by
  rw [pc2Aut_inv_eq]
  apply Subtype.ext
  apply Equiv.ext
  intro X
  rw [aut_mul_apply, aut_mul_apply, aut_mul_apply, aut_mul_apply]
  change G2TwoSylowPCGenerators.pc2Fun
      (G2TwoSylowPCGenerators.pc1Fun
        (G2TwoSylowPCGenerators.pc2Fun
          (G2TwoSylowPCGenerators.pc6Fun X))) =
    G2TwoSylowPCGenerators.pc1Fun
      (G2TwoSylowPCGenerators.pc3Fun
        (G2TwoSylowPCGenerators.pc4Fun
          (G2TwoSylowPCGenerators.pc6Fun X)))
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  ext <;> dsimp [G2TwoSylowPCGenerators.pc1Fun,
    G2TwoSylowPCGenerators.pc2Fun,
    G2TwoSylowPCGenerators.pc3Fun,
    G2TwoSylowPCGenerators.pc4Fun,
    G2TwoSylowPCGenerators.pc6Fun,
    InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add2]
  all_goals simp [Bool.xor_left_comm, Bool.xor_comm]

end InfoGeometry.Algebra.Zorn.G2TwoPCConjugation
