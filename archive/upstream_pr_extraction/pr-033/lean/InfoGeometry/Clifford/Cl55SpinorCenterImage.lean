import InfoGeometry.Clifford.Cl55SpinorRepresentationGeneration

namespace InfoGeometry.Clifford.Clifford55

open InfoGeometry.Clifford.SpinorRep

/-!
The spinor representation is already proved surjective by the recursive
gamma-generation owner.  This file records the exact consequence available
without yet asserting faithfulness: a central `Cl(5,5)` element has scalar
matrix image.
-/

theorem cl55_center_image_scalar
    {z : Cl55} (hz : z ∈ Subalgebra.center ℝ Cl55) :
    ∃ r : ℝ,
      cl55SpinorRepresentation z =
        algebraMap ℝ (SpinorMatrix 5) r := by
  have hcenter : cl55SpinorRepresentation z ∈
      Set.center (SpinorMatrix 5) := by
    rw [Set.mem_center_iff]
    refine ⟨?_, ?_, ?_⟩
    · intro y
      obtain ⟨x, rfl⟩ := cl55SpinorRepresentation_surjective y
      have hzx := (Subalgebra.mem_center_iff.mp hz) x
      simpa only [map_mul] using (congrArg cl55SpinorRepresentation hzx).symm
    · intro b c
      simp only [mul_assoc]
    · intro a b
      simp only [mul_assoc]
  have hscalar : cl55SpinorRepresentation z ∈
      Set.range (Matrix.scalar (Fin (2 ^ 5))) := by
    rw [← Matrix.center_eq_range ℝ]
    exact hcenter
  rcases hscalar with ⟨r, hr⟩
  refine ⟨r, ?_⟩
  rw [← hr]
  rfl

end InfoGeometry.Clifford.Clifford55
