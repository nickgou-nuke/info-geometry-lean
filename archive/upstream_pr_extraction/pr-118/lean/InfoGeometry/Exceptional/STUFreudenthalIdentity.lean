import InfoGeometry.Exceptional.STUDatum

/-!
# The concrete STU Freudenthal adjoint identity

This is the finite cubic identity for the existing diagonal STU datum.  It is
the precise algebraic prerequisite for a later Freudenthal construction; it
does not assert a full Albert or exceptional Lie algebra model.
-/

noncomputable section

namespace InfoGeometry.Exceptional.STUDatum

theorem stuAdjointQuad_adjointQuad (x : STUCarrier) :
    stuAdjointQuad (stuAdjointQuad x) =
      stuNormCubic x • x := by
  funext i
  fin_cases i <;>
    simp [stuAdjointQuad, stuNormCubic, Pi.smul_apply]
    <;> ring

end InfoGeometry.Exceptional.STUDatum
