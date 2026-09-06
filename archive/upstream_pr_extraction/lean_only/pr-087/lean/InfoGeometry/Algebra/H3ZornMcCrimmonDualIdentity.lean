import InfoGeometry.Algebra.H3ZornMcCrimmonTraceIdentities

/-!
# McCrimmon's dual polarized adjoint identity

This module proves the hard identity (19) from Kevin McCrimmon,
*The Freudenthal--Springer--Tits constructions of exceptional Jordan
algebras*, Trans. AMS 139 (1969), 495--510. The proof follows McCrimmon's
characteristic-free calculation: fully polarize identity (18), then specialize
one argument to `X#`. It never cancels the split cubic norm.
-/

namespace InfoGeometry.Algebra.H3Zorn

private theorem adjointQuad_add_real (X Y : H3Zorn ℝ) :
    adjointQuad (X + Y) = adjointQuad X + crossProduct X Y + adjointQuad Y := by
  simp only [crossProduct]
  abel

/-- The full polarization of McCrimmon's identity (18). -/
theorem mccrimmon_identity_18_full_polarization (X Y Z : H3Zorn ℝ) :
    crossProduct (crossProduct X Y) Z +
        crossProduct (crossProduct X Z) Y +
        crossProduct (crossProduct Y Z) X =
      (linearTrace (crossProduct X Y) * linearTrace Z +
          linearTrace (crossProduct X Z) * linearTrace Y +
          linearTrace (crossProduct Y Z) * linearTrace X -
          traceBilin (crossProduct X Y) Z) • (1 : H3Zorn ℝ) -
        linearTrace (crossProduct X Y) • Z -
        linearTrace (crossProduct X Z) • Y -
        linearTrace (crossProduct Y Z) • X -
        linearTrace X • crossProduct Y Z -
        linearTrace Y • crossProduct X Z -
        linearTrace Z • crossProduct X Y := by
  have h :
      crossProduct (adjointQuad (X + Y + Z)) (X + Y + Z) -
          crossProduct (adjointQuad (X + Y)) (X + Y) -
          crossProduct (adjointQuad (X + Z)) (X + Z) -
          crossProduct (adjointQuad (Y + Z)) (Y + Z) +
          crossProduct (adjointQuad X) X +
          crossProduct (adjointQuad Y) Y +
          crossProduct (adjointQuad Z) Z =
        ((linearTrace (adjointQuad (X + Y + Z)) * linearTrace (X + Y + Z) -
              normCubic (X + Y + Z)) • (1 : H3Zorn ℝ) -
            linearTrace (adjointQuad (X + Y + Z)) • (X + Y + Z) -
            linearTrace (X + Y + Z) • adjointQuad (X + Y + Z)) -
        ((linearTrace (adjointQuad (X + Y)) * linearTrace (X + Y) -
              normCubic (X + Y)) • (1 : H3Zorn ℝ) -
            linearTrace (adjointQuad (X + Y)) • (X + Y) -
            linearTrace (X + Y) • adjointQuad (X + Y)) -
        ((linearTrace (adjointQuad (X + Z)) * linearTrace (X + Z) -
              normCubic (X + Z)) • (1 : H3Zorn ℝ) -
            linearTrace (adjointQuad (X + Z)) • (X + Z) -
            linearTrace (X + Z) • adjointQuad (X + Z)) -
        ((linearTrace (adjointQuad (Y + Z)) * linearTrace (Y + Z) -
              normCubic (Y + Z)) • (1 : H3Zorn ℝ) -
            linearTrace (adjointQuad (Y + Z)) • (Y + Z) -
            linearTrace (Y + Z) • adjointQuad (Y + Z)) +
        ((linearTrace (adjointQuad X) * linearTrace X - normCubic X) •
              (1 : H3Zorn ℝ) -
            linearTrace (adjointQuad X) • X - linearTrace X • adjointQuad X) +
        ((linearTrace (adjointQuad Y) * linearTrace Y - normCubic Y) •
              (1 : H3Zorn ℝ) -
            linearTrace (adjointQuad Y) • Y - linearTrace Y • adjointQuad Y) +
        ((linearTrace (adjointQuad Z) * linearTrace Z - normCubic Z) •
              (1 : H3Zorn ℝ) -
            linearTrace (adjointQuad Z) • Z - linearTrace Z • adjointQuad Z) := by
    rw [mccrimmon_identity_18 (X + Y + Z), mccrimmon_identity_18 (X + Y),
      mccrimmon_identity_18 (X + Z), mccrimmon_identity_18 (Y + Z),
      mccrimmon_identity_18 X, mccrimmon_identity_18 Y, mccrimmon_identity_18 Z]
  simp only [adjointQuad_add_real, crossProduct_add_left, crossProduct_add_right,
    linearTrace_add, normCubic_add, traceBilin_add_left, traceBilin_add_right,
    add_smul, smul_add] at h
  convert h using 1 <;> module

/-- McCrimmon's identity (19), the dual polarized adjoint identity. -/
theorem mccrimmon_identity_19 (X Y : H3Zorn ℝ) :
    crossProduct X (crossProduct (adjointQuad X) Y) =
      normCubic X • Y + traceBilin X Y • adjointQuad X := by
  have h := mccrimmon_identity_18_full_polarization X (adjointQuad X) Y
  have h18 : crossProduct (adjointQuad X) X =
      (linearTrace (adjointQuad X) * linearTrace X - normCubic X) •
          (1 : H3Zorn ℝ) +
        (-linearTrace (adjointQuad X)) • X +
        (-linearTrace X) • adjointQuad X := by
    rw [mccrimmon_identity_18 X]
    module
  rw [crossProduct_symm X (adjointQuad X), h18] at h
  simp only [crossProduct_add_left,
    crossProduct_smul_left, linearTrace_add,
    linearTrace_smul, traceBilin_add_left,
    traceBilin_smul_left, add_smul, smul_add] at h
  rw [crossProduct_symm (1 : H3Zorn ℝ) Y, crossProduct_one Y,
    traceBilin_symm (1 : H3Zorn ℝ) Y, traceBilin_one Y] at h
  have ht1 : linearTrace (1 : H3Zorn ℝ) = 3 := by
    change (1 : ℝ) + 1 + 1 = 3
    norm_num
  rw [ht1] at h
  rw [crossProduct_symm (crossProduct X Y) (adjointQuad X),
    mccrimmon_identity_10 X Y,
    crossProduct_symm (crossProduct (adjointQuad X) Y) X] at h
  rw [mccrimmon_identity_16 X Y, mccrimmon_identity_16 (adjointQuad X) Y] at h
  let E : H3Zorn ℝ :=
    (linearTrace (adjointQuad X) * linearTrace X - normCubic X) •
        (linearTrace Y • (1 : H3Zorn ℝ) - Y) +
      (-linearTrace (adjointQuad X)) • crossProduct X Y +
      (-linearTrace X) • crossProduct (adjointQuad X) Y +
      (normCubic X • Y + traceBilin (adjointQuad X) Y • X)
  have hh := congrArg (fun W : H3Zorn ℝ => W - E) h
  dsimp [E] at hh
  convert hh using 1 <;> module

end InfoGeometry.Algebra.H3Zorn
