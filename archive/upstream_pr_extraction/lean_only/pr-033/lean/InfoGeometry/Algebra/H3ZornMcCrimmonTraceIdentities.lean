import InfoGeometry.Algebra.H3ZornMcCrimmonLinearization

/-!
# McCrimmon trace identities for the real split Albert algebra

This module continues the theorem ladder in Kevin McCrimmon,
*The Freudenthal--Springer--Tits constructions of exceptional Jordan
algebras*, Trans. AMS 139 (1969), 495--510, proving identities
(13), (15), (16), (17), and (18) from the already verified cubic data.
-/

namespace InfoGeometry.Algebra.H3Zorn

private theorem adjointQuad_add_real (X Y : H3Zorn ℝ) :
    adjointQuad (X + Y) = adjointQuad X + crossProduct X Y + adjointQuad Y := by
  simp only [crossProduct]
  abel

/-- McCrimmon's identity (13), the Euler relation `T(X#,X) = 3 N(X)`. -/
theorem mccrimmon_identity_13 (X : H3Zorn ℝ) :
    traceBilin (adjointQuad X) X = 3 * normCubic X := by
  have h := normCubic_add X X
  rw [show X + X = (2 : ℝ) • X by module, normCubic_smul] at h
  norm_num at h
  linarith

/-- McCrimmon's identity (15): the full polarization of the cubic norm is
symmetric in its three arguments. -/
theorem mccrimmon_identity_15 (X Y Z : H3Zorn ℝ) :
    traceBilin (crossProduct X Y) Z =
      traceBilin X (crossProduct Y Z) := by
  have hl := normCubic_add (X + Y) Z
  have hr := normCubic_add X (Y + Z)
  rw [normCubic_add X Y, adjointQuad_add_real,
    traceBilin_add_left, traceBilin_add_left] at hl
  rw [normCubic_add Y Z, adjointQuad_add_real] at hr
  simp only [traceBilin_add_left, traceBilin_add_right] at hr
  have h :
      normCubic X + normCubic Y + traceBilin (adjointQuad X) Y +
          traceBilin (adjointQuad Y) X + normCubic Z +
          ((traceBilin (adjointQuad X) Z + traceBilin (crossProduct X Y) Z) +
            traceBilin (adjointQuad Y) Z) +
          traceBilin (adjointQuad Z) (X + Y) =
        normCubic X +
          (normCubic Y + normCubic Z + traceBilin (adjointQuad Y) Z +
            traceBilin (adjointQuad Z) Y) +
          (traceBilin (adjointQuad X) Y + traceBilin (adjointQuad X) Z) +
          ((traceBilin (adjointQuad Y) X + traceBilin (crossProduct Y Z) X) +
            traceBilin (adjointQuad Z) X) := by
    calc
      _ = normCubic ((X + Y) + Z) := hl.symm
      _ = normCubic (X + (Y + Z)) := by rw [add_assoc]
      _ = _ := hr
  simp only [traceBilin_add_right] at h
  rw [traceBilin_symm X (crossProduct Y Z)]
  linarith

/-- McCrimmon's identity (16), the linear trace of a cross product. -/
theorem mccrimmon_identity_16 (X Y : H3Zorn ℝ) :
    linearTrace (crossProduct X Y) =
      linearTrace X * linearTrace Y - traceBilin X Y := by
  have h := mccrimmon_identity_15 X Y (1 : H3Zorn ℝ)
  rw [traceBilin_one, crossProduct_one] at h
  rw [show linearTrace Y • (1 : H3Zorn ℝ) - Y =
    linearTrace Y • (1 : H3Zorn ℝ) + (-1 : ℝ) • Y by module] at h
  simp only [traceBilin_add_right, traceBilin_smul_right, traceBilin_one] at h
  rw [h]
  ring

/-- McCrimmon's identity (17), the contraction `U_X(X × Y)`. -/
theorem mccrimmon_identity_17 (X Y : H3Zorn ℝ) :
    U X (crossProduct X Y) =
      traceBilin (adjointQuad X) Y • X - normCubic X • Y := by
  have ht := mccrimmon_identity_15 X X Y
  rw [crossProduct_self, traceBilin_smul_left] at ht
  rw [U, ← ht, mccrimmon_identity_10]
  module

/-- McCrimmon's identity (18), the cross product of an element and its
adjoint. -/
theorem mccrimmon_identity_18 (X : H3Zorn ℝ) :
    crossProduct (adjointQuad X) X =
      (linearTrace (adjointQuad X) * linearTrace X - normCubic X) •
          (1 : H3Zorn ℝ) -
        linearTrace (adjointQuad X) • X -
        linearTrace X • adjointQuad X := by
  have h := mccrimmon_identity_10 X (1 : H3Zorn ℝ)
  rw [crossProduct_one] at h
  rw [show linearTrace X • (1 : H3Zorn ℝ) - X =
    linearTrace X • (1 : H3Zorn ℝ) + (-1 : ℝ) • X by module] at h
  rw [crossProduct_add_right, crossProduct_smul_right,
    crossProduct_smul_right, crossProduct_one, traceBilin_one] at h
  have hs := congrArg
    (fun W : H3Zorn ℝ =>
      linearTrace X • (linearTrace (adjointQuad X) • (1 : H3Zorn ℝ) - adjointQuad X) - W)
    h
  convert hs using 1 <;> module

end InfoGeometry.Algebra.H3Zorn
