import InfoGeometry.Algebra.H3ZornCubicOperators
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# McCrimmon linearizations for the real split Albert algebra

This module proves identities (10)--(12) from Kevin McCrimmon,
*The Freudenthal--Springer--Tits constructions of exceptional Jordan
algebras*, Trans. AMS 139 (1969), 495--510, DOI
`10.1090/s0002-9947-1969-0238916-9`.

The coefficients are extracted from the global adjoint identity by finite
differences over `ℝ`. No cancellation or nonvanishing hypothesis on the
split cubic norm is used.
-/

namespace InfoGeometry.Algebra.H3Zorn

private theorem adjointQuad_add_real (A B : H3Zorn ℝ) :
    adjointQuad (A + B) = adjointQuad A + crossProduct A B + adjointQuad B := by
  simp only [crossProduct]
  abel

private theorem adjointQuad_line_real (r : ℝ) (X Y : H3Zorn ℝ) :
    adjointQuad (X + r • Y) =
      adjointQuad X + r • crossProduct X Y + r ^ 2 • adjointQuad Y := by
  rw [adjointQuad_add_real, adjointQuad_smul, crossProduct_smul_right]

private theorem master_linearization (r : ℝ) (X Y : H3Zorn ℝ) :
    adjointQuad (adjointQuad X) +
        r • crossProduct (adjointQuad X) (crossProduct X Y) +
        r ^ 2 • (adjointQuad (crossProduct X Y) +
          crossProduct (adjointQuad X) (adjointQuad Y)) +
        r ^ 3 • crossProduct (crossProduct X Y) (adjointQuad Y) +
        r ^ 4 • adjointQuad (adjointQuad Y) =
      normCubic X • X +
        r • (normCubic X • Y + traceBilin (adjointQuad X) Y • X) +
        r ^ 2 • (traceBilin (adjointQuad X) Y • Y +
          traceBilin (adjointQuad Y) X • X) +
        r ^ 3 • (traceBilin (adjointQuad Y) X • Y + normCubic Y • X) +
        r ^ 4 • (normCubic Y • Y) := by
  have h := adjointQuad_adjointQuad (X + r • Y)
  rw [adjointQuad_line_real] at h
  rw [adjointQuad_add_real, adjointQuad_add_real,
    adjointQuad_smul, adjointQuad_smul] at h
  rw [crossProduct_add_left] at h
  simp only [crossProduct_smul_left, crossProduct_smul_right] at h
  rw [normCubic_line] at h
  convert h using 1 <;>
    simp only [pow_succ, add_smul, smul_add, mul_smul] <;>
    module

/-- McCrimmon's identity (10): the part of the linearized adjoint identity
which is homogeneous of bidegree `(3,1)` in `(X,Y)`. -/
theorem mccrimmon_identity_10 (X Y : H3Zorn ℝ) :
    crossProduct (adjointQuad X) (crossProduct X Y) =
      normCubic X • Y + traceBilin (adjointQuad X) Y • X := by
  have h1 := master_linearization (1 : ℝ) X Y
  have hm1 := master_linearization (-1 : ℝ) X Y
  have h2 := master_linearization (2 : ℝ) X Y
  have hm2 := master_linearization (-2 : ℝ) X Y
  rw [adjointQuad_adjointQuad X, adjointQuad_adjointQuad Y] at h1 hm1 h2 hm2
  norm_num at h1 hm1 h2 hm2
  have ha := congrArg (fun W : H3Zorn ℝ => (2 / 3 : ℝ) • W) h1
  have hb := congrArg (fun W : H3Zorn ℝ => (2 / 3 : ℝ) • W) hm1
  have hc := congrArg (fun W : H3Zorn ℝ => (1 / 12 : ℝ) • W) h2
  have hd := congrArg (fun W : H3Zorn ℝ => (1 / 12 : ℝ) • W) hm2
  have hab := congrArg₂ (fun A B : H3Zorn ℝ => A - B) ha hb
  have hdc := congrArg₂ (fun A B : H3Zorn ℝ => A - B) hd hc
  have he := congrArg₂ (fun A B : H3Zorn ℝ => A + B) hab hdc
  convert he using 1 <;> module

/-- McCrimmon's identity (11): the part of the linearized adjoint identity
which is homogeneous of bidegree `(2,2)` in `(X,Y)`. -/
theorem mccrimmon_identity_11 (X Y : H3Zorn ℝ) :
    crossProduct (adjointQuad X) (adjointQuad Y) +
        adjointQuad (crossProduct X Y) =
      traceBilin (adjointQuad X) Y • Y +
        traceBilin (adjointQuad Y) X • X := by
  have h1 := master_linearization (1 : ℝ) X Y
  have hm1 := master_linearization (-1 : ℝ) X Y
  rw [adjointQuad_adjointQuad X, adjointQuad_adjointQuad Y] at h1 hm1
  norm_num at h1 hm1
  have ha := congrArg (fun W : H3Zorn ℝ => (1 / 2 : ℝ) • W) h1
  have hb := congrArg (fun W : H3Zorn ℝ => (1 / 2 : ℝ) • W) hm1
  have hc := congrArg₂ (fun A B : H3Zorn ℝ => A + B) ha hb
  have hc0 := congrArg (fun W : H3Zorn ℝ => W - normCubic X • X) hc
  convert hc0 using 1 <;> module

/-- McCrimmon's identity (12), obtained by polarizing identity (11) in `Y`. -/
theorem mccrimmon_identity_12 (X Y Z : H3Zorn ℝ) :
    crossProduct (adjointQuad X) (crossProduct Y Z) +
        crossProduct (crossProduct X Y) (crossProduct X Z) =
      traceBilin (adjointQuad X) Y • Z +
        traceBilin (adjointQuad X) Z • Y +
        traceBilin (crossProduct Y Z) X • X := by
  have h := mccrimmon_identity_11 X (Y + Z)
  have hy := mccrimmon_identity_11 X Y
  have hz := mccrimmon_identity_11 X Z
  rw [adjointQuad_add_real] at h
  rw [crossProduct_add_right X Y Z] at h
  rw [adjointQuad_add_real] at h
  simp only [crossProduct_add_right, traceBilin_add_right,
    traceBilin_add_left, add_smul] at h
  have hhy := congrArg₂ (fun A B : H3Zorn ℝ => A - B) h hy
  have hc := congrArg₂ (fun A B : H3Zorn ℝ => A - B) hhy hz
  convert hc using 1 <;> module

end InfoGeometry.Algebra.H3Zorn
