import sys
import re

with open("lean/InfoGeometry/Canonical/DrazinCoreFlow.lean", "r") as f:
    content = f.read()

# Target 1
content = content.replace("""theorem commute_projection
    (h : IsDrazinInverse a b k) :
    Commute a (projection a b) := by
  unfold Commute
  simpa using (projection_mul_eq_mul_projection (h := h)).symm""", """theorem commute_projection
    (h : IsDrazinInverse a b k) :
    Commute a (projection a b) := by
  unfold Commute SemiconjBy
  exact (projection_mul_eq_mul_projection (h := h)).symm""")

# Target 2
content = content.replace("""theorem commute_complementaryProjection
    (h : IsDrazinInverse a b k) :
    Commute a (complementaryProjection a b) := by
  unfold Commute complementaryProjection projection
  have hproj : a * (a * b) = (a * b) * a := by
    simpa [projection] using (projection_mul_eq_mul_projection (h := h)).symm""", """theorem commute_complementaryProjection
    (h : IsDrazinInverse a b k) :
    Commute a (complementaryProjection a b) := by
  unfold Commute SemiconjBy complementaryProjection projection
  have hproj : a * (a * b) = (a * b) * a := by
    exact (projection_mul_eq_mul_projection (h := h)).symm""")

# Target 3
content = content.replace("""    (a * complementaryProjection a b) ^ (m + 1)
        = a ^ (m + 1) * complementaryProjection a b ^ (m + 1) := by
            simpa using hcomm.mul_pow (m + 1)""", """    (a * complementaryProjection a b) ^ (m + 1)
        = a ^ (m + 1) * complementaryProjection a b ^ (m + 1) := by
            exact hcomm.mul_pow (m + 1)""")

# Target 4
content = content.replace("""@[rep_depth operator, simp] theorem A_mul_drazinCoreProj_eq_drazinCoreProj_mul_A :
    CIK.A * CIK.drazinCoreProj = CIK.drazinCoreProj * CIK.A := by
  change CIK.A * IsDrazinInverse.projection CIK.A CIK.A_D =
      IsDrazinInverse.projection CIK.A CIK.A_D * CIK.A
  simpa using (IsDrazinInverse.projection_mul_eq_mul_projection (h := CIK.hDrazin)).symm""", """@[rep_depth operator, simp] theorem A_mul_drazinCoreProj_eq_drazinCoreProj_mul_A :
    CIK.A * CIK.drazinCoreProj = CIK.drazinCoreProj * CIK.A := by
  change CIK.A * IsDrazinInverse.projection CIK.A CIK.A_D =
      IsDrazinInverse.projection CIK.A CIK.A_D * CIK.A
  exact (IsDrazinInverse.projection_mul_eq_mul_projection (h := CIK.hDrazin)).symm""")

# Target 5
content = content.replace("""@[rep_depth operator, simp] theorem A_mul_nilpotentProj_eq_nilpotentProj_mul_A :
    CIK.A * CIK.nilpotentProj = CIK.nilpotentProj * CIK.A := by
  change CIK.A * IsDrazinInverse.complementaryProjection CIK.A CIK.A_D =
      IsDrazinInverse.complementaryProjection CIK.A CIK.A_D * CIK.A
  simpa using (IsDrazinInverse.commute_complementaryProjection (h := CIK.hDrazin)).eq""", """@[rep_depth operator, simp] theorem A_mul_nilpotentProj_eq_nilpotentProj_mul_A :
    CIK.A * CIK.nilpotentProj = CIK.nilpotentProj * CIK.A := by
  change CIK.A * IsDrazinInverse.complementaryProjection CIK.A CIK.A_D =
      IsDrazinInverse.complementaryProjection CIK.A CIK.A_D * CIK.A
  exact (IsDrazinInverse.commute_complementaryProjection (h := CIK.hDrazin)).eq""")

# Target 6
content = content.replace("""@[rep_depth operator] theorem A_pow_mul_nilpotentProj_eq_zero_of_index_le
    {m : ℕ} (hm : CIK.drazinIndex ≤ m) :
    CIK.A ^ m * CIK.nilpotentProj = 0 := by
  change CIK.A ^ m * IsDrazinInverse.complementaryProjection CIK.A CIK.A_D = 0
  simpa using
    IsDrazinInverse.pow_mul_complementaryProjection_eq_zero_of_le
      (h := CIK.hDrazin) hm""", """@[rep_depth operator] theorem A_pow_mul_nilpotentProj_eq_zero_of_index_le
    {m : ℕ} (hm : CIK.drazinIndex ≤ m) :
    CIK.A ^ m * CIK.nilpotentProj = 0 := by
  change CIK.A ^ m * IsDrazinInverse.complementaryProjection CIK.A CIK.A_D = 0
  exact
    IsDrazinInverse.pow_mul_complementaryProjection_eq_zero_of_le
      (h := CIK.hDrazin) hm""")

# Target 7
content = content.replace("""  have hnil :
      (IsDrazinInverse.nilpotent CIK.A CIK.A_D) ^ (m + 1) = 0 :=
    IsDrazinInverse.nilpotent_pow_succ_eq_zero_of_le
      (a := CIK.A) (b := CIK.A_D) (k := CIK.drazinIndex) (m := m) (h := CIK.hDrazin) hm
  rw [IsDrazinInverse.nilpotent_eq_complementaryProjection_mul (h := CIK.hDrazin)] at hnil
  simpa [CertifiedInverseKernel.nilpotentProj, CertifiedInverseKernel.spectralComplementaryProjector] using hnil""", """  have hnil :
      (IsDrazinInverse.nilpotent CIK.A CIK.A_D) ^ (m + 1) = 0 :=
    IsDrazinInverse.nilpotent_pow_succ_eq_zero_of_le
      (a := CIK.A) (b := CIK.A_D) (k := CIK.drazinIndex) (m := m) (h := CIK.hDrazin) hm
  rw [IsDrazinInverse.nilpotent_eq_complementaryProjection_mul (h := CIK.hDrazin)] at hnil
  change (CIK.nilpotentProj * CIK.A) ^ (m + 1) = 0 at hnil
  exact hnil""")

with open("lean/InfoGeometry/Canonical/DrazinCoreFlow.lean", "w") as f:
    f.write(content)

