import InfoGeometry.Clifford.SplitQ11
import InfoGeometry.Krein.DoubledSpace
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.Tactic

namespace InfoGeometry.Krein

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma modularJ_complexI_anticommute :
    (modularJ (E := E)).comp (complexI (E := E)) = -((complexI (E := E)).comp (modularJ (E := E))) := by
  apply ContinuousLinearMap.ext
  intro v
  rcases v with ⟨x, y⟩
  simp [complexI, modularJ, spectralEpsilon]

noncomputable def cl11RepLin :
    (ℝ × ℝ) →ₗ[ℝ] (DoubledSpace E →L[ℝ] DoubledSpace E) where
  toFun v := v.1 • modularJ (E := E) + v.2 • complexI (E := E)
  map_add' := by intro u v; simp [add_smul, add_assoc, add_left_comm]
  map_smul' := by intro a v; simp [smul_add, smul_smul]

lemma cl11RepLin_apply_pair (a b : ℝ) (x y : E) :
    cl11RepLin (E := E) (a, b) (x, y) = ((a - b) • y, (a + b) • x) := by
  ext <;> simp [cl11RepLin, complexI, modularJ, spectralEpsilon, sub_eq_add_neg, add_smul]

lemma cl11RepLin_sq (v : ℝ × ℝ) :
    (cl11RepLin (E := E) v) * (cl11RepLin (E := E) v)
      = algebraMap ℝ (DoubledSpace E →L[ℝ] DoubledSpace E) (InfoGeometry.Clifford.splitQ11 v) := by
  rcases v with ⟨a, b⟩
  have hab1 : (a - b) * (a + b) = a * a - b * b := by ring
  have hab2 : (a + b) * (a - b) = a * a - b * b := by ring
  apply ContinuousLinearMap.ext
  intro w
  rcases w with ⟨x, y⟩
  calc
    ((cl11RepLin (E := E) (a, b)) * (cl11RepLin (E := E) (a, b))) (x, y)
        = cl11RepLin (E := E) (a, b) ((a - b) • y, (a + b) • x) := by
            simp [cl11RepLin_apply_pair]
    _ = ((a - b) • ((a + b) • x), (a + b) • ((a - b) • y)) := by
            simp [cl11RepLin_apply_pair]
    _ = ((a * a - b * b) • x, (a * a - b * b) • y) := by
            simp [smul_smul, hab1, hab2]
    _ = (algebraMap ℝ (DoubledSpace E →L[ℝ] DoubledSpace E) (InfoGeometry.Clifford.splitQ11 (a, b))) (x, y) := by
            simp [Algebra.algebraMap_eq_smul_one]

noncomputable def cl11Rep :
    CliffordAlgebra InfoGeometry.Clifford.splitQ11 →ₐ[ℝ] (DoubledSpace E →L[ℝ] DoubledSpace E) :=
  CliffordAlgebra.lift InfoGeometry.Clifford.splitQ11 ⟨cl11RepLin (E := E), cl11RepLin_sq (E := E)⟩

@[simp] lemma cl11Rep_ι_apply (v : ℝ × ℝ) :
    cl11Rep (E := E) (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 v) = cl11RepLin (E := E) v := by
  simp [cl11Rep]

lemma cl11Rep_ι_one_zero :
    cl11Rep (E := E) (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (1, 0)) = modularJ (E := E) := by
  simp [cl11RepLin]

lemma cl11Rep_ι_zero_one :
    cl11Rep (E := E) (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (0, 1)) = complexI (E := E) := by
  simp [cl11RepLin]

lemma cl11Rep_ι_one_zero_sq :
    cl11Rep (E := E) (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (1, 0))
      * cl11Rep (E := E) (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (1, 0))
      = ContinuousLinearMap.id ℝ (DoubledSpace E) := by
  simpa [InfoGeometry.Clifford.splitQ11_apply] using (cl11RepLin_sq (E := E) (1, 0))

lemma cl11Rep_pseudoscalar :
    cl11Rep (E := E)
      (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (1, 0)
        * CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (0, 1))
      = spectralEpsilon (E := E) := by
  rw [map_mul, cl11Rep_ι_one_zero, cl11Rep_ι_zero_one]
  apply ContinuousLinearMap.ext
  intro v
  rcases v with ⟨x, y⟩
  simp [complexI, modularJ, spectralEpsilon]

end InfoGeometry.Krein
