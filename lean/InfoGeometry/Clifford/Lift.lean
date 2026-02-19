import InfoGeometry.Clifford.Cl11
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.Tactic

section KreinClifford

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Split quadratic form on `ℝ × ℝ`: `a^2 - b^2`. -/
noncomputable def Q11 : QuadraticForm ℝ (ℝ × ℝ) :=
  QuadraticMap.linMulLin (LinearMap.fst ℝ ℝ ℝ) (LinearMap.fst ℝ ℝ ℝ)
    - QuadraticMap.linMulLin (LinearMap.snd ℝ ℝ ℝ) (LinearMap.snd ℝ ℝ ℝ)

@[simp] lemma Q11_apply (v : ℝ × ℝ) : Q11 v = v.1 * v.1 - v.2 * v.2 := by
  simp [Q11]

/-- `I^2 = -Id` for `I := J ∘ ε`. -/
lemma complexI_sq_neg_id_lift :
    (complexI (E := E)).comp (complexI (E := E))
      = -(ContinuousLinearMap.id ℝ (DoubledSpace E)) := by
  apply ContinuousLinearMap.ext
  intro v
  rcases v with ⟨x, y⟩
  simp [complexI, modularJ, spectralEpsilon]

/-- `J I = - I J` for `J` and `I := J ∘ ε`. -/
lemma modularJ_complexI_anticommute :
    (modularJ (E := E)).comp (complexI (E := E))
      = -((complexI (E := E)).comp (modularJ (E := E))) := by
  apply ContinuousLinearMap.ext
  intro v
  rcases v with ⟨x, y⟩
  simp [complexI, modularJ, spectralEpsilon]

/-- Linear map `(a,b) ↦ a • J + b • I` into endomorphisms of `E × E`. -/
noncomputable def cl11RepLin :
    (ℝ × ℝ) →ₗ[ℝ] (DoubledSpace E →L[ℝ] DoubledSpace E) where
  toFun v := v.1 • modularJ (E := E) + v.2 • complexI (E := E)
  map_add' := by
    intro u v
    simp [add_smul, add_assoc, add_left_comm]
  map_smul' := by
    intro a v
    simp [smul_add, smul_smul]

lemma cl11RepLin_apply_pair (a b : ℝ) (x y : E) :
    cl11RepLin (E := E) (a, b) (x, y) = ((a - b) • y, (a + b) • x) := by
  ext <;> simp [cl11RepLin, complexI, modularJ, spectralEpsilon, sub_eq_add_neg, add_smul]

/-- Key Clifford relation for `cl11RepLin`: `(aJ + bI)^2 = (a^2 - b^2) • Id`. -/
lemma cl11RepLin_sq (v : ℝ × ℝ) :
    (cl11RepLin (E := E) v) * (cl11RepLin (E := E) v)
      = algebraMap ℝ (DoubledSpace E →L[ℝ] DoubledSpace E) (Q11 v) := by
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
    _ = (algebraMap ℝ (DoubledSpace E →L[ℝ] DoubledSpace E) (Q11 (a, b))) (x, y) := by
          simp [Q11_apply, Algebra.algebraMap_eq_smul_one]

/-- The induced algebra hom `Cl(1,1) → End(E × E)`. -/
noncomputable def cl11Rep :
    CliffordAlgebra Q11 →ₐ[ℝ] (DoubledSpace E →L[ℝ] DoubledSpace E) :=
  CliffordAlgebra.lift Q11 ⟨cl11RepLin (E := E), cl11RepLin_sq (E := E)⟩

@[simp] lemma cl11Rep_ι_apply (v : ℝ × ℝ) :
    cl11Rep (E := E) (CliffordAlgebra.ι Q11 v) = cl11RepLin (E := E) v := by
  simp [cl11Rep]

@[simp] lemma cl11Rep_ι_one_zero :
    cl11Rep (E := E) (CliffordAlgebra.ι Q11 (1, 0)) = modularJ (E := E) := by
  simp [cl11RepLin]

@[simp] lemma cl11Rep_ι_zero_one :
    cl11Rep (E := E) (CliffordAlgebra.ι Q11 (0, 1)) = complexI (E := E) := by
  simp [cl11RepLin]

end KreinClifford
