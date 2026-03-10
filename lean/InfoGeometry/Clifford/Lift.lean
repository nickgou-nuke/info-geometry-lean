import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Clifford.SplitQ11
import InfoGeometry.Krein.Representation
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic

/-- Backward-compatible alias to the canonical split form. -/
noncomputable abbrev Q11 : QuadraticForm ℝ (ℝ × ℝ) := InfoGeometry.Clifford.splitQ11

@[simp] lemma Q11_apply (v : ℝ × ℝ) : Q11 v = v.1 * v.1 - v.2 * v.2 := by
  exact InfoGeometry.Clifford.splitQ11_apply v

section KreinClifford

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `J I = - I J` for `J` and `I := J ∘ ε`. -/
lemma modularJ_complexI_anticommute :
    (modularJ (E := E)).comp (complexI (E := E))
      = -((complexI (E := E)).comp (modularJ (E := E))) := by
  simpa using (InfoGeometry.Krein.modularJ_complexI_anticommute (E := E))

/-- Linear map `(a,b) ↦ a • J + b • I` into endomorphisms of `E × E`. -/
noncomputable abbrev cl11RepLin :
    (ℝ × ℝ) →ₗ[ℝ] (DoubledSpace E →L[ℝ] DoubledSpace E) :=
  InfoGeometry.Krein.cl11RepLin (E := E)

lemma cl11RepLin_apply_pair (a b : ℝ) (x y : E) :
    cl11RepLin (E := E) (a, b) (x, y) = ((a - b) • y, (a + b) • x) := by
  simpa using (InfoGeometry.Krein.cl11RepLin_apply_pair (E := E) a b x y)

/-- Key Clifford relation for `cl11RepLin`: `(aJ + bI)^2 = (a^2 - b^2) • Id`. -/
lemma cl11RepLin_sq (v : ℝ × ℝ) :
    (cl11RepLin (E := E) v) * (cl11RepLin (E := E) v)
      = algebraMap ℝ (DoubledSpace E →L[ℝ] DoubledSpace E) (Q11 v) := by
  simpa [Q11] using (InfoGeometry.Krein.cl11RepLin_sq (E := E) v)

/-- The induced algebra hom `Cl(1,1) → End(E × E)`. -/
noncomputable abbrev cl11Rep :
    CliffordAlgebra Q11 →ₐ[ℝ] (DoubledSpace E →L[ℝ] DoubledSpace E) :=
  InfoGeometry.Krein.cl11Rep (E := E)

@[simp] lemma cl11Rep_ι_apply (v : ℝ × ℝ) :
    cl11Rep (E := E) (CliffordAlgebra.ι Q11 v) = cl11RepLin (E := E) v := by
  simpa [Q11, cl11Rep, cl11RepLin] using (InfoGeometry.Krein.cl11Rep_ι_apply (E := E) v)

lemma cl11Rep_ι_one_zero :
    cl11Rep (E := E) (CliffordAlgebra.ι Q11 (1, 0)) = modularJ (E := E) := by
  simpa [Q11, cl11Rep, cl11RepLin] using (InfoGeometry.Krein.cl11Rep_ι_one_zero (E := E))

lemma cl11Rep_ι_zero_one :
    cl11Rep (E := E) (CliffordAlgebra.ι Q11 (0, 1)) = complexI (E := E) := by
  simpa [Q11, cl11Rep, cl11RepLin] using (InfoGeometry.Krein.cl11Rep_ι_zero_one (E := E))

/-- Image of the first Clifford basis vector squares to `+Id`. -/
lemma cl11Rep_ι_one_zero_sq :
    cl11Rep (E := E) (CliffordAlgebra.ι Q11 (1, 0))
      * cl11Rep (E := E) (CliffordAlgebra.ι Q11 (1, 0))
      = ContinuousLinearMap.id ℝ (DoubledSpace E) := by
  simpa [Q11, cl11Rep, cl11RepLin] using (InfoGeometry.Krein.cl11Rep_ι_one_zero_sq (E := E))

/-- Image of the second Clifford basis vector squares to `-Id`. -/
lemma cl11Rep_ι_zero_one_sq :
    cl11Rep (E := E) (CliffordAlgebra.ι Q11 (0, 1))
      * cl11Rep (E := E) (CliffordAlgebra.ι Q11 (0, 1))
      = -(ContinuousLinearMap.id ℝ (DoubledSpace E)) := by
  simpa [Q11, cl11Rep, cl11RepLin] using (InfoGeometry.Krein.cl11Rep_ι_zero_one_sq (E := E))

/-- Images of the two Clifford basis vectors anticommute. -/
lemma cl11Rep_ι_one_zero_anticommute_ι_zero_one :
    cl11Rep (E := E) (CliffordAlgebra.ι Q11 (1, 0))
      * cl11Rep (E := E) (CliffordAlgebra.ι Q11 (0, 1))
      = -(cl11Rep (E := E) (CliffordAlgebra.ι Q11 (0, 1))
          * cl11Rep (E := E) (CliffordAlgebra.ι Q11 (1, 0)) ) := by
  simpa [Q11, cl11Rep, cl11RepLin] using
    (InfoGeometry.Krein.cl11Rep_ι_one_zero_anticommute_ι_zero_one (E := E))

/-- Pseudoscalar image: `ρ(e₁e₂) = ε` in the chosen sign/order convention. -/
lemma cl11Rep_pseudoscalar :
    cl11Rep (E := E)
      (CliffordAlgebra.ι Q11 (1, 0) * CliffordAlgebra.ι Q11 (0, 1))
      = spectralEpsilon (E := E) := by
  simpa [Q11, cl11Rep, cl11RepLin] using (InfoGeometry.Krein.cl11Rep_pseudoscalar (E := E))

end KreinClifford
