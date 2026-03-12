import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Clifford.SplitQ11
import InfoGeometry.Krein.Representation
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic

set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

/-- Backward-compatible alias to the canonical split form. -/
noncomputable abbrev Q11 : QuadraticForm ℝ (ℝ × ℝ) := InfoGeometry.Clifford.splitQ11

@[simp] lemma Q11_apply (v : ℝ × ℝ) : Q11 v = v.1 * v.1 - v.2 * v.2 := by
  exact InfoGeometry.Clifford.splitQ11_apply v

section KreinClifford

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- `J I = - I J` for `J` and `I := J ∘ ε`. -/
lemma modular_j_complex_i_anticommute :
    (InfoGeometry.Krein.modular_j (E := E)).comp (InfoGeometry.Krein.complex_i (E := E))
      = -((InfoGeometry.Krein.complex_i (E := E)).comp (InfoGeometry.Krein.modular_j (E := E))) := by
  simpa using (InfoGeometry.Krein.modular_j_complex_i_anticommute (E := E))

/-- Linear map `(a,b) ↦ a • J + b • I` into endomorphisms of `E × E`. -/
noncomputable abbrev cl11RepLin :
    (ℝ × ℝ) →ₗ[ℝ] (InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E) :=
  InfoGeometry.Krein.cl11RepLin (E := E)

omit [CompleteSpace E] in
/-- Linear map `(a,b) ↦ a • J + b • I` applied to a doubled vector. -/
lemma cl11RepLin_apply_pair (a b : ℝ) (x y : E) :
    cl11RepLin (E := E) (a, b) (InfoGeometry.Krein.to_doubled x y)
      = InfoGeometry.Krein.to_doubled ((a - b) • y) ((a + b) • x) := by
  simp [cl11RepLin, InfoGeometry.Krein.cl11RepLin_apply_to_doubled]

omit [CompleteSpace E] in
/-- Key Clifford relation for `cl11RepLin`: `(aJ + bI)^2 = (a^2 - b^2) • Id`. -/
lemma cl11RepLin_sq (v : ℝ × ℝ) :
    (cl11RepLin (E := E) v) * (cl11RepLin (E := E) v)
      = algebraMap ℝ (InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E) (Q11 v) := by
  simpa [Q11, cl11RepLin] using (InfoGeometry.Krein.cl11RepLin_sq (E := E) v)

/-- The induced algebra hom `Cl(1,1) → End(E × E)`. -/
noncomputable abbrev cl11Rep :
    CliffordAlgebra Q11 →ₐ[ℝ] (InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E) :=
  InfoGeometry.Krein.cl11Rep (E := E)

@[simp] lemma cl11Rep_ι_apply (v : ℝ × ℝ) :
    cl11Rep (E := E) (CliffordAlgebra.ι Q11 v) = cl11RepLin (E := E) v := by
  simpa [Q11, cl11Rep, cl11RepLin] using (InfoGeometry.Krein.cl11Rep_ι_apply (E := E) v)

lemma cl11Rep_ι_one_zero :
    cl11Rep (E := E) (CliffordAlgebra.ι Q11 (1, 0)) = InfoGeometry.Krein.modular_j (E := E) := by
  simpa [Q11, cl11Rep] using (InfoGeometry.Krein.cl11Rep_ι_one_zero (E := E))

lemma cl11Rep_ι_zero_one :
    cl11Rep (E := E) (CliffordAlgebra.ι Q11 (0, 1)) = InfoGeometry.Krein.complex_i (E := E) := by
  simpa [Q11, cl11Rep] using (InfoGeometry.Krein.cl11Rep_ι_zero_one (E := E))

/-- Image of the first Clifford basis vector squares to `+Id`. -/
lemma cl11Rep_ι_one_zero_sq :
    cl11Rep (E := E) (CliffordAlgebra.ι Q11 (1, 0))
      * cl11Rep (E := E) (CliffordAlgebra.ι Q11 (1, 0))
      = ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace E) := by
  simpa [Q11, cl11Rep] using (InfoGeometry.Krein.cl11Rep_ι_one_zero_sq (E := E))

/-- Image of the second Clifford basis vector squares to `-Id`. -/
lemma cl11Rep_ι_zero_one_sq :
    cl11Rep (E := E) (CliffordAlgebra.ι Q11 (0, 1))
      * cl11Rep (E := E) (CliffordAlgebra.ι Q11 (0, 1))
      = -(ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace E)) := by
  simpa [Q11, cl11Rep] using (InfoGeometry.Krein.cl11Rep_ι_zero_one_sq (E := E))

/-- Images of the two Clifford basis vectors anticommute. -/
lemma cl11Rep_ι_one_zero_anticommute_ι_zero_one :
    cl11Rep (E := E) (CliffordAlgebra.ι Q11 (1, 0))
      * cl11Rep (E := E) (CliffordAlgebra.ι Q11 (0, 1))
      = -(cl11Rep (E := E) (CliffordAlgebra.ι Q11 (0, 1))
          * cl11Rep (E := E) (CliffordAlgebra.ι Q11 (1, 0)) ) := by
  simpa [Q11, cl11Rep] using
    (InfoGeometry.Krein.cl11Rep_ι_one_zero_anticommute_ι_zero_one (E := E))

/-- Pseudoscalar image: `ρ(e₁e₂) = ε` in the chosen sign/order convention. -/
lemma cl11Rep_pseudoscalar :
    cl11Rep (E := E)
      (CliffordAlgebra.ι Q11 (1, 0) * CliffordAlgebra.ι Q11 (0, 1))
      = InfoGeometry.Krein.spectral_epsilon (E := E) := by
  simpa [Q11, cl11Rep] using (InfoGeometry.Krein.cl11Rep_pseudoscalar (E := E))

end KreinClifford
