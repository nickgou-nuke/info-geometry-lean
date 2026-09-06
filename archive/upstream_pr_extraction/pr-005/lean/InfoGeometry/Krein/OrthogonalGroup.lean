import InfoGeometry.Krein.Metric

/-!
# Krein Orthogonal Group

Group structure for automorphisms preserving the neutral Hessian pairing.
Provides the model for the indefinite orthogonal group `O(n,n)`.
-/

section KreinOrthogonal

variable {E : Type} [NormedAddCommGroup E]
variable [InnerProductSpace ℝ E]

/-- Continuous automorphisms preserving the neutral Hessian pairing. -/
structure KreinIsometry where
  U : DoubledSpace E ≃L[ℝ] DoubledSpace E
  isometry : preservesMetric (E := E) (U : DoubledSpace E →L[ℝ] DoubledSpace E)

/-- Continuous automorphisms reversing the neutral Hessian pairing. -/
structure KreinAntiIsometry where
  U : DoubledSpace E ≃L[ℝ] DoubledSpace E
  antiIsometry : antiPreservesMetric (E := E) (U : DoubledSpace E →L[ℝ] DoubledSpace E)

/-- Orthogonal isometries of the doubled neutral form `hessianIndefiniteForm`
(`O(hessianIndefiniteForm)`, finite-dimensional model of `O(n,n)`). -/
def HessianOrthogonalGroup (E : Type) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] : Type _ :=
  {U : DoubledSpace E ≃L[ℝ] DoubledSpace E //
    preservesMetric (E := E) (U : DoubledSpace E →L[ℝ] DoubledSpace E)}

lemma preservesMetric_equiv_comp
    (U V : DoubledSpace E ≃L[ℝ] DoubledSpace E)
    (hU : preservesMetric (E := E) (U : DoubledSpace E →L[ℝ] DoubledSpace E))
    (hV : preservesMetric (E := E) (V : DoubledSpace E →L[ℝ] DoubledSpace E)) :
    preservesMetric (E := E)
      ((U : DoubledSpace E →L[ℝ] DoubledSpace E).comp
        (V : DoubledSpace E →L[ℝ] DoubledSpace E) : DoubledSpace E →L[ℝ] DoubledSpace E) := by
  exact preservesMetric_comp (E := E) hU hV

/-- Subgroup model of the orthogonal isometry group of `hessianIndefiniteForm`. -/
def hessianOrthogonalSubgroup :
    Subgroup (DoubledSpace E ≃L[ℝ] DoubledSpace E) where
  carrier := {U | preservesMetric (E := E) (U : DoubledSpace E →L[ℝ] DoubledSpace E)}
  one_mem' := preservesMetric_id (E := E)
  mul_mem' := by
    intro U V hU hV
    simpa using preservesMetric_equiv_comp (E := E) U V hU hV
  inv_mem' := by
    intro U hU
    simpa using preservesMetric_symm (E := E) U hU

def HessianOrthogonalGroup.one : HessianOrthogonalGroup E :=
  ⟨ContinuousLinearEquiv.refl ℝ (DoubledSpace E), preservesMetric_id (E := E)⟩

def HessianOrthogonalGroup.comp
    (U V : HessianOrthogonalGroup E) :
    HessianOrthogonalGroup E := by
  refine ⟨U.1.trans V.1, ?_⟩
  intro v w
  change hessianIndefiniteForm (E := E) (V.1 (U.1 v)) (V.1 (U.1 w))
      = hessianIndefiniteForm (E := E) v w
  calc
    hessianIndefiniteForm (E := E) (V.1 (U.1 v)) (V.1 (U.1 w))
        = hessianIndefiniteForm (E := E) (U.1 v) (U.1 w) := V.2 (U.1 v) (U.1 w)
    _ = hessianIndefiniteForm (E := E) v w := U.2 v w

def HessianOrthogonalGroup.inv
    (U : HessianOrthogonalGroup E) :
    HessianOrthogonalGroup E :=
  ⟨U.1.symm, preservesMetric_symm (E := E) U.1 U.2⟩

/-- Convert a wrapper isometry into the canonical orthogonal-group subtype. -/
def KreinIsometry.toHessianOrthogonalGroup
    (U : KreinIsometry (E := E)) : HessianOrthogonalGroup E :=
  ⟨U.U, U.isometry⟩

/-- Convert a canonical orthogonal-group element into the wrapper isometry structure. -/
def HessianOrthogonalGroup.toKreinIsometry
    (U : HessianOrthogonalGroup E) : KreinIsometry (E := E) where
  U := U.1
  isometry := U.2

instance : Group (HessianOrthogonalGroup E) := by
  simpa [HessianOrthogonalGroup, hessianOrthogonalSubgroup] using
    (inferInstance : Group (hessianOrthogonalSubgroup (E := E)))

/-- Swap involution as a continuous linear equivalence. -/
def modularJEquiv : DoubledSpace E ≃L[ℝ] DoubledSpace E where
  toLinearEquiv :=
    { toFun := fun v => (v.2, v.1)
      invFun := fun v => (v.2, v.1)
      left_inv := by intro v; rfl
      right_inv := by intro v; rfl
      map_add' := by intro v w; simp
      map_smul' := by intro a v; simp }
  continuous_toFun := by continuity
  continuous_invFun := by continuity

/-- Sign involution as a continuous linear equivalence. -/
def spectralEpsilonEquiv : DoubledSpace E ≃L[ℝ] DoubledSpace E where
  toLinearEquiv :=
    { toFun := fun v => (v.1, -v.2)
      invFun := fun v => (v.1, -v.2)
      left_inv := by intro v; simp
      right_inv := by intro v; simp
      map_add' := by intro v w; simp [add_comm]
      map_smul' := by intro a v; simp [smul_neg] }
  continuous_toFun := by continuity
  continuous_invFun := by continuity

def modularJKreinIsometry : KreinIsometry (E := E) where
  U := modularJEquiv (E := E)
  isometry := by
    simpa [modularJEquiv] using modularJ_preservesMetric (E := E)

def modularJHessianOrthogonal : HessianOrthogonalGroup E :=
  ⟨modularJEquiv (E := E), by
    simpa [modularJEquiv] using modularJ_preservesMetric (E := E)⟩

def spectralEpsilonKreinAntiIsometry : KreinAntiIsometry (E := E) where
  U := spectralEpsilonEquiv (E := E)
  antiIsometry := by
    simpa [spectralEpsilonEquiv] using spectralEpsilon_antiPreservesMetric (E := E)

end KreinOrthogonal
