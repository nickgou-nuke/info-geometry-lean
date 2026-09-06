import InfoGeometry.Twistor.PenroseIncidence

/-!
# Two-twistor spacetime nodes

This is the finite algebraic node of the light-ray incidence picture.  The
owner uses the existing Penrose incidence map; it does not assert a curved
bundle, a connection, or a holonomy theorem.
-/

namespace InfoGeometry.Twistor.TwoTwistorSpacetimeNode

open InfoGeometry.Twistor.PenroseIncidence

/- The two spinors span the spinor fibre. -/
def SpansSpinorPair (π₁ π₂ : Spinor2) : Prop :=
  ∀ π : Spinor2, ∃ a b : ℂ, π = a • π₁ + b • π₂

/- The node theorem keeps independence and spanning as separate, explicit
   hypotheses.  This avoids conflating a generating pair with a basis. -/
def IndependentSpanningSpinorPair (π₁ π₂ : Spinor2) : Prop :=
  LinearIndependent ℂ ![π₁, π₂] ∧ SpansSpinorPair π₁ π₂

theorem incidence_first_coordinate_eq
    (x : ComplexSpacetime) (π : Spinor2) (Z : Twistor4)
    (h : incidenceLinearMap x π = Z) :
    Complex.I • omegaLinearMap x π = Z.1 := by
  exact congrArg Prod.fst h

theorem equal_incidence_on_spanning_pair
    (x y : ComplexSpacetime) (π₁ π₂ : Spinor2)
    (Z₁ Z₂ : Twistor4)
    (h₁x : incidenceLinearMap x π₁ = Z₁)
    (h₂x : incidenceLinearMap x π₂ = Z₂)
    (h₁y : incidenceLinearMap y π₁ = Z₁)
    (h₂y : incidenceLinearMap y π₂ = Z₂)
    (hpair : IndependentSpanningSpinorPair π₁ π₂) :
    ∀ π : Spinor2, omegaLinearMap x π = omegaLinearMap y π := by
  have h₁ : omegaLinearMap x π₁ = omegaLinearMap y π₁ := by
    have h := congrArg Prod.fst (h₁x.trans h₁y.symm)
    simpa [incidenceLinearMap] using h
  have h₂ : omegaLinearMap x π₂ = omegaLinearMap y π₂ := by
    have h := congrArg Prod.fst (h₂x.trans h₂y.symm)
    simpa [incidenceLinearMap] using h
  intro π
  rcases hpair.2 π with ⟨a, b, rfl⟩
  simp only [map_add, map_smul]
  rw [h₁, h₂]

/-- Two spanning incident twistor directions determine at most one spacetime
point.  This is the uniqueness half of the two-twistor node theorem. -/
theorem two_twistor_spacetime_node_unique
    (x y : ComplexSpacetime) (π₁ π₂ : Spinor2)
    (Z₁ Z₂ : Twistor4)
    (h₁x : incidenceLinearMap x π₁ = Z₁)
    (h₂x : incidenceLinearMap x π₂ = Z₂)
    (h₁y : incidenceLinearMap y π₁ = Z₁)
    (h₂y : incidenceLinearMap y π₂ = Z₂)
    (hpair : IndependentSpanningSpinorPair π₁ π₂) :
    x = y := by
  apply Matrix.mulVec_injective
  funext π
  exact equal_incidence_on_spanning_pair x y π₁ π₂ Z₁ Z₂
    h₁x h₂x h₁y h₂y hpair π

/- A frame presentation of the node.  The columns of `P` are the two
   spinor directions and the columns of `Ω` are their `ω` data.  Since the
   incidence convention is `ω = i X π`, the reconstructed node is
   `X = -i Ω P⁻¹`. -/
noncomputable def frameSpacetimeNode
    (P Ω : Matrix (Fin 2) (Fin 2) ℂ) : ComplexSpacetime :=
  (-Complex.I) • (Ω * P⁻¹)

theorem frameSpacetimeNode_incidence
    (P Ω : Matrix (Fin 2) (Fin 2) ℂ)
    (hP : IsUnit P.det) (π : Spinor2) :
    incidenceLinearMap (frameSpacetimeNode P Ω) (P.mulVec π) =
      (Ω.mulVec π, P.mulVec π) := by
  apply Prod.ext
  · simp only [incidenceLinearMap_apply, omegaLinearMap_apply,
      frameSpacetimeNode]
    have hmul : (Ω * P⁻¹).mulVec (P.mulVec π) = Ω.mulVec π := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_assoc,
        Matrix.nonsing_inv_mul P hP]
      simp
    rw [Matrix.smul_mulVec, hmul]
    simp [smul_smul]
  · rfl

theorem two_twistor_spacetime_node_exists_unique
    (P Ω : Matrix (Fin 2) (Fin 2) ℂ)
    (hP : IsUnit P.det)
    (hpair : IndependentSpanningSpinorPair (P.mulVec ![1, 0])
      (P.mulVec ![0, 1])) :
    ∃! x : ComplexSpacetime,
      incidenceLinearMap x (P.mulVec ![1, 0]) =
          (Ω.mulVec ![1, 0], P.mulVec ![1, 0]) ∧
      incidenceLinearMap x (P.mulVec ![0, 1]) =
          (Ω.mulVec ![0, 1], P.mulVec ![0, 1]) := by
  refine ⟨frameSpacetimeNode P Ω, ?_, ?_⟩
  · exact ⟨frameSpacetimeNode_incidence P Ω hP ![1, 0],
      frameSpacetimeNode_incidence P Ω hP ![0, 1]⟩
  · intro y hy
    symm
    apply two_twistor_spacetime_node_unique
      (frameSpacetimeNode P Ω) y (P.mulVec ![1, 0]) (P.mulVec ![0, 1])
      (Ω.mulVec ![1, 0], P.mulVec ![1, 0])
      (Ω.mulVec ![0, 1], P.mulVec ![0, 1])
    · exact frameSpacetimeNode_incidence P Ω hP ![1, 0]
    · exact frameSpacetimeNode_incidence P Ω hP ![0, 1]
    · exact hy.1
    · exact hy.2
    · exact hpair

end InfoGeometry.Twistor.TwoTwistorSpacetimeNode
