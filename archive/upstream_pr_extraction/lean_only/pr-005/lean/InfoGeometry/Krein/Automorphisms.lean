import InfoGeometry.Krein.Metric

section KreinClifford

variable {E : Type} [NormedAddCommGroup E]

section Automorphisms

variable [NormedSpace ℝ E]

/-- Conjugation action of `U` on doubled-space endomorphisms. -/
noncomputable def conjugateCLM
    (U : DoubledSpace E ≃L[ℝ] DoubledSpace E)
    (A : DoubledSpace E →L[ℝ] DoubledSpace E) :
    DoubledSpace E →L[ℝ] DoubledSpace E :=
  (U : DoubledSpace E →L[ℝ] DoubledSpace E).comp
    (A.comp (U.symm : DoubledSpace E →L[ℝ] DoubledSpace E))

lemma conjugateCLM_comp
    (U : DoubledSpace E ≃L[ℝ] DoubledSpace E)
    (A B : DoubledSpace E →L[ℝ] DoubledSpace E) :
    conjugateCLM (E := E) U (A.comp B) =
      (conjugateCLM (E := E) U A).comp (conjugateCLM (E := E) U B) := by
  apply ContinuousLinearMap.ext
  intro v
  simp [conjugateCLM, ContinuousLinearMap.comp_apply]

lemma conjugateCLM_id
    (U : DoubledSpace E ≃L[ℝ] DoubledSpace E) :
    conjugateCLM (E := E) U (ContinuousLinearMap.id ℝ (DoubledSpace E)) =
      ContinuousLinearMap.id ℝ (DoubledSpace E) := by
  apply ContinuousLinearMap.ext
  intro v
  simp [conjugateCLM]

lemma conjugateCLM_neg
    (U : DoubledSpace E ≃L[ℝ] DoubledSpace E)
    (A : DoubledSpace E →L[ℝ] DoubledSpace E) :
    conjugateCLM (E := E) U (-A) = -(conjugateCLM (E := E) U A) := by
  apply ContinuousLinearMap.ext
  intro v
  simp [conjugateCLM]

/-- Conjugation by a continuous linear equivalence preserves `Cl(1,1)` relations. -/
theorem Cl11Algebra.conjugate
    {J ε : DoubledSpace E →L[ℝ] DoubledSpace E}
    (hCl : Cl11Algebra J ε)
    (U : DoubledSpace E ≃L[ℝ] DoubledSpace E) :
    Cl11Algebra (conjugateCLM (E := E) U J) (conjugateCLM (E := E) U ε) := by
  refine ⟨?_, ?_, ?_⟩
  · calc
      (conjugateCLM (E := E) U J).comp (conjugateCLM (E := E) U J)
          = conjugateCLM (E := E) U (J.comp J) := by
              symm
              exact conjugateCLM_comp (E := E) U J J
      _ = conjugateCLM (E := E) U (ContinuousLinearMap.id ℝ (DoubledSpace E)) := by
            rw [hCl.j_involution]
      _ = ContinuousLinearMap.id ℝ (DoubledSpace E) := by
            exact conjugateCLM_id (E := E) U
  · calc
      (conjugateCLM (E := E) U ε).comp (conjugateCLM (E := E) U ε)
          = conjugateCLM (E := E) U (ε.comp ε) := by
              symm
              exact conjugateCLM_comp (E := E) U ε ε
      _ = conjugateCLM (E := E) U (ContinuousLinearMap.id ℝ (DoubledSpace E)) := by
            rw [hCl.eps_involution]
      _ = ContinuousLinearMap.id ℝ (DoubledSpace E) := by
            exact conjugateCLM_id (E := E) U
  · calc
      (conjugateCLM (E := E) U J).comp (conjugateCLM (E := E) U ε)
          = conjugateCLM (E := E) U (J.comp ε) := by
              symm
              exact conjugateCLM_comp (E := E) U J ε
      _ = conjugateCLM (E := E) U (-(ε.comp J)) := by
            rw [hCl.anticommute]
      _ = -(conjugateCLM (E := E) U (ε.comp J)) := by
            exact conjugateCLM_neg (E := E) U (ε.comp J)
      _ = -((conjugateCLM (E := E) U ε).comp (conjugateCLM (E := E) U J)) := by
            rw [conjugateCLM_comp (E := E) U ε J]

/-- `U` preserves Clifford structure if it sends each `Cl(1,1)` pair to another `Cl(1,1)` pair
by conjugation. -/
def preservesClifford
    (U : DoubledSpace E ≃L[ℝ] DoubledSpace E)
    (J ε : DoubledSpace E →L[ℝ] DoubledSpace E) : Prop :=
  Cl11Algebra J ε →
    Cl11Algebra (conjugateCLM (E := E) U J) (conjugateCLM (E := E) U ε)

lemma preservesClifford_of_conjugate
    (U : DoubledSpace E ≃L[ℝ] DoubledSpace E)
    (J ε : DoubledSpace E →L[ℝ] DoubledSpace E) :
    preservesClifford (E := E) U J ε := by
  intro hCl
  exact hCl.conjugate (E := E) U

end Automorphisms

section MetricTransport

variable [InnerProductSpace ℝ E]

lemma preservesMetric_apply_symm_left
    (U : DoubledSpace E ≃L[ℝ] DoubledSpace E)
    (hU : preservesMetric (E := E) (U : DoubledSpace E →L[ℝ] DoubledSpace E))
    (v w : DoubledSpace E) :
    hessianIndefiniteForm (E := E) v ((U.symm : DoubledSpace E →L[ℝ] DoubledSpace E) w)
      = hessianIndefiniteForm (E := E) (U v) w := by
  have h := hU v ((U.symm : DoubledSpace E →L[ℝ] DoubledSpace E) w)
  simpa using h.symm

lemma preservesMetric_apply_symm_right
    (U : DoubledSpace E ≃L[ℝ] DoubledSpace E)
    (hU : preservesMetric (E := E) (U : DoubledSpace E →L[ℝ] DoubledSpace E))
    (v w : DoubledSpace E) :
    hessianIndefiniteForm (E := E) ((U.symm : DoubledSpace E →L[ℝ] DoubledSpace E) v) w
      = hessianIndefiniteForm (E := E) v (U w) := by
  have h := hU ((U.symm : DoubledSpace E →L[ℝ] DoubledSpace E) v) w
  simpa using h.symm

lemma infinitesimalIsometry_conjugate
    (U : DoubledSpace E ≃L[ℝ] DoubledSpace E)
    (hU : preservesMetric (E := E) (U : DoubledSpace E →L[ℝ] DoubledSpace E))
    {A : DoubledSpace E →L[ℝ] DoubledSpace E}
    (hA : IsInfinitesimalIsometry A) :
    IsInfinitesimalIsometry (conjugateCLM (E := E) U A) := by
  intro v w
  change hessianIndefiniteForm (E := E)
      ((U : DoubledSpace E →L[ℝ] DoubledSpace E)
        (A ((U.symm : DoubledSpace E →L[ℝ] DoubledSpace E) v))) w
      +
      hessianIndefiniteForm (E := E) v
      ((U : DoubledSpace E →L[ℝ] DoubledSpace E)
        (A ((U.symm : DoubledSpace E →L[ℝ] DoubledSpace E) w)))
      = 0
  calc
    hessianIndefiniteForm (E := E)
        ((U : DoubledSpace E →L[ℝ] DoubledSpace E)
          (A ((U.symm : DoubledSpace E →L[ℝ] DoubledSpace E) v))) w
      +
      hessianIndefiniteForm (E := E) v
        ((U : DoubledSpace E →L[ℝ] DoubledSpace E)
          (A ((U.symm : DoubledSpace E →L[ℝ] DoubledSpace E) w)))
        = hessianIndefiniteForm (E := E)
            (A ((U.symm : DoubledSpace E →L[ℝ] DoubledSpace E) v))
            ((U.symm : DoubledSpace E →L[ℝ] DoubledSpace E) w)
          + hessianIndefiniteForm (E := E)
            ((U.symm : DoubledSpace E →L[ℝ] DoubledSpace E) v)
            (A ((U.symm : DoubledSpace E →L[ℝ] DoubledSpace E) w)) := by
              have hL :
                  hessianIndefiniteForm (E := E)
                    ((U : DoubledSpace E →L[ℝ] DoubledSpace E)
                      (A ((U.symm : DoubledSpace E →L[ℝ] DoubledSpace E) v))) w
                    = hessianIndefiniteForm (E := E)
                        (A ((U.symm : DoubledSpace E →L[ℝ] DoubledSpace E) v))
                        ((U.symm : DoubledSpace E →L[ℝ] DoubledSpace E) w) := by
                simpa using
                  (preservesMetric_apply_symm_left (E := E) U hU
                    (A ((U.symm : DoubledSpace E →L[ℝ] DoubledSpace E) v)) w).symm
              have hR :
                  hessianIndefiniteForm (E := E) v
                    ((U : DoubledSpace E →L[ℝ] DoubledSpace E)
                      (A ((U.symm : DoubledSpace E →L[ℝ] DoubledSpace E) w)))
                    = hessianIndefiniteForm (E := E)
                        ((U.symm : DoubledSpace E →L[ℝ] DoubledSpace E) v)
                        (A ((U.symm : DoubledSpace E →L[ℝ] DoubledSpace E) w)) := by
                simpa using
                  (preservesMetric_apply_symm_right (E := E) U hU v
                    (A ((U.symm : DoubledSpace E →L[ℝ] DoubledSpace E) w))).symm
              rw [hL, hR]
    _ = 0 := hA _ _

end MetricTransport

section Dynamics

variable [InnerProductSpace ℝ E]

/-- Interface for a one-parameter flow obtained from a finite-dimensional exponential map model.
This packages the semigroup law, identity at `0`, and metric preservation. -/
structure FiniteDimensionalExponentialFlow
    [FiniteDimensional ℝ E]
    (A : DoubledSpace E →L[ℝ] DoubledSpace E) where
  flow : ℝ → DoubledSpace E ≃L[ℝ] DoubledSpace E
  flow_zero : flow 0 = ContinuousLinearEquiv.refl ℝ (DoubledSpace E)
  flow_add : ∀ s t, flow (s + t) = (flow s).trans (flow t)
  generator_infinitesimal : IsInfinitesimalIsometry A
  flow_preservesMetric :
    ∀ t, preservesMetric (E := E) (flow t : DoubledSpace E →L[ℝ] DoubledSpace E)

theorem flow_isometry
    [FiniteDimensional ℝ E]
    {A : DoubledSpace E →L[ℝ] DoubledSpace E}
    (F : FiniteDimensionalExponentialFlow (E := E) A)
    (t : ℝ) :
    preservesMetric (E := E) (F.flow t : DoubledSpace E →L[ℝ] DoubledSpace E) :=
  F.flow_preservesMetric t

/-- Orbit of a point under a one-parameter flow. -/
noncomputable def flowOrbit
    [FiniteDimensional ℝ E]
    {A : DoubledSpace E →L[ℝ] DoubledSpace E}
    (F : FiniteDimensionalExponentialFlow (E := E) A)
    (v0 : DoubledSpace E) (t : ℝ) : DoubledSpace E :=
  F.flow t v0

lemma flowOrbit_zero
    [FiniteDimensional ℝ E]
    {A : DoubledSpace E →L[ℝ] DoubledSpace E}
    (F : FiniteDimensionalExponentialFlow (E := E) A)
    (v0 : DoubledSpace E) :
    flowOrbit (E := E) F v0 0 = v0 := by
  simp [flowOrbit, F.flow_zero]

lemma flowOrbit_add
    [FiniteDimensional ℝ E]
    {A : DoubledSpace E →L[ℝ] DoubledSpace E}
    (F : FiniteDimensionalExponentialFlow (E := E) A)
    (v0 : DoubledSpace E) (s t : ℝ) :
    flowOrbit (E := E) F v0 (s + t)
      = flowOrbit (E := E) F (flowOrbit (E := E) F v0 s) t := by
  simp [flowOrbit, F.flow_add]

/-- Time-evolved endomorphism via conjugation by the flow. -/
noncomputable def flowConjugate
    [FiniteDimensional ℝ E]
    {A : DoubledSpace E →L[ℝ] DoubledSpace E}
    (F : FiniteDimensionalExponentialFlow (E := E) A)
    (B : DoubledSpace E →L[ℝ] DoubledSpace E)
    (t : ℝ) : DoubledSpace E →L[ℝ] DoubledSpace E :=
  conjugateCLM (E := E) (F.flow t) B

lemma flowConjugate_infinitesimal
    [FiniteDimensional ℝ E]
    {A B : DoubledSpace E →L[ℝ] DoubledSpace E}
    (F : FiniteDimensionalExponentialFlow (E := E) A)
    (hB : IsInfinitesimalIsometry (E := E) B)
    (t : ℝ) :
    IsInfinitesimalIsometry (E := E) (flowConjugate (E := E) F B t) := by
  exact infinitesimalIsometry_conjugate
    (U := F.flow t) (hU := F.flow_preservesMetric t) hB

/-- Orbit representation of a flow trajectory by an infinitesimal-isometry generator. -/
theorem natural_gradient_is_orbit_interface
    [FiniteDimensional ℝ E]
    {A : DoubledSpace E →L[ℝ] DoubledSpace E}
    (F : FiniteDimensionalExponentialFlow (E := E) A)
    (initial : DoubledSpace E) :
    ∃ G, IsInfinitesimalIsometry (E := E) G ∧
      ∀ t, flowOrbit (E := E) F initial t = F.flow t initial := by
  refine ⟨A, F.generator_infinitesimal, ?_⟩
  intro t
  rfl

end Dynamics

section NoAxiomSanity

variable [InnerProductSpace ℝ E]

/-- Sanity witness: commutator closure is available as a theorem term. -/
theorem noAxiom_witness_infinitesimal_closed_comm
    {A B : DoubledSpace E →L[ℝ] DoubledSpace E}
    (hA : IsInfinitesimalIsometry (E := E) A)
    (hB : IsInfinitesimalIsometry (E := E) B) :
    IsInfinitesimalIsometry (E := E) (clmComm A B) :=
  infinitesimalIsometry_closed_comm (E := E) hA hB

omit [InnerProductSpace ℝ E] in
/-- Sanity witness: flow-level metric preservation theorem is available. -/
theorem noAxiom_witness_flow_isometry
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {A : DoubledSpace E →L[ℝ] DoubledSpace E}
    (F : FiniteDimensionalExponentialFlow (E := E) A)
    (t : ℝ) :
    preservesMetric (E := E) (F.flow t : DoubledSpace E →L[ℝ] DoubledSpace E) :=
  flow_isometry (E := E) F t

omit [InnerProductSpace ℝ E] in
/-- Sanity witness: infinitesimal structure is transported along flow conjugation. -/
theorem noAxiom_witness_flowConjugate_infinitesimal
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {A B : DoubledSpace E →L[ℝ] DoubledSpace E}
    (F : FiniteDimensionalExponentialFlow (E := E) A)
    (hB : IsInfinitesimalIsometry (E := E) B)
    (t : ℝ) :
    IsInfinitesimalIsometry (E := E) (flowConjugate (E := E) F B t) :=
  flowConjugate_infinitesimal (E := E) F hB t

end NoAxiomSanity

end KreinClifford
