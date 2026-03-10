import InfoGeometry.Prequantum.Connection

/-!
# InfoGeometry.Prequantum.Quotient

Gauge-orbit quotient structures for projective prequantum bundle points.
-/

namespace InfoGeometry.Prequantum.Quotient
end InfoGeometry.Prequantum.Quotient

namespace InfoGeometry.Prequantum

section KreinClifford

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace ProjectivePrequantumBundle

@[simp] theorem smul_base (c : Gauge) (P : ProjectivePrequantumBundle (E := E)) :
    (c • P).base = P.base := rfl

@[simp] theorem smul_data (c : Gauge) (P : ProjectivePrequantumBundle (E := E)) :
    (c • P).data = c • P.data := rfl

/-- Gauge-orbit relation on projective prequantum bundle points. -/
def GaugeEquivalent
    (P Q : ProjectivePrequantumBundle (E := E)) : Prop :=
  ∃ u : Gauge, u • P = Q

lemma gaugeEquivalent_refl (P : ProjectivePrequantumBundle (E := E)) :
    GaugeEquivalent (E := E) P P := by
  refine ⟨1, ?_⟩
  simp

lemma gaugeEquivalent_symm
    {P Q : ProjectivePrequantumBundle (E := E)}
    (h : GaugeEquivalent (E := E) P Q) :
    GaugeEquivalent (E := E) Q P := by
  rcases h with ⟨u, rfl⟩
  refine ⟨u⁻¹, ?_⟩
  simp [smul_smul]

lemma gaugeEquivalent_trans
    {P Q R : ProjectivePrequantumBundle (E := E)}
    (hPQ : GaugeEquivalent (E := E) P Q)
    (hQR : GaugeEquivalent (E := E) Q R) :
    GaugeEquivalent (E := E) P R := by
  rcases hPQ with ⟨u, rfl⟩
  rcases hQR with ⟨v, rfl⟩
  refine ⟨v * u, ?_⟩
  simp [smul_smul]

/-- Setoid of gauge-equivalent bundle points. -/
def gaugeSetoid : Setoid (ProjectivePrequantumBundle (E := E)) where
  r := GaugeEquivalent (E := E)
  iseqv := ⟨gaugeEquivalent_refl (E := E), gaugeEquivalent_symm (E := E),
    gaugeEquivalent_trans (E := E)⟩

/-- Gauge invariance of the physically meaningful scalar `F * ℏ`. -/
lemma covariantDerivative_constant_on_orbits
    {P Q : ProjectivePrequantumBundle (E := E)}
    (h : GaugeEquivalent (E := E) P Q) :
    ProjectivePrequantumBundle.covariantDerivative P =
      ProjectivePrequantumBundle.covariantDerivative Q := by
  rcases h with ⟨u, rfl⟩
  symm
  exact ProjectivePrequantumBundle.covariantDerivative_gauge_invariant u P

/-- The gauge-invariant scalar descends to the quotient by gauge orbits. -/
noncomputable def covariantDerivativeOnQuotient :
    Quotient (gaugeSetoid (E := E)) → ℝ :=
  Quotient.lift
    (fun P => ProjectivePrequantumBundle.covariantDerivative P)
    (by
      intro P Q hPQ
      exact covariantDerivative_constant_on_orbits (E := E) hPQ)

@[simp] lemma covariantDerivativeOnQuotient_mk
    (P : ProjectivePrequantumBundle (E := E)) :
    covariantDerivativeOnQuotient (E := E) (Quotient.mk (gaugeSetoid (E := E)) P)
      = ProjectivePrequantumBundle.covariantDerivative P := rfl

/-- The projective base ray is also gauge-invariant and descends to the quotient. -/
noncomputable def baseOnQuotient :
    Quotient (gaugeSetoid (E := E)) → ProjectiveState (E := E) :=
  Quotient.lift
    (fun P => P.base)
    (by
      intro P Q hPQ
      rcases hPQ with ⟨u, rfl⟩
      simp)

@[simp] lemma baseOnQuotient_mk
    (P : ProjectivePrequantumBundle (E := E)) :
    baseOnQuotient (E := E) (Quotient.mk (gaugeSetoid (E := E)) P) = P.base := rfl

/-- Convenient extensional criterion. -/
theorem eq_iff
    {P Q : ProjectivePrequantumBundle (E := E)} :
    P = Q ↔ P.base = Q.base ∧ P.data = Q.data := by
  constructor
  · intro h
    cases h
    exact ⟨rfl, rfl⟩
  · intro h
    exact ProjectivePrequantumBundle.ext h.1 h.2

end ProjectivePrequantumBundle

end KreinClifford

end InfoGeometry.Prequantum
