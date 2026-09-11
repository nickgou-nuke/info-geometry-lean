import InfoGeometry.Canonical.ZornMaxwellFormsBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge
import Mathlib.Algebra.Algebra.Bilinear

/-!
# Degree-aware Maxwell form readout

The underlying finite Maxwell bridge works on the full exterior algebra.  This
owner adds explicit homogeneous-degree witnesses without claiming that an
arbitrary differential preserves degree.
-/

noncomputable section

namespace InfoGeometry.Canonical.ZornMaxwellFormsDegreeBridge

open ExteriorAlgebra
open ZornDifferentialFormsLaplacianBridge
open ZornMaxwellFormsBridge
open ExteriorHomogeneousDegreeBridge

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

def exteriorCliffordAction :
    ExteriorAlgebra R V →ₐ[R] Module.End R (ExteriorAlgebra R V) :=
  Algebra.lmul R (ExteriorAlgebra R V)

@[simp] theorem exteriorCliffordAction_apply
    (ω η : ExteriorAlgebra R V) :
    exteriorCliffordAction ω η = ω * η := by
  rfl

theorem exteriorCliffordAction_mul
    (ω η : ExteriorAlgebra R V) :
    exteriorCliffordAction (ω * η) =
      (exteriorCliffordAction ω).comp (exteriorCliffordAction η) := by
  exact (exteriorCliffordAction).map_mul ω η

@[simp] theorem exteriorCliffordAction_one :
    exteriorCliffordAction (1 : ExteriorAlgebra R V) =
      (1 : Module.End R (ExteriorAlgebra R V)) := by
  exact (exteriorCliffordAction).map_one

structure CliffordFormRepresentation
    (Q : QuadraticForm R V) where
  rho : CliffordAlgebra Q →ₐ[R] Module.End R (ExteriorAlgebra R V)

theorem cliffordFormRepresentation_mul
    (Q : QuadraticForm R V) (ρ : CliffordFormRepresentation Q)
    (x y : CliffordAlgebra Q) :
    ρ.rho (x * y) = (ρ.rho x).comp (ρ.rho y) := by
  exact ρ.rho.map_mul x y

@[simp] theorem cliffordFormRepresentation_one
    (Q : QuadraticForm R V) (ρ : CliffordFormRepresentation Q) :
    ρ.rho (1 : CliffordAlgebra Q) =
      (1 : Module.End R (ExteriorAlgebra R V)) := by
  exact ρ.rho.map_one

theorem cliffordFormRepresentation_generator_square
    (Q : QuadraticForm R V) (ρ : CliffordFormRepresentation Q) (v : V) :
    ρ.rho (CliffordAlgebra.ι Q v) * ρ.rho (CliffordAlgebra.ι Q v) =
      ρ.rho (algebraMap R (CliffordAlgebra Q) (Q v)) := by
  calc
    ρ.rho (CliffordAlgebra.ι Q v) * ρ.rho (CliffordAlgebra.ι Q v) =
        ρ.rho ((CliffordAlgebra.ι Q v) * (CliffordAlgebra.ι Q v)) :=
      (ρ.rho.map_mul _ _).symm
    _ = ρ.rho (algebraMap R (CliffordAlgebra Q) (Q v)) := by
      rw [CliffordAlgebra.ι_sq_scalar]

theorem cliffordFormRepresentation_generator_square_comp
    (Q : QuadraticForm R V) (ρ : CliffordFormRepresentation Q) (v : V) :
    (ρ.rho (CliffordAlgebra.ι Q v)).comp
        (ρ.rho (CliffordAlgebra.ι Q v)) =
      (Algebra.lsmul R R (ExteriorAlgebra R V)) (Q v) := by
  ext ω
  change ρ.rho (CliffordAlgebra.ι Q v) (
      ρ.rho (CliffordAlgebra.ι Q v) ω) = _
  calc
    ρ.rho (CliffordAlgebra.ι Q v) (
        ρ.rho (CliffordAlgebra.ι Q v) ω) =
        ρ.rho (algebraMap R (CliffordAlgebra Q) (Q v)) ω := by
      change (ρ.rho (CliffordAlgebra.ι Q v) *
          ρ.rho (CliffordAlgebra.ι Q v)) ω = _
      calc
        (ρ.rho (CliffordAlgebra.ι Q v) *
            ρ.rho (CliffordAlgebra.ι Q v)) ω =
            ρ.rho ((CliffordAlgebra.ι Q v) *
              (CliffordAlgebra.ι Q v)) ω := by
          exact congrArg (fun T : Module.End R (ExteriorAlgebra R V) => T ω)
            (ρ.rho.map_mul _ _).symm
        _ = ρ.rho (algebraMap R (CliffordAlgebra Q) (Q v)) ω := by
          rw [CliffordAlgebra.ι_sq_scalar]
    _ = Q v • ω := by
      rw [ρ.rho.commutes]
      rfl

def operatorAnticommutator
    (S T : Module.End R (ExteriorAlgebra R V)) :
    Module.End R (ExteriorAlgebra R V) :=
  S.comp T + T.comp S

structure CliffordDiracCompatibility
    (Q : QuadraticForm R V)
    (ρ : CliffordFormRepresentation (R := R) (V := V) Q) where
  dirac : Module.End R (ExteriorAlgebra R V)
  metric : V → R
  generator_anticommutator : ∀ v,
    operatorAnticommutator dirac (ρ.rho (CliffordAlgebra.ι Q v)) =
      (Algebra.lsmul R R (ExteriorAlgebra R V)) (metric v)

theorem cliffordDirac_generator_anticommutator
    (Q : QuadraticForm R V)
    (ρ : CliffordFormRepresentation (R := R) (V := V) Q)
    (C : CliffordDiracCompatibility Q ρ) (v : V) :
    operatorAnticommutator C.dirac (ρ.rho (CliffordAlgebra.ι Q v)) =
      (Algebra.lsmul R R (ExteriorAlgebra R V)) (C.metric v) :=
  C.generator_anticommutator v

def coupledDirac
    (Q : QuadraticForm R V)
    (ρ : CliffordFormRepresentation (R := R) (V := V) Q)
    (C : CliffordDiracCompatibility Q ρ) (v : V) :
    Module.End R (ExteriorAlgebra R V) :=
  C.dirac + ρ.rho (CliffordAlgebra.ι Q v)

theorem coupledDirac_square_expand
    (Q : QuadraticForm R V)
    (ρ : CliffordFormRepresentation (R := R) (V := V) Q)
    (C : CliffordDiracCompatibility Q ρ) (v : V) :
    (coupledDirac Q ρ C v).comp (coupledDirac Q ρ C v) =
      C.dirac.comp C.dirac +
        operatorAnticommutator C.dirac
          (ρ.rho (CliffordAlgebra.ι Q v)) +
        (ρ.rho (CliffordAlgebra.ι Q v)).comp
          (ρ.rho (CliffordAlgebra.ι Q v)) := by
  ext ω
  simp [coupledDirac, operatorAnticommutator, LinearMap.comp_apply]
  abel

theorem coupledDirac_square_metric_term
    (Q : QuadraticForm R V)
    (ρ : CliffordFormRepresentation (R := R) (V := V) Q)
    (C : CliffordDiracCompatibility Q ρ) (v : V) :
    (coupledDirac Q ρ C v).comp (coupledDirac Q ρ C v) =
      C.dirac.comp C.dirac +
        (Algebra.lsmul R R (ExteriorAlgebra R V)) (C.metric v) +
        (ρ.rho (CliffordAlgebra.ι Q v)).comp
          (ρ.rho (CliffordAlgebra.ι Q v)) := by
  rw [coupledDirac_square_expand]
  rw [C.generator_anticommutator]

theorem coupledDirac_square_quadratic_term
    (Q : QuadraticForm R V)
    (ρ : CliffordFormRepresentation (R := R) (V := V) Q)
    (C : CliffordDiracCompatibility Q ρ) (v : V) :
    (coupledDirac Q ρ C v).comp (coupledDirac Q ρ C v) =
      C.dirac.comp C.dirac +
        (Algebra.lsmul R R (ExteriorAlgebra R V)) (C.metric v) +
        (Algebra.lsmul R R (ExteriorAlgebra R V)) (Q v) := by
  rw [coupledDirac_square_metric_term,
    cliffordFormRepresentation_generator_square_comp]

theorem coupledDirac_square_matched_metric
    (Q : QuadraticForm R V)
    (ρ : CliffordFormRepresentation (R := R) (V := V) Q)
    (C : CliffordDiracCompatibility Q ρ) (hmetric : ∀ v, C.metric v = Q v)
    (v : V) :
    (coupledDirac Q ρ C v).comp (coupledDirac Q ρ C v) =
      C.dirac.comp C.dirac +
        (Algebra.lsmul R R (ExteriorAlgebra R V)) (Q v) +
        (Algebra.lsmul R R (ExteriorAlgebra R V)) (Q v) := by
  rw [coupledDirac_square_quadratic_term, hmetric]

theorem coupledDirac_square_matched_metric_two
    (Q : QuadraticForm R V)
    (ρ : CliffordFormRepresentation (R := R) (V := V) Q)
    (C : CliffordDiracCompatibility Q ρ) (hmetric : ∀ v, C.metric v = Q v)
    (v : V) :
    (coupledDirac Q ρ C v).comp (coupledDirac Q ρ C v) =
      C.dirac.comp C.dirac +
        (2 : R) •
          (Algebra.lsmul R R (ExteriorAlgebra R V)) (Q v) := by
  rw [coupledDirac_square_matched_metric Q ρ C hmetric v]
  ext ω
  simp [LinearMap.comp_apply, two_smul]
  abel

theorem coupledMaxwellDirac_square
    (D : FormDifferentialLaplacianData (R := R) (V := V))
    (Q : QuadraticForm R V)
    (ρ : CliffordFormRepresentation (R := R) (V := V) Q)
    (C : CliffordDiracCompatibility Q ρ)
    (hdirac : C.dirac = diracOperator D)
    (hmetric : ∀ v, C.metric v = Q v) (v : V) :
    (coupledDirac Q ρ C v).comp (coupledDirac Q ρ C v) =
      hodgeLaplacian D +
        (2 : R) • (Algebra.lsmul R R (ExteriorAlgebra R V)) (Q v) := by
  rw [coupledDirac_square_matched_metric_two Q ρ C hmetric v, hdirac,
    diracOperator_square]

theorem coupledMaxwellDirac_square_apply
    (D : FormDifferentialLaplacianData (R := R) (V := V))
    (Q : QuadraticForm R V)
    (ρ : CliffordFormRepresentation (R := R) (V := V) Q)
    (C : CliffordDiracCompatibility Q ρ)
    (hdirac : C.dirac = diracOperator D)
    (hmetric : ∀ v, C.metric v = Q v) (v : V)
    (ω : ExteriorAlgebra R V) :
    coupledDirac Q ρ C v (coupledDirac Q ρ C v ω) =
      hodgeLaplacian D ω + (2 * Q v) • ω := by
  have h := congrArg
    (fun T : Module.End R (ExteriorAlgebra R V) => T ω)
    (coupledMaxwellDirac_square D Q ρ C hdirac hmetric v)
  simpa [LinearMap.comp_apply, smul_eq_mul, mul_smul] using h

structure HomogeneousForm (k : ℕ) where
  value : ExteriorAlgebra R V
  homogeneous : IsHomogeneousExteriorDegree k value

structure TypedMaxwellOperators
    (D : FormDifferentialLaplacianData (R := R) (V := V)) where
  d₀ : HomogeneousForm (R := R) (V := V) 0 →
    HomogeneousForm (R := R) (V := V) 1
  d₁ : HomogeneousForm (R := R) (V := V) 1 →
    HomogeneousForm (R := R) (V := V) 2
  δ₂ : HomogeneousForm (R := R) (V := V) 2 →
    HomogeneousForm (R := R) (V := V) 1
  d₀_value : ∀ (Λ : HomogeneousForm (R := R) (V := V) 0),
    (d₀ Λ).value = D.differential Λ.value
  d₁_value : ∀ (A : HomogeneousForm (R := R) (V := V) 1),
    (d₁ A).value = fieldStrength D A.value
  d₁_d₀_zero : ∀ (Λ : HomogeneousForm (R := R) (V := V) 0),
    (d₁ (d₀ Λ)).value = 0
  δ₂_value : ∀ (F : HomogeneousForm (R := R) (V := V) 2),
    (δ₂ F).value = D.codifferential F.value
  hodgeStar : Module.End R (ExteriorAlgebra R V)
  hodgeSign : R
  δ₂_hodge : ∀ (F : HomogeneousForm (R := R) (V := V) 2),
    (δ₂ F).value = hodgeSign •
      hodgeStar (D.differential (hodgeStar F.value))
  d_gradedLeibniz : ∀ (n : ℕ) (x y : ExteriorAlgebra R V),
    IsHomogeneousExteriorDegree n x →
      D.differential (x * y) =
        D.differential x * y +
          ((-1 : R) ^ n) • (x * D.differential y)

theorem typed_differential_closed
    (D : FormDifferentialLaplacianData (R := R) (V := V))
    (O : TypedMaxwellOperators D)
    (A : HomogeneousForm (R := R) (V := V) 1) :
    D.differential (O.d₁ A).value = 0 := by
  rw [O.d₁_value]
  exact fieldStrength_closed D A.value

def typedGaugeTransformedPotential
    (O : TypedMaxwellOperators (R := R) (V := V) D)
    (potential : HomogeneousForm (R := R) (V := V) 1)
    (gauge : HomogeneousForm (R := R) (V := V) 0) :
    HomogeneousForm (R := R) (V := V) 1 :=
  ⟨potential.value + (O.d₀ gauge).value,
    by
      apply Submodule.add_mem
      · exact potential.homogeneous
      · exact (O.d₀ gauge).homogeneous⟩

theorem typedGaugeTransformedPotential_fieldStrength
    (D : FormDifferentialLaplacianData (R := R) (V := V))
    (O : TypedMaxwellOperators D)
    (potential : HomogeneousForm (R := R) (V := V) 1)
    (gauge : HomogeneousForm (R := R) (V := V) 0) :
    (O.d₁ (typedGaugeTransformedPotential O potential gauge)).value =
      (O.d₁ potential).value := by
  rw [O.d₁_value, O.d₁_value]
  rw [typedGaugeTransformedPotential]
  change D.differential (potential.value + (O.d₀ gauge).value) =
    D.differential potential.value
  rw [map_add, O.d₀_value]
  have hz := O.d₁_d₀_zero gauge
  rw [O.d₁_value] at hz
  rw [← O.d₀_value gauge]
  simpa [LinearMap.comp_apply] using hz

theorem typed_sourced_equation
    (D : FormDifferentialLaplacianData (R := R) (V := V))
    (O : TypedMaxwellOperators D)
    (F : HomogeneousForm (R := R) (V := V) 2) :
    D.codifferential F.value = (O.δ₂ F).value := by
  rw [O.δ₂_value]

theorem typedMaxwell_equations
    (D : FormDifferentialLaplacianData (R := R) (V := V))
    (O : TypedMaxwellOperators D)
    (potential : HomogeneousForm (R := R) (V := V) 1) :
    D.differential (O.d₁ potential).value = 0 ∧
      D.codifferential (O.d₁ potential).value =
        (O.δ₂ (O.d₁ potential)).value := by
  exact ⟨typed_differential_closed D O potential,
    typed_sourced_equation D O (O.d₁ potential)⟩

theorem typedMaxwell_gauge_invariant_equations
    (D : FormDifferentialLaplacianData (R := R) (V := V))
    (O : TypedMaxwellOperators D)
    (potential : HomogeneousForm (R := R) (V := V) 1)
    (gauge : HomogeneousForm (R := R) (V := V) 0) :
    D.differential
        (O.d₁ (typedGaugeTransformedPotential O potential gauge)).value = 0 ∧
      D.codifferential
          (O.d₁ (typedGaugeTransformedPotential O potential gauge)).value =
        (O.δ₂ (O.d₁ potential)).value := by
  rw [typedGaugeTransformedPotential_fieldStrength]
  exact typedMaxwell_equations D O potential

theorem typedMaxwell_potential_laplacian
    (D : FormDifferentialLaplacianData (R := R) (V := V))
    (O : TypedMaxwellOperators D)
    (potential : HomogeneousForm (R := R) (V := V) 1)
    (current : ExteriorAlgebra R V)
    (hgauge : D.codifferential potential.value = 0)
    (hsource : D.codifferential (O.d₁ potential).value = current) :
    hodgeLaplacian D potential.value = current := by
  apply maxwell_potential_laplacian D potential.value current hgauge
  rw [← O.d₁_value potential]
  exact hsource

theorem typedMaxwell_potential_laplacian_hodge
    (D : FormDifferentialLaplacianData (R := R) (V := V))
    (O : TypedMaxwellOperators D)
    (potential : HomogeneousForm (R := R) (V := V) 1)
    (current : ExteriorAlgebra R V)
    (hgauge : D.codifferential potential.value = 0)
    (hsource : (O.δ₂ (O.d₁ potential)).value = current) :
    hodgeLaplacian D potential.value = current ∧
      current = O.hodgeSign •
        O.hodgeStar (D.differential (O.hodgeStar (O.d₁ potential).value)) := by
  constructor
  · apply typedMaxwell_potential_laplacian D O potential current hgauge
    rw [← O.δ₂_value (O.d₁ potential)]
    exact hsource
  · calc
      current = (O.δ₂ (O.d₁ potential)).value := hsource.symm
      _ = O.hodgeSign •
          O.hodgeStar (D.differential (O.hodgeStar (O.d₁ potential).value)) :=
        O.δ₂_hodge (O.d₁ potential)

theorem typedMaxwell_gauge_invariant_potential_laplacian
    (D : FormDifferentialLaplacianData (R := R) (V := V))
    (O : TypedMaxwellOperators D)
    (potential : HomogeneousForm (R := R) (V := V) 1)
    (gauge : HomogeneousForm (R := R) (V := V) 0)
    (current : ExteriorAlgebra R V)
    (hgauge : D.codifferential
        (typedGaugeTransformedPotential O potential gauge).value = 0)
    (hsource : D.codifferential (O.d₁ potential).value = current) :
    hodgeLaplacian D
        (typedGaugeTransformedPotential O potential gauge).value = current := by
  apply maxwell_potential_laplacian D
    (typedGaugeTransformedPotential O potential gauge).value current hgauge
  rw [← O.d₁_value (typedGaugeTransformedPotential O potential gauge)]
  rw [typedGaugeTransformedPotential_fieldStrength]
  exact hsource

theorem typed_codifferential_hodgeConjugate
    (D : FormDifferentialLaplacianData (R := R) (V := V))
    (O : TypedMaxwellOperators D)
    (F : HomogeneousForm (R := R) (V := V) 2) :
    (O.δ₂ F).value = O.hodgeSign •
      O.hodgeStar (D.differential (O.hodgeStar F.value)) :=
  O.δ₂_hodge F

theorem typed_differential_gradedLeibniz
    (D : FormDifferentialLaplacianData (R := R) (V := V))
    (O : TypedMaxwellOperators D)
    (n : ℕ) (x y : ExteriorAlgebra R V)
    (hx : IsHomogeneousExteriorDegree n x) :
    D.differential (x * y) =
      D.differential x * y + ((-1 : R) ^ n) • (x * D.differential y) :=
  O.d_gradedLeibniz n x y hx

def degreeTaggedFieldStrength
    (D : FormDifferentialLaplacianData (R := R) (V := V))
    (potential : HomogeneousForm (R := R) (V := V) 1)
    (hF : IsHomogeneousExteriorDegree 2
      (fieldStrength D potential.value)) :
    HomogeneousForm (R := R) (V := V) 2 :=
  ⟨fieldStrength D potential.value, hF⟩

theorem degreeTaggedFieldStrength_closed
    (D : FormDifferentialLaplacianData (R := R) (V := V))
    (potential : HomogeneousForm (R := R) (V := V) 1)
    (hF : IsHomogeneousExteriorDegree 2
      (fieldStrength D potential.value)) :
    D.differential (degreeTaggedFieldStrength D potential hF).value = 0 :=
  fieldStrength_closed D potential.value

theorem degreeTaggedMaxwell_form_equations
    (D : FormDifferentialLaplacianData (R := R) (V := V))
    (potential : HomogeneousForm (R := R) (V := V) 1)
    (hF : IsHomogeneousExteriorDegree 2
      (fieldStrength D potential.value))
    (current : ExteriorAlgebra R V)
    (hsource : D.codifferential
      (degreeTaggedFieldStrength D potential hF).value = current) :
    D.differential (degreeTaggedFieldStrength D potential hF).value = 0 ∧
      D.codifferential (degreeTaggedFieldStrength D potential hF).value = current := by
  exact ⟨degreeTaggedFieldStrength_closed D potential hF, hsource⟩

def degreeTaggedCurrent
    (D : FormDifferentialLaplacianData (R := R) (V := V))
    (potential : HomogeneousForm (R := R) (V := V) 1)
    (hF : IsHomogeneousExteriorDegree 2
      (fieldStrength D potential.value))
    (hJ : IsHomogeneousExteriorDegree 1
      (D.codifferential (degreeTaggedFieldStrength D potential hF).value)) :
    HomogeneousForm (R := R) (V := V) 1 :=
  ⟨D.codifferential (degreeTaggedFieldStrength D potential hF).value, hJ⟩

theorem degreeTaggedSourcedMaxwell_equation
    (D : FormDifferentialLaplacianData (R := R) (V := V))
    (potential : HomogeneousForm (R := R) (V := V) 1)
    (hF : IsHomogeneousExteriorDegree 2
      (fieldStrength D potential.value))
    (hJ : IsHomogeneousExteriorDegree 1
      (D.codifferential (degreeTaggedFieldStrength D potential hF).value)) :
    D.codifferential (degreeTaggedFieldStrength D potential hF).value =
      (degreeTaggedCurrent D potential hF hJ).value := by
  rfl

end InfoGeometry.Canonical.ZornMaxwellFormsDegreeBridge
