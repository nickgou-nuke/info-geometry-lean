import InfoGeometry.Krein.Automorphisms
import Mathlib.Analysis.InnerProductSpace.Adjoint

section KreinModular

variable {V : Type _} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- Fundamental symmetry for Krein-space style constructions. -/
structure FundamentalSymmetry (V : Type _) [NormedAddCommGroup V] [InnerProductSpace ℝ V] where
  toLinear : V →ₗ[ℝ] V
  is_involution : toLinear ∘ₗ toLinear = LinearMap.id
  is_self_adjoint : LinearMap.IsSymmetric toLinear

namespace FundamentalSymmetry

/-- Krein adjoint `A♯ = J A† J` relative to a fundamental symmetry `J`. -/
noncomputable def kreinAdjoint
    (J : FundamentalSymmetry V) (A : V →ₗ[ℝ] V) : V →ₗ[ℝ] V :=
  letI : CompleteSpace V := FiniteDimensional.complete ℝ V
  J.toLinear ∘ₗ A.adjoint ∘ₗ J.toLinear

/-- Krein self-adjoint operators: `A♯ = A`. -/
def IsKreinSelfAdjoint (J : FundamentalSymmetry V) (A : V →ₗ[ℝ] V) : Prop :=
  kreinAdjoint J A = A

/-- Krein skew-adjoint operators: `A♯ = -A`. -/
def IsKreinSkewAdjoint (J : FundamentalSymmetry V) (A : V →ₗ[ℝ] V) : Prop :=
  kreinAdjoint J A = -A

/-- Krein sesquilinear form specialized to real spaces. -/
def kreinForm (J : FundamentalSymmetry V) (x y : V) : ℝ :=
  inner ℝ (J.toLinear x) y

/-- Hilbert-side representative `J ∘ A` of a Krein operator `A`. -/
def hilbertPart (J : FundamentalSymmetry V) (A : V →ₗ[ℝ] V) : V →ₗ[ℝ] V :=
  J.toLinear ∘ₗ A

/-- Krein-positive operator:
`J ∘ A` is symmetric and Hilbert-positive. -/
def IsKreinPositive (J : FundamentalSymmetry V) (A : V →ₗ[ℝ] V) : Prop :=
  LinearMap.IsSymmetric (hilbertPart J A) ∧
    ∀ x, 0 ≤ inner ℝ ((hilbertPart J A) x) x

/-- Strict Krein positivity. -/
def IsStrictKreinPositive (J : FundamentalSymmetry V) (A : V →ₗ[ℝ] V) : Prop :=
  LinearMap.IsSymmetric (hilbertPart J A) ∧
    ∀ x, x ≠ 0 → 0 < inner ℝ ((hilbertPart J A) x) x

/-- Krein-unitary operators: `U♯ U = Id`. -/
def IsKreinUnitary (J : FundamentalSymmetry V) (U : V →ₗ[ℝ] V) : Prop :=
  kreinAdjoint J U ∘ₗ U = LinearMap.id

/-- Witness data for a Krein polar factorization of `T`. -/
structure KreinPolarData (J : FundamentalSymmetry V) (T : V →ₗ[ℝ] V) where
  U : V →ₗ[ℝ] V
  P : V →ₗ[ℝ] V
  unitary : IsKreinUnitary J U
  selfAdjoint : IsKreinSelfAdjoint J P
  positive : IsKreinPositive J P
  invertibleP : LinearMap.ker P = ⊥
  factorization : T = U ∘ₗ P

/-- Interface theorem: unpack a polar-factorization witness. -/
theorem finiteDimensional_krein_polar
    (J : FundamentalSymmetry V)
    (T : V →ₗ[ℝ] V)
    (hT : KreinPolarData J T) :
    ∃ (U P : V →ₗ[ℝ] V),
      IsKreinUnitary J U ∧
      IsKreinSelfAdjoint J P ∧
      IsKreinPositive J P ∧
      LinearMap.ker P = ⊥ ∧
      T = U ∘ₗ P := by
  refine
    ⟨hT.U, hT.P, hT.unitary, hT.selfAdjoint, hT.positive, hT.invertibleP, hT.factorization⟩

/-- Krein absolute value extracted from polar witness data. -/
def kreinAbs
    (J : FundamentalSymmetry V)
    (T : V →ₗ[ℝ] V)
    (hT : KreinPolarData J T) : V →ₗ[ℝ] V :=
  hT.P

/-- Modular operator `Δ := T♯ ∘ T`. -/
noncomputable def modularOperator
    (J : FundamentalSymmetry V) (T : V →ₗ[ℝ] V) : V →ₗ[ℝ] V :=
  kreinAdjoint J T ∘ₗ T

/-- Bridge layer from polar data to modular-flow style data. -/
structure ModularFlowData (J : FundamentalSymmetry V) (T : V →ₗ[ℝ] V) where
  delta : V →ₗ[ℝ] V
  is_def : delta = modularOperator J T
  positive : IsKreinPositive J delta
  selfAdjoint : IsKreinSelfAdjoint J delta

/-- Data for a candidate modular generator, with compatibility to `Δ`. -/
structure ModularGeneratorData (J : FundamentalSymmetry V) (T : V →ₗ[ℝ] V) where
  flowData : ModularFlowData J T
  generator : V →ₗ[ℝ] V
  commutes_delta : generator.comp flowData.delta = flowData.delta.comp generator

/-- One-parameter modular flow interface.
No spectral-calculus claims are made here. -/
structure ModularFlow (J : FundamentalSymmetry V) (T : V →ₗ[ℝ] V) where
  genData : ModularGeneratorData J T
  flow : ℝ → V →ₗ[ℝ] V
  flow_zero : flow 0 = LinearMap.id
  flow_add : ∀ s t, flow (s + t) = (flow s).comp (flow t)
  preserves_delta :
    ∀ t, (flow t).comp genData.flowData.delta = genData.flowData.delta.comp (flow t)

section FlowBridge

variable {E : Type _}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

/-- Bridge from modular interfaces to the existing doubled-space flow stack. -/
structure ModularFlowBridge
    (J : FundamentalSymmetry V)
    (T : V →ₗ[ℝ] V) where
  transport : V ≃L[ℝ] DoubledSpace E
  modularFlow : ModularFlow J T
  generatorCLM : DoubledSpace E →L[ℝ] DoubledSpace E
  generator_matches :
    generatorCLM.toLinearMap =
      transport.toLinearMap ∘ₗ modularFlow.genData.generator ∘ₗ transport.symm.toLinearMap
  kreinFlow : FiniteDimensionalExponentialFlow (E := E) generatorCLM
  preserves_modularOperator :
    ∀ t,
      let Δ : DoubledSpace E →L[ℝ] DoubledSpace E :=
        (transport.toLinearMap ∘ₗ modularFlow.genData.flowData.delta ∘ₗ
          transport.symm.toLinearMap).toContinuousLinearMap
      ((kreinFlow.flow t : DoubledSpace E →L[ℝ] DoubledSpace E).comp Δ)
        = Δ.comp (kreinFlow.flow t : DoubledSpace E →L[ℝ] DoubledSpace E)

/-- Forgetful map: a modular-flow bridge carries an admissible flow-stack object. -/
def ModularFlowBridge.toFlowStack
    {J : FundamentalSymmetry V}
    {T : V →ₗ[ℝ] V}
    (B : ModularFlowBridge (E := E) J T) :
    FiniteDimensionalExponentialFlow (E := E) B.generatorCLM :=
  B.kreinFlow

end FlowBridge

end FundamentalSymmetry

end KreinModular
