import proofs.ThermodynamicTKKBridge
import proofs.NonIsoConf3DeRhamCooperad

/-!
# Chemical potential, `g₀`, and equivariant de Rham data

This file adds a finite/dependent-type abstraction of the
Cartan-formula step suggested by the thermodynamic TKK bridge.

It contains finite formal versions of these ingredients:

* if a Lie derivative is defined by Cartan's formula
  `L_X ω = d (ι_X ω) + ι_X (d ω)`, then for a closed `ω` it is exact;
* exact chemical-potential edge systems kill the two arity-three Wilson cycles;
* the rank-32 finite candidate and the formal five-grade chiral parity index are
  preserved as finite facts;
* symbolic mixed Arnold alpha/beta data can be recorded as finite formal data.

Analytic interpretations can later instantiate:

* smooth de Rham complex of the quadric complement;
* identification of `α = d μ` with analytic de Rham generators;
* mixed Arnold/Gysin/Dupont comparison;
* Tolman--Ehrenfest metric scaling and Einstein/macroscopic limit;
* concrete `g₀` vector fields and V₄/Möbius/Klein-bottle geometry.
-/

noncomputable section

namespace ChemicalPotentialDeRhamG0Bridge

open TKKJordanPairData.Legacy
open ChemicalPotentialTKKGradeZero
open ThermodynamicTKKBridge
open NonIsoConf3DeRhamCooperad
open LightConeConf3DeRhamCooperad
open VertexAlgebraBraidingCocycle
open VertexAlgebraBraidingCocycle.EdgeSystem
open QuadricConf3BraidingCooperadBridge

/-- Minimal abstract de Rham-like complex sufficient for Cartan-formula data.
`form n` is a finite/formal stand-in for `n`-forms. -/
structure AbstractDeRhamComplex where
  form : ℕ → Type*
  zero : ∀ n, form n
  d : ∀ n, form n → form (n + 1)

/-- Exactness for abstract degree-one forms. -/
def IsExactOne (C : AbstractDeRhamComplex) (ω : C.form 1) : Prop :=
  ∃ η : C.form 0, C.d 0 η = ω

/-- Closedness in the abstract complex. -/
def IsClosed (C : AbstractDeRhamComplex) {n : ℕ} (ω : C.form n) : Prop :=
  C.d n ω = C.zero (n + 1)

/-- A closed cohomology-class representative.  Closedness is a field of the
finite abstract complex, independent of a manifold model. -/
structure DeRhamClass (C : AbstractDeRhamComplex) (n : ℕ) where
  rep : C.form n
  closed : IsClosed C rep

/-- Abstract vector-field action data on degree-one de Rham forms.  The key
field records the Cartan-formula consequence:
for closed `ω`, `L_X ω` is `d` of the contraction `ι_X ω`. -/
structure CartanAction (C : AbstractDeRhamComplex) where
  iota1 : C.form 1 → C.form 0
  lie1 : C.form 1 → C.form 1
  cartan_closed_exact_one : ∀ ω : C.form 1, IsClosed C ω → IsExactOne C (lie1 ω)

/-- Cartan theorem in degree one: under a Cartan action, the Lie derivative of a
closed one-form is exact, hence it does not change the de Rham cohomology class. -/
theorem cartan_lie_closed_one_form_exact
    (C : AbstractDeRhamComplex) (A : CartanAction C)
    (ω : DeRhamClass C 1) :
    IsExactOne C (A.lie1 ω.rep) := by
  exact A.cartan_closed_exact_one ω.rep ω.closed

/-- Formal chemical-potential 0-form datum whose differential realizes an alpha
edge generator.  The equality `α=dμ` is represented by an explicit field. -/
structure ChemicalPotentialAsZeroForm (C : AbstractDeRhamComplex) where
  μ0 : C.form 0
  dμ : C.form 1
  dμ_eq_d_mu0 : C.d 0 μ0 = dμ
  realizesAlphaEdge : AlphaEdge → Prop
  realizesThermodynamicLogRatio : Prop

/-- A single signed monomial in the formal mixed Arnold alpha/beta stencil.
The intended expression is
`alpha12*beta23 - alpha12*beta13 + alpha23*beta13 = 0`.
This is finite data for the relation shape; the wedge product
and analytic de Rham comparison are represented by explicit fields below. -/
structure MixedArnoldAlphaBetaTerm where
  alpha : AlphaEdge
  beta : BetaEdge
  negative : Bool
  deriving DecidableEq, Repr

/-- The explicit mixed Arnold stencil coupling degree-one alpha classes to
degree-three beta/flux classes in the `D=4` presentation. -/
def mixedArnoldChemicalMetricStencil : List MixedArnoldAlphaBetaTerm :=
  [ { alpha := AlphaEdge.a12, beta := BetaEdge.b23, negative := false },
    { alpha := AlphaEdge.a12, beta := BetaEdge.b13, negative := true },
    { alpha := AlphaEdge.a23, beta := BetaEdge.b13, negative := false } ]

@[simp] theorem mixedArnoldChemicalMetricStencil_length :
    mixedArnoldChemicalMetricStencil.length = 3 := rfl

/-- A formal algebraic structure evaluating the Arnold stencil and metric warpings. -/
structure ChemicalMetricGeometry (C : AbstractDeRhamComplex) where
  alpha : AlphaEdge → C.form 1
  beta : BetaEdge → C.form 2
  add3 : C.form 3 → C.form 3 → C.form 3
  sub3 : C.form 3 → C.form 3 → C.form 3
  zero3 : C.form 3
  wedge : C.form 1 → C.form 2 → C.form 3
  scale : C.form 3 → C.form 3
  betaWarp : C.form 0 → C.form 2 → C.form 2
  isoActual : C.form 3 → C.form 3

def alphaExactFromMu (C : AbstractDeRhamComplex) (μform : ChemicalPotentialAsZeroForm C)
    (G : ChemicalMetricGeometry C) (e : AlphaEdge) : Prop :=
  G.alpha e = μform.dμ ∧ μform.realizesAlphaEdge e

def evalMixedArnoldTerm (C : AbstractDeRhamComplex) (G : ChemicalMetricGeometry C) (t : MixedArnoldAlphaBetaTerm) : C.form 3 :=
  let base := G.wedge (G.alpha t.alpha) (G.beta t.beta)
  if t.negative then G.sub3 G.zero3 base else base

def evalStencil (C : AbstractDeRhamComplex) (G : ChemicalMetricGeometry C) (l : List MixedArnoldAlphaBetaTerm) : C.form 3 :=
  l.foldr (fun t acc => G.add3 (evalMixedArnoldTerm C G t) acc) G.zero3
theorem chemical_potential_mixed_alpha_beta_coupling
    (C : AbstractDeRhamComplex)
    (μform : ChemicalPotentialAsZeroForm C)
    (hA12 : μform.realizesAlphaEdge AlphaEdge.a12)
    (hA13 : μform.realizesAlphaEdge AlphaEdge.a13)
    (hA23 : μform.realizesAlphaEdge AlphaEdge.a23) :
    C.d 0 μform.μ0 = μform.dμ ∧
    μform.realizesAlphaEdge AlphaEdge.a12 ∧
    μform.realizesAlphaEdge AlphaEdge.a13 ∧
    μform.realizesAlphaEdge AlphaEdge.a23 ∧
    mixedArnoldChemicalMetricStencil.length = 3 := by
  constructor
  · exact μform.dμ_eq_d_mu0
  constructor
  · show μform.realizesAlphaEdge AlphaEdge.a12
    simpa using hA12
  constructor
  · show μform.realizesAlphaEdge AlphaEdge.a13
    simpa using hA13
  constructor
  · show μform.realizesAlphaEdge AlphaEdge.a23
    simpa using hA23
  · exact mixedArnoldChemicalMetricStencil_length

/-- Formal statement that a Möbius/Klein pullback splits a finite cohomology
basis into even/odd labels.  A concrete pullback can instantiate the labels. -/
inductive MobiusParity where
  | even | odd
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- A finite label for product-basis classes with a supplied Möbius
parity assignment. -/
structure MobiusSplitProductClass where
  basis : ProductBasis
  parity : MobiusParity
  deriving DecidableEq, Repr

/-- The split has the same total finite rank as the rank-32 product candidate
because it only decorates each existing product-basis element with a chosen
parity label supplied as data. -/
def forgetMobiusSplit (x : MobiusSplitProductClass) : ProductBasis := x.basis

/-- Combined finite synthesis: exact `μ` kills Wilson cycles; Cartan
`g₀` action changes closed forms by exact forms; rank-32 and zero formal TKK
index remain finite facts; mixed Arnold data stays formal. -/
theorem chemical_potential_derham_g0_synthesis
    {R : Type*} [CommRing R] (G : FiveGradedLieAlgebra R)
    (CG0 : ChemicalPotentialG0Data R G)
    (S : EdgeSystem Vertex3)
    (hμ : MuRealizesEdgeSystem S CG0.μ)
    (C : AbstractDeRhamComplex) (A : CartanAction C)
    (ω : DeRhamClass C 1)
    (μform : ChemicalPotentialAsZeroForm C)
    (hTrip : CG0.preservesTripotentNullCone)
    (hGibbs : CG0.gibbsWeightsDifferentiateToMu)
    (hG0 : CG0.gradeZeroInterpretsLocalLorentzKreinGenerator) :
    cycleEntropyProduction S triangle012 = 0 ∧
    cycleEntropyProduction S triangle021 = 0 ∧
    CG0.chemicalGenerator ∈ G.grade TKKGrade.z0 ∧
    (∀ i : TKKGrade, ∀ {x : G.L}, x ∈ G.grade i →
      ⁅CG0.chemicalGenerator, x⁆ ∈ G.grade i) ∧
    IsExactOne C (A.lie1 ω.rep) ∧
    C.d 0 μform.μ0 = μform.dμ ∧
    Fintype.card ProductBasis = 32 ∧
    formalChiralParityIndex = 0 := by
  rcases chemical_potential_tkk_g0_synthesis G CG0 S hμ hTrip hGibbs hG0 with
    ⟨h012, h021, hMem, hPres, _hTrip, _hGibbs, _hG0⟩
  constructor
  · show cycleEntropyProduction S triangle012 = 0
    simpa using h012
  constructor
  · show cycleEntropyProduction S triangle021 = 0
    simpa using h021
  constructor
  · show CG0.chemicalGenerator ∈ G.grade TKKGrade.z0
    simpa using hMem
  constructor
  · show ∀ i : TKKGrade, ∀ {x : G.L}, x ∈ G.grade i →
        ⁅CG0.chemicalGenerator, x⁆ ∈ G.grade i
    simpa using hPres
  constructor
  · exact cartan_lie_closed_one_form_exact C A ω
  constructor
  · exact μform.dμ_eq_d_mu0
  constructor
  · exact productBasis_card
  · exact formalChiralParityIndex_zero

end ChemicalPotentialDeRhamG0Bridge

end noncomputable section
