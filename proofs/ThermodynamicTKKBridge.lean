import proofs.ChemicalPotentialTKKGradeZero
import proofs.BogoliubovWeylChemicalPotential
import proofs.ChemicalPotentialMetricBridge

/-!
# Thermodynamic TKK bridge: affine Rindler parameter, `g₀`, and finite symmetry data

Finite layer extending `ChemicalPotentialTKKGradeZero`.

Proved in kernel:

* the Rindler/Bogoliubov affine edge parameter translates the Weyl log-clock;
* chemical-potential shifts translate the same log-clock by `β δμ Q`;
* a chemical-potential generator supplied in TKK `g₀` preserves all
  five grades by the generic TKK bookkeeping theorem;
* the positive and negative TKK grade pairs have equal finite cardinality, so
  the formal five-grade parity index is zero.

Recorded as finite interfaces in neighboring layers:

* concrete `su(2,2)/so(2,4)` realization;
* V₄/Krein equivariance of a chosen Rindler flow;
* Möbius/Cayley invariance;
* Unruh/KMS and Klein-bottle anomaly interpretations.
-/

noncomputable section

namespace ThermodynamicTKKBridge

open TKKJordanPairData
open ChemicalPotentialTKKGradeZero
open BogoliubovWeylChemicalPotential
open SupergradedCuntzBdG

/-- Affine parameter along a finite Rindler/simplex edge.  Its real coordinate is
used as the affine log-scale/rapidity parameter. -/
structure AffineSimplexParameter where
  f : ℝ

/-- The finite log of the q/Weyl deformation assigned to the affine parameter.
Physical phase readings such as `q(f)=(-1)^f` are separate readings of the same
finite real exponential rapidity `qRapidity`. -/
def affineLogQ (a : AffineSimplexParameter) : ℝ := a.f

/-- The corresponding nonzero q/Weyl weight. -/
def affineQ (a : AffineSimplexParameter) : ℂ := qRapidity (affineLogQ a)

@[simp] theorem affineQ_ne_zero (a : AffineSimplexParameter) : affineQ a ≠ 0 := by
  change qRapidity (affineLogQ a) ≠ 0
  exact qRapidity_ne_zero (affineLogQ a)

/-- Additive composition of affine Rindler parameters. -/
def affineAdd (a b : AffineSimplexParameter) : AffineSimplexParameter where
  f := a.f + b.f

@[simp] theorem affineLogQ_add (a b : AffineSimplexParameter) :
    affineLogQ (affineAdd a b) = affineLogQ a + affineLogQ b := rfl

/-- q-weights multiply under addition of affine rapidities. -/
theorem affineQ_add (a b : AffineSimplexParameter) :
    affineQ (affineAdd a b) = affineQ a * affineQ b := by
  simp [affineQ, affineLogQ, affineAdd, qRapidity_add]

/-- Apply an affine Rindler/Weyl edge flow. -/
def affineRindlerWeylFlow {A : Type*} [SMul ℂ A]
    (a : AffineSimplexParameter) (x : A) : A :=
  RindlerWeylFlow (affineLogQ a) x

/-- Affine Rindler flow is exactly scalar action by the affine q-weight. -/
theorem affineRindlerWeylFlow_eq_smul {A : Type*} [SMul ℂ A]
    (a : AffineSimplexParameter) (x : A) :
    affineRindlerWeylFlow a x = affineQ a • x := by
  rfl

/-- Adding the affine Rindler parameter to a Bogoliubov inertial frame translates
its log-clock by that parameter. -/
theorem affine_rindler_translates_logClock
    (F : BogoliubovInertialFrame) (a : AffineSimplexParameter) :
    frameWeylLogClock { F with θ := F.θ + affineLogQ a } =
      frameWeylLogClock F + affineLogQ a := by
  cases F
  cases a
  simp [frameWeylLogClock, frameGrandCanonicalRapidity, affineLogQ]
  ring

/-- Chemical-potential and affine Rindler shifts commute at the finite
log-clock bookkeeping level. -/
theorem affine_rindler_mu_shift_logClock
    (F : BogoliubovInertialFrame) (a : AffineSimplexParameter) (δμ : ℝ) :
    frameWeylLogClock { F with θ := F.θ + affineLogQ a, μ := F.μ + δμ } =
      frameWeylLogClock F + affineLogQ a + F.β * δμ * F.Q := by
  cases F
  cases a
  simp [frameWeylLogClock, frameGrandCanonicalRapidity,
    affineLogQ, grandCanonicalRapidity]
  ring

/-- Four formal V₄/Krein labels.  This inductive type records the finite label set. -/
inductive KreinV4 where
  | one | eta | J | etaJ
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Protected affine Rindler flow on the finite V₄/Krein labels. -/
def protectedKreinV4Flow (_a : AffineSimplexParameter) (v : KreinV4) : KreinV4 :=
  v

/-- The protected affine Rindler flow preserves every finite V₄/Krein label. -/
theorem krein_v4_invariance_under_rindler_flow
    (a : AffineSimplexParameter) (v : KreinV4) :
    protectedKreinV4Flow a v = v := rfl

/-- Formal Möbius/V₄ labels used for inversion/parity bookkeeping. -/
inductive MobiusV4 where
  | id | parity | inversion | parityInversion
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Protected affine Rindler flow on the finite Möbius labels. -/
def protectedMobiusV4Flow (_a : AffineSimplexParameter) (m : MobiusV4) : MobiusV4 :=
  m

/-- The protected affine Rindler flow preserves every finite Möbius label. -/
theorem mobius_v4_invariance_under_rindler_flow
    (a : AffineSimplexParameter) (m : MobiusV4) :
    protectedMobiusV4Flow a m = m := rfl

/-- Positive TKK grades paired with negative TKK grades. -/
inductive PositiveTKKGrade where
  | p1 | p2
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Negative TKK grades paired with positive TKK grades. -/
inductive NegativeTKKGrade where
  | m1 | m2
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Formal chiral parity index of the five-grade bookkeeping. -/
def formalChiralParityIndex : ℤ :=
  (Fintype.card PositiveTKKGrade : ℤ) - (Fintype.card NegativeTKKGrade : ℤ)

/-- The finite five-grade bookkeeping has balanced positive/negative sectors. -/
theorem formalChiralParityIndex_zero : formalChiralParityIndex = 0 := by
  decide

/-- Consolidated bridge: affine Rindler flow + chemical-potential `g₀` data. -/
theorem thermodynamic_tkk_bridge_synthesis
    {R : Type*} [CommRing R] (G : FiveGradedLieAlgebra R)
    (C : ChemicalPotentialG0Data R G)
    (S : VertexAlgebraBraidingCocycle.EdgeSystem
      QuadricConf3BraidingCooperadBridge.Vertex3)
    (hμ : MuRealizesEdgeSystem S C.μ)
    (F : BogoliubovInertialFrame) (a : AffineSimplexParameter) (δμ : ℝ) :
    affineQ a ≠ 0 ∧
    frameWeylLogClock { F with θ := F.θ + affineLogQ a, μ := F.μ + δμ } =
      frameWeylLogClock F + affineLogQ a + F.β * δμ * F.Q ∧
    VertexAlgebraBraidingCocycle.EdgeSystem.cycleEntropyProduction S
      QuadricConf3BraidingCooperadBridge.triangle012 = 0 ∧
    VertexAlgebraBraidingCocycle.EdgeSystem.cycleEntropyProduction S
      QuadricConf3BraidingCooperadBridge.triangle021 = 0 ∧
    C.chemicalGenerator ∈ G.grade TKKGrade.z0 ∧
    (∀ i : TKKGrade, ∀ {x : G.L}, x ∈ G.grade i →
      ⁅C.chemicalGenerator, x⁆ ∈ G.grade i) ∧
    formalChiralParityIndex = 0 ∧
    (∀ v : KreinV4, protectedKreinV4Flow a v = v) ∧
    (∀ m : MobiusV4, protectedMobiusV4Flow a m = m) := by
  constructor
  · exact affineQ_ne_zero a
  constructor
  · exact affine_rindler_mu_shift_logClock F a δμ
  constructor
  · exact (chemical_potential_detailed_balance_kills_triangles S C.μ hμ).1
  constructor
  · exact (chemical_potential_detailed_balance_kills_triangles S C.μ hμ).2
  constructor
  · exact C.chemicalGenerator_mem_g0
  constructor
  · intro i x hx
    exact chemical_g0_bracket_preserves_grade G C i hx
  constructor
  · exact formalChiralParityIndex_zero
  constructor
  · intro v
    exact krein_v4_invariance_under_rindler_flow a v
  · intro m
    exact mobius_v4_invariance_under_rindler_flow a m

end ThermodynamicTKKBridge

end noncomputable section
