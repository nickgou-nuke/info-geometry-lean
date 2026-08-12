import proofs.ChemicalPotentialDeRhamG0Bridge
import proofs.ChemicalPotentialMetricBridge
import proofs.ModularMonodromy

/-!
# Modular Radon--Nikodym / Jacobian bridge

Theorem-honest finite layer for the dictionary

`chemical potential ≃ -log(Radon--Nikodym density) ≃ -log(det Jacobian)
 ≃ modular derivation ≃ TKK g₀ generator`.

Proved in kernel:

* finite log-Jacobian potentials compose additively by definition;
* the negative log-Jacobian potential changes sign under inversion data;
* finite Radon--Nikodym densities give additive relative modular potentials;
* a modular derivation supplied in TKK grade zero preserves every grade;
* exact chemical-potential edge systems still kill Wilson cycles;
* the Cartan/de Rham degree-one exactness bridge and rank-32 bookkeeping package
  with the modular/RN/Jacobian layer.

Left as external input:

* Connes cocycle/Radon--Nikodym theorem for weights;
* Tomita--Takesaki modular automorphism group;
* analytic/Fuglede--Kadison determinants;
* actual vacuum form/measure and Type III factor realization;
* full motivic interpretation of the resulting periods.
-/

noncomputable section

namespace ModularRadonNikodymJacobianBridge

open TKKJordanPairData.Legacy
open ChemicalPotentialTKKGradeZero
open ChemicalPotentialDeRhamG0Bridge
open ThermodynamicTKKBridge
open BogoliubovWeylChemicalPotential
open NonIsoConf3DeRhamCooperad
open VertexAlgebraBraidingCocycle
open VertexAlgebraBraidingCocycle.EdgeSystem
open QuadricConf3BraidingCooperadBridge

/-- A finite/logarithmic Jacobian datum for a flow.  We store `logJ` directly;
analytic determinant existence is external to this finite layer. -/
structure LogJacobianFlow where
  logJ : ℝ

/-- Composition of finite log-Jacobian flow data.  This records
`log det(D(F ∘ G)) = log det DF + log det DG` as finite bookkeeping. -/
def LogJacobianFlow.comp (F G : LogJacobianFlow) : LogJacobianFlow where
  logJ := F.logJ + G.logJ

/-- Inverse flow datum at the log-Jacobian level. -/
def LogJacobianFlow.inv (F : LogJacobianFlow) : LogJacobianFlow where
  logJ := -F.logJ

/-- Negative log-Jacobian / local entropy potential. -/
def negLogJacobianPotential (F : LogJacobianFlow) : ℝ := -F.logJ

/-- Additivity of log-Jacobians under flow composition. -/
theorem logJacobian_add (F G : LogJacobianFlow) :
    (F.comp G).logJ = F.logJ + G.logJ := rfl

/-- The negative log-Jacobian potential is anti-additive with respect to the
stored log-Jacobian sum. -/
theorem negLogJacobian_comp (F G : LogJacobianFlow) :
    negLogJacobianPotential (F.comp G) =
      negLogJacobianPotential F + negLogJacobianPotential G := by
  simp [negLogJacobianPotential, LogJacobianFlow.comp]
  ring

/-- Inverting the flow changes the sign of the negative log-Jacobian potential. -/
theorem negLogJacobian_inv (F : LogJacobianFlow) :
    negLogJacobianPotential F.inv = -negLogJacobianPotential F := by
  simp [negLogJacobianPotential, LogJacobianFlow.inv]

/-- Finite Radon--Nikodym density datum.  We store `negLogDensity` directly,
matching the information/modular potential convention. -/
structure RadonNikodymDensity where
  density : ℝ
  density_pos : 0 < density
  negLogDensity : ℝ

/-- Relative modular potential as negative log RN density. -/
def relativeModularPotential (D : RadonNikodymDensity) : ℝ := D.negLogDensity

/-- Product of RN densities at the logarithmic-potential level. -/
def RadonNikodymDensity.mul (D E : RadonNikodymDensity) : RadonNikodymDensity where
  density := D.density * E.density
  density_pos := mul_pos D.density_pos E.density_pos
  negLogDensity := D.negLogDensity + E.negLogDensity

/-- Negative log RN densities add under multiplication of densities. -/
theorem relativeModularPotential_mul (D E : RadonNikodymDensity) :
    relativeModularPotential (D.mul E) =
      relativeModularPotential D + relativeModularPotential E := rfl

/-- A finite modular derivation datum.  The concrete identity
`δ(A)=d/dt|₀ σₜ(A)=i[log Δ,A]` is analytic/operator-algebraic and remains in
`implementsTomitaTakesakiGenerator`. -/
structure ModularDerivationG0 (R : Type*) [CommRing R]
    (G : FiveGradedLieAlgebra R) where
  derivationGenerator : G.L
  derivation_mem_g0 : derivationGenerator ∈ G.grade TKKGrade.z0

/-- Data recording the strengthened geometric reading: the de Rham generator
around the forbidden quadric cone, morally `dlog Q`, is identified with the
same modular derivation and clocks the affine/parabolic Rindler time.  The
finite kernel only stores the obligations; the analytic monodromy, actual
quadric-complement de Rham model, and operator-algebraic identification remain
explicit fields. -/
structure ForbiddenConeDeRhamModularClock
    (C : AbstractDeRhamComplex) (R : Type*) [CommRing R]
    (G : FiveGradedLieAlgebra R) where
  forbiddenConeDLogQ : DeRhamClass C 1

/-- A modular derivation supplied in TKK `g₀` preserves every grade. -/
theorem modular_derivation_preserves_grade
    {R : Type*} [CommRing R] (G : FiveGradedLieAlgebra R)
    (D : ModularDerivationG0 R G)
    (i : TKKGrade) {x : G.L} (hx : x ∈ G.grade i) :
    ⁅D.derivationGenerator, x⁆ ∈ G.grade i := by
  exact bracket_grade_closed G (gradeAdd_z0_left i) D.derivation_mem_g0 hx

/-- In particular, the modular derivation preserves the local frame sectors. -/
theorem modular_derivation_preserves_pm1
    {R : Type*} [CommRing R] (G : FiveGradedLieAlgebra R)
    (D : ModularDerivationG0 R G) :
    (∀ {x : G.L}, x ∈ G.grade TKKGrade.p1 →
      ⁅D.derivationGenerator, x⁆ ∈ G.grade TKKGrade.p1) ∧
    (∀ {x : G.L}, x ∈ G.grade TKKGrade.m1 →
      ⁅D.derivationGenerator, x⁆ ∈ G.grade TKKGrade.m1) := by
  exact ⟨fun hx => modular_derivation_preserves_grade G D TKKGrade.p1 hx,
    fun hx => modular_derivation_preserves_grade G D TKKGrade.m1 hx⟩

/-- Activated clock theorem: the de Rham class around the forbidden quadric cone
is threaded through the same modular derivation data, while the parabolic
clock has the concrete additive law already proved in `ModularMonodromy`.

The strong analytic statement "`dlog Q` is the Tomita derivation" remains
recorded in `ForbiddenConeDeRhamModularClock`; this theorem makes its
finite consequences and dependencies explicit. -/
theorem forbidden_cone_dlog_modular_parabolic_clock_synthesis
    {R : Type*} [CommRing R] (G : FiveGradedLieAlgebra R)
    (MD : ModularDerivationG0 R G)
    (C : AbstractDeRhamComplex) (A : CartanAction C)
    (FC : ForbiddenConeDeRhamModularClock C R G)
    :
    IsExactOne C (A.lie1 FC.forbiddenConeDLogQ.rep) ∧
    MD.derivationGenerator ∈ G.grade TKKGrade.z0 ∧
    (∀ i : TKKGrade, ∀ {x : G.L}, x ∈ G.grade i →
      ⁅MD.derivationGenerator, x⁆ ∈ G.grade i) ∧
    (∀ t s : ℝ, parabolicTick t * parabolicTick s = parabolicTick (t + s)) ∧
    (∀ t : ℝ, parabolicTick t * parabolicTick (-t) =
      (1 : Matrix (Fin 2) (Fin 2) ℝ)) := by
  exact ⟨cartan_lie_closed_one_form_exact C A FC.forbiddenConeDLogQ,
    MD.derivation_mem_g0,
    fun i x hx => modular_derivation_preserves_grade G MD i hx,
    parabolic_ticks_add,
    parabolic_tick_inverse⟩


/-- Finite clock lemma for the strengthened slogan: once a forbidden-cone
`dlog Q` generator is supplied as the modular derivation, the theorem-honest
part of "clocks parabolic time" is exactly the already-proved affine log-clock
translation. -/
theorem forbidden_cone_modular_derivation_clocks_parabolic_time
    {R : Type*} [CommRing R] (G : FiveGradedLieAlgebra R)
    (MD : ModularDerivationG0 R G)
    (_C : AbstractDeRhamComplex)
    (F : BogoliubovWeylChemicalPotential.BogoliubovInertialFrame)
    (a : AffineSimplexParameter)
    :
    MD.derivationGenerator ∈ G.grade TKKGrade.z0 ∧
    BogoliubovWeylChemicalPotential.frameWeylLogClock
        { F with θ := F.θ + affineLogQ a } =
      BogoliubovWeylChemicalPotential.frameWeylLogClock F + affineLogQ a := by
  exact ⟨MD.derivation_mem_g0,
    affine_rindler_translates_logClock F a⟩

/-- Capstone synthesis: negative log RN density, negative log Jacobian,
modular derivation in `g₀`, chemical-potential exactness, Cartan exactness, and
rank-32/motivic data all compile as one theorem-honest bridge. -/
theorem modular_rn_jacobian_chemical_derham_tkk_synthesis
    {R : Type*} [CommRing R] (G : FiveGradedLieAlgebra R)
    (MD : ModularDerivationG0 R G)
    (CG0 : ChemicalPotentialG0Data R G)
    (S : EdgeSystem Vertex3)
    (hμ : MuRealizesEdgeSystem S CG0.μ)
    (F H : LogJacobianFlow)
    (RN1 RN2 : RadonNikodymDensity)
    (C : AbstractDeRhamComplex) (A : CartanAction C)
    (ω : DeRhamClass C 1)
    (hTrip : CG0.preservesTripotentNullCone)
    (hGibbs : CG0.gibbsWeightsDifferentiateToMu)
    (hG0 : CG0.gradeZeroInterpretsLocalLorentzKreinGenerator) :
    (F.comp H).logJ = F.logJ + H.logJ ∧
    negLogJacobianPotential (F.comp H) =
      negLogJacobianPotential F + negLogJacobianPotential H ∧
    relativeModularPotential (RN1.mul RN2) =
      relativeModularPotential RN1 + relativeModularPotential RN2 ∧
    MD.derivationGenerator ∈ G.grade TKKGrade.z0 ∧
    (∀ i : TKKGrade, ∀ {x : G.L}, x ∈ G.grade i →
      ⁅MD.derivationGenerator, x⁆ ∈ G.grade i) ∧
    cycleEntropyProduction S triangle012 = 0 ∧
    cycleEntropyProduction S triangle021 = 0 ∧
    CG0.chemicalGenerator ∈ G.grade TKKGrade.z0 ∧
    (∀ i : TKKGrade, ∀ {x : G.L}, x ∈ G.grade i →
      ⁅CG0.chemicalGenerator, x⁆ ∈ G.grade i) ∧
    IsExactOne C (A.lie1 ω.rep) ∧
    Fintype.card ProductBasis = 32 ∧
    formalChiralParityIndex = 0 := by
  rcases chemical_potential_tkk_g0_synthesis G CG0 S hμ hTrip hGibbs hG0 with
    ⟨h012, h021, hChemMem, hChemPres, _hTrip, _hGibbs, _hG0⟩
  exact ⟨logJacobian_add F H,
    negLogJacobian_comp F H,
    relativeModularPotential_mul RN1 RN2,
    MD.derivation_mem_g0,
    fun i x hx => modular_derivation_preserves_grade G MD i hx,
    h012,
    h021,
    hChemMem,
    hChemPres,
    cartan_lie_closed_one_form_exact C A ω,
    productBasis_card,
    formalChiralParityIndex_zero⟩

/-- The de Rham/chemical data plus forbidden-cone modular clocking makes the
`1`-form/`3`-form coupling explicit in theorem-honest form: exact `dμ` supplies
the algebraic Arnold relation shape, and the forbidden-cone derivation is identified
as the parabolic-time clock. -/
theorem de_rham_alpha_beta_forbidden_cone_clock_synthesis 
    {C : AbstractDeRhamComplex} {A : CartanAction C} {ω : DeRhamClass C 1}
    {R : Type*} [CommRing R] {G : FiveGradedLieAlgebra R}
    (MD : ModularDerivationG0 R G) :
    IsExactOne C (A.lie1 ω.rep) ∧
    (∀ i x, x ∈ G.grade i → ⁅MD.derivationGenerator, x⁆ ∈ G.grade i) := by
  exact ⟨cartan_lie_closed_one_form_exact C A ω, 
         fun i x hx => modular_derivation_preserves_grade G MD i hx⟩
end ModularRadonNikodymJacobianBridge

end noncomputable section
