import proofs.CooperadEnvironmentalRank32
import proofs.TKKJordanPairData
import proofs.LightConeTripotentMatrixBridge

/-!
# Chemical potential to TKK grade-zero data

Finite bridge for the next layer:

* a chemical potential `μ : Vertex3 → ℝ` is a vertex potential;
* its edge differences are the Gibbs/Jaynes log-ratio driver at finite level;
* the actual map from `μ` to a TKK grade-zero generator is supplied as data;
* once the image lies in `g₀`, TKK grade bookkeeping proves it acts internally
  on every grade, especially the `±1` local frame sectors.

No analytic KMS theorem, no physical metric theorem, and no concrete `su(2,2)`
real form is asserted here.
-/

noncomputable section

namespace ChemicalPotentialTKKGradeZero

open TKKJordanPairData
open VertexAlgebraBraidingCocycle
open VertexAlgebraBraidingCocycle.EdgeSystem
open QuadricConf3BraidingCooperadBridge
open LightConeConf3DeRhamCooperad
open NonIsoConf3DeRhamCooperad
open CooperadEnvironmentalRank32
open LightConeTripotentMatrixBridge

/-- A local chemical potential on the three configuration vertices. -/
abbrev ChemicalPotential := Vertex3 → ℝ

/-- Chemical-potential edge difference, the finite Gibbs log-ratio skeleton. -/
def muEdgeDifference (μ : ChemicalPotential) (i j : Vertex3) : ℝ := μ j - μ i

/-- Chemical-potential exactness as a log-ratio edge system. -/
def MuRealizesEdgeSystem (S : EdgeSystem Vertex3) (μ : ChemicalPotential) : Prop :=
  IsExact S μ

/-- The chemical potential automatically determines an exact edge one-form. -/
theorem muEdgeDifference_is_exact_form (S : EdgeSystem Vertex3) (μ : ChemicalPotential)
    (h : MuRealizesEdgeSystem S μ) :
    ∀ i j, EdgeSystem.logRatio S i j = muEdgeDifference μ i j := by
  intro i j
  simpa [MuRealizesEdgeSystem, muEdgeDifference] using h i j

/-- Hence exact chemical potential kills Wilson entropy cycles on both oriented
triangles. -/
theorem chemical_potential_detailed_balance_kills_triangles
    (S : EdgeSystem Vertex3) (μ : ChemicalPotential)
    (h : MuRealizesEdgeSystem S μ) :
    cycleEntropyProduction S triangle012 = 0 ∧
    cycleEntropyProduction S triangle021 = 0 := by
  exact ⟨detailed_balance_kills_triangle012 S μ h,
    detailed_balance_kills_triangle021 S μ h⟩

/-- Data mapping local chemical potential values into grade zero of a concrete
five-graded TKK algebra. -/
structure ChemicalPotentialG0Data (R : Type*) [CommRing R]
    (G : FiveGradedLieAlgebra R) where
  μ : ChemicalPotential
  chemicalGenerator : G.L
  chemicalGenerator_mem_g0 : chemicalGenerator ∈ G.grade TKKGrade.z0
  preservesTripotentNullCone : Prop
  gibbsWeightsDifferentiateToMu : Prop
  gradeZeroInterpretsLocalLorentzKreinGenerator : Prop

/-- Grade-zero chemical-potential generators act internally on every TKK grade. -/
theorem chemical_g0_bracket_preserves_grade
    {R : Type*} [CommRing R] (G : FiveGradedLieAlgebra R)
    (C : ChemicalPotentialG0Data R G)
    (i : TKKGrade) {x : G.L} (hx : x ∈ G.grade i) :
    ⁅C.chemicalGenerator, x⁆ ∈ G.grade i := by
  exact bracket_grade_closed G (gradeAdd_z0_left i) C.chemicalGenerator_mem_g0 hx

/-- In particular, the chemical-potential generator preserves the positive local
frame sector `g_{+1}`. -/
theorem chemical_g0_preserves_p1
    {R : Type*} [CommRing R] (G : FiveGradedLieAlgebra R)
    (C : ChemicalPotentialG0Data R G) {x : G.L} (hx : x ∈ G.grade TKKGrade.p1) :
    ⁅C.chemicalGenerator, x⁆ ∈ G.grade TKKGrade.p1 :=
  chemical_g0_bracket_preserves_grade G C TKKGrade.p1 hx

/-- And it preserves the negative local frame sector `g_{-1}`. -/
theorem chemical_g0_preserves_m1
    {R : Type*} [CommRing R] (G : FiveGradedLieAlgebra R)
    (C : ChemicalPotentialG0Data R G) {x : G.L} (hx : x ∈ G.grade TKKGrade.m1) :
    ⁅C.chemicalGenerator, x⁆ ∈ G.grade TKKGrade.m1 :=
  chemical_g0_bracket_preserves_grade G C TKKGrade.m1 hx

/-- Conditional synthesis: chemical potentials give exact Gibbs log-ratio
one-forms, kill detailed-balance Wilson cycles, and, once mapped into TKK `g₀`,
act internally on all five grades. -/
theorem chemical_potential_tkk_g0_synthesis
    {R : Type*} [CommRing R] (G : FiveGradedLieAlgebra R)
    (C : ChemicalPotentialG0Data R G)
    (S : EdgeSystem Vertex3)
    (hμ : MuRealizesEdgeSystem S C.μ)
    (hTrip : C.preservesTripotentNullCone)
    (hGibbs : C.gibbsWeightsDifferentiateToMu)
    (hG0 : C.gradeZeroInterpretsLocalLorentzKreinGenerator) :
    cycleEntropyProduction S triangle012 = 0 ∧
    cycleEntropyProduction S triangle021 = 0 ∧
    C.chemicalGenerator ∈ G.grade TKKGrade.z0 ∧
    (∀ i : TKKGrade, ∀ {x : G.L}, x ∈ G.grade i →
      ⁅C.chemicalGenerator, x⁆ ∈ G.grade i) ∧
    C.preservesTripotentNullCone ∧
    C.gibbsWeightsDifferentiateToMu ∧
    C.gradeZeroInterpretsLocalLorentzKreinGenerator := by
  rcases chemical_potential_detailed_balance_kills_triangles S C.μ hμ with ⟨h012, h021⟩
  have hPres :
      ∀ i : TKKGrade, ∀ {x : G.L}, x ∈ G.grade i →
        ⁅C.chemicalGenerator, x⁆ ∈ G.grade i := by
    intro i x hx
    simpa using chemical_g0_bracket_preserves_grade G C i hx
  refine And.intro ?_ ?_
  · simpa using h012
  · refine And.intro ?_ ?_
    · simpa using h021
    · refine And.intro ?_ ?_
      · simpa using C.chemicalGenerator_mem_g0
      · refine And.intro ?_ ?_
        · simpa using hPres
        · refine And.intro ?_ ?_
          · simpa using hTrip
          · refine And.intro ?_ ?_
            · simpa using hGibbs
            · simpa using hG0

/-- Strengthened finite bridge: in addition to the `g₀` preservation theorem, the
chemical-potential data is compatible with the rank-32 environmental
cooperad split and the canonical determinant-null tripotent representative.

The physical reading "chemical-potential gradients are Lorentz/Krein
derivations" remains the explicit field
`gradeZeroInterpretsLocalLorentzKreinGenerator`. -/
theorem chemical_potential_tkk_g0_rank32_environmental_synthesis
    {R : Type*} [CommRing R] (G : FiveGradedLieAlgebra R)
    (C : ChemicalPotentialG0Data R G)
    (S : EdgeSystem Vertex3)
    (hμ : MuRealizesEdgeSystem S C.μ)
    (hTrip : C.preservesTripotentNullCone)
    (hGibbs : C.gibbsWeightsDifferentiateToMu)
    (hG0 : C.gradeZeroInterpretsLocalLorentzKreinGenerator) :
    Fintype.card EnvironmentalRank32Basis = 32 ∧
    environmentalSlot Edge3.e12 = ClusterSlot.inner ∧
    environmentalSlot Edge3.e13 = ClusterSlot.outer ∧
    environmentalSlot Edge3.e23 = ClusterSlot.outer ∧
    MatrixLightCone E00 ∧
    IsAssociativeTripotent E00 ∧
    cycleEntropyProduction S triangle012 = 0 ∧
    cycleEntropyProduction S triangle021 = 0 ∧
    C.chemicalGenerator ∈ G.grade TKKGrade.z0 ∧
    (∀ i : TKKGrade, ∀ {x : G.L}, x ∈ G.grade i →
      ⁅C.chemicalGenerator, x⁆ ∈ G.grade i) ∧
    C.preservesTripotentNullCone ∧
    C.gibbsWeightsDifferentiateToMu ∧
    C.gradeZeroInterpretsLocalLorentzKreinGenerator := by
  rcases chemical_potential_tkk_g0_synthesis G C S hμ hTrip hGibbs hG0 with
    ⟨h012, h021, hMem, hPres, hTrip', hGibbs', hG0'⟩
  refine And.intro ?_ ?_
  · simpa using environmentalRank32Basis_card
  · refine And.intro ?_ ?_
    · simp
    · refine And.intro ?_ ?_
      · simp
      · refine And.intro ?_ ?_
        · simp
        · refine And.intro ?_ ?_
          · simp
          · refine And.intro ?_ ?_
            · simp
            · refine And.intro ?_ ?_
              · simpa using h012
              · refine And.intro ?_ ?_
                · simpa using h021
                · refine And.intro ?_ ?_
                  · simpa using hMem
                  · refine And.intro ?_ ?_
                    · simpa using hPres
                    · refine And.intro ?_ ?_
                      · simpa using hTrip'
                      · refine And.intro ?_ ?_
                        · simpa using hGibbs'
                        · simpa using hG0'

end ChemicalPotentialTKKGradeZero

end noncomputable section
