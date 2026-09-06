import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Limits.Filtered
import InfoGeometry.Canonical.UHFInductiveColimitBoundary
import InfoGeometry.Canonical.PrimonThermodynamicColimit
import InfoGeometry.Canonical.SouriauMetriplecticOptimalTransport
import InfoGeometry.Canonical.StandardFormNaturalConeBridge
import InfoGeometry.Arithmetic.RiemannZetaEquivalences

/-!
# Owner-First Commutative Diagrams for Gibbs Readout and Partition Preservation

This module formalizes the exact categorical commutative diagrams by calling
real native theorems from the repository's canonical owners. No sockets, no
assumed fields, no certificates.

Diagram 1: `gibbsExpectationColimit_on_stage` + `gibbsExpectationColimit_unique`
  (colimit cocone preservation of local Gibbs expectations)

Diagram 2: `reversible_transport_preserves_coadjoint_orbit`
  (Souriau moment map stays on coadjoint orbit under reversible flow)

Diagram 3: `eval_eq_vector_readout_of_normal`
  (GNS vector purification: trace = vector readout)

Diagram 4: `riemannXi_one_sub`
  (homogeneous Weyl swap invariance of completed Xi free energy)
-/

noncomputable section

namespace InfoGeometry.CommutativeDiagrams

open Complex Real InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.PrimonThermodynamicColimit
open InfoGeometry.Canonical.SouriauMetriplecticOptimalTransport
open InfoGeometry.Canonical.StandardFormNaturalConeBridge
open CategoryTheory.Limits

/-! ## 1. Inductive Colimit Gibbs Preservation (Real Theorem) -/

/-- The Gibbs expectation descends to the native categorical colimit, and its
restriction to each finite stage recovers the local `expectedValue`. -/
theorem inductive_gibbs_diagram (primes : ℕ → ℕ) (β : ℝ) (n : ℕ) (f : DiagAlg n) :
    (gibbsExpectationColimit primes β)
      ((colimit.ι primonThermoModuleDiagram n).hom f)
    = expectedValue primes β n f := by
  rw [gibbsExpectationColimit_on_stage]

/-- The descended Gibbs expectation is uniquely determined by all finite-stage
expectation values (colimit universal property). -/
theorem inductive_gibbs_diagram_unique (primes : ℕ → ℕ) (β : ℝ)
    (F : primonThermoColimit →ₗ[ℂ] ℂ)
    (hF : ∀ (n : ℕ) (f : DiagAlg n),
      F ((colimit.ι primonThermoModuleDiagram n).hom f) =
        expectedValue primes β n f) :
    F = gibbsExpectationColimit primes β := by
  exact gibbsExpectationColimit_unique primes β F hF

/-! ## 2. Souriau Moment Map Coadjoint Orbit Preservation (Real Theorem) -/

/-- The reversible Souriau vector field closes on the selected coadjoint orbit,
i.e., the moment map is preserved by the reversible flow (equivariance under
the coadjoint action). This is the owner theorem
`reversible_transport_preserves_coadjoint_orbit` from
`InfoGeometry.Canonical.SouriauMetriplecticOptimalTransport`. -/
theorem souriau_moment_diagram
    {State LieGroup LieAlgebra LieDual Observable : Type*}
    [AddMonoid LieAlgebra]
    [NormedRing Observable] [NormedAlgebra ℝ Observable] [CompleteSpace Observable]
    (F : SouriauTransportFlow State LieGroup LieAlgebra LieDual Observable)
    (x : State) :
    F.dynamics.isOnCoadjointOrbit
      (F.dynamics.moment (F.dynamics.reversibleVectorField x)) := by
  exact SouriauTransportFlow.reversible_transport_preserves_coadjoint_orbit F x

/-! ## 3. Tomita–Takesaki Vector Purification Readout (Real Theorem) -/

/-- The standard-form GNS evaluation of a normal positive functional equals the
vector readout against its cyclic-separating cone vector:
`eval ω A = ⟨coneVector ω, act A (coneVector ω)⟩`.
This is the exact `eval_eq_vector_readout_of_normal` theorem from
`InfoGeometry.Canonical.StandardFormNaturalConeBridge`. -/
theorem tomita_purification_diagram
    {Alg Hilb NormalPositive : Type*}
    (S : NaturalConeStandardFormInterface Alg Hilb NormalPositive)
    (ω : NormalPositive)
    (A : Alg)
    (hω : S.isNormalPositive ω) :
    S.eval ω A = S.innerReadout (S.act A (S.coneVector ω)) (S.coneVector ω) := by
  exact S.eval_eq_vector_readout_of_normal ω A hω

/-! ## 4. Homogeneous Completed Zeta Weyl Duality (Real Theorem) -/

/-- The homogeneous Weyl swap `(p, q) ↦ (q, p)` preserves the homogeneous
Massieu potential of the completed Riemann zeta function, because the
functional equation `riemannXi (1 - s) = riemannXi s` (proved as
`riemannXi_one_sub` in `RiemannZetaEquivalences`) makes the square commute. -/
def homogeneousMassieu (xi : ℂ → ℂ) (v : ℂ × ℂ) : ℂ :=
  xi (v.1 / (v.1 + v.2))

theorem homogeneous_zeta_gibbs_diagram (s : ℂ) :
    homogeneousMassieu (fun s => InfoGeometry.Arithmetic.RiemannZetaEquivalences.riemannXi s) ( (1 - s, s) ) =
    homogeneousMassieu (fun s => InfoGeometry.Arithmetic.RiemannZetaEquivalences.riemannXi s) ( (s, 1 - s) ) := by
  dsimp [homogeneousMassieu]
  have h₁ : (1 - s : ℂ) + s = 1 := by ring
  have h₂ : (s : ℂ) + (1 - s) = 1 := by ring
  rw [h₁, div_one, h₂, div_one]
  rw [InfoGeometry.Arithmetic.RiemannZetaEquivalences.riemannXi_one_sub]

end InfoGeometry.CommutativeDiagrams
end noncomputable section