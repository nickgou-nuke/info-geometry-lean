import Mathlib
import InfoGeometry.Meta.Architecture
import InfoGeometry.Analytic.ZetaRegVolume
import InfoGeometry.Canonical.OperatorSurgery
import InfoGeometry.Canonical.WeylCharacterEquivalence
import InfoGeometry.Canonical.SuperKMS_Equilibrium
import InfoGeometry.Exceptional.Freudenthal
import InfoGeometry.Applications.STUBlackHoleQubit

/-!
# InfoGeometry/Canonical/OpenProblemFormalization.lean

Formal mathematical problem statements for witness-gated closure.

This file records precise mathematical conjecture schemas required to bridge
current witness-gated interfaces to full constructive proofs. These problems
are stated as `Prop` definitions, not as theorems or axioms, so they do not
contaminate the verified core.
-/

namespace InfoGeometry.Canonical.OpenProblems

open InfoGeometry.Exceptional.Freudenthal
open InfoGeometry.Applications.STUQubit
open Filter

/--
Placeholder type for the analytic elliptic-operator object that the open
problem asks future work to formalize.

This is intentionally weak: it records only the dependency shape. A future
version should replace this by a structured elliptic operator datum.
-/
abbrev AnyEllipticOperator (_M : Type*) := Unit

noncomputable section

/-! ## Infinite-dimensional relative and Koliha-Drazin spectral surgery -/

/-
Placeholder predicates.

These are deliberately proof-carrying predicates, not raw `Prop` slots inside
the witness structures.  When the closed-operator API exists, replace the
bodies `True` by the real definitions.
-/

def IsClosedGraph
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (Dom : Submodule ℂ X)
    (_op : Dom →ₗ[ℂ] X) : Prop :=
  True

def IsDenseDomain
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (_Dom : Submodule ℂ X) : Prop :=
  True

def HasNonemptyResolvent
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (_Dom : Submodule ℂ X)
    (_op : _Dom →ₗ[ℂ] X) : Prop :=
  True

/--
Schematic closed densely-defined complex operator.

A future version should replace this by the repository's actual closed-operator
API, including graph closedness, domain density, resolvent, extended spectrum,
Riesz projections, and holomorphic functional calculus.
-/
structure ClosedOperatorDatum
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X] where
  Dom : Submodule ℂ X
  op : Dom →ₗ[ℂ] X
  closedGraph : IsClosedGraph Dom op
  denseDomain : IsDenseDomain Dom
  resolventNonempty : HasNonemptyResolvent Dom op

namespace ClosedOperatorDatum

/--
A bounded operator maps into the domain of a closed operator.
-/
def MapsIntoDomain
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (A : ClosedOperatorDatum X)
    (B : X →L[ℂ] X) : Prop :=
  ∀ x : X, B x ∈ A.Dom

/--
Domain-sensitive application of a closed operator after a bounded operator.
-/
def applyAfterBounded
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (A : ClosedOperatorDatum X)
    (B : X →L[ℂ] X)
    (hB : A.MapsIntoDomain B)
    (x : X) : X :=
  A.op ⟨B x, hB x⟩

/--
A bounded projection/operator reduces the closed operator `A` on its domain.
-/
def ReducesBounded
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (A : ClosedOperatorDatum X)
    (P : X →L[ℂ] X) : Prop :=
  ∃ hP : ∀ x : A.Dom, P (x : X) ∈ A.Dom,
    ∀ x : A.Dom,
      A.op ⟨P (x : X), hP x⟩ = P (A.op x)

end ClosedOperatorDatum
/--
Quasinilpotence for a bounded operator.

The use of `n + 1` avoids the irrelevant `n = 0` root.
-/
def IsQuasinilpotent
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (T : X →L[ℂ] X) : Prop :=
  Tendsto
    (fun n : ℕ =>
      Real.rpow ‖T ^ (n + 1)‖ (1 / ((n + 1 : ℕ) : ℝ)))
    atTop
    (nhds 0)

/--
Hypotheses for a bounded relative spectral set `σ₀` of the extended spectrum.

Mathematically this means:

* `σ₀ ⊂ σₑ(A)`;
* `σ₀` is clopen in the relative topology of `σₑ(A)`;
* `0 ∈ σ₀`;
* `σ₀` is bounded in `ℂ`;
* an admissible contour `Γ₀` separates `σ₀` from the complementary spectral set;
* `ξ` is chosen with `‖ξ‖ > 2 sup_{λ ∈ σ₀} ‖λ‖`.

The concrete spectral-set and contour fields are placeholders until the local
closed-operator spectral calculus is formalized.
-/
structure RelativeSpectralSetHypotheses
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (A : ClosedOperatorDatum X) where
  sigma0 : Set ℂ
  zero_mem : 0 ∈ sigma0
  radius : ℝ
  radius_nonneg : 0 ≤ radius
  sigma_norm_le : ∀ z : ℂ, z ∈ sigma0 → ‖z‖ ≤ radius
  xi : ℂ
  xi_large : 2 * radius < ‖xi‖
  spectralSetOfExtendedSpectrum : Prop
  Gamma0 : Type
  Gamma0_admissible : Prop

/--
Placeholder for the contour formula

  `Pσ = (2πi)⁻¹ ∮_{Γ₀} (zI - A)⁻¹ dz`.
-/
def RieszProjectionFormula
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (_A : ClosedOperatorDatum X)
    (_σ : RelativeSpectralSetHypotheses _A)
    (_Pσ : X →L[ℂ] X) : Prop :=
  True

/--
Placeholder for the topological spectral decomposition

  `X = R(Pσ) ⊕ N(Pσ)`.
-/
def SpectralTopologicalDecompositionFormula
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (_A : ClosedOperatorDatum X)
    (_σ : RelativeSpectralSetHypotheses _A)
    (_Pσ _Pcore : X →L[ℂ] X) : Prop :=
  True

/--
Placeholder for bounded spectral-set branch regularity:

  `R(Pσ) ⊂ D(Aⁿ)` for every `n`.
-/
def BranchMapsDomainAllPowersFormula
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (_A : ClosedOperatorDatum X)
    (_σ : RelativeSpectralSetHypotheses _A)
    (_Pσ : X →L[ℂ] X) : Prop :=
  True

/--
Placeholder for Tran's shifted inverse formula

  `ADσ = (A - ξ • Pσ)⁻¹ * Pcore`.
-/
def ShiftedRelativeDrazinFormula
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (_A : ClosedOperatorDatum X)
    (_σ : RelativeSpectralSetHypotheses _A)
    (_Pσ _Pcore _ADσ : X →L[ℂ] X) : Prop :=
  True

/--
Placeholder for the spectral-set identity

  `spectrum(APσ) = σ₀`.
-/
def SpectralBranchSpectrumFormula
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (_A : ClosedOperatorDatum X)
    (_σ : RelativeSpectralSetHypotheses _A)
    (_Pσ _APσ : X →L[ℂ] X) : Prop :=
  True

/--
Placeholder for the Koliha-Drazin holomorphic functional calculus formula.

Mathematically, `AD = f(A)`, where `f = 0` near `0` and `f z = z⁻¹` on the
core spectral component. For an unbounded closed operator this should be read
in the extended/Riemann-sphere calculus, not necessarily as a finite contour
around the entire nonzero component.
-/
def KolihaDrazinFunctionalCalculusFormula
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (_A : ClosedOperatorDatum X)
    (_AD : X →L[ℂ] X) : Prop :=
  True

/--
Full Koliha zero-branch hypotheses.

Here the zero branch may be empty, as in the invertible case, or `{0}`, as in
the isolated singular case.
-/
structure KolihaZeroBranchHypotheses
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (A : ClosedOperatorDatum X) where
  sigmaNil : Set ℂ
  sigmaNil_subset_singleton :
    sigmaNil ⊆ ({0} : Set ℂ)
  zeroNotAccumulation : Prop
  coreBoundedAwayFromZero : Prop
  spectralSetOfExtendedSpectrum : Prop
  GammaZero : Type
  GammaZero_admissible : Prop
  GammaCore : Type
  GammaCore_admissibleInRiemannSphere : Prop

/--
Relative spectral-set Drazin surgery.

This is the correct owner target for an arbitrary bounded spectral set `σ₀`
containing `0`.

Important: the branch `APσ` is only a bounded spectral-set branch. It is not
claimed to be quasinilpotent unless `σ₀ = {0}`.
-/
structure RelativeSpectralDrazinSurgeryWitness
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (A : ClosedOperatorDatum X)
    (σ : RelativeSpectralSetHypotheses A) where
  /-- Riesz projection for the bounded spectral set `σ₀`. -/
  Pσ : X →L[ℂ] X
  /-- Complementary core projection. -/
  Pcore : X →L[ℂ] X
  /-- Relative Drazin inverse `A^{D,σ}`. -/
  ADσ : X →L[ℂ] X
  /--
  The bounded spectral branch represented by `A ∘ Pσ`.

  For a general spectral set this branch has spectrum `σ₀`, not necessarily
  `{0}`.
  -/
  APσ : X →L[ℂ] X
  Pσ_idempotent :
    Pσ.comp Pσ = Pσ
  Pcore_eq :
    Pcore = ContinuousLinearMap.id ℂ X - Pσ
  Pcore_idempotent :
    Pcore.comp Pcore = Pcore
  complementary :
    Pσ + Pcore = ContinuousLinearMap.id ℂ X
  disjoint_left :
    Pσ.comp Pcore = 0
  disjoint_right :
    Pcore.comp Pσ = 0
  /--
  Placeholder for the contour formula

  `Pσ = (2πi)⁻¹ ∮_{Γ₀} (zI - A)⁻¹ dz`.
  -/
  Pσ_contour_formula :
    RieszProjectionFormula A σ Pσ
  /--
  Placeholder for the topological spectral decomposition

  `X = R(Pσ) ⊕ N(Pσ)`.
  -/
  topological_decomposition :
    SpectralTopologicalDecompositionFormula A σ Pσ Pcore
  /--
  Placeholder for bounded spectral-set branch regularity:

  `R(Pσ) ⊂ D(Aⁿ)` for every `n`.
  -/
  Pσ_maps_domain_all_powers :
    BranchMapsDomainAllPowersFormula A σ Pσ
  Pσ_reduces_A :
    A.ReducesBounded Pσ
  Pcore_reduces_A :
    A.ReducesBounded Pcore
  /-- The range of `Pσ` lies in `D(A)`. -/
  Pσ_maps_domain :
    A.MapsIntoDomain Pσ
  /--
  `APσ` is the bounded operator represented by `A ∘ Pσ`.
  -/
  APσ_agrees :
    ∀ x : X,
      A.applyAfterBounded Pσ Pσ_maps_domain x = APσ x
  /--
  Placeholder for the spectral-set identity

  `spectrum(APσ) = σ₀`.

  This is the field that prevents the general branch from being mislabeled
  quasinilpotent.
  -/
  spectral_branch_spectrum :
    SpectralBranchSpectrumFormula A σ Pσ APσ
  /--
  Placeholder for Tran's shifted-inverse formula

  `ADσ = (A - ξ • Pσ)⁻¹ * Pcore`.
  -/
  ADσ_shifted_inverse_formula :
    ShiftedRelativeDrazinFormula A σ Pσ Pcore ADσ
  /-- The range of `ADσ` lies in `D(A)`, so `A ∘ ADσ` is meaningful. -/
  ADσ_maps_domain :
    A.MapsIntoDomain ADσ
  /--
  Core identity:

  `A A^{D,σ} = Pcore`.
  -/
  ADσ_core_identity :
    ∀ x : X,
      A.applyAfterBounded ADσ ADσ_maps_domain x = Pcore x
  /--
  Companion identity on the domain of the closed operator:

  `Aᴰ,σ A = Pcore` on `D(A)`.
  -/
  ADσ_left_core_identity :
    ∀ x : A.Dom,
      ADσ (A.op x) = Pcore (x : X)
  /--
  Equivalent projection identity:

  `Pσ = I - A A^{D,σ}`.
  -/
  projection_identity :
    ∀ x : X,
      Pσ x =
        x - A.applyAfterBounded ADσ ADσ_maps_domain x

/--
Owner theorem target for relative spectral-set Drazin surgery.

This theorem is valid for a bounded spectral set `σ₀` containing `0`.

It must not assert quasinilpotence of `APσ`.
-/
def RelativeSpectralDrazinSurgery : Prop :=
  ∀ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (A : ClosedOperatorDatum X)
    (σ : RelativeSpectralSetHypotheses (X := X) A),
      σ.spectralSetOfExtendedSpectrum →
      σ.Gamma0_admissible →
      Nonempty (RelativeSpectralDrazinSurgeryWitness A σ)

/--
Strict Koliha-Drazin singleton surgery.

This is the non-invertible/singular branch formulation where the relative
spectral set is exactly `{0}`.
-/
structure StrictKolihaDrazinSingletonSurgeryWitness
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (A : ClosedOperatorDatum X)
    (σ : RelativeSpectralSetHypotheses (X := X) A)
    where
  relative :
    RelativeSpectralDrazinSurgeryWitness A σ
  sigma_zero :
    σ.sigma0 = {0}
  AD_functional_calculus_formula :
    KolihaDrazinFunctionalCalculusFormula A relative.ADσ
  /--
  The singleton spectral branch is quasinilpotent.

  This is the infinite-dimensional replacement for finite-dimensional
  nilpotence.
  -/
  nil_branch_quasinilpotent :
    IsQuasinilpotent relative.APσ

/--
Owner theorem target for the strict Koliha-Drazin singleton case.

This is the singleton specialization of the relative theorem, not the full
generalized Drazin invertible case.
-/
def StrictKolihaDrazinSingletonSurgery : Prop :=
  ∀ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (A : ClosedOperatorDatum X)
    (σ : RelativeSpectralSetHypotheses (X := X) A),
      σ.spectralSetOfExtendedSpectrum →
      σ.Gamma0_admissible →
      σ.sigma0 = {0} →
      Nonempty (StrictKolihaDrazinSingletonSurgeryWitness A σ)

/--
Full Koliha-Drazin surgery witness.

This is separate from the Tran-style relative witness so that the invertible
case is included. The zero branch is allowed to be empty; if it is nonempty,
the hypothesis `sigmaNil_subset_singleton` forces it to be `{0}`.
-/
structure KolihaDrazinSurgeryWitness
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (A : ClosedOperatorDatum X)
    (κ : KolihaZeroBranchHypotheses A) where
  Pnil : X →L[ℂ] X
  Pcore : X →L[ℂ] X
  AD : X →L[ℂ] X
  Anil : X →L[ℂ] X
  Pcore_eq :
    Pcore = ContinuousLinearMap.id ℂ X - Pnil
  Pnil_idempotent :
    Pnil.comp Pnil = Pnil
  Pcore_idempotent :
    Pcore.comp Pcore = Pcore
  complementary :
    Pnil + Pcore = ContinuousLinearMap.id ℂ X
  disjoint_left :
    Pnil.comp Pcore = 0
  disjoint_right :
    Pcore.comp Pnil = 0
  Pnil_maps_domain :
    A.MapsIntoDomain Pnil
  nil_agrees :
    ∀ x : X,
      A.applyAfterBounded Pnil Pnil_maps_domain x = Anil x
  /--
  The zero branch is quasinilpotent. In the invertible case this is the zero
  branch with `Pnil = 0`.
  -/
  nil_quasinilpotent :
    IsQuasinilpotent Anil
  AD_functional_calculus_formula :
    KolihaDrazinFunctionalCalculusFormula A AD
  AD_maps_domain :
    A.MapsIntoDomain AD
  /--
  Domain-sensitive core identity:

  `A Aᴰ = Pcore`.
  -/
  core_identity :
    ∀ x : X,
      A.applyAfterBounded AD AD_maps_domain x = Pcore x
  /--
  Companion identity on the domain of the closed operator:

  `Aᴰ A = Pcore` on `D(A)`.
  -/
  drazin_left_core_identity :
    ∀ x : A.Dom,
      AD (A.op x) = Pcore (x : X)
  AD_kills_nil_right :
    AD.comp Pnil = 0
  AD_kills_nil_left :
    Pnil.comp AD = 0
  AD_supported_on_core_left :
    Pcore.comp AD = AD
  AD_supported_on_core_right :
    AD.comp Pcore = AD

/--
Owner target for full Koliha-Drazin surgery.

This includes both cases:

* `0 ∈ ρ(A)`, where the zero branch is empty and `AD = A⁻¹`;
* `0 ∈ iso σ(A)`, where the zero branch is `{0}` and `Anil` is
  quasinilpotent.
-/
def KolihaDrazinSurgery : Prop :=
  ∀ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (A : ClosedOperatorDatum X)
    (κ : KolihaZeroBranchHypotheses A),
      κ.zeroNotAccumulation →
      κ.coreBoundedAwayFromZero →
      κ.spectralSetOfExtendedSpectrum →
      κ.GammaZero_admissible →
      κ.GammaCore_admissibleInRiemannSphere →
      Nonempty (KolihaDrazinSurgeryWitness A κ)

namespace Statements

/--
## Problem 1: General Drazin Existence

Every endomorphism of a finite-dimensional real vector space admits a Drazin
inverse witness.
-/
def DrazinExistenceFiniteDimensional : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (A : V →ₗ[ℝ] V),
    ∃ D : V →ₗ[ℝ] V,
      InfoGeometry.Canonical.DrazinInverseWitness A D

/--
## Problem 2: Heat Kernel Small-Time Asymptotics

For elliptic operators on compact spaces/manifolds, the heat-kernel supertrace
exists and admits a canonical small-time asymptotic expansion.

The current formulation uses only a topological compactness hypothesis and a
placeholder operator type. A future version should strengthen this to smooth
compact manifolds, vector bundles, elliptic differential operators, and trace
class heat semigroups.
-/
def HeatKernelAsymptoticsExistence : Prop :=
  ∀ {M : Type*} [TopologicalSpace M] [CompactSpace M]
    (_Δ : AnyEllipticOperator M),
    ∃ W : InfoGeometry.Analytic.HeatKernelWitness,
      W.smallTimeAsymptotics ∧ W.traceClass

/--
## Problem 3: Zeta Analytic Continuation

The spectral zeta function associated to a heat-kernel witness admits a
meromorphic continuation regular at `s = 0`.
-/
def SpectralZetaContinuationExistence : Prop :=
  ∀ (W : InfoGeometry.Analytic.HeatKernelWitness),
    ∃ Z : InfoGeometry.Analytic.SpectralZetaWitness,
      Z.kernel = W ∧ Z.analyticContinuation

/--
## Problem 4 placeholder: TKK Jacobi identity predicate not yet formalized

This is a marker that the actual bracket-level Jacobi predicate still needs to
be written. It is deliberately not stated as a mathematical theorem.
-/
def TKKJacobiIdentity_FormalizationPending : Prop :=
  True

/--
## Problem 5: STU-Freudenthal polynomial embedding for a supplied cubic datum

For a supplied cubic Jordan datum `D`, an STU embedding is a map from the real
3-qubit amplitude space into the Freudenthal charge space such that the
Freudenthal quartic invariant agrees with Cayley's hyperdeterminant, up to an
explicit sign convention.

The fully concrete theorem should later specialize `D` to the diagonal STU
datum.
-/
def STUFreudenthalEmbeddingFor
    {J : Type*} [AddCommGroup J] [Module ℝ J]
    (D : CubicJordanDatum J) : Prop :=
  ∃ (embedSTU : ThreeQubitState → FreudenthalCharge J) (sign : ℝ),
    (sign = 1 ∨ sign = -1) ∧
      ∀ ψ : ThreeQubitState,
        FreudenthalCharge.quarticInvariant D (embedSTU ψ) =
          sign * ThreeQubitState.cayleyHyperdeterminant ψ

/--
## Problem 6: KMS State Existence for Supercharges

Every admissible supercharge datum admits a KMS equilibrium state satisfying
the detailed-balance identity.

The present statement is intentionally schematic. A stronger future version
should include the algebra of observables, the dynamics, inverse temperature,
positivity/self-adjointness hypotheses, and the actual KMS boundary condition.
-/
def KMSExistenceSupercharge : Prop :=
  ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (_Q : H →L[ℝ] H),
    ∃ S : InfoGeometry.Canonical.SuperKMS_Equilibrium.SuperKMSEquilibriumState,
      S.absorption = S.spontaneousEmission + S.stimulatedEmission

/--
## Problem 7 placeholder: information-bottleneck monotonicity predicate not yet formalized

This is a marker that the actual mutual-information inequality still needs to
be written.
-/
def IBMonotonicity_FormalizationPending : Prop :=
  True

end Statements

end

end InfoGeometry.Canonical.OpenProblems
