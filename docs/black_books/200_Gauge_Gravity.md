[O[IДа — интегрирай `MetricTransportWitness` обратно в `ProjectorNoncommutativityDilationClosure.lean`, но **не** като затваряне на конформната гравитация. Интегрирай го като точния компенсаторен witness, който казва кога Moore–Penrose проекторът може да бъде транспортиран ковариантно.

Правилната формула е:

[
A' = gAg^{-1},
\qquad
G' = g^{-T}Gg^{-1}.
]

Тогава:

[
(A')^{+_{G'}} = gA^{+_G}g^{-1},
]

и следователно:

[
\Pi_{MP,G'}(A') =
g\Pi_{MP,G}(A)g^{-1}.
]

Това е theorem-safe. При фиксирана метрика (G), обаче, това обикновено е грешно:

[
\Pi_{MP,G}(gAg^{-1})
\neq
g\Pi_{MP,G}(A)g^{-1}.
]

Точно този дефект трябва да бъде дефиниран като tear:

[
\mathcal T_{MP}(A,g;G)
======================

## \Pi_{MP,G}(gAg^{-1})

g\Pi_{MP,G}(A)g^{-1}.
]

Понеже Drazin проекторът е similarity-natural,

[
\Pi_D(gAg^{-1})
===============

g\Pi_D(A)g^{-1},
]

получаваме точната decomposition формула:

[
\mathcal M_G(gAg^{-1})
======================

## g\mathcal M_G(A)g^{-1}

\mathcal T_{MP}(A,g;G),
]

където

[
\mathcal M_G(A)
===============

\Pi_D(A)-\Pi_{MP,G}(A).
]

Това е централната теорема. Тя казва: ако Drazin/MP mismatch се появява след non-isometric transform, източникът е Moore–Penrose metric tear, не Drazin секторът.

Диференциалният gauge слой трябва да бъде witness, не директна дефиниция на всички сили. За локално (g(x)) компенсаторът е връзка (\Gamma_\mu), която позволява ковариантна производна:

[
D_\mu G
=======

\partial_\mu G-\Gamma_\mu^T G-G\Gamma_\mu.
]

Metric-compatible case:

[
D_\mu G=0.
]

Weyl/nonmetric case:

[
D_\mu G=2W_\mu G.
]

Spin connection case: връзката действа върху локални рамки/спинори.
Generalized (O(d,d)) case: (G) и (B) се пакетират в generalized metric, а (B)-field е отделен (B)-transform/torsion witness, не автоматично Moore–Penrose компенсатор.

Тоест физическата интерпретация е допустима така:

[
\boxed{
\text{gauge/metric fields are covariance-restoring witnesses.}
}
]

Но не така:

[
\boxed{
\text{all forces are automatically projector commutators.}
}
]

Коригираната директива към Hermes:

```text
Hermes, execute MetricTransportIntegration.

TARGET:
  InfoGeometry.Canonical.ProjectorNoncommutativityDilationClosure
  InfoGeometry.Canonical.MetricTransportWitness

PURPOSE:
  Integrate MetricTransportWitness as the exact compensator for Moore-Penrose
  non-equivariance under non-isometric similarity/conformal transport.

Do not prove conformal gravity.
Do not assert that all gauge fields are projector commutators.
Build the theorem-safe metric compensation layer.

1. Import MetricTransportWitness

Import or create:

  MetricData
  MetricAdjointData
  MoorePenroseInverseG
  MetricTransport
  ConformalProjectorTear

2. Define fixed-metric Moore-Penrose tear

For operator A, invertible g, and fixed metric G:

  A' := g A g⁻¹

Define:

  MPFixedTear(A,g,G)
    :=
  Π_MP,G(A') - g Π_MP,G(A) g⁻¹.

This measures exactly the failure of Moore-Penrose projectors to transform
covariantly when the metric is not transported.

3. Prove Drazin similarity transport

Under Drazin inverse transport witnesses:

  Π_D(g A g⁻¹) = g Π_D(A) g⁻¹.

This is the spectral/topological naturality theorem.

4. Prove Moore-Penrose transported-metric covariance

For:

  G' := g⁻ᵀ G g⁻¹,

prove:

  IsMPInverseG(G,A,B)
    →
  IsMPInverseG(G', gAg⁻¹, gBg⁻¹).

Then prove:

  Π_MP,G'(gAg⁻¹)
    =
  g Π_MP,G(A) g⁻¹.

This is the metric-natural theorem.

5. Prove fixed-metric mismatch decomposition

Define:

  M_G(A) := Π_D(A) - Π_MP,G(A).

Prove:

  M_G(gAg⁻¹)
    =
  g M_G(A) g⁻¹ - MPFixedTear(A,g,G).

This theorem identifies the exact tear point.

6. Prove transported-metric mismatch covariance

For transported metric G':

  M_G'(gAg⁻¹)
    =
  g M_G(A) g⁻¹.

Corollary:

  if M_G(A)=0, then M_G'(gAg⁻¹)=0.

This proves that metric transport compensates the projector mismatch.

7. Define MetricCompensatorWitness

Create:

  structure MetricCompensatorWitness where
    G_initial
    g
    G_transported
    transport_law :
      G_transported = g⁻ᵀ G_initial g⁻¹
    mp_transport :
      Π_MP,G_transported(gAg⁻¹)
        =
      g Π_MP,G_initial(A) g⁻¹
    mismatch_transport :
      M_G_transported(gAg⁻¹)
        =
      g M_G_initial(A) g⁻¹

This is the formal compensator object.

8. Define LocalGaugeMetricTransportWitness

Only as a witness structure.

Fields:

  baseMetric       : G(x)
  connection       : Γ_μ
  covariantDerivative :
    D_μ G = ∂_μ G - Γ_μᵀ G - G Γ_μ
  transportEquation :
    Prop
  mpEquivarianceLocal :
    Prop

Do not identify Γ automatically with gravity, Weyl field, Yang-Mills field,
spin connection, or B-field. Those are separate readout witnesses.

9. Add physical readout witnesses

Define optional structures:

  WeylMetricReadout
    with D_μ G = 2 W_μ G.

  SpinConnectionReadout
    with tetrad/vierbein and spinor-connection compatibility.

  GeneralizedMetricBFieldReadout
    with O(d,d) generalized metric built from G and B.

Each is a witness layer, not a theorem from projector algebra alone.

10. Update Cl44BridgeCandidate

Add required field:

  metricTransportWitness : MetricCompensatorWitness

Add optional fields:

  generalizedMetricWitness
  spin44ReadoutWitness
  conformalClosureWitness
  nullConePreservationWitness

Do not close Cl(4,4) unless all witnesses are supplied.

GOAL:

  Green theorem:
    Moore-Penrose non-equivariance under fixed metric is exactly the
    conformal/projector tear.

  Green theorem:
    transported metric restores Moore-Penrose covariance.

  Yellow witness:
    metric compensator may be read physically as a gauge/gravity field only
    after a readout witness is supplied.

  Red forbidden:
    projector mismatch automatically proves conformal gravity.
```

След този файл мостът ще има правилната форма:

[
\boxed{
\text{Drazin sector transports by similarity.}
}
]

[
\boxed{
\text{Moore--Penrose sector transports only with the metric.}
}
]

[
\boxed{
\text{the compensator is the transported metric/connection witness.}
}
]

[
\boxed{
\text{gravity/gauge/B-field interpretations are readouts, not automatic theorems.}
}
]

Това е правилният бутон. Не затваря „конформната гравитация“ като готова теорема; затваря **алгебричния tear point**, без който такава теорема изобщо не може да бъде формулирана строго.
[O[IДа — изпрати директива към Hermes, но **не** във формата “MetricTransportWitness занулява аномалията”. Това е една стъпка твърде силно.

Точната theorem-safe поправка е:

[
\boxed{
\text{MetricTransportWitness възстановява ковариантността на Moore--Penrose слоя, но не занулява автоматично mismatch-а.}
}
]

Ако

[
\mathcal M(A)=\Pi_D(A)-\Pi_{MP}^G(A),
]

и транспортираме едновременно оператора и метриката,

[
A' = gAg^{-1},
\qquad
G'=(g^{-1})^\dagger Gg^{-1},
]

тогава правилното твърдение е:

[
\mathcal M_{G'}(A')=g,\mathcal M_G(A),g^{-1}.
]

Тоест metric transport премахва **изкуствения fixed-metric tear**, но ако има истински Drazin/MP mismatch в началната система, той се транспортира ковариантно, не изчезва магически.

Зануляване имаме само при допълнителен witness:

[
\mathcal M_G(A)=0
]

или при структура от вида:

[
\texttt{AgreementAfterTransportWitness}.
]

Така че следващият Entanglement pass трябва да използва тази по-строга логика.

Още една важна корекция: Drazin проекторът (\Pi_D) е идемпотент, но не е задължително ортогонален или самоспрегнат. Следователно компресията

[
a\mapsto \Pi_D a\Pi_D
]

не дефинира автоматично положително физическо състояние. За да говорим за covariance, Gaussian criterion или entanglement върху Drazin-null sector, Hermes трябва да изисква **positive compression witness**:

[
\Pi_D^{\dagger_G}=\Pi_D
]

или условна експектация

[
E:\mathcal A\to \Pi_D\mathcal A\Pi_D
]

която е положителна, идемпотентна и нормализира състоянието.

Без това имаме algebraic residual sector, но не още physical entanglement sector.

Коригираната директива:

```text
Hermes, create:

  lean/InfoGeometry/Canonical/EntanglementResidualOwner.lean

Purpose:
  Formalize Drazin-null-supported residual covariance after the metric
  transport layer has supplied a valid metric/positive-compression witness.

Do not define entanglement as the Drazin projector.
Do not assert that MetricTransportWitness kills projector mismatch.
MetricTransportWitness restores MP covariance; mismatch vanishes only under an
explicit ProjectorAgreement or AgreementAfterTransport witness.

1. TransportedMismatchPrerequisite.lean

Import:

  MetricTransport
  ConformalProjectorTear
  ProjectorNoncommutativityDilationClosure

Record theorem-level fact:

  If A' = g A g⁻¹ and G' = g^{-†} G g⁻¹, then

      Π_MP^{G'}(A') = g Π_MP^G(A) g⁻¹.

Together with Drazin similarity naturality, prove:

      M_{G'}(A') = g M_G(A) g⁻¹

where

      M_G(A) := Π_D(A) - Π_MP^G(A).

Do not conclude M_{G'}(A') = 0 unless M_G(A)=0 or an explicit
AgreementAfterTransportWitness is supplied.

2. PositiveCompressionWitness.lean

Define a compression witness for a projector P on a *-algebra or finite Hilbert
module:

  structure PositiveCompressionWitness where
    P_idem       : P * P = P
    P_selfAdj_G  : adjoint_G(P) = P
    state        : State A
    denom_pos    : state(P) > 0
    compressedState :
        State (P A P)
    compression_eq :
        compressedState(a) =
          state(P * a * P) / state(P)

Drazin projectors are not automatically valid physical compressions.
Require one of:

  - Π_D is G-self-adjoint;
  - Π_D = Π_MP^G;
  - a positive conditional expectation E onto the Drazin sector.

3. DrazinNullSector.lean

Given a Drazin zero projector:

    Π_D0 := I - A Aᴰ,

define the algebraic null sector:

    Null_D := Ran(Π_D0).

Define the physical null sector only when PositiveCompressionWitness is present:

    PhysicalNull_D := compressed sector from Π_D0.

Record:

    algebraic null sector ≠ physical Hilbert/Krein sector by default.

4. BipartiteStateData.lean

Define a bipartite algebra/state package:

  structure BipartiteStateData where
    A          : Algebra
    A_L A_R    : Subalgebra A
    commute_LR : ∀ a∈A_L, ∀ b∈A_R, a*b=b*a
    ω          : State A

Define factorization:

    Factorizes(ω, A_L, A_R) :=
      ∀ a∈A_L, ∀ b∈A_R,
        ω(a*b) = ω(a) * ω(b).

5. ResidualCovariance.lean

Given a physical Drazin-null compression witness P₀, define the projected state:

    ω₀(a) := ω(P₀ a P₀) / ω(P₀).

For local observables a∈A_L, b∈A_R, define residual covariance:

    Corr_D0(a,b) :=
      ω₀(a*b) - ω₀(a) * ω₀(b).

Prove:

    Factorizes(ω₀, A_L, A_R)
      →
    Corr_D0(a,b)=0.

Prove the contrapositive theorem:

    Corr_D0(a,b) ≠ 0
      →
    ω₀ does not factorize on A_L,A_R.

Do not call this entanglement yet.
It is nonfactorizing residual correlation.

6. EntanglementWitness.lean

Define entanglement only through explicit witnesses.

Allowed witness structures:

  EntropyWitness:
    reduced density matrices,
    von Neumann entropy,
    nonzero mutual information or entanglement entropy under pure-state
    hypotheses.

  NegativityWitness:
    partial transpose,
    negative eigenvalue / trace norm criterion.

  GaussianBosonicWitness:
    CCR symplectic space (L,Ω),
    covariance matrix V,
    uncertainty condition,
    PPT/symplectic eigenvalue criterion.

  GaussianFermionicWitness:
    CAR/Majorana space,
    covariance matrix Γ,
    parity/superselection constraints,
    chosen separability criterion.

Allowed theorem:

    EntanglementWitness(ω₀)
      →
    ω₀ is entangled.

Forbidden theorem:

    Corr_D0 ≠ 0 → entanglement.

Because nonzero covariance may also arise from classical separable mixtures.

7. ResidualCorrelationThroughMismatch.lean

Define residual obstruction:

    R_DMP := Π_D0 - Π_MP0^G.

If a cross-correlation functional C_AB factors through R_DMP, prove:

    R_DMP = 0 → C_AB = 0.

Allowed theorem:

    mismatch vanishing kills mismatch-supported correlations.

Forbidden converse:

    C_AB = 0 → R_DMP = 0.

8. GaussianCovarianceOwner.lean

For Gaussian states, define restricted covariance:

    C_D0 := (P_D0 ⊗ P_D0) C (P_D0 ⊗ P_D0)

only under a positive projection/compression witness.

Prove:

    C_D0 = 0 → no Drazin-null-supported Gaussian covariance.

Nonzero C_D0 is only a correlation candidate.
Entanglement requires GaussianBosonicWitness or GaussianFermionicWitness.

9. LightconeReadoutBoundary.lean

Do not identify Drazin-null sector with lightcone by default.

A lightcone interpretation requires Lorentzian witness:

    D(p)^2 = η(p,p) I,
    Ker D(p) ≠ 0 → η(p,p)=0.

Only then may ProjectiveNullRays be attached to the Drazin-null sector.

Goal:
  Green theorem corridor:
    metric-transported MP covariance;
    mismatch transports covariantly;
    positive compression yields projected state;
    nonzero projected covariance implies nonfactorization.

  Yellow witness corridor:
    nonfactorization → entanglement only with EntanglementWitness;
    Drazin-null sector → lightcone only with LorentzianDiracWitness.

  Red forbidden corridor:
    Drazin projector = entanglement;
    MetricTransportWitness = anomaly deletion;
    Drazin null sector = lightcone automatically.
```

Най-точната концептуална формула е:

[
\boxed{
\text{Metric transport makes the MP layer covariant.}
}
]

[
\boxed{
\text{Projector agreement is an additional condition, not automatic.}
}
]

[
\boxed{
\text{Drazin isolates a zero sector; positive compression turns it into a physical sector.}
}
]

[
\boxed{
\text{Residual covariance on that sector is the entanglement candidate.}
}
]

И за заплитането:

[
\boxed{
\text{Entanglement is not the Drazin residue.}
}
]

[
\boxed{
\text{Entanglement is nonseparability of the projected state, detected by an explicit witness.}
}
]

Затова следващият реален theorem target не е “нелокалността на Вселената”, а:

[
\boxed{
Corr_{D0}(a,b)\neq0
\Rightarrow
\omega_0\text{ does not factorize on }A_L,A_R.
}
]

После, с допълнителен Gaussian/entropy/negativity witness, може да се надгради до entanglement theorem.
[O[IДа. След `MetricTransportWitness` вече е безопасно да се отвори `EntanglementResidualOwner.lean`.

Но директивата трябва да бъде формулирана така:

[
\boxed{
\text{Drazin-null sector supports residual correlations;}
}
]

не така:

[
\boxed{
\text{Drazin residue is entanglement.}
}
]

И още една важна корекция: `MetricTransportWitness` не занулява автоматично mismatch-а. Той доказва ковариантен транспорт:

[
\mathcal M_{G'}(gAg^{-1})
=========================

g\mathcal M_G(A)g^{-1}.
]

Следователно:

[
\mathcal M_G(A)=0
\Rightarrow
\mathcal M_{G'}(gAg^{-1})=0.
]

Но ако първоначално

[
\mathcal M_G(A)\neq0,
]

метричният транспорт го пренася коректно; не го унищожава. За реално зануляване трябва отделен `AlignmentWitness` или `AnomalyResolutionWitness`.

Също: Drazin проекторът

[
P_{D0}=I-AA^D
]

е идемпотент, но не е задължително самоспрегнат. За квантова ковариация и състояния това е критично, защото compression

[
a\mapsto P_{D0}aP_{D0}
]

не е физически положителна операция, ако (P_{D0}) не е (*)-проектор. Затова entanglement layer-ът трябва да различава:

[
\text{algebraic Drazin residual sector}
]

от

[
\text{physical residual projection}.
]

Физическият residual projector трябва да има witness:

[
P_R^2=P_R,
\qquad
P_R^*=P_R,
\qquad
\operatorname{Ran}(P_R)=\operatorname{Ran}(P_{D0}).
]

Едва тогава може да се дефинира нормализирано compressed state.

Коригираната директива към Hermes:

```text
[SYSTEM DIRECTIVE TO HERMES]

TARGET:
  InfoGeometry.Canonical.EntanglementResidualOwner

PROTOCOL:
  Formalize Drazin-null-supported residual correlations.
  Do not identify entanglement with the Drazin projector.
  Entanglement requires an explicit nonseparability witness.

Prerequisites:
  Import:
    OperatorProjectorMismatch
    MetricTransportWitness
    ConformalProjectorTear
    DrazinPenroseAnomalyOwner

1. DrazinNullSector

Given DrazinMPData with

    P_D0 := I - A * Aᴰ,

define the algebraic Drazin-null sector:

    DrazinNullSector(A) := range(P_D0).

Record:

    P_D0 is idempotent.

Do not assume:

    P_D0 is self-adjoint.

2. PhysicalResidualProjectionWitness

Define a witness structure:

    structure PhysicalResidualProjectionWitness where
      P_R : End V
      idempotent : P_R * P_R = P_R
      selfAdjoint_G : adjoint_G(P_R) = P_R
      range_eq_drazinNull :
        range(P_R) = range(P_D0)

This is the physical projection onto the Drazin-null sector.

Without this witness, only algebraic residual data is available.

3. BipartiteStateData

Define a bipartite observable system:

    A_L
    A_R
    A_total

with embeddings:

    i_L : A_L → A_total
    i_R : A_R → A_total

and locality/commutation witness:

    [i_L(a), i_R(b)] = 0

where appropriate.

Define a state:

    ω : A_total → Scalar

with witnesses:

    positivity
    normalization
    compatibility with the chosen *-structure.

4. ResidualCompressedState

Given a physical residual projector P_R and a state ω with

    ω(P_R) ≠ 0,

define the compressed residual state:

    ω_R(x) := ω(P_R * x * P_R) / ω(P_R).

Prove, under the projection and positivity witnesses:

    ω_R(1) = 1

and positivity of ω_R.

5. ResidualCovariance

For observables a ∈ A_L and b ∈ A_R, define:

    Corr_R(a,b)
      :=
    ω_R(i_L(a) * i_R(b))
      -
    ω_R(i_L(a)) * ω_R(i_R(b)).

Define:

    HasResidualCorrelation(a,b) :=
      Corr_R(a,b) ≠ 0.

6. NonproductCorrelationTheorem

Define product factorization:

    IsProductState(ω_R) :=
      ∀ a b,
        ω_R(i_L(a) * i_R(b))
          =
        ω_R(i_L(a)) * ω_R(i_R(b)).

Prove:

    Corr_R(a,b) ≠ 0
      →
    ¬ IsProductState(ω_R).

This proves Drazin-null-supported nonproduct correlation.

Do not call this entanglement yet.

7. EntanglementWitness

Define entanglement only as a separate witness layer.

Allowed structures:

    NonseparabilityWitness
    EntropyEntanglementWitness
    NegativityWitness
    GaussianCovarianceEntanglementWitness
    FermionicGaussianEntanglementWitness

Define:

    HasResidualEntanglement :=
      HasResidualCorrelation ∧ EntanglementWitness(ω_R).

Forbidden theorem:

    HasResidualCorrelation → HasResidualEntanglement.

Allowed theorem:

    HasResidualEntanglement → HasResidualCorrelation

only if the chosen witness implies nonproductness.

8. GaussianCovarianceCriterion

Optionally define a Gaussian layer.

For bosonic Gaussian states:

    covariance matrix C
    symplectic form Ω
    physicality witness:
      C + iΩ/2 ≥ 0

Define partial transpose / negativity witness only as a structure unless the
matrix-positivity API is available.

For fermionic Gaussian states:

    covariance Γ real skew-symmetric
    parity / CAR compatibility witnesses

Do not conflate bosonic and fermionic Gaussian criteria.

9. MetricTransportCompatibility

Given MetricTransportWitness:

    G' = g⁻ᵀ G g⁻¹,

prove covariance of the residual physical projection when supplied with a
transport witness:

    P_R' = g P_R g⁻¹.

Then prove:

    Corr_R'(g·a, g·b)
      =
    transported(Corr_R(a,b))

under state-transport and observable-transport witnesses.

Do not assert covariance of residual entanglement unless the entanglement
criterion is also transport-invariant.

10. ResidualEntanglementReadout

Add optional readout structures:

    ProjectiveCCRResidualReadout
    NullConeResidualReadout
    HolographicBoundaryCorrelationReadout
    Cl44ResidualReadout

Each requires explicit witnesses:

    causal quadratic form
    null-sector proof
    CCR/CAR compatibility
    tensor-factor decomposition
    state positivity
    entanglement criterion.

GOAL:

  Green theorem:
    Drazin-null physical compression can support nonproduct residual covariance.

  Green theorem:
    nonzero residual covariance implies nonfactorization of the compressed state.

  Yellow witness:
    with an explicit entanglement criterion, residual covariance may become
    residual entanglement.

  Red forbidden:
    Drazin projector residue = entanglement.
```

Това е правилният следващ ход.

Формално, следващият theorem corridor трябва да бъде:

[
P_{D0}=I-AA^D
]

изолира algebraic zero sector;

[
P_R=P_R^*=P_R^2
]

е физическият projector към този сектор;

[
\omega_R(x)=\frac{\omega(P_RxP_R)}{\omega(P_R)}
]

е residual compressed state;

[
\operatorname{Corr}_R(a,b)\neq0
]

доказва nonproduct residual correlation;

[
\operatorname{Corr}_R(a,b)\neq0
+
\text{EntanglementWitness}
]

дава theorem-level residual entanglement.

Най-кратката формула е:

[
\boxed{
\text{Drazin isolates the stage; the state supplies the correlation; the witness certifies entanglement.}
}
]

Така Hermes няма да „докаже нелокалността на Вселената“ чрез риторичен скок. Той ще докаже точния безопасен резултат: Drazin-null секторът може да носи остатъчни нефакторизиращи корелации, а entanglement се получава само когато бъде предоставен валиден критерий за неразделимост.
Точният слой е този:

[
\boxed{
\text{log Radon--Nikodym derivative}
====================================

# \text{relative modular Hamiltonian}

\text{thermodynamic force}.
}
]

Ако (\rho=p,\mu) и (\sigma=q,\mu), тогава модулният Hamiltonian на (\rho) спрямо базовата мярка (\mu) е

[
K_\rho=-\log p.
]

Relative log-likelihood е

[
\log\frac{d\rho}{d\sigma}
=========================

# \log\frac{p}{q}

K_\sigma-K_\rho.
]

Следователно относителната ентропия е

[
D(\rho\Vert\sigma)
==================

# \int \log\frac{d\rho}{d\sigma},d\rho

\mathbb E_\rho[K_\sigma-K_\rho].
]

Това е комутативната версия на Araki relative entropy, която в операторния случай се формулира чрез relative modular operator; Araki доказва positivity, convexity, lower semicontinuity и monotonicity за тази относителна ентропия. ([EMS Press][1])

При промяна на координати (T:x\mapsto y), ако

[
\rho'=T_#\rho,
]

тогава

[
p'(T(x))=\frac{p(x)}{|\det DT(x)|}.
]

Значи

[
K_{\rho'}(T(x))
===============

# -\log p'(T(x))

K_\rho(x)+\log|\det DT(x)|.
]

Това е точната връзка между Jacobian, entropy production и metric transport: логаритъмът на обемния фактор е additive correction към модулния Hamiltonian.

В Souriau слой това става Lie-algebraic. Имаме Hamiltonian (G)-space

[
(M,\omega,J),
\qquad
J:M\to\mathfrak g^*,
]

и geometric inverse temperature

[
\beta\in\mathfrak g.
]

Термалният Hamiltonian е

[
K_\beta(x)=\langle J(x),\beta\rangle.
]

Souriau Gibbs state е

[
\rho_\beta(x)
=============

Z(\beta)^{-1}e^{-K_\beta(x)}.
]

Тук (\beta) не е просто скаларна температура; тя е Lie-algebra element, а (K_\beta) е pairing с moment map. Това е същият принцип, който преди формулирахме като “(\beta) е geometric modular generator, а (K_\beta) е modular Hamiltonian.”

Partition potential:

[
\Psi(\beta)=\log Z(\beta).
]

Тогава, ако (J_i) са компонентите на moment map,

[
\partial_{\beta_i}\Psi(\beta)
=============================

-\mathbb E_{\rho_\beta}[J_i],
]

а Hessian-ът дава covariance/Fisher-type tensor:

[
\partial_{\beta_i}\partial_{\beta_j}\Psi(\beta)
===============================================

\operatorname{Cov}*{\rho*\beta}(J_i,J_j).
]

Това е Souriau thermodynamics as information geometry.

Квантово:

[
K_\rho=-\log\rho.
]

За две density matrices (\rho,\sigma),

[
D(\rho\Vert\sigma)
==================

# \operatorname{Tr}\rho(\log\rho-\log\sigma)

\mathbb E_\rho[K_\sigma-K_\rho].
]

В noncommutative setting модулният flow се записва

[
\sigma_t^\rho(A)
================

# \rho^{it}A\rho^{-it}

e^{-itK_\rho}Ae^{itK_\rho}.
]

Tomita–Takesaki теорията обобщава това чрез modular operator (\Delta), като modular automorphism group има вида (\Delta^{it}A\Delta^{-it}). Източникът върху quantum statistical manifolds изрично описва modular automorphisms, индуцирани от (\Delta_\rho^{it}), а Tomita–Takesaki/KMS връзката е стандартната операторно-алгебрична основа на equilibrium dynamics. ([PMC][2])

Когато (K=K(\theta)) зависи от параметри и операторите не комутират, не може да се пише наивно

[
\partial_\theta e^{-K}=-(\partial_\theta K)e^{-K}.
]

Правилната Duhamel/Kubo формула е

[
\partial_\theta e^{-K}
======================

-\int_0^1
e^{-sK}(\partial_\theta K)e^{-(1-s)K},ds.
]

Това е мястото, където се ражда Kubo–Mori metric / Bogoliubov inner product. В нашия език: noncommutativity на Hamiltonian-деформациите създава thermodynamic metric tensor.

Сега идва metriplectic layer. Той комбинира обратима Hamiltonian динамика и необратима entropy-gradient динамика:

[
\dot F
======

{F,E}
+
(F,S).
]

Тук

[
{F,E}
]

е skew Poisson bracket, а

[
(F,S)
]

е symmetric dissipative bracket. За theorem-safe thermodynamics трябва:

[
(E,F)=0,
]

[
{S,F}=0,
]

[
(S,S)\ge0.
]

Тогава

[
\dot E=0,
\qquad
\dot S\ge0.
]

Тоест energy се запазва, entropy расте. Съвременната literature описва Onsager non-equilibrium thermodynamics именно като gradient-flow структура в information geometry; metriplectic/GENERIC формите са стандартният начин да се държат заедно Hamiltonian и dissipative частите. ([MDPI][3])

Optimal transport layer избира конкретната metric bracket. На пространството от вероятностни плътности (\mathcal P(M)), Wasserstein gradient flow на free energy (\mathcal F) е

[
\partial_t\rho
==============

\nabla\cdot
\left(
\rho\nabla\frac{\delta\mathcal F}{\delta\rho}
\right).
]

JKO стъпката е

[
\rho_{k+1}
\in
\arg\min_\rho
\left[
\mathcal F(\rho)
+
\frac{1}{2\tau}W_2^2(\rho,\rho_k)
\right].
]

Santambrogio описва Wasserstein gradient flows като gradient flows върху пространството от мерки, вдъхновени от Jordan–Kinderlehrer–Otto структурата за heat/Fokker–Planck equations; Ambrosio–Gigli–Savaré дават общата metric-space gradient-flow рамка. ([Springer][4])

Комбинираният Souriau–metriplectic–optimal transport flow е:

[
\boxed{
\partial_t\rho
==============

-\mathcal L_{X_{K_\beta}}\rho
+
\nabla\cdot
\left(
\rho\nabla
\frac{\delta\mathcal F_\beta}{\delta\rho}
\right).
}
]

Първият член е Souriau/Lie/Hamiltonian transport:

[
-\mathcal L_{X_{K_\beta}}\rho.
]

Вторият е optimal-transport dissipation:

[
\nabla\cdot
\left(
\rho\nabla
\frac{\delta\mathcal F_\beta}{\delta\rho}
\right).
]

Free energy спрямо Souriau equilibrium е

[
\mathcal F_\beta(\rho)
======================

# D(\rho\Vert\rho_\beta)

\int \rho\log\frac{\rho}{\rho_\beta}.
]

Понеже

[
\rho_\beta=Z(\beta)^{-1}e^{-K_\beta},
]

получаваме

[
\mathcal F_\beta(\rho)
======================

\int \rho\log\rho
+
\int \rho K_\beta
+
\log Z(\beta).
]

Значи variational force е

[
\frac{\delta\mathcal F_\beta}{\delta\rho}
=========================================

\log\frac{\rho}{\rho_\beta}+1.
]

Без константата:

[
\boxed{
\text{thermodynamic force}
==========================

\nabla\log\frac{\rho}{\rho_\beta}.
}
]

Това е logarithmic Radon–Nikodym derivative като force.

Rényi слой е deformation layer, но трябва да се държи отделно. За density matrix (\rho),

[
Z_\rho(\alpha)
==============

# \operatorname{Tr}\rho^\alpha

\operatorname{Tr}e^{-\alpha K_\rho}.
]

Rényi entropy е

[
S_\alpha(\rho)
==============

\frac{1}{1-\alpha}
\log\operatorname{Tr}\rho^\alpha.
]

Тоест Rényi entropy е “partition function” на modular Hamiltonian (K_\rho) при inverse temperature (\alpha). При (\alpha\to1) се връща von Neumann entropy:

[
S(\rho)=-\operatorname{Tr}\rho\log\rho
======================================

\mathbb E_\rho[K_\rho].
]

Relative Rényi има няколко версии. В commutative case:

[
D_\alpha(\rho\Vert\sigma)
=========================

\frac{1}{\alpha-1}
\log
\int
\left(\frac{d\rho}{d\sigma}\right)^\alpha
d\sigma.
]

В quantum noncommutative case трябва да се избере Petz или sandwiched Rényi. Това не е козметика; ако (\rho) и (\sigma) не комутират, двете дефиниции не съвпадат.

Lean/Hermes архитектурата трябва да бъде:

```text
SouriauMetriplecticOT.lean

1. LogRadonNikodymHamiltonian

Define:
  K_ρ := -log(dρ/dμ)

For two measures ρ, σ:
  RelLog(ρ|σ) := log(dρ/dσ)
  RelHamiltonian(ρ|σ) := K_σ - K_ρ

Prove:
  D(ρ||σ) = E_ρ[RelHamiltonian(ρ|σ)]

2. SouriauThermalHamiltonian

Fields:
  Lie algebra 𝔤
  moment map J : M → 𝔤*
  β : 𝔤

Define:
  K_β(x) := ⟨J(x), β⟩
  ρ_β := Z(β)^{-1} exp(-K_β)

Prove finite-dimensional identities:
  ∂ log Z / ∂β_i = -E[J_i]
  Hessian log Z = covariance tensor

3. ModularHamiltonianQuantum

Define:
  K_ρ := -log ρ

Prove finite matrix identity:
  D(ρ||σ) = Tr ρ (K_σ - K_ρ)

Add Duhamel derivative witness:
  ∂ exp(-K(θ))
    =
  -∫₀¹ exp(-sK)(∂K)exp(-(1-s)K) ds

4. MetriplecticData

Fields:
  PoissonBracket
  MetricBracket
  Energy E
  Entropy S

Witnesses:
  Poisson skew/Jacobi
  Metric symmetry/positive-semidefinite
  degeneracy:
    metricBracket(E,F)=0
    poissonBracket(S,F)=0

Theorems:
  dE/dt = 0
  dS/dt ≥ 0

5. OptimalTransportMetricWitness

Fields:
  probability space
  continuity equation
  Wasserstein action
  mobility tensor / Onsager operator
  gradient flow equation

Define:
  ∂tρ = div(ρ ∇ δF/δρ)

6. SouriauMetriplecticOTFlow

Define:
  ∂tρ =
    -LieDerivative(X_Kβ, ρ)
    + div(ρ ∇ δFβ/δρ)

with:
  Fβ(ρ)=D(ρ||ρβ)

Prove conditionally:
  Hamiltonian part preserves Fβ if symmetry hypotheses hold.
  OT part dissipates Fβ under convexity/positivity witnesses.

7. RenyiModularDeformation

Define:
  Z_ρ(α)=Tr(ρ^α)
  S_α=(1/(1-α)) log Z_ρ(α)

Keep Petz and sandwiched relative Rényi as separate structures.

8. Forbidden claims

Do not assert:
  Souriau + OT proves quantum gravity.
  Rényi deformation equals non-equilibrium dynamics without flow witness.
  Modular Hamiltonian is entropy itself.

Allowed:
  Entropy is expectation of modular Hamiltonian:
    S(ρ)=E_ρ[K_ρ].
  Relative entropy is expectation difference:
    D(ρ||σ)=E_ρ[K_σ-K_ρ].
  OT gradient flow dissipates relative entropy/free energy.
```

Най-кратката правилна формула е:

[
\boxed{
K_\sigma-K_\rho
===============

\log\frac{d\rho}{d\sigma}
}
]

[
\boxed{
D(\rho\Vert\sigma)
==================

\mathbb E_\rho[K_\sigma-K_\rho]
}
]

[
\boxed{
\partial_t\rho
==============

-\mathcal L_{X_{K_\beta}}\rho
+
\operatorname{grad}*{W_2}^-,
D(\rho\Vert\rho*\beta)
}
]

или в PDE форма:

[
\boxed{
\partial_t\rho
==============

-\mathcal L_{X_{K_\beta}}\rho
+
\nabla\cdot
\left(
\rho\nabla\log\frac{\rho}{\rho_\beta}
\right).
}
]

Това е clean synthesis: Souriau дава Lie-геометричния Hamiltonian, modular/Radon–Nikodym log дава thermodynamic force, metriplectic geometry гарантира energy/entropy bookkeeping, а optimal transport дава конкретната dissipative dynamics.

[1]: https://ems.press/journals/prims/articles/2800?utm_source=chatgpt.com "Relative Entropy of States of von Neumann Algebras | EMS Press"
[2]: https://pmc.ncbi.nlm.nih.gov/articles/PMC7512990/?utm_source=chatgpt.com "Quantum Statistical Manifolds - PMC"
[3]: https://www.mdpi.com/1099-4300/27/7/710?utm_source=chatgpt.com "Onsager’s Non-Equilibrium Thermodynamics as Gradient Flow in Information Geometry | MDPI"
[4]: https://link.springer.com/article/10.1007/s13373-017-0101-1?utm_source=chatgpt.com "{Euclidean, metric, and Wasserstein} gradient flows: an overview | Bulletin of Mathematical Sciences | Springer Nature Link"
