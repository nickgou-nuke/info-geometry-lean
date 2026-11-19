# R1 Specification: Unified Differential Geometry of the Noncommutative Operator Ring

Status: `[qms_document_accepted]` (M1A–M1D materialized, kernel-checked, and verified)  
Document ID: `SPEC-R1-NCG-DIFFGEOM`  
QMS Governing SOP: `docs/ALCHEMICAL_QMS_SOP.md` (`QMS-SOP-ALC-001` v4.1)  
Baseline Commit: `abd5826b3676fab6231c66b646ec1cc5aeed6732`  
Toolchain Fingerprint: Lean `v4.34.1`, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`  

---

## 1. Scope & Requirement Mapping (F1.1–F1.7)

This specification governs the mathematical reconciliation of **Requirement R1** (*Reconcile differential forms, the Maurer-Cartan tower, Onsager operator theory, Fréchet derivations, Leibniz derivations, and n-operator-forms within a unified differential geometry of the noncommutative operator ring*). It separates kernel-checked native theorems (`BUCKET 1`), conditional parameterized constructions (`BUCKET 2`), and open closure debt (`BUCKET 3`), and fixes canonical sign conventions, type disambiguations, and owner boundaries across the M1A–M1D sub-milestones.

| Feature | Summary | Sub-Milestone(s) | Primary Lean Owner(s) |
|---|---|---|---|
| **F1.1** | Arbitrary-degree CE $d_n$, graded $\wedge$, graded Leibniz, $d^2=0$, `TwoForm ↔ DerivationOperatorForm K 2`, commutative `deRhamComplex` specialization, universal $\Omega^1_{\text{univ}}(A)$ factorization | M1A, M1B | `OperatorAlgebra/DerivationExteriorCalculus.lean`, `OperatorAlgebra/DerivationDifferentialForms.lean`, `OperatorAlgebra/PeirceSpine/UniversalNoncommutativeOneForms.lean` |
| **F1.2** | Canonical $\theta_L(g) = g^{-1} D(g)$ sign dictionary vs $\theta_R$ / `pureGaugeForm` / `gaugeOneForm`; unified multi-stage Maurer–Cartan tower (degree-1 flatness, 5-graded Peirce MC, tensor-tower stages) | M1C | `OperatorAlgebra/MaurerCartanTower.lean` |
| **F1.3** | Consolidate duplicate `TransportTensor`/`TimeReversal`; extend `OnsagerCasimirSystem` + `OnsagerDifferentialFormsBridge` to general `DerivationOperatorForm` / `OpForm` beyond finite Gibbs BKM | M1D | `Thermo/OnsagerDifferentialFormsBridge.lean`, `Synthesis/OnsagerOperatorDifferentialCalculus.lean` |
| **F1.4** | `FrechetOperatorDerivation` adapter + Fréchet exterior derivative $d_{\text{Fr}}$ on `OperatorFrechetForm` matching CE $d_n$ and Mathlib `extDeriv`, plus Duhamel/BKM Hessian alignment | M1B, M1D | `Optics/OperatorDerivationForms.lean`, `Canonical/OperatorFrechetForms.lean` |
| **F1.5** | Non-faithful-tolerant Leibniz derivation spine (`LieActionLane` / `DerivationLieLane` image & quotient factorizations) unifying 14 derivation wrappers/predicates | M1A, M1B, M1D | `OperatorAlgebra/DerivationExteriorCalculus.lean` (+ M1B/M1D adapters) |
| **F1.6** | Typed disambiguation of `NOperatorForm n` (`Fin n → 1-form` tuple) vs alternating $n$-operator-forms (`OpForm`, `DerivationOperatorForm`, `NativeDerivationForm`, `OperatorFrechetForm`) and symmetric `OperatorFrechetJet` | M1A, M1B, M1D | `Optics/OperatorDerivationForms.lean`, `OperatorAlgebra/OperatorExteriorAlgebraGeneral.lean`, `OperatorAlgebra/DerivationExteriorCalculus.lean`, `Canonical/OperatorFrechetForms.lean` |
| **F1.7** | Noncommutative operator-ring covariant derivative, curvature $F = d\Gamma + \Gamma \wedge \Gamma$, arbitrary-degree Ricci & Bianchi identities, gauge equivariance, Connes cyclic/Hochschild connection | M1A, M1B, M1C | `OperatorAlgebra/DerivationExteriorCalculus.lean`, `OperatorAlgebra/MaurerCartanTower.lean`, `OperatorAlgebra/PeirceSpine/UniversalNoncommutativeOneForms.lean` |

---

## 2. Formal Intent Envelopes (`ALCHEMICAL_QMS_SOP.md` §3.6)

### 2.1 `r1-leibniz-derivation-spine`

```json
{
  "concept_id": "r1-leibniz-derivation-spine",
  "source_text": "Unify all 14 Leibniz derivation wrappers/predicates across Algebra, NCG, OperatorAlgebra, Geometry, Modular, Optics, and Thermo into a single faithfulness-tolerant Lie-action spine without creating duplicate Derivation structures.",
  "intake_classification": "theorem-bearing",
  "classification": "algebraic Lie-derivation adapter spine",
  "mathematical_domain": ["noncommutative algebra", "nonassociative derivations", "Lie algebra representations"],
  "target_status": "theorem-backed",
  "risk_level": "R3",
  "allowed_imports": [
    "Mathlib.Algebra.Lie.OfAssociative",
    "Mathlib.Algebra.Lie.Subalgebra",
    "Mathlib.Algebra.Lie.Quotient",
    "InfoGeometry.Algebra.NonAssocDerivation",
    "InfoGeometry.Algebra.DerivationLieLane",
    "InfoGeometry.Algebra.DerivationLieLaneRepresentation",
    "InfoGeometry.Geometry.AssociativeGaugeConnection",
    "InfoGeometry.Algebra.NonAssocIteratedLeibniz",
    "InfoGeometry.Algebra.AlternativeDerivations",
    "InfoGeometry.NCG.NoncommutativeDifferentialCalculus",
    "InfoGeometry.NCG.NoncommutativeConnectionCurvature",
    "InfoGeometry.NCG.NoncommutativeCyclicCocycle",
    "InfoGeometry.NCG.DerivationDifferential",
    "InfoGeometry.Modular.ExactSequence"
  ],
  "non_theorem_claims": [
    "Out(A) = Der(A) / Inn(A) does not act on all of A (acts only on center Z(A))",
    "NCG.DerivationDifferential.LieSystem without bracket_self does not force 2-torsion g to be a LieRing; only its range/quotient is unconditionally a LieRing"
  ],
  "formal_objects": [
    "ActionOperatorForm",
    "IsLeibnizAction",
    "DerivationLieLane.toLieActionLane",
    "fullDerivationLieLane",
    "lieSubalgebraLane",
    "lieActionToDerivationHom",
    "rangeDerivationLieLane",
    "quotientDerivationLieLane",
    "pullbackRangeForm",
    "ncDerivationEquivDerivations",
    "lieSystemRangeSubalgebra",
    "lieSystemToDerivationLieLane",
    "lieSystemToLieActionLane",
    "innerLieActionLane",
    "modularDerivationToDerivations",
    "modularDerivationsLane",
    "modularInnerIdeal"
  ],
  "acceptance_theorems": [
    "actionExteriorDerivative_succ_comp",
    "pullbackActionForm_actionExteriorDerivative",
    "pullbackRangeForm_injective",
    "pullbackRangeForm_actionExteriorDerivative",
    "lieSystem_bracket_self_mem_ker",
    "modularDerivationToDerivations_commutator"
  ]
}
```

### 2.2 `r1-nc-exterior-calculus`

```json
{
  "concept_id": "r1-nc-exterior-calculus",
  "source_text": "Upgrade DerivationDifferentialForms from low-degree (0..3) cochains to an arbitrary-degree noncommutative Chevalley-Eilenberg differential graded algebra, universal Omega^1 factorization, and commutative deRhamComplex specialization.",
  "intake_classification": "theorem-bearing",
  "classification": "noncommutative differential graded algebra and commutative specialization",
  "mathematical_domain": ["Chevalley-Eilenberg cohomology", "exterior calculus", "noncommutative differential geometry"],
  "target_status": "theorem-backed",
  "risk_level": "R3",
  "allowed_imports": [
    "Mathlib.LinearAlgebra.Alternating.Basic",
    "Mathlib.LinearAlgebra.Alternating.Curry",
    "Mathlib.Algebra.Lie.Cochain",
    "Mathlib.Algebra.Algebra.Bilinear",
    "InfoGeometry.Algebra.DerivationLieLaneRepresentation",
    "InfoGeometry.Spectral.Cohomology.deRham",
    "InfoGeometry.Continuous.DeRhamBridge"
  ],
  "non_theorem_claims": [
    "Unconditional construction of analytic Hodge star or Hestenes-Krein operator on infinite-dimensional noncommutative operator algebras (supplied as BUCKET 2 parameters in derivationDeRhamComplex)"
  ],
  "formal_objects": [
    "DerivationOperatorForm",
    "reindexForm",
    "alternatingOfCurry",
    "lieDeriv",
    "ceLieDeriv",
    "ceExteriorDerivative",
    "ceWedgeBil",
    "ceWedge",
    "twoCochainEquivDerivationOperatorForm",
    "ceCurvature",
    "covariantExteriorDerivativeN",
    "derivationDifferentialForms",
    "derivationDeRhamComplex"
  ],
  "acceptance_theorems": [
    "ceExteriorDerivative_succ_comp",
    "ceWedge_assoc",
    "lieDeriv_ceWedge",
    "ceExteriorDerivative_ceWedge",
    "covariantExteriorDerivativeN_comp",
    "ceCurvature_bianchi",
    "ceWedge_comm_of_commRing",
    "ceExteriorDerivative_zero_eq",
    "ceExteriorDerivative_one_eq",
    "ceExteriorDerivative_two_eq"
  ]
}
```

### 2.3 `r1-maurer-cartan-tower`

> **Status**: Materialized and verified in M1C (`lean/InfoGeometry/OperatorAlgebra/MaurerCartanTower.lean`, 2,301 lines).

```json
{
  "concept_id": "r1-maurer-cartan-tower",
  "source_text": "Reconcile all Maurer-Cartan sign conventions around canonical theta_L(g) = g^-1 D(g) and unite degree-1 flatness, 5-graded nilpotent Peirce dressing, and tensor-tower stages into a coherent multi-stage Maurer-Cartan tower.",
  "intake_classification": "theorem-bearing",
  "classification": "noncommutative gauge connection and multi-stage tower",
  "mathematical_domain": ["gauge theory", "Maurer-Cartan equation", "Peirce decomposition", "tensor towers"],
  "target_status": "theorem-backed",
  "risk_level": "R4",
  "allowed_imports": [
    "InfoGeometry.OperatorAlgebra.DerivationExteriorCalculus",
    "InfoGeometry.OperatorAlgebra.DerivationDifferentialForms",
    "InfoGeometry.OperatorAlgebra.DerivationGaugeTransport",
    "InfoGeometry.OperatorAlgebra.DerivationRightLogarithmicForm",
    "InfoGeometry.OperatorAlgebra.MaurerCartanFrameTransport",
    "InfoGeometry.OperatorAlgebra.DerivationMatrixGeometry",
    "InfoGeometry.OperatorAlgebra.MatrixMaurerCartan",
    "InfoGeometry.OperatorAlgebra.NoncommutativeMaurerCartanAdjointBridge",
    "InfoGeometry.Optics.DerivationBackedMaurerCartanFrame",
    "InfoGeometry.Canonical.MaurerCartanFactorization",
    "InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceMaurerCartanCurvatureWitness",
    "InfoGeometry.OperatorAlgebra.PeirceSpine.HistoricalDictionaryAndTomitaFrontiersPoset",
    "InfoGeometry.Canonical.TensorStageExactConnection"
  ],
  "non_theorem_claims": [
    "Existence of an infinite-stage direct-limit connection (TensorStageExactConnection provides stagewise exact connections and direct-limit cocone descent of cut curvature, not a limit connection)"
  ],
  "formal_objects": [
    "thetaL",
    "thetaR",
    "MaurerCartanStage",
    "MaurerCartanStageHom",
    "MaurerCartanTower",
    "TowerForm",
    "peirceFiveGradedStage",
    "tensorStageTower"
  ],
  "acceptance_theorems": [
    "thetaL_flat",
    "thetaR_eq_conj_thetaL",
    "thetaR_eq_neg_thetaL_inv",
    "pureGaugeForm_eq_thetaL_inv",
    "gaugeOneForm_zero_eq_thetaL_inv",
    "peirce_five_graded_mc_stage",
    "tensor_stage_mc_transport"
  ]
}
```

### 2.4 `r1-frechet-and-onsager`

> **Status**: Materialized and verified across M1B and M1D (`Optics/OperatorDerivationForms.lean`, `Canonical/OperatorFrechetForms.lean`, `Thermo/OnsagerDifferentialFormsBridge.lean`, `Synthesis/OnsagerOperatorDifferentialCalculus.lean`).

```json
{
  "concept_id": "r1-frechet-and-onsager",
  "source_text": "Equip OperatorFrechetForm with Fréchet exterior derivative matching CE d_n and Mathlib extDeriv, extend OnsagerCasimirSystem to general DerivationOperatorForm/OpForm carriers, disambiguate NOperatorForm tuples, and consolidate duplicate TransportTensor/TimeReversal.",
  "intake_classification": "theorem-bearing",
  "classification": "Fréchet exterior calculus and Onsager-Casimir operator coupling",
  "mathematical_domain": ["Fréchet calculus", "non-equilibrium thermodynamics", "operator differential forms"],
  "target_status": "theorem-backed",
  "risk_level": "R3",
  "allowed_imports": [
    "Mathlib.Analysis.Calculus.DifferentialForm.Basic",
    "InfoGeometry.OperatorAlgebra.DerivationExteriorCalculus",
    "InfoGeometry.OperatorAlgebra.DerivationDifferentialForms",
    "InfoGeometry.OperatorAlgebra.OperatorExteriorAlgebraGeneral",
    "InfoGeometry.Optics.OperatorDerivationForms",
    "InfoGeometry.Continuous.DeRhamBridge",
    "InfoGeometry.Canonical.NoncommutativeGibbsBKMHessianBridge",
    "InfoGeometry.Canonical.NoncommutativeGibbsDuhamelTwoPointBridge",
    "InfoGeometry.Canonical.NoncommutativeGibbsFaithfulNormalizationBridge",
    "InfoGeometry.Canonical.NoncommutativeGibbsCenteredFrechetBKMBridge",
    "InfoGeometry.Canonical.OperatorFrechetForms",
    "InfoGeometry.Thermo.OnsagerOperatorClosure",
    "InfoGeometry.Thermo.SusceptibilityOnsagerStress",
    "InfoGeometry.Thermo.OnsagerDifferentialFormsBridge",
    "InfoGeometry.Synthesis.OnsagerOperatorDifferentialCalculus"
  ],
  "non_theorem_claims": [
    "Unbounded infinite-dimensional KMS/BKM Duhamel integral existence without explicit finite-dimensional or boundedness hypotheses"
  ],
  "formal_objects": [
    "OneFormTuple",
    "OperatorFrechetFormK",
    "RealOperatorFrechetForm",
    "frechetExtDerivK",
    "frechetExtDeriv",
    "frechetExtDerivReal",
    "SmoothOpMap",
    "FrechetVectorField",
    "OnsagerFormPairing",
    "ParityOnsagerFormPairing",
    "InfoGeometry.OperatorAlgebra.General.TransportTensor",
    "InfoGeometry.Thermo.OnsagerClosure.OnsagerCasimirSystem.TimeReversal",
    "InfoGeometry.Synthesis.OnsagerNCG.TransportTensor.equivGeneral",
    "InfoGeometry.Synthesis.OnsagerNCG.TimeReversal.equivClosure",
    "InfoGeometry.Thermo.OnsagerFormsBridge.thermodynamicDerivationEquivDerivations"
  ],
  "acceptance_theorems": [
    "frechetExtDerivK_frechetExtDeriv",
    "frechetExtDeriv_frechetExtDeriv",
    "frechetExtDerivK_linear_eq_ceExteriorDerivative",
    "frechetExtDeriv_linear_eq_ceExteriorDerivative",
    "frechetExtDeriv_chart_eq_mathlib_extDeriv",
    "frechetExtDeriv_expFrechetZeroForm_eq_duhamelDerivative",
    "frechetExtDeriv_logPartition_bkmHessian_alignment",
    "onsager_pairing_general_form_reciprocity",
    "onsager_pairing_actionForm_reciprocity",
    "onsager_pairing_derivationForm_reciprocity",
    "onsager_pairing_opForm_reciprocity",
    "thermodynamicDerivationEquivDerivations_commutator",
    "onsager_casimir_reciprocity_via_general"
  ]
}
```

---

## 3. Canonical Maurer–Cartan Sign Convention & Dictionary

### 3.1 Canonical Left-Logarithmic Convention ($\theta_L$)

We freeze the **canonical Maurer–Cartan 1-form** on a unit $g \in A^\times$ for a derivation lane $K$ as the **left-logarithmic form**:
$$\theta_L(g)(x) := g^{-1} \cdot D_x(g), \qquad d\theta_L + \theta_L \wedge \theta_L = 0.$$
This is verified natively in:
- `OperatorAlgebra/MaurerCartanFrameTransport.lean:77,92` (`gaugeForm K g x = (↑g⁻¹ : A) * K.operatorAction x (↑g : A)`, `gaugeForm_flat : connectionCurvature K (gaugeForm K g) = 0`),
- `OperatorAlgebra/MatrixMaurerCartan.lean:35,122` (`maurerCartan G H = G⁻¹ * H * G - H = G⁻¹ * ⁅H, G⁆`, `maurerCartan_equation`),
- `OperatorAlgebra/NoncommutativeMaurerCartanAdjointBridge.lean:214` (`maurerCartanForm G Ginv H = Ginv * adCLM H G`),
- `OperatorAlgebra/PeirceSpine/HistoricalDictionaryAndTomitaFrontiersPoset.lean:728` (5-graded Peirce inner dressing $g^{-1}[H, g]$).

Under the covariant derivative `covariantDerivative K Γ x a = D_x(a) + Γ(x) a - a Γ(x)` (`DerivationDifferentialForms.lean:342–344`), the frame transport `frameTransport g a = g⁻¹ * a * g` (`MaurerCartanFrameTransport.lean:28,102`) intertwines identically:
$$\nabla^{\theta_L(g)}_x (g^{-1} a g) = g^{-1} (D_x a) g.$$

### 3.2 Exact Sign & Conjugation Dictionary

Every alternative MC convention in the repository relates to $\theta_L(g)$ by exact algebraic identities (all `BUCKET 1`):

| Symbol & Owner | Formula | Curvature / MC Equation | Exact Identity Relating to $\theta_L$ |
|---|---|---|---|
| `MaurerCartanFrameTransport.gaugeForm` | $\theta_L(g)(x) = g^{-1} D_x(g)$ | $d\theta_L + \theta_L \wedge \theta_L = 0$ | Canonical $\theta_L(g)$ |
| `DerivationRightLogarithmicForm.rightLogarithmicOneForm` (`L30,65`) | $\theta_R(g)(x) = D_x(g) g^{-1}$ | $d\theta_R - \theta_R \wedge \theta_R = 0$ | $\theta_R(g) = g\,\theta_L(g)\,g^{-1} = -\theta_L(g^{-1})$ |
| `DerivationGaugeTransport.gaugeOneForm` at $\Gamma = 0$ (`L80`) | `gaugeOneForm K 0 u x` $= -D_x(u) u^{-1}$ | $d\omega + \omega \wedge \omega = 0$ | `gaugeOneForm K 0 u` $= -\theta_R(u) = \theta_L(u^{-1})$ |
| `NCG.AlgebraDerivation.pureGaugeForm` (`NoncommutativeConnectionCurvature.lean:169,184,499`) | $u D(u^{-1}) = -D(u) u^{-1}$ | $D(u) D(u^{-1}) + \theta^2 = 0$ | `pureGaugeForm D u` $= -\theta_R(u) = \theta_L(u^{-1})$ |
| `Optics.DerivationBackedMaurerCartanFrame.fromDirectionalDerivation` (`L39,49`) | $D_p(X)(u(p))\, u(p)^{-1}$ | right MC cocycle | $= \theta_R(u(p)) = -\text{pureGaugeForm} = \theta_L(u(p)^{-1})$ |
| `DerivationGaugeTransport.fundamentalCovariantDerivative` (`L35`) | $\nabla^{\text{fund}}_x(a) = D_x(a) + \Gamma(x) a$ | $[\nabla^{\text{fund}}_x, \nabla^{\text{fund}}_y] - \nabla^{\text{fund}}_{[x,y]} = L_{F(x,y)}$ | Left regular module connection (faithfully detects central curvature) |
| `DerivationDifferentialForms.covariantDerivative` (`L342`) | $\nabla_x(a) = D_x(a) + [\Gamma(x), a]$ | $[\nabla_x, \nabla_y] - \nabla_{[x,y]} = \text{ad}_{F(x,y)}$ | Bimodule / adjoint connection (kills central curvature) |
| `Canonical.MaurerCartanFactorization.maurerCartanForm` (`L159`) | $\pi(X) \mapsto \pi([D, X])$ on `Out(A)` | Outer-derivation quotient descent | **Semantic disambiguation**: NOT a unit-valued $g^{-1} dg$ 1-form; outer modular descent map on `Derivation A ⧸ Inn A` (`MaurerCartanTower.outer_maurerCartanForm_commutator_disambiguation` `L1033`) |

Canonical M1C consolidation in `OperatorAlgebra/MaurerCartanTower.lean` fixes `thetaL` (`L802`) and `thetaR` (`L807`) in `DerivationOperatorForm K 1` together with `thetaL_flat` (`L853`), `thetaR_eq_conj_thetaL` (`L907`), `thetaR_eq_neg_thetaL_inv` (`L912`), `gaugeOneForm_zero_eq_thetaL_inv` (`L932`), and `pureGaugeForm_eq_thetaL_inv` (`L938`), plus `peirce_five_graded_mc_stage` (`L1821`) and `tensor_stage_mc_transport` (`L2230`).

---

## 4. Canonical Disambiguation of $n$-Operator-Forms

The repository uses several distinct types loosely referred to as "$n$-forms". Their exact mathematical roles are frozen as follows:

| Type & Owner | Exact Carrier | Alternating? | $R$-Linear? | Exterior Derivative $d_n$ & Wedge $\wedge$ |
|---|---|---|---|---|
| `NOperatorForm n` (`Optics/OperatorDerivationForms.lean:42`) | `Fin n → (Point → Tangent → Value)` | **No** (ordered $n$-tuple of 1-forms) | **No** | None (`OneFormTuple` `L49`, `opFormToOneFormTuple` `L973`, `opFormWedgeTuple` `L1066`, contrast witnesses `L1075, L1088` and `OperatorFrechetForms.lean:1488`) |
| `DerivationOperatorForm K n` (`OperatorAlgebra/DerivationExteriorCalculus.lean:1204`) | `K.L [⋀^(Fin n)]→ₗ[R] A` | **Yes** | **Yes** | Full CE DGA (`ceExteriorDerivative`, `ceWedge`, $d^2=0$, graded Leibniz) |
| `ActionOperatorForm K n` (`OperatorAlgebra/DerivationExteriorCalculus.lean:306`) | `K.L [⋀^(Fin n)]→ₗ[R] A` for `K : LieActionLane R A` | **Yes** | **Yes** | Full CE differential `actionExteriorDerivative` ($d^2=0$ without faithfulness) |
| `OpForm R V A n` (`OperatorAlgebra/OperatorExteriorAlgebraGeneral.lean:56`) | `V [⋀^(Fin n)]→ₗ[R] A` | **Yes** | **Yes** | Pullback `pullbackN`, coeff `derivN`/`mapN`, wedge `opWedge` (`L358`), `opExteriorDerivative` (`L749`), `opFormEquivActionForm` (`L744`), `opFormEquivDerivationForm` (`L848`) |
| `NativeDerivationForm R V M n` / `DerivationForm` (`NCG/DerivationDifferential.lean:130,296`) | `V [⋀^(Fin n)]→ₗ[R] M` / `𝔤 [⋀^(Fin n)]→ₗ[ℤ] A` | **Yes** | **Yes** (`ℤ` for `DerivationForm`) | Low-degree `differential0..2`; `System`/`LieSystem` embeds into M1A spine |
| `OperatorFrechetForm A T M n` (`Canonical/OperatorFrechetForms.lean:43`) / `OperatorFrechetFormK` (`L232`) / `RealOperatorFrechetForm` (`L241`) | `A → (T [⋀^(Fin n)]→L[𝕜] M)` (`𝕜 = ℂ, ℝ`) | **Yes** (continuous) | **Yes** (continuous) | `frechetExtDerivK` (`L248`), `frechetExtDeriv` (`L257`), `frechetExtDerivReal` (`L265`), $d_{\text{Fr}}^2=0$ (`L338, L355`), CE `frechetExtDeriv_linear_eq_ceExteriorDerivative` (`L972`), chart `extDeriv` (`L1093, L1119`), Duhamel/BKM Hessian (`L1168, L1338`) |
| `OperatorFrechetJet E F n` (`Canonical/OperatorFrechetForms.lean:32`) | `E → ContinuousMultilinearMap ℂ (Fin n → E) F` | **No** (symmetric `iteratedFDeriv`) | **Yes** (continuous) | Symmetric jet, NOT alternating form (`operatorFrechetFormToJet` `L1373`, `operatorFrechetJet_two_diag_nonzero_witness` `L1412`, `operatorFrechetJet_one_eq_frechetExtDeriv` `L1449`) |

---

## 5. Canonical Onsager Carrier & Duplicate Consolidation

1. **Canonical Real Onsager-Casimir System**: `InfoGeometry.Thermo.OnsagerClosure.OnsagerCasimirSystem V` (`Thermo/OnsagerOperatorClosure.lean:13`) and `InfoGeometry.Thermo.OnsagerClosure.OnsagerCasimirSystem.TimeReversal V` (`L78`), with `InfoGeometry.Thermo.OnsagerClosure.OnsagerCasimirSystem.ParityOnsagerSystem V` (`L83`) carrying the exact reciprocity law `W(Tx, Ty) = W(y, x)`.
2. **Canonical $A$-Valued Transport Tensor**: `InfoGeometry.OperatorAlgebra.General.TransportTensor R V A` (`OperatorAlgebra/OperatorExteriorAlgebraGeneral.lean:179`), defined over general `[Ring R]` with `symmPart`, `altPart`, and `onsager_casimir_reciprocity_exact`.
3. **Materialized Compatibility Equivalences & General-Form Onsager Pairing (M1D)**:
   - `InfoGeometry.Synthesis.OnsagerNCG.TransportTensor R V A` (`Synthesis/OnsagerOperatorDifferentialCalculus.lean:59`) remains a compatibility carrier (`toBilin : V →ₗ[R] V →ₗ[R] A` over `[CommRing R] [Algebra R A]`) equipped with lossless `toGeneral` (`L186`), `ofGeneral` (`L196`), `equivGeneral` (`L222`, preserving `apply`/`symmPart`/`altPart`), and `onsager_casimir_reciprocity_via_general` (`L308`) without breaking `Synthesis/All.lean`.
   - `InfoGeometry.Synthesis.OnsagerNCG.TimeReversal R V` (`L267`) remains a compatibility carrier for arbitrary `[Ring R]` (`toLinearMap`, `involutive'`, `CoeFun`), bridged at `R = ℝ` to `OnsagerClosure.OnsagerCasimirSystem.TimeReversal V` via `toClosure` (`L321`), `ofClosure` (`L329`), `equivClosure` (`L348`), `ofOnsagerCasimirSystem` (`L357`), and `ofParityOnsagerSystem_reciprocity` (`L377`).
   - `InfoGeometry.Thermo.OnsagerFormsBridge.OnsagerFormPairing V A n` (`Thermo/OnsagerDifferentialFormsBridge.lean:187`) and `ParityOnsagerFormPairing V A n` (`L339`) extend `OnsagerCasimirSystem` / `ParityOnsagerSystem` to arbitrary-degree alternating forms `V [⋀^Fin n]→ₗ[ℝ] A` (`onsager_pairing_general_form_reciprocity` `L430`), covering `ActionOperatorForm` (`L513`), `DerivationOperatorForm` / `ceExteriorDerivative` / `ceWedge` / `ceCurvature` (`L549, L557, L569, L579`), and `OpForm` (`L642`) definitionally.
   - Unrelated concrete Clifford/matrix involutions (`TwinWaveCayleyDickson.TimeReversal`, `KasparovKreinDIIIBridge.DIII_TimeReversal`) remain distinct domain-specific structures in R2/R3.

---

## 6. Unified Leibniz Derivation Spine (14 Wrappers)

Every Leibniz derivation wrapper in the repository satisfies `D (x * y) = D x * y + x * D y`. Because `DerivationLieLane.faithful : Function.Injective act` rejects inner-derivation systems with nontrivial center (e.g. `innerLieSystem`) and quotienting/range-factorization collapses 1-forms that are nonzero on `ker(act)` (e.g. `innerSystem_identityForm_curvature`), the unified spine in `DerivationExteriorCalculus.lean` operates in **three tiers**:

1. **Tier 1 — Faithfulness-Free CE Calculus (`LieActionLane R A`)**:
   - `ActionOperatorForm K n := K.L [⋀^(Fin n)]→ₗ[R] A` carries `actionExteriorDerivative` and $d_{n+1} \circ d_n = 0$ with **no** faithfulness and **no** multiplication on `A`.
   - `IsLeibnizAction K := ∀ x : K.L, NonAssocDerivation.IsLeibniz R A (K.operatorAction x)` enables graded `ceWedge` and graded Leibniz.
   - `DerivationLieLane.toLieActionLane K` satisfies `ActionOperatorForm K.toLieActionLane n ≡ DerivationOperatorForm K n` definitionally (`rfl`).
2. **Tier 2 — Faithful Quotient / Range Factorization (`DerivationLieLane R A`)**:
   - `fullDerivationLieLane R A`, `lieSubalgebraLane S`, `rangeDerivationLieLane act` (`L := act.range`), and `quotientDerivationLieLane act` (`L := L ⧸ act.ker`, equivalent via `LieHom.quotKerEquivRange act`).
   - `pullbackRangeForm` pulls `DerivationOperatorForm (rangeDerivationLieLane act) n` back to `ActionOperatorForm` injectively and `(d_n, ∧)`-equivariantly for forms vanishing on `ker(act)`.
3. **Tier 3 — Adapter Inventory (All 14 Surfaces)**:

| # | Wrapper / Predicate | Scalar Ring | Target in Spine | Owner Milestone |
|---|---|---|---|---|
| 1 | `NonAssocDerivation.IsLeibniz` / `derivations` | `[CommRing R]` (`[Ring R]` for `IsLeibniz`) | Canonical Lie subalgebra target | Existing (`Algebra/NonAssocDerivation.lean`) |
| 2 | `LieActionLane R A` | `[CommRing R]` | Tier 1 direct carrier | Existing (`Algebra/DerivationLieLane.lean`) |
| 3 | `DerivationLieLane R A` | `[CommRing R]` | `toLieActionLane` (Tier 1) | Existing (`Algebra/DerivationLieLane.lean`) |
| 4 | `Geometry.AssociativeGaugeConnection.IsLeibniz` | `[Ring R]` (`[CommRing R]` for `derivations R A`) | `associativeIsLeibnizToDerivations` | M1A (`DerivationExteriorCalculus.lean`) |
| 5 | `NonAssocIteratedLeibniz.IsDerivation` | `[CommSemiring R]` (`[CommRing R]` with `LinearMap.mul`) | `iteratedIsDerivation_iff_isLeibniz` | M1A (`DerivationExteriorCalculus.lean`) |
| 6 | `AlternativeDerivations.NonAssocDerivation` | `[Ring R]` (`[CommRing R]` for `derivations R A`) | `nonAssocDerivationEquivDerivations` | M1A (`DerivationExteriorCalculus.lean`) |
| 7 | `NCG.Calculus.NCDerivation A` | `ℤ` | `ncDerivationEquivDerivations` (commutator-preserving) | M1A (`DerivationExteriorCalculus.lean`) |
| 8 | `NCG.DerivationDifferential.System` / `LieSystem` | `ℤ` | `lieSystemRangeSubalgebra` / `lieSystemToDerivationLieLane` (unconditional, no `bracket_self` needed); `lieSystemToLieActionLane` (with `hself`); `innerLieActionLane` | M1A (`DerivationExteriorCalculus.lean`) |
| 9 | `NCG.AlgebraDerivation R A` | `[Ring R]` (`[CommRing R]` → `derivations R A`; general → `NCDerivation A`) | `algebraDerivationToDerivations`, `algebraDerivationToNCDerivation` | M1A (`DerivationExteriorCalculus.lean`) |
| 10 | `NCG.CyclicAlgebraDerivation R A` | `[Ring R]` (`[CommRing R]` → `derivations R A`; general → `NCDerivation A`) | `cyclicAlgebraDerivationToDerivations`, `cyclicAlgebraDerivationToNCDerivation` | M1A (`DerivationExteriorCalculus.lean`) |
| 11 | `Modular.ExactSequence.Derivation A` | `ℤ` | `modularDerivationToDerivations` (`AddEquiv` + commutator), `modularDerivationsLane`, `modularInnerIdeal` (`LieIdeal ℤ`) | M1A (`DerivationExteriorCalculus.lean`) |
| 12 | `OperatorAlgebra.ExteriorAlgebra.OpDerivation` | `[Ring R]` (`[CommRing R]` → `derivations R A`) | `opDerivationEquivDerivations` (`L1144`), `opDerivationSpanLane` (`L1173`), `opDerivationActionLane` (`L1178`) | M1B (`OperatorAlgebra/OperatorExteriorAlgebra.lean:387`; adapter in `OperatorExteriorAlgebraGeneral.lean`) |
| 13 | `InfoGeometry.OperatorAlgebra.General.FormDerivation` | `[Ring R]` (`[CommRing R]` → `derivations R A`) | `formDerivationEquivDerivations` (`L1072`), `formDerivationLieLane` (`L1092`), `formDerivationActionLane` (`L1113`) | M1B (`OperatorAlgebra/OperatorExteriorAlgebraGeneral.lean:84`) |
| 14 | `Optics.OperatorDerivationForms.FrechetOperatorDerivation` | `[NontriviallyNormedField 𝕜]` | `toDerivationsLieHom` (`L1233`), `derivationLieLane` (`L1249`), `lieActionLane` (`L1258`), `toDerivationDifferentialLieSystem` (`L1388`), `innerFrechetLieSystem` (`L1504`), `frechetOperatorDerivationOfThermodynamic_toDerivations` (`L1535`) | M1B (`Optics/OperatorDerivationForms.lean:144`) |
| (+1) | `Thermo.SusceptibilityOnsagerStress.ThermodynamicOperatorDerivation` | `ℝ` | `thermodynamicDerivationEquivDerivations` (`L746`), `_commutator` (`L775`), `thermodynamicDerivationSpanLane` (`L786`), `thermodynamicDerivationActionLane` (`L793`), `thermodynamicFamilyRangeLane`/`QuotientLane` (`L860, L870`), `formDerivationEquivThermodynamic` (`L949`; zero orphan instances) | M1D (`Thermo/SusceptibilityOnsagerStress.lean:169`; adapters in `Thermo/OnsagerDifferentialFormsBridge.lean`) |

---

## 7. Erlangen 2.0 Coordinate-Independent Symmetry & Pfaffian/Maurer–Cartan Bridge

Primary-source reference: Felix Klein, *Vergleichende Betrachtungen über neuere geometrische Forschungen* (*Erlanger Programm*, Erlangen: A. Deichert, 1872; University of Michigan Historical Mathematics Collection `ABN7632.0001.001`) and its English translation *A Comparative Review of Recent Researches in Geometry*, M. W. Haskell, *Bull. New York Math. Soc.* **2** (1892–1893), 215–249 (`arXiv:0807.3161v1`).

1. **Coordinate-Independent Exterior Calculus & Grassmann *Ausdehnungslehre* (Klein §10, Concluding Remarks, Note IV)**:
   - Klein emphasizes Grassmann's *Ausdehnungslehre* and noncommutative/quaternionic coordinate-free analytic calculi (Concluding Remarks & Footnote 37) as coordinate-system-independent realizations of the transformation-invariant theory of an $n$-dimensional manifoldness.
   - In R1, `ActionOperatorForm K n := K.L [⋀^(Fin n)]→ₗ[R] A` and `DerivationOperatorForm K n` express alternating multilinear forms, exterior differentiation `ceExteriorDerivative`, graded wedge `ceWedge`, and covariant curvature `ceCurvature` purely intrinsically over a Lie algebra of derivations `K.L` without fixing a coordinate basis, while specializing natively to `Continuous.DeRhamBridge` (`chartDirectionalLieAction`) and `Spectral.Cohomology.deRham.DifferentialForms` (`derivationDifferentialForms`).
2. **Pfaffian 1-Form Relations & Lie Contact Transformations (Klein §§8–9)**:
   - Klein §§8.3–9 distinguishes the infinite group of all point transformations (whose infinitesimal differentials act linearly on differentials) from Lie's contact transformations on surface-elements $(x,y,z,p,q)$, characterized by invariance of the Pfaffian 1-form equation $dz - p\,dx - q\,dy = 0$ (and its Clebsch connex generalizations), together with Lie's use of infinitesimal transformations to integrate differential equations (Note VII).
   - In R1, Cartan's identity (`actionExteriorDerivative_succ_curryLeft`, `lieDeriv_ceWedge`) and pullback invariance along Lie-algebra homomorphisms (`pullbackActionForm_actionExteriorDerivative`, `pullbackActionForm_actionWedge`, `pullbackRangeForm`) formulate infinitesimal action of `x : K.L` on Pfaffian 1-forms $\omega \in \text{DerivationOperatorForm}\; K\; 1$ and arbitrary-degree $n$-forms via $L_x = d \circ \iota_x + \iota_x \circ d$. Preserving a Pfaffian kernel $\ker(\omega)$ under infinitesimal Lie-action flows corresponds directly to `lieDeriv K x ω` lying in the differential ideal generated by $\omega$.
3. **Maurer–Cartan Flatness, Transfer by Representation (*Abbildung*), and R2/R3 Handoff (Klein §§1, 2, 4, 5)**:
   - Klein's *Abbildung* (§4) conjugates transformation groups along equivariant maps, while §5 notes that faithful representation of $G$ on space-elements excludes elements fixed by nontrivial normal ("self-conjugate") subgroups.
   - In R1's derivation spine, `quotientDerivationLieLane act` and `rangeDerivationLieLane act` quotient out the kernel ideal $\ker(\text{act})$ (matching Klein §5's faithfulness criterion for the action on $A$), while gauge transport $g \cdot \Gamma = g^{-1}\Gamma g + \theta_L(g)$ with $\theta_L(g) = g^{-1} D(g)$ (`SatisfiesMaurerCartan`) gives the flat infinitesimal symmetry transport whose noncommutative operator-ring invariants connect forward to R2 (double-real Krein / Kasparov spectral cycles) and R3 (coordinate-less `Cl(1,1)` symmetry invariance).

---

## 8. `BUCKET 1 / 2 / 3` Scope & Hypotheses Ledger

### `BUCKET 1` — Kernel-Checked Native Theorems (Unconditional within algebraic hypotheses)
- **Arbitrary-degree Lie-action & derivation CE complex** (`DerivationExteriorCalculus.lean`): `actionExteriorDerivative`, `ceExteriorDerivative`, $d_{n+1} \circ d_n = 0$ for all $n \in \mathbb{N}$ (no faithfulness, division-free over arbitrary `[CommRing R]`), `twoCochainEquivDerivationOperatorForm`, `threeFormToThreeCochain`, degree `0, 1, 2` compatibility with `DerivationDifferentialForms.lean`.
- **Noncommutative graded wedge & DGA identities** (`DerivationExteriorCalculus.lean`): `ceWedge` via structural `WedgeHistory` / `buildWedgeHistory` recursion, `ceWedge_assoc` (over `[Ring A]`), `lieDeriv_ceWedge`, graded Leibniz `ceExteriorDerivative_ceWedge` (over `[NonUnitalNonAssocRing A]`).
- **Arbitrary-degree covariant exterior calculus** (`DerivationExteriorCalculus.lean`): `ceCurvature`, `covariantExteriorDerivativeN`, Ricci identity `covariantExteriorDerivativeN_comp` ($d_\Gamma^2 \omega = [F, \omega]_\wedge$), Bianchi identity `ceCurvature_bianchi` ($d_\Gamma F = 0$).
- **Commutative specialization** (`DerivationExteriorCalculus.lean`): under `[CommRing A] [Algebra R A]`, graded commutativity `ceWedge_comm_of_commRing`, `ceWedge_self_one_eq_zero_of_commRing`, `ceCurvature_eq_exteriorDerivative_of_commRing`, `covariantExteriorDerivativeN_eq_ceExteriorDerivative_of_commRing`, and `DifferentialForms M A` instantiation (`derivationDifferentialForms`).
- **Maurer–Cartan sign dictionary & finite-stage towers** (`MaurerCartanFrameTransport.lean`, `DerivationRightLogarithmicForm.lean`, `DerivationGaugeTransport.lean`, `NoncommutativeConnectionCurvature.lean`, `MaurerCartanTower.lean`): exact identities between $\theta_L$, $\theta_R$, `pureGaugeForm`, `gaugeOneForm`, `MaurerCartanStage`/`MaurerCartanTower`, 5-graded Peirce MC tower (`peirce_five_graded_mc_stage`), and `TensorStageExactConnection` finite-stage cut curvature descent (`tensor_stage_mc_transport`).
- **Universal $\Omega^1_{\text{univ}}(A)$ & general-degree `OpForm` DGA** (`PeirceSpine/UniversalNoncommutativeOneForms.lean`, `OperatorExteriorAlgebraGeneral.lean`, `Optics/OperatorDerivationForms.lean`): universal derivation factorization (`universalOneFormToActionForm`, `universalOneFormToDerivationForm`), `opWedge`/`opExteriorDerivative` bridges (`opFormEquivActionForm`, `opFormEquivDerivationForm`), `OneFormTuple` vs `OpForm` contrast witnesses (`L1075, L1088`), and `FrechetOperatorDerivation` Lie-lane adapters (`L1233–1535`).
- **Tier 1–3 derivation adapters** (`DerivationExteriorCalculus.lean`, `OperatorExteriorAlgebraGeneral.lean`, `Optics/OperatorDerivationForms.lean`, `Thermo/OnsagerDifferentialFormsBridge.lean`): all 14 (+1) algebraic and thermodynamic adapters, plus `lieSystemRangeSubalgebra` without `bracket_self`.
- **Onsager carrier consolidation & general-form reciprocity** (`Synthesis/OnsagerOperatorDifferentialCalculus.lean`, `Thermo/OnsagerDifferentialFormsBridge.lean`): `TransportTensor.equivGeneral`, `TimeReversal.equivClosure`, `OnsagerFormPairing`, `ParityOnsagerFormPairing`, `onsager_pairing_general_form_reciprocity` (`L430`), and `ActionOperatorForm`/`DerivationOperatorForm`/`OpForm` DGA reciprocity compatibility theorems.
- **Linear CE alignment & algebraic disambiguation of Fréchet forms** (`Canonical/OperatorFrechetForms.lean`): linear `FrechetOperatorDerivation` CE alignment (`frechetExtDeriv_linear_eq_ceExteriorDerivative` for `ContDiff 𝕜 (⊤ : WithTop ℕ∞)` `SmoothOpMap`), `OperatorFrechetJet` (`L1373–1458`), and `NOperatorForm`/`OneFormTuple` (`L1459–1497`) disambiguation.

### `BUCKET 2` — Conditional Theorems (Explicit Analytic / Metric / Finite-Dimensional Parameters)
- **`derivationDeRhamComplex`** (`DerivationExteriorCalculus.lean` targeting `Spectral/Cohomology/deRham.lean`): DGA fields (`wedge`, `wedge_assoc`, `wedge_graded_comm`, `d_wedge`) are proved natively; `hodge`, `hkOperator`, and `hk_sq_zero` are supplied as explicit geometric/metric parameters.
- **Continuous chart alignment** (`DerivationExteriorCalculus.lean` targeting `Continuous/DeRhamBridge.lean`, and `Canonical/OperatorFrechetForms.lean`): pointwise `Chart α` directional-derivative `LieActionLane` and `frechetExtDerivReal` alignment with `extDeriv` on scalar `0`-forms (`frechetExtDeriv_chart_eq_mathlib_extDeriv` `L1093`, `frechetExtDeriv_complexChart_eq_mathlib_extDeriv` `L1119`) under `DifferentiableAt`/`HasFDerivAt` and `Chart α` nonzero-coordinate hypotheses.
- **Fréchet exterior derivative & Duhamel/BKM Hessian readouts** (`Canonical/OperatorFrechetForms.lean`): `frechetExtDerivK`/`frechetExtDeriv` (`d_Fr² = 0` at `L338, L355`) require `DifferentiableAt`/`ContDiff` smoothness (`minSmoothness 𝕜 2`); Banach exponential Duhamel alignment (`frechetExtDeriv_expFrechetZeroForm_eq_duhamelDerivative` `L1168`) requires `[CompleteSpace A]`; finite Gibbs BKM Hessian alignment (`frechetExtDeriv_logPartition_bkmHessian_alignment` `L1338`) holds on `FiniteOperatorAlgebra n` under `tracedExponential H ∈ Complex.slitPlane`.

### `BUCKET 3` — Open Closure Debt (Explicitly Out of Current Scope; Never `sorry`)
- **Infinite-dimensional analytic Hodge star & Hestenes–Krein operator construction** on general noncommutative `DerivationOperatorForm K n` (requires infinite-dimensional Riemannian/spectral metric volume theory not present in `DerivationLieLane`).
- **Infinite-stage direct-limit gauge connection**: `TensorStageExactConnection` constructs stagewise exact connections and direct-limit cocone descent of cut curvature (`ofStage`), NOT a global connection on the direct limit itself.
- **Full periodic cyclic homology ($S$-operator / SBI exact sequence)** beyond low-degree Hochschild coboundaries (`b₁ ∘ b₀ = 0` in `Physics/ConnesCyclicCohomology.lean`) and cyclic 1-cocycles (`NCG/NoncommutativeCyclicCocycle.lean`).
- **Mirror lane `src/` sync**: `src/InfoGeometry/NCG/NoncommutativeConnectionCurvature.lean` lags `lean/` and is deferred to M3 hygiene sync.

---

## 9. Verification Matrix

Every M1 deliverable must pass all gates below with zero `sorry`, `admit`, custom `axiom`, `native_decide`, or vacuous wrappers, and `#print axioms` restricted to `{propext, Classical.choice, Quot.sound}`:

| Check | Command | Scope |
|---|---|---|
| Single-file Lean kernel check | `python3 tools/infra/run_locked_lean.py <file.lean>` | Every created/modified `.lean` file |
| Locked Lake build (owners + consumers) | `python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock <Modules...>` | Owned modules + all direct downstream importers |
| Placeholder & bypass audit | `python3 tools/quality/placeholder_audit.py <files...>` | Byte-0 Apache 2.0 2026 header, zero `sorry`/`admit`/custom axioms |
| Axiom dependency audit | `#print axioms <theorem>` | Subset of `{propext, Classical.choice, Quot.sound}` |
