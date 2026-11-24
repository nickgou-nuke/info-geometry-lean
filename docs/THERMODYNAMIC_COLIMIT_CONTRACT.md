# Metriplectic laws on compatible algebraic colimits

## Intake and source

This continues the user's request to apply inductive colimits to finite
definitions and publish a PR. The implementation starts from PR #436,
commit `2a7558d4b2e9bf073eebd9d2efe6e45ee763b679`.

The newly available attachment is Frédéric Barbaresco's 220-page lecture
*Thermodynamics-Informed Neural Networks — Transverse Symplectic Foliation
Structure of Souriau's Lie Groups Thermodynamics*. Its cover is dated
2025-02-06; repeated slide footers refer to GIML'24, Mines ParisTech,
2024-09-03. Page numbers here are one-based PDF pages.

Source identity: 14,604,215 bytes; SHA-256
`733bc37aa042e866ebe4e02b052a3188f7cb745978c704e62c0f7314cec6bfaa`.
The supplied PDF is retained in the conversation, not copied into this
repository. The other attempted attachments were unavailable and are not
evidence for this change.

Pages 18, 121–123, and 189–190 motivate the algebraic target:

\[
v=L e+M s,\qquad Ls=0,\quad Me=0,\qquad
\dot E=B(e,v)=0,\quad \dot S=B(s,v)=B(s,Ms)\ge0.
\]

The dots in this source equation are interpreted here as the existing
algebraic rate readouts. Differentiable functions, gradient witnesses,
solution trajectories, and their derivatives are separate obligations.

## Existing owners and the missing implication

| Inspected owner | Reused content and scope |
| --- | --- |
| `Physics/FiniteMetriplecticDynamics` | Actual state-dependent linear endomorphisms, a bilinear pairing, and explicit skew/symmetry/positivity/kernel hypotheses; proves the algebraic energy and entropy rate laws. Its carrier need not be finite-dimensional. |
| `Thermo/GenericMetriplecticFlow` | Genuine covector-to-vector operators and the same laws; coordinate transport is already present. This interface cannot be obtained by silently identifying a direct limit of dual spaces with the dual of a direct limit. |
| `Categorical/CompatibleEndomorphisms` | Constructs an endomorphism of native `DirectLimit` from intertwining stage endomorphisms. |
| `LinearAlgebra/CompatibleBilinearColimit` | Constructs a real bilinear form by native `DirectLimit.lift₂`, with exact stage readback and symmetry/positivity transport. |
| `Canonical/MadelungMetriplecticColimitBridge` | Specialized finite matrix observable-action transport; does not supply the general pairing/operator adjoint descent needed here. |
| `SuperMetriplectic/HestenesKreinColimitMetriplecticEvolution` | Explicitly retired scalar surface; exports no operatorial colimit evolution theorem. |
| `Mathlib.LinearAlgebra.SesquilinearForm.Basic` | Native `LinearMap.IsAdjointPair`, `LinearMap.IsSelfAdjoint`, and `LinearMap.IsSkewAdjoint`. |

The missing implication is the interaction between the already constructed
limit pairing and limit operators. The new source proves it by common-stage
representative induction, then applies the existing rate-law theorems.

## Exact carrier and hypotheses

Let `I` be a nonempty directed preorder, `V i` real modules, and `f i j h`
coherent linear-map-class transition maps with a native `DirectedSystem`.
The carrier is `_root_.DirectLimit V f`, with canonical linear maps `ιᵢ`.

The supplied bilinear forms and operators obey

\[
B_j(f_{ij}x,f_{ij}y)=B_i(x,y),\qquad
T_j f_{ij}=f_{ij}T_i.
\]

Every operator used has its own intertwining hypothesis. The construction
does not require commuting operators, injective transition maps,
nondegenerate forms, a positive pairing, or finite-dimensional stages.

The rate laws additionally use symmetry of `B`, skew-adjointness of `L`,
self-adjointness of `M` where required for energy conservation, and
nonnegativity of `B(x,Mx)` where required for entropy production. These are
distinct conditions: positivity of `B` alone does not imply positivity of
the Onsager quadratic expression.

Energy and entropy vectors are explicit inputs. A vanishing stage vector
`Mᵢ e = 0` or `Lᵢ s = 0` has a vanishing limit image. A converse at the same
stage is not asserted without injective canonical maps.

## Target statements

1. Native adjoint-pair equivalence: the descended `T∞, U∞` are mutually
   adjoint for `B∞` if and only if all `Tᵢ, Uᵢ` are mutually adjoint for `Bᵢ`.
2. Native self-adjointness and skew-adjointness have the same equivalence.
3. Onsager nonnegativity is exact:
   `(∀ x, 0 ≤ B∞ x (M∞ x)) ↔ ∀ i x, 0 ≤ Bᵢ x (Mᵢ x)`.
4. Using these results, the existing algebraic energy and entropy laws hold
   on the actual native colimit with explicit kernel hypotheses.
5. For stage vectors, the velocity has the exact readback
   `L∞ (ιᵢ e) + M∞ (ιᵢ s) = ιᵢ (Lᵢ e + Mᵢ s)`; conservation and entropy
   production descend from the stated stage degeneracy conditions.

No replacement colimit carrier, assumed limit-law record, or commutative
surrogate is introduced.

The adjoint-pair statement transports a supplied compatible partner; it does
not produce an adjoint for an arbitrary operator. The rate-law hypotheses
match the existing physics owner, without claiming an optimal set of
assumptions. In particular, the entropy consumer retains that owner's
symmetric-pairing interface.

## Public declarations

| Owner | Declarations added |
| --- | --- |
| `LinearAlgebra/CompatibleBilinearColimit` | `form_isAdjointPair_iff`, `form_isSelfAdjoint_iff`, `form_isSkewAdjoint_iff`, `form_apply_liftEnd_nonneg_iff` |
| `Thermo/CompatibleMetriplecticColimit` | `velocity_of`, `energy_rate`, `entropy_rate_eq_dissipative`, `entropy_rate_nonneg`, `energy_rate_of`, `entropy_rate_of_eq`, `entropy_rate_of_nonneg` |

`Thermo/CompatibleMetriplecticColimitAudit` lists these eleven declarations.
Together with the previous disjoint inventories, the focused checker requires
87 fresh axiom records. Only `propext`, `Classical.choice`, and `Quot.sound`
are allowed. The focused workflow now screens seventeen explicit Lean files
and builds all three audit entry points, with unchanged dependency pins.

## Claims kept separate

The conditions on page 189 are treated as mathematical assumptions, not
derived from the displayed informal limit `k_B → 0`.

The orthogonal/transverse foliation diagram on pages 18 and 125 needs more
than these algebraic laws. For example, with the ordinary pairing on `ℝ³`,
take `e=e₁`, `s=e₃`,

\[
L=\begin{pmatrix}0&-1&0\\1&0&0\\0&0&0\end{pmatrix},\qquad
M=\begin{pmatrix}0&0&0\\0&2&1\\0&1&1\end{pmatrix}.
\]

Here `L` is skew, `M` is symmetric positive semidefinite, `Ls=0`, and `Me=0`.
Indeed `M=e₂e₂ᵀ+(e₂+e₃)(e₂+e₃)ᵀ`. Nevertheless,
`⟨Le,Ms⟩=⟨e₂,e₂+e₃⟩=1`, and the two operator images intersect in the
`e₂` direction. This independently checked elementary counterexample is
explanatory mathematics, not a new kernel-checked declaration in this PR.

The implementation does not construct a Poisson Jacobi identity,
integrable distributions, smooth foliations, Hilbert completion,
continuous-time evolution, a neural-network training result, or an
arithmetic/GRH consequence. Compatible covectors, Riesz identification, and
gradient compatibility need their own maps and proofs before these vectors
can be interpreted as gradients on a limit state space.

Further source normalization, reviewed separately from this implementation:

- Under the lecture's convention `Φ = -log Z`, `Q = dΦ`, and
  `Fisher = -Hess Φ`, a differentiable invertible Legendre map gives
  `Hess S = -Fisher⁻¹`. The slogans on pages 21 and 193 do not remove that
  sign or the inverse-map assumptions.
- Pages 75 and 78 display opposite signs between the differentiated group
  cocycle and the same named moment-map defect. A later affine-Casimir
  contribution must choose one coherent convention before translating them.
- Page 102's cocycle/bracket pairing is skew under the preceding definitions.
  Contracting it with the entropy Casimir direction gives zero; it does not
  supply dissipative positivity. The present result instead uses the
  separate real quadratic `B(s,Ms)`.
- A small nonzero squared degeneracy penalty on page 191 establishes neither
  exact degeneracy nor exact rate laws. Quantitative residual bounds are a
  separate target.

These are source-review conclusions, not additional theorems claimed by the
eleven-declaration Lean inventory. Existing finite Gibbs/Fisher and affine
Casimir owners remain distinct from the operator-colimit contribution.

## Validation

The selected theorem surface passed the complete
[hosted focused workflow](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45360324260)
on 2026-11-24. The accepted implementation revision is
`d83f97a4911844c2dbc4001ef2601c93568e37d0`, tree
`e9cd04a95b637ef34884c80d9397f26a6290aec2`.

Independent semantic review passed. Independent QA verified the exact hosted
revision, original evidence archive digest, build output, and fresh axiom
logs, then reran the committed axiom checker on the downloaded logs.

| Check | Observed result |
| --- | --- |
| Three focused audit targets, `--wfail` | Passed, 3,809 selected Lake jobs; no Lean warnings or errors. |
| Fresh compiler output from all three audits | Passed; 87 expected declarations, 87 reported records. |
| Axiom allow-list | Passed; only `propext`, `Classical.choice`, and `Quot.sound`. |
| Source proof gate and strict OpenGauss screen | Passed for all seventeen explicit Lean files. |
| Semantic-vacuity screen at error severity | Passed; 21 reviewed findings in existing declarations, none in the eleven new declarations. |
| Staged whitespace and actual pre-commit hooks | Passed for the implementation and both narrow repairs. |
| Dependency integrity | Lean `v4.34.1` and all nine dependency URL/revision pairs agree with the root pins, including Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. |

The accepted command was:

```bash
python3 verification/zeta-weil-krein/check.py --wfail build \
  InfoGeometry.Arithmetic.ZetaDihedralWeilKreinAudit \
  InfoGeometry.Categorical.CompatibleColimitAudit \
  InfoGeometry.Thermo.CompatibleMetriplecticColimitAudit
```

The workflow then ran fresh `check.py env lean` invocations on each audit and
`check_axioms.py` on those three logs. Independent QA reproduced the checker
result: exit 0, no errors, and parsed JSON equal to the hosted result.
The verification archive SHA-256 is
`44d9b4ee238907ef5914e8baad29daf298066b2256c15120d5eaade06bd38ee0`.

The accepted metriplectic owner SHA-256 is
`8e571f10b2c6bec7681a05c84804d1b44883ea3a0a89ea2d4f0e1c3e0524a3c2`.
The bilinear-colimit owner and new audit hashes are, respectively,
`dd59cb8df8997d13cbd987209884fcdaaf9a57433fd407bb5ae53ac8a938ba1b`
and `3be4dd1d29dca8ca5bf2084c44db56ea7f576f65624a5d457a02ca43a52ca52f`.

Two earlier hosted runs exposed elaboration issues now closed by the
accepted run. Run `45357274534` required explicit `LinearMap.IsSymm` in six
consumer hypotheses; native `LinearMap.BilinForm.isSymm_iff` proves the
alternative imported predicate equivalent. Run `45359391068` required a
fixed universe for the dummy state index. The adapter now uses monomorphic
`Unit`, while its tangent fiber remains the full native `DirectLimit`.
Neither repair changes the mathematical assumptions or conclusions.

Local compiler and unchanged pre-push attempts, including an attempt on the
accepted implementation revision, remained queued behind another job's
shared build lock. They were stopped while still waiting, before any local
Lake process started. No local compiler or publication-gate success is
claimed. The kernel evidence above comes from the isolated hosted runner.

Root path dependencies `HomotopyHypothesis`, `Atlas`, and `GIFT` remain absent
in this checkout. The accepted scope is the stated algebraic colimit and
rate-law surface and its audited import closure. It does not certify the
root-package build, the complete repository, or its publication gate.
