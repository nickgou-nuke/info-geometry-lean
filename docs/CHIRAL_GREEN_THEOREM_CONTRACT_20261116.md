# Chiral Green operator and normalized spectral pairing

## Intake and provenance

This task compiles the attached chiral/Möbius/Witten discussion into bounded,
native Lean/Mathlib statements. The original text is preserved in
[`CHIRAL_MOBIUS_WITTEN_INTAKE_20261116.md`](CHIRAL_MOBIUS_WITTEN_INTAKE_20261116.md).
Its original byte SHA-256 is
`0c090eb9ef05b43c17a291fb8fbdd6447afd26d669203f1c3a75f85fc05dd4cd`.

The source baseline is `08c34e03f610b452e03422037949196dc7d92d6d` of
`nickgou-nuke/info-geometry-lean`. The pinned environment is Lean `v4.34.1`
and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. This contract is
written before mathematical owner edits. Validation and completion status are
recorded separately; a target below is not evidence that it has been proved.

## Owner search and genuine gaps

The bounded source audit inspected declarations, assumptions, imports, and
selected consumers, with alternative-name and external Mathlib searches.

| Existing owner | Reuse and boundary |
| --- | --- |
| `OperatorAlgebra/PartnerEigenspaces` | Actual nonzero `BA`/`AB` eigenspace equivalence; do not reproduce it. |
| `OperatorAlgebra/PartnerGeneralizedEigenspaces` | Generalized eigenspace pairing; no new Jordan claim is needed. |
| `Analysis/HilbertGramDuality` | Continuous Gram eigenspace equivalence and exact inner/norm scaling; the normalized linear isometry is the missing upgrade. |
| `Singular/MoorePenrose` | Actual closed-range inverse, all four Penrose equations, uniqueness, and range projection. Use this construction, not a supplied inverse field. |
| `Singular/SquareZeroChiralHodge` | General `star_same_order` transport is reusable without square-zero assumptions. Its normalized `a + a⁺` is distinct from `a + a†`. |
| `Singular/MoorePenroseTransport` | Exact similarity/Gram-commutation criterion. Audited as a possible route; the selected self-adjoint case admits a stronger group-inverse argument. |
| `Dynamics/ChiralHodgeMoorePenroseBridge` | Existing real Hodge Laplacian inverse and harmonic projection. Does not derive general odd-supercharge inverse or square compatibility. |
| `Canonical/ReflexiveNilpotentFlows`, `Core/PeirceWeylUnits` | Existing reflexive square-zero and supported Weyl algebra. No duplicate owner is planned. |
| `Canonical/GramianGroupInverse` | Finite square real matrices with supplied group-inverse witnesses; does not construct the target Hilbert-space Green operator. |
| `Dynamics/RealTokenChiralGreenBridge` | Green laws are witness fields; they do not establish the present construction. |

The scoped negative finding is that the examined owners and their consumers do
not contain the normalized native eigenspace isometry or the canonical
closed-range self-adjoint/chiral square-inverse theorem below. This is not a
claim that every historical file has been verified.

## Contract A: normalized positive-eigenspace isometry

Carrier: complete real or complex Hilbert spaces `E`, `F`, represented uniformly
by `[RCLike 𝕜]`, and a bounded operator `A : E →L[𝕜] F`.

For a real `λ > 0`, construct the native `LinearIsometryEquiv`

$$
U_\lambda : E_\lambda(A^\dagger A) \simeq_{\!\mathrm{isom}}
E_\lambda(AA^\dagger),
\quad U_\lambda x=(\sqrt\lambda)^{-1}Ax,
\quad U_\lambda^{-1}y=(\sqrt\lambda)^{-1}A^\dagger y.
$$

Reuse `gramEigenspaceEquiv` and its norm scaling. Extend the actual
`Analysis/HilbertGramDuality` owner. No finite-dimensional ambient space,
spectral basis, compactness, or global polar decomposition is assumed or
concluded. Eigenvalue zero is deliberately excluded.

## Contract B: canonical bounded chiral Green operator

Carrier: a complete real or complex Hilbert space `E`. Let
`Q : E →L[𝕜] E` be self-adjoint and have closed range. Define `B` by the
existing function `moorePenroseInverse Q hClosedRange`.

Derive, rather than assume:

$$
B^\dagger=B,\qquad QB=BQ=P_{(\ker Q)^\perp},
\qquad BP_{\ker Q}=P_{\ker Q}B=0.
$$

Derive `range (Q * Q) = range Q`, and hence closed range of the square.
Using the existing canonical inverse for this derived closed range, prove

$$
(Q^2)^+=B^2,\qquad (Q^2)^+Q=B=Q(Q^2)^+.
$$

For any bounded `Γ : E →L[𝕜] E` satisfying `Γ * Q = -(Q * Γ)`, derive

$$
\Gamma B= -B\Gamma
$$

and commutation of `Γ` with the regular and kernel projections. This includes
chiral gradings. Independent contract review identified a useful strengthening:
in the selected self-adjoint closed-range setting, no self-adjointness or
involution hypothesis on `Γ` is needed. Its anticommutation preserves the
kernel and range. Algebraically, the derived group-inverse identities suffice.
This does not assert Moore–Penrose covariance under arbitrary similarities.

Generic noncommutative star-ring lemmas used by the construction may be
exposed in the same focused `Singular/MoorePenroseChiralGreen` owner. No global
commutativity or diagonal representation is permitted. Commutation of `Q`
and `B` must follow from the Penrose and self-adjointness laws.

## Actual proof dependency plan

1. Existing closed-range Hilbert construction gives all four Penrose laws.
2. Existing star transport plus uniqueness gives self-adjointness of `B`.
3. Self-adjoint support laws give `QB = BQ`.
4. Reflexivity plus this commutation gives range equality and the square MP
   witness; uniqueness identifies the canonical inverse of `Q²` with `B²`.
5. The existing range projection, self-adjointness, and closed range identify
   regular/kernel support and annihilation.
6. The derived commuting Penrose pair gives support commutation and inverse
   anticommutation for every element anticommuting with the original operator.
   Specialize this noncommutative ring argument to bounded Hilbert operators.
7. Independently, existing Gram norm scaling and positive square-root
   normalization give the native eigenspace isometry.

These are proposed proof dependencies, not a causal graph of physical laws.
Only implications that appear in accepted proofs will be reported as proved.

## Atomic claim ledger

| Intake claim | Epistemic classification and exact treatment |
| --- | --- |
| Opposite Lie grades are associative square-zero operators | Requires a chosen representation/Peirce realization; not implied by grading alone. |
| Nonzero square-zero operator has an ordinary inverse | False in a nontrivial unital algebra; existing nilpotent-nonunit owner applies. |
| Reflexive inverse equations establish Moore–Penrose inversion | Insufficient: the two self-adjoint support equations are additional data. |
| Supports `EF`, `FE` are noncommuting under square-zero assumptions | False: both products of these supports are zero, so they commute. |
| Failure of mutual inversion forces a nonzero commutator | False in general; noninvertibility alone supplies no modular dynamics. |
| One Weyl exchange condition uniquely forces `S² = -1` | False without additional conditions. Existing supported Weyl results state their exact support hypotheses. |
| Positive-energy chiral eigenspaces pair | Existing algebraic/continuous pairing is reused; normalized isometry is Contract A. |
| Zero Witten index implies no zero modes or SUSY breaking | False: equal nonzero chiral kernel dimensions give zero index. No such conclusion is promoted. |
| Noncompactness forces heat-supertrace drift | Unsupported. Trace class, domains, boundary conditions, and regularization must be specified. |
| A bulk drift integral universally equals an eta correction | Unsupported. APS and Callias statements require their own operator and boundary/asymptotic hypotheses and conventions. |
| `H = ker Q ⊕ range Q` for every self-adjoint operator | Generally requires closure of the range; Contract B explicitly assumes closed range. |
| `Q⁺ = (Q²)⁺ Q` on the full bounded Hilbert space | Contract B; inverse means the constructed Moore–Penrose inverse, not a nonexistent global ordinary inverse. |
| Canonical Green inverse respects chirality | Contract B; anticommutation alone suffices for the bounded grading operator once `Q` is self-adjoint with closed range. |
| A 15-node rank-labelled graph proves analytic necessity, uniqueness, or a nonzero colimit | Not established by graph labels; no theorem is promoted from this narrative. |

## Excluded consequences and remaining analytic debt

The targets do not construct an unbounded Dirac operator, a self-adjoint
domain, a heat semigroup/trace, a Fredholm index theorem, an APS or Callias
boundary problem, an eta invariant, a continuous-spectrum decomposition, a
metaplectic cover, or a categorical colimit. They neither prove a physical
vacuum-volume law nor identify a para-Kähler potential with a partition
function. Those claims require independent constructions and hypotheses.

## Acceptance plan

G-A supplies candidate proofs; A-A performs independent owner/type and
semantic review; a distinct QA-A performs the final verification review.
Builds and tests are serialized through the repository's shared lock. Use
the exact pinned Lean/Mathlib sources, compile the repository import closure,
and audit every declaration owned by the two changed mathematical modules,
including their transitive axiom dependencies. Only `propext`, `Classical.choice`, and
`Quot.sound` are allowed axioms. Record warning/debt scans, staged gates,
and root-wrapper results separately. No proof holes or new axioms may be
introduced to promote a target.

## Primary references for the claim boundaries

- Edward Witten, [*Constraints on Supersymmetry Breaking*](https://web2.ph.utexas.edu/~vadim/Classes/2025f/Witten1982.pdf),
  Nuclear Physics B 202 (1982), 253–316, especially pp. 256–257: nonzero-energy
  pairing and the distinction between zero index with and without zero modes.
- M. F. Atiyah, V. K. Patodi, I. M. Singer,
  [*Spectral Asymmetry and Riemannian Geometry I*](https://webhomes.maths.ed.ac.uk/~v1ranick/papers/aps001.pdf),
  Math. Proc. Cambridge Philos. Soc. 77 (1975), 43–69, Theorem 4.2: the stated
  Dirac boundary problem has a correction involving both the boundary eta
  invariant and boundary kernel dimension, with a factor of one half.
- A. Carey, F. Gesztesy, D. Potapov, F. Sukochev, Y. Tomilov,
  [*On the Witten Index in Terms of Spectral Shift Functions*](https://arxiv.org/abs/1404.0740):
  a specified regularization and analytic hypotheses are required in the
  non-Fredholm setting.

These references constrain the interpretation. They are not Lean proofs and
are not used as axioms of the formal development.
