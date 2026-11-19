# Finite matrix obstructions, Kraus fixed effects and instrument history states

**Fresh restoration — 17 November 2026. Native verification pending.**
This report is reconstructed from the retained scoped task and recovered
candidate sources after the original scratch checkout became unavailable.
It is not a byte-identical recovery of the lost report, a recovered command
receipt, or a statement that the restored source has been compiled.

## 1. Selected mathematical contribution

The original three streams connect cyclotomic operators, finite binary matrix
stages, quantum measurements and infinite state constructions. The selected
formalization separates three claims with different hypotheses:

1. A unital representation of a finite full matrix algebra has dimension
   divisible by its source matrix size.
2. A fixed effect need not commute with a complete Kraus family; stronger
   quadratic fixedness or bistochastic hypotheses supply the missing bridge.
3. Ordered complete instruments construct a particular compatible family of
   finite pointer states, which instantiates an existing represented GNS state.

The algebraic obstruction and the instrument construction are separate owner
branches. No claim identifies every finite matrix representation with a
history process or transports a finite-stage obstruction into a completion.

## 2. Owner inventory

The restoration target is **47 public theorems and 13 public definitions**.
Three private instance-family abbreviations and two local instances are
additional implementation declarations in the GNS owner. Native audit counts
must be measured from the final compiled environment, not inferred from this
source inventory.

| Owner | Theorems | Public definitions | Purpose |
|---|---:|---:|---|
| `InfoGeometry.Algebra.MatrixAlgebraDivisibility` | 5 | 0 | Actual representations, dimension identity, divisibility and dyadic exclusions |
| `InfoGeometry.Quantum.KrausCommutatorGeometry` | 7 | 0 | Full-matrix commutator energy and fixed-point hypotheses |
| `InfoGeometry.Quantum.KrausFixedEffectCounterexample` | 10 | 2 | Explicit complete qutrit family and fixed unsharp effect |
| `InfoGeometry.Quantum.InstrumentHistory` | 18 | 5 | Ordered branches, weights, densities and finite-stage compatibility |
| `InfoGeometry.Canonical.InstrumentHistoryGNS` | 7 | 6 | Native C⋆ transport, constructed states and represented closure uniqueness |

Integration requires exactly these five new imports in `InfoGeometry.All`.
The intended three companion documents are this report,
`INSTRUMENT_STATE_COMPILER_CONTRACT.md` and `INSTRUMENT_HISTORY_CONTRACT.md`.
No dependency, generic GNS owner, historical proof owner or gate change is
part of the mathematical contribution.

## 3. Dimension divisibility uses actual matrix units

Let `K` be a characteristic-zero field, `V` a finite-dimensional `K`-module,
and `ρ : Matrix n n K →ₐ[K] Module.End K V` a unital algebra representation.
For a chosen index `i : n`, the source theorem states

\[
\dim_K V=|n|\,\dim_K\operatorname{range}(\rho(E_{ii})).
\]

The diagonal matrix units have idempotent images. The identities
`EᵢⱼEⱼᵢ=Eᵢᵢ`, together with cyclic linear-map trace, make those images'
traces equal. Their sum is the identity. Native algebraic projection trace
identifies each trace with the dimension of its range, and characteristic
zero converts the resulting scalar equality to a natural-number equality.
No adjoint preservation or positivity of the representation is required.

For an actual unital map `M_d(K) →ₐ[K] M_N(K)` with nonempty finite source
index, this yields `d ∣ N`. If a prime `p ≠ 2` divides `d`, it cannot divide
`2^k`, so no such map exists into any finite binary matrix stage.
The cases `d=12` and `d=24` use `p=3` and apply to every natural `k`.
The formal conclusion is an `IsEmpty` algebra-homomorphism type.

This contribution does not prove the converse existence direction or rule
out maps into a norm completion, a represented closure or a von Neumann
algebra. Those are different carriers requiring their own arguments.
The new divisibility owner makes no normality or unitarity conclusion from
a cyclotomic identity.

## 4. Fixed observables and genuine Kraus commutators

The backward map uses the existing `Choi.krausMap` at the adjointed family:

\[
\Phi(X)=\sum_i K_i^\dagger X K_i.
\]

The normalization `∑ᵢKᵢ†Kᵢ=I` makes this map unital. Its opposite
normalization `∑ᵢKᵢKᵢ†=I` is a separate hypothesis and supplies trace
preservation. The proof route retains full complex matrices and the ordered
commutators `Cᵢ=XKᵢ-KᵢX`.

Their positive energy is obtained by expanding the actual products:

\[
\sum_i C_i^\dagger C_i
=\Phi(X^\dagger X)-\Phi(X^\dagger)X-X^\dagger\Phi(X)+X^\dagger X.
\]

Fixedness of `X` and `X†X` makes the right side vanish. Positivity then
forces every commutator to vanish, and the converse is also established.
This equivalence quantifies arbitrary full complex matrices `X`.
For a self-adjoint fixed `E`, either `E²=E` or the explicit relation
`E²=aE+bI` supplies the square premise. Under both normalization laws,
ordinary trace yields `Φ(X)=X` if and only if all `XKᵢ=KᵢX`, again for
arbitrary `X`. No fixed-square premise is silently dropped from the merely
unital case.

## 5. A fixed positive effect outside the Kraus commutant

The counterexample lives on the full qutrit algebra `Matrix (Fin 3) (Fin 3) ℂ`:

\[
K=(E_{00},E_{11},\tfrac35E_{02},\tfrac45E_{12}),\qquad
E=\operatorname{diag}(0,1,\tfrac{16}{25}).
\]

The recovered source proves `E.PosSemidef`, `(1-E).PosSemidef`,
`∑Kᵢ†Kᵢ=I`, and `Φ(E)=E`. It also gives the concrete commutators

\[
[E,K_2]=-\tfrac{48}{125}E_{02},\qquad
[E,K_3]=\tfrac{36}{125}E_{12}.
\]

The theorem `effect_mul_kraus_ne` is inequality of actual ordered matrix
products. `exists_fixed_effect_outside_kraus_commutant` packages the same
concrete witnesses with positivity, positive complement, fixedness,
the transfer-operator identity and the family's completeness.

The source also proves that the opposite completeness relation fails and
that `Φ(E²)≠E²`. Thus the example does not contradict either the fixed-square
criterion or the bistochastic conclusion. The rational coefficients make
the exact finite witness inspectable without probabilistic sampling.

## 6. Complete instruments construct the finite history family

Take arbitrary finite system and internal-label types `S` and `κ` with
decidable equality. At time `n`, the binary recorded outcome `a : Fin 2`
selects a family `K n a : κ → Matrix S S ℂ`.
The input `ρ` is positive semidefinite; trace one is needed for normalized
states. The completeness law is time dependent:

\[
\sum_{a\in\{0,1\}}\sum_{i\in\kappa}K_{n,a,i}^\dagger K_{n,a,i}=I.
\]

The source constructs the selected chronological word and applies the
existing `forwardWord`. A new outcome applies the later Kraus map to the
previous branch. It does not reorder noncommuting system operations.
The history weight is the ordinary trace of that actual branch matrix.
Positivity proves nonnegativity and zero imaginary part; completeness proves
prefix marginalization and total weight `trace ρ` at every depth.

On the full pointer algebra `M_(2^n)(ℂ)`, the chosen density is the diagonal
matrix of those weights. Ordinary partial trace over the newest binary
factor, after the explicit index equivalence, recovers the previous density.
The positive linear functional on every full matrix observable is

\[
\Omega_n(X)=\operatorname{Tr}(X D_n)=\sum_h X_{hh}p_n(h).
\]

The diagonal dependence is a property of this specified dephased density.
It is not a claim that all quantum history states are diagonal. Compatibility
is proved for the actual `X ↦ X ⊗ I₂` embedding and then for every concrete
filtered transition. A compatible family is constructed from the instrument;
it is not inserted as an assumption.

## 7. What the GNS extension and uniqueness say

The existing tower is transported to Mathlib's native `CStarMatrix` type
copies with `StarAlgEquiv.arrowCongr`. Identity, composition and matrix
readback are proved using the original concrete maps.
The actual history functional is transported, proved positive in the C⋆
order, and packaged into the existing repository
`CStarStateColimit.Native.State` wrapper: a native positive linear map with
unit normalization. The proved restriction law supplies `cstarHistoryStateFamily`.

`representedHistoryState` instantiates the existing filtered GNS vacuum
state at stage zero on the norm closure of the represented algebraic
colimit. Its stage theorem recovers the specified functional on every
represented full finite matrix. Uniqueness compares two states on that same
closure and assumes agreement on every full stage observable. Dense range
and continuity give equality.

Outcome probabilities alone do not determine arbitrary off-diagonal state
values. The uniqueness theorem therefore uses the entire specified family,
not only its diagonal outcomes. No traciality, KMS property, faithful
representation, UHF identification or von Neumann factor classification is
asserted. The detailed source hypotheses are in the history contract.

## 8. Reuse and current verification status

The contribution reuses native matrix units, algebraic projection trace,
the existing `Choi.krausMap`, `InfoGeometry.Quantum.Choi.forwardWord`
(defined in `Quantum/KrausBoundaryDuality.lean`), focused `FinitePartialTrace`,
`CuntzMatrixTraceTower`, native `CStarMatrix`, and
`FilteredGNSVacuumState`. It does not duplicate the generic state or GNS APIs.

The intended base remains `08c34e03f610b452e03422037949196dc7d92d6d`,
with Lean 4.34.1 and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, subject to reconciliation
against the restored checkout. Source hashes identify recovered bytes;
they do not certify compilation.

At this restoration checkpoint, native development, final independent
kernel/axiom verification, final source gates and actual publication-hook
results are **pending**. No lost run log or acceptance receipt has been
reconstructed. All final evidence must identify the new frozen source tree.

The prior unchanged-base setup diagnosis found untracked Atlas and
HomotopyHypothesis path dependencies and an uninitialized pinned GIFT
submodule. That is retained historical context, not a freshly executed
preflight. The restored checkout's actual root preflight and required push
gate must be reported separately. A targeted native pass cannot certify
root Lake integration or replace a required gate.

## 9. Attachment provenance and mathematical corrections

The three supplied streams motivate separate mathematical branches: finite
matrix representations; fixed effects of quantum operations; and states
constructed from ordered instrument histories. The original files were freshly
reread and SHA256-fingerprinted on 17 November 2026.

| ID | Attachment | SHA256 |
|---|---|---|
| A | `Pasted text(20261116-180221).txt` | `d3e71750561f7077d8602e6d10519331c313f680f8e5db00b3359d827a8d9216` |
| B | `Pasted text (3).txt` | `12f8529e51f534c71e33d0f087b95cb6628cb3fbe2459bbe9b57dbbaa140e603` |
| C | `Pasted text (2)(4).txt` | `64d11fcf3a22c10bc6676018df350da225001f08993139e5e955491071c7bd63` |

The following corrections govern the selection. They add no Lean declarations
and make no compilation or acceptance claim.

| Source passage | Precise correction or scope restriction |
|---|---|
| A, Phase 0.1: cyclotomic annihilation and unitary diagonalization | A split square-free annihilating polynomial yields algebraic diagonalizability. It does not imply normality, unitarity, or diagonalization by a unitary matrix. A nonunitary similarity of a diagonal root-of-unity matrix preserves the polynomial identity. No new unitarity theorem is claimed here. |
| A, V Ded.1 and terminal synthesis item 2: the 24th-root phase | Multiplying a 12-dimensional Weyl product by a scalar 24th root remains an element of `M₁₂(ℂ)`. The phase correction does not construct the full `M₂₄(ℂ)` algebra or double the representation dimension. |
| A, V Ded.4–5: dyadic obstruction and completion | The selected matrix-unit argument excludes unital maps into each finite dyadic stage. A CAR norm-completion obstruction requires an additional projection/trace or K-theory argument; a tracial weak closure is another carrier. Neither a completed obstruction nor a hyperfinite-factor identification is a result of these five owners. |
| A, IV Level 4; B, Phase 0.4 and IV Level 4: KMS and factor type | The KMS condition does not determine type III: matrix Gibbs states already give type I examples [1]. Infinite-system factor classification requires further model hypotheses. Type III rules out realizing that algebra as `B(H₁) ⊗ I` in a type I tensor split; it does not prohibit an abstract Hilbert-space tensor isomorphism. Norm closure and weak closure remain distinct. |
| B, Phase 0.1 and IV Level 0: Hodge and algebra multiplication | A Hilbert-complex Hodge splitting is linear. It does not imply the universal claim that exact spaces are never multiplicatively closed: in a differential graded algebra, `(da)(db)=d(a db)`. An adjoint is not automatically a BV operator; the BV identities require additional graded algebraic hypotheses [2]. Closed-range claims also require hypotheses: `d=0` on an infinite-dimensional Hilbert space has closed range although zero is in the essential spectrum of its Laplacian. These topics are outside the selected owners. |
| B, IV Level 2 and V Ded.6: zero weak-value denominator | Orthogonal pre- and post-selection makes the usual quotient undefined. It does not assign infinity or determine a limiting value; the numerator may vanish too. Lean's totalized division must not be read as an operational post-selection definition without a nonzero-denominator premise. |
| B, V Ded.5; C, Phase 0.4 versus V Ded.1: fixed effects and disturbance | For a fixed complete instrument, conservation for every input state is exactly `Φ(E)=E`, equivalently the summed commutator defect vanishes. An individual nonzero commutator does not force a nonzero sum, and `E=I` is sufficient but unnecessary. C's own V Ded.1 gives the correct summed criterion. The selected Gram identity and qutrit counterexample address this distinction [3]. |
| C, III Bridge A and V Ded.5: full history state and uniqueness | Bridge A explicitly inserts diagonal entries of each observable, specifying a dephased functional on the full pointer algebra. That full family is the chosen input to the represented-state construction. Bare outcome probabilities do not determine arbitrary off-diagonal state values. The selected uniqueness theorem concerns agreement on every full stage observable on the same represented norm closure. |
| C, V Ded.2: tomographic span | For normalized density matrices and Hermitian observables `S`, the criterion is real span of `S ∪ {I}` equal to all Hermitian matrices. Normalization already fixes the identity expectation; the three traceless Pauli observables therefore suffice for a qubit. The stronger span-of-`S` requirement applies to an unconstrained linear readout, not automatically to normalized states. No new tomography theorem is claimed. |
| C, III Bridge B and V Ded.3: selecting complex quantum theory | The real-versus-complex dimension comparison identifies a failure of local tomography in ordinary real quantum theory [4]. Local tomography alone does not uniquely reconstruct complex quantum theory; reconstruction results use further operational axioms [5]. |
| C, IV Level 2 and V Ded.4: circulation and gauge | Nonzero circulation obstructs a single-valued additive primitive. Gauge equivalence also depends on the domain and allowed gauge group. For example, on the punctured plane and for nonzero integer `k`, `k dθ` has no single-valued real primitive but is gauge equivalent to zero through a globally defined circle-valued map `e^(±ikθ)` when all smooth `U(1)` gauges are allowed; the sign depends on the gauge-action convention. This must be distinguished from a gauge class restricted to globally exponentiated real functions [6]. No new gauge theorem is claimed. |

The streams' rank-increasing narrative posets can encode a proposed dependency
order. Acyclicity does not prove the mathematical assertions assigned to their
vertices or establish a unique physical synthesis. The actual dependencies of
the selected contribution are the five owner modules and their explicit imports.

### Primary references for the scope corrections

1. Afsar, Larsen and Neshveyev, [KMS States on Nica–Toeplitz C*-algebras](https://link.springer.com/article/10.1007/s00220-020-03711-6), introduction: the matrix-algebra Gibbs example.
2. Getzler, [Batalin–Vilkovisky algebras and two-dimensional topological field theories](https://arxiv.org/abs/hep-th/9212043), opening definition and Section 1.
3. Arias, Gheondea and Gudder, [Fixed Points of Quantum Operations](https://cs.du.edu/~mathfiles/preprints/nsm-math-preprint-0311.pdf): fixed points need additional hypotheses to equal the operation-element commutant.
4. Hardy and Wootters, [Limited Holism and Real-Vector-Space Quantum Theory](https://arxiv.org/abs/1005.4870).
5. Chiribella, D'Ariano and Perinotti, [Informational derivation of Quantum Theory](https://arxiv.org/abs/1011.6451): reconstruction uses several axioms, including purification.
6. Sanders, Dappiaggi and Hack, [Electromagnetism, Local Covariance, the Aharonov–Bohm Effect and Gauss' Law](https://arxiv.org/abs/1211.6420), Section 2.3.1: all smooth `U(1)` transformations and the more restrictive gauge group are explicitly distinguished.
