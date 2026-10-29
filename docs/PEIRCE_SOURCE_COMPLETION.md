# Source-matched Peirce completion and iterated inner action

## Intake

The two requested streams are:
- `Pasted text(20261028-150320).txt`, 12297 bytes, SHA256 `c9ea1b3660df958f1492aa1bb7aa48a1a59abb84439546bd958ba1180cfe8c85`.
- `Pasted text (2)(20261028-150355).txt`, 18108 bytes, SHA256 `8cad16c145458a913ffb933dab2ab48a47f590f36daa85ce58657bf6544f3ad9`.

Base: main at `d23c9afe00275126fd4d4e25cb0842ee55fe82af`. PR #260 is merged.
The second input is byte-identical to the existing octet intake. No duplicate
commutator, Jordan multiplication, Peirce carrier or sandwich map is added.

## Source-derived mathematics and existing owners

`Core.PeirceQuadraticFrame` proves opposite squares, anticommutation, quadratic
centralizers, weighted commutators and both double commutators, and reciprocal
Leibniz conservation equivalences. `Core.PeirceAdjointCycle` owns the idempotent
inner-action cycle. `OperatorAlgebra.LieJordanOctet` and its imported
`LieJordanBoundaryCalculus` own the eight endomorphism equalities and trace
readouts; `Algebra.PeirceSandwichDuality` owns reflection transport and support.
These owners are included unchanged in the new focused verification target.

The source's physics names are not theorem conclusions. In particular, a plus
reciprocal algebraic cycle is not a proved periodic time evolution; an operator
coefficient is not a scalar frequency. Commutation with specified generators
is not ambient centrality. The word Kraus does not give arbitrary or signed
sandwich maps positivity or trace normalization. The isolated N_- X N_- in
stream two conflicts with its following definition and table; the formalization
uses the explicit N_- X N_+ definition and records this choice.

## Explicit derived continuation, beyond the source's second iterate

Carrier: an arbitrary associative R-algebra A, with R commutative but A not
assumed commutative. Concrete tests are full real matrix algebras. No scalar
extension, diagonalization or commuting-generator assumption is introduced.

Let p^2=p, u in pA(1-p), v in (1-p)Ap. Put
E=u+v, J=u-v, M=uv+vu, C=uv-vu, T=2M, and D=LieAlgebra.ad R A C.
The existing source proves D(E)=T J, D(J)=T E and [C,T]=0. The continuation
proves, for every natural n,
D^(2n)(E)=T^(2n)E, D^(2n+1)(E)=T^(2n+1)J,
D^(2n)(J)=T^(2n)J, D^(2n+1)(J)=T^(2n+1)E.

Powers of D are native Module.End composition powers. Powers of T are ambient
noncommutative algebra products. A reusable arbitrary-inner-action lemma proves
transport of a commuting left factor; the Peirce specialization derives that
particular commutation from the established quadratic frame.

The invariant submodule is the actual native span of all T^n E and T^n J.
It is not declared two-dimensional, free, or nonzero without a witness.
A dense real four-by-four example certifies nonzero opposite corners,
noncommutation and nonscalar T; no diagonal surrogate is used.

## Prerequisite order

A finite native partial order records sufficient theorem stages: associative
operators, independent Peirce support and cyclic trace branches, composition
octet, quadratic frame, all-order action, and the combined completion. It is
not an automatically extracted whole-repository DAG or physical causality.

## Verification

Pending a completed focused kernel run. This authoring container has no Lean
executable and cannot resolve external hosts. The GitHub Actions workflow uses
the unchanged repository toolchain and Mathlib pin and the existing serial
source-closure/Lean.collectAxioms checker. No full root build or independent
human/agent review is claimed. All authored files are additive.
