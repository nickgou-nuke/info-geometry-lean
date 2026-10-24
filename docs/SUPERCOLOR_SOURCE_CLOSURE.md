# Supercolor source closure: theorem contract

Source base: `e568ad8b67030bd48251ded61ec86af2abcce8f7`.
Intake: `Pasted text(20261023-165528).txt`, the extended-supercolor note.

## Existing owners are retained

`Core.SuperGrassmannianSusy` owns the ring operations, MP-based supercolor
predicates, total charges and several star identities. `Core.SupercolorMultiplication`
already proves common-source matrix-unit multiplication and ordinary commutator
closure. `Core.SupercolorMatrixExamples` already contains both the common-source
`Option iota` matrix units and disjoint `iota × Bool` sectors, including Fin 2
and Fin 4 signed-square certificates. These definitions are not duplicated.
`Singular.MoorePenrose.IsMoorePenroseInverse` is the sole MP predicate used here.

The submitted `Matrix.stdBasisMatrix` construction is represented by the existing
native `Matrix.single` owner. The existing Bool coordinate has two elements,
just as the proposed Fin 2 coordinate does; no new competing matrix model is
introduced. Existing owner files and root test aggregators remain unchanged.

## New generic claims

For a native supercolor system, the following are equivalent:

- every forward arrow absorbs every co-range projection on the right;
- all co-range projections `b i * d i` are equal.

The proof uses the existing MP self-adjointness laws. A single absorption
hypothesis also suffices for the corresponding matching-middle product.

For common source q, prove the endpoint relations and actual odd actions:

```
[E_ij, d_l] = delta_jl d_i
[E_ij, b_l] = -delta_li b_j
{d_i, b_j} = E_ij + delta_ij q
```

The reference-coordinate term q is essential in the odd--odd bracket. A
structure containing common-source absorption is not by itself an sl(k|1)
representation. The proposed `IsSlk1SuperalgebraSpec` is therefore not copied
under a classification-suggesting name. Its substantive common-source content
is expressed and characterized directly; full classification remains separate.

Star symmetry of the sector sum/difference and total charge requires MP only.
The existing primitive/Majorana star theorems retain their explicit `b = star d`
hypothesis. The parity-labelled bracket satisfies all eight associative
super-Jacobi derivation identities; the two requested cyclic/derivation sectors
are also exposed. This does not supply a grading on every arbitrary ring.

## Concrete realizations and a real representation map

`colorEmbeddingHom` is a native nonunital ring hom from matrices on iota to
matrices on Option iota, extending by zero on the reference coordinate. It is
injective, star-preserving, commutator-preserving, and sends single-entry units
to the existing common-source color bosons. It is intentionally nonunital in
the full ambient matrix algebra. This is an ordinary color-algebra embedding,
not a representation theorem for an independently defined Lie superalgebra.

The disjoint model has noncommuting forward/backward arrows within each sector
but zero off-diagonal color bosons. A theorem proves that combining distinct
orthogonal colors with common-source absorption forces the relevant arrows to
vanish. The nonzero concrete model refutes that absorption. It must not be used
as a witness for off-diagonal color mixing. The submitted N=4/N=8 terminology
is retained only as a two/four-color generator count, not as proof that all
individual odd squares equal a common physical Hamiltonian.

## Verification

A narrow test module imports the complete new surface and checks the reused
API plus concrete nonzero and vanishing entries. The new workflow compiles
unchanged complete owner dependencies and additions against repository pins
under the shared build lock; it then enumerates new declarations in the actual
imported environment. It uses public `Lean.collectAxioms`, rejects unsafe or
partial declarations and axioms outside propext/Classical.choice/Quot.sound.

At authoring time verification is pending. The workflow result and artifact,
not this document, decide acceptance. No claim is made that the uploaded module
compiles unchanged or that the full root Lake package is verified.

Local full-checkout command, once root dependencies are available:

```
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Core.SupercolorClosureTests
```
