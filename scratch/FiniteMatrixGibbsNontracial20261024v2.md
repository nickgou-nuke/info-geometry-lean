# Native tilt Gibbs nontraciality

Uncompiled candidate; independent AA and locked QA required. No builds or live edits.

## Stable public interface

Namespace: `InfoGeometry.Canonical.FiniteMatrixGibbsFunctional`.
Final theorem: `tiltHamiltonian_gibbs_matrixUnits_ne (h beta : real)
(hbetah : beta * h != 0)`.
Its conclusion is the inequality of native Gibbs expectations of E01*E10
and E10*E01 for H = h • `KleinBottleSewingExact.tilt2`.
Eij is written directly as `Matrix.single i j (1 : complex)` on Fin 2.
Parent can transport this exact inequality through the existing finite-seed
readback and stageInjection multiplication laws. No colimit definitions here.

## Reuse and proof contract

- `Canonical.FiniteMatrixGibbsParity`: existing tilt, Hermitian proof,
  native `gibbsDensity`/`gibbsFunctional`, and finite parity context.
- Mathlib `Matrix.diagonalAlgHom` is locally equipped with the actual star
  law `Matrix.diagonal_conjTranspose`; this is a homomorphism, not a new carrier.
- `StarAlgHom.map_cfc`, `cfc_map_pi`, and `cfc_algebraMap` evaluate the native
  real continuous functional calculus on a real diagonal Hamiltonian.
- `gibbsDensity_diagonal` exposes that reusable general diagonal calculation.
- `tiltHamiltonian_gibbsDensity` specializes it to diag(h,-h).
- `tiltHamiltonian_gibbs_matrixUnits_difference` gives the exact difference
  (exp(-beta*h)+exp(beta*h))^-1 * (exp(-beta*h)-exp(beta*h)), in complex scalars.
- `tiltBoltzmann_weights_ne` uses injectivity of the real exponential.
- The final inequality uses positivity of the real partition sum.

The required condition is beta*h != 0. Nonconstant H alone is insufficient
at beta=0. No positivity condition on beta is needed. This is finite algebraic
nontraciality of the actual CFC Gibbs functional, not an analytic KMS claim.
The helper's Hermitian hypothesis is the existing Gibbs definition's proof
argument, not the desired density identity. No new density or state is defined.

## QA focus

Check diagonalAlgHom parameters, function-space CFC instance elaboration,
map_cfc predicate/coercion inference, dependent rewriting of the Hermitian
proof argument, and simplification of Matrix.single products. Source proof
only at handoff: no kernel or axiom-clean result is claimed.

## V2 correction record

Preserves v1 and all theorem statements. Based on independent QA log
`/tmp/qa-a-finite-gibbs-nontracial-vuh2fu07/compile.log`:

- `Matrix.diagonalAlgHom` has implicit n and alpha, explicit R; pass named
  n/alpha and only complex as the positional scalar argument.
- Eliminate the dependent Hermitian proof argument via `IsHermitian.cfc_eq`
  before rewriting the tilt matrix equality. Transport the Hermitian proof
  explicitly to obtain the general diagonal helper's result.
- Remove the unnecessary `<;>` before ring.
- Change the directional weights lemma's prose from “exactly away” to “when”;
  no iff theorem is claimed.

No v2 build or tests run. Prior AA semantic PASS applies to the mathematical
contract as reported by parent; this revised source still needs serial QA.
