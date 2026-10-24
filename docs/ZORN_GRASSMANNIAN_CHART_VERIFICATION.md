# Native Zorn Grassmannian chart verification

Verified on Lean v4.34.1, 2026-10-24. Contract:
`docs/ZORN_GRASSMANNIAN_CHART_CONTRACT.md`.

## Implemented scope

Three new owners in `lean/InfoGeometry/SuperGrassmannian/`, imported through
`InfoGeometry.All`:

- `ZornGraphChart.lean`: linear splitting of the existing Zorn carrier into
  `(a,u)` and `(v,b)` halves; intertwining of the existing left E11 projector
  with the standard graph projector; native graph kernels and their explicit
  quotient equivalences; an injective family
  `grassmannianChart : (Positive R →ₗ[R] Negative R) → Module.Grassmannian R (ZornVectorMatrix R) 4`.
  The quotient is proved finite projective with stalk rank four, not assumed.
  The zero graph is exactly the range of `L_map E11`.
- `GraphIdempotentDirections.lean`: for arbitrary modules over a commutative
  ring, a linear equivalence between the solutions of `PT + TP = T` and
  `Hom(M,N) × Hom(N,M)`. Reuses `Core.PeirceTangent` and `ProjectorGraphChart`.
  Graph-projector differences use only the first factor. An injective family
  of complement-changing idempotents retains exactly the same image submodule.
- `ZornGraphDirections.lean`: transports these constructions to native Zorn
  endomorphisms; identifies membership with the actual left E11 tangent
  equation; places the existing CAR odd submodule in it; constructs native
  idempotent graph projectors with the same graph kernels; proves the two
  dimensions over every field; computes both blocks of CAR odd operators.

For the signed operator `oddMap(p,q) = L(offDiagonal(p,-q))`, the two blocks are

```text
image-moving:      (a,u) ↦ (-a q + p × u, -q · u)
complement-moving: (v,b) ↦ (p · v, b p + q × v).
```

Both blocks of the `p = basis 0, q = 0` generator are proved nonzero over every
nontrivial commutative ring. Thus the entire color operator must not be
mistaken for a single fixed-complement graph direction.

Mathlib's Grassmannian rank is **quotient rank**. Its points here are ordinary
algebraic submodules. The graph parameter dimension is **16**; the full
idempotent first-order direction dimension is **32**. No analytic derivative,
global super-Grassmannian, sheaf gluing, moduli representability, tautological
superbundle, or continuum construction is asserted. No new CAS assertion was
used in these proofs.

## Verification

- Locked `InfoGeometry.All` build: **27,015 jobs**, exit 0.
  Log: `/tmp/zorn-grassmannian-integrated-final.log`.
- Strict kernel replay and transitive axiom audit: **720 declarations across
  10 selected owners**, all PASS. The three new owners contribute **83**.
  Log: `/tmp/zorn-grassmannian-axioms-final.log`.
- Allowed axioms only: `propext`, `Classical.choice`, `Quot.sound`.
- New owners pass the source-aware admission/unsafe/partial/native-decision
  scan and staged whitespace check. Final builds of these owners have no
  warnings; existing dependency warnings remain.
- Source hashes checked before and after the audit and again after the source
  scan: no drift. This is not a repository-wide axiom or warning-free audit.
- Observed other agents' compiler jobs were allowed to finish; verification
  used the shared build lock. Existing shared changes were preserved. Work is
  staged, with no task commit.

| Selected owner (relative to `InfoGeometry/`) | Declarations |
|---|---:|
| `SuperGrassmannian/ZornGraphChart` | 25 |
| `SuperGrassmannian/GraphIdempotentDirections` | 34 |
| `SuperGrassmannian/ZornGraphDirections` | 24 |
| `SuperGrassmannian/ProjectorGraphChart` | 14 |
| `SuperGrassmannian/GradedGraphChart` | 26 |
| `Core/PeirceTangent` | 28 |
| `Algebra/ZornLeftGrading` | 8 |
| `Algebra/ZornVectorMatrix` | 524 |
| `Algebra/ZornColorOperatorCoordinates` | 24 |
| `Algebra/ZornColorOperatorClosure` | 13 |

## Reproduction

Inspect and wait for existing Lean/Lake tasks before each verification command.

```sh
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.All
```

Under `tools.build_lock.acquire_build_lock(None, description, block=True)`, run
`lake env lean --run tools/infra/axiom_check.lean` with each selected owner's
`.lake/build/lib/lean/InfoGeometry/<owner>.olean` path from the table above.

## SHA-256 of selected source files

```text
d50af376eb933120097b4058fee578520bcc09638430267ebc16686b8fd61255  SuperGrassmannian/ZornGraphChart.lean
ea6bc01bf53bae09d324ea724d6f1189f4cd3dd2080f34f54b15859b18a24a5b  SuperGrassmannian/GraphIdempotentDirections.lean
f42fe645dd953fb054f985e078ad992c1df6585259a51a40fcfd7c63b854e13a  SuperGrassmannian/ZornGraphDirections.lean
2b1c3ef795385aea60509c7100c56e850ebec0bd4da9f5a99e5d76fb3ce73813  SuperGrassmannian/ProjectorGraphChart.lean
599e64d5819258480a95fa36300aea186503fe89e9de1759501aea9aebe63e8c  SuperGrassmannian/GradedGraphChart.lean
2119570fb07a8c639877ab033f2b6eaa2a110b00e12ac5576a96c0cbac60de8d  Core/PeirceTangent.lean
1da8ed287e208fb45e9b8891cb9713ea4c1b813f3ce81f1022501be9efd469fb  Algebra/ZornLeftGrading.lean
d3835a3df1d3f4bdbec5827a5cf23a9395e366cef35352c4ca6f3db13c7def62  Algebra/ZornVectorMatrix.lean
66e441a85922e1ce562dd800d57e462e056e4c172ed112487d82bdec55738caf  Algebra/ZornColorOperatorCoordinates.lean
e1dd50c2cbacce7e64a8efe9777e3d05c6f6565e7dc3e5ac0330ee9364227763  Algebra/ZornColorOperatorClosure.lean
```
