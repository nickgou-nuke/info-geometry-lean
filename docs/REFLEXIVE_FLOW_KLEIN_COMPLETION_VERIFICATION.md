# Reflexive flow / Klein kernel and synthesis correction verification

## Result and attribution

The current native associative-ring flow and Klein-representation chain is
integrated and verified. This task added the kernel obstruction and rational
regressions, repaired reduced-hypothesis constructor calls, and corrected the
Jordan sign and overstatements in the existing shared synthesis owner.

The flow, parabolic-unit, diagonal-unit, presented-group, semidirect-product,
Witt representation, and large synthesis implementations were already present
or concurrently added. They are reused and audited, not claimed as this task's
new implementation.

### Task edits

All paths below are relative to `lean/InfoGeometry/`.

- `Canonical/ReflexiveFlowUnits.lean`: update both conjugation statements to
  the actual `weylUnit hd hB hr` constructor (the fourth hypothesis remains
  necessary for support exchange).
- `Canonical/ReflexiveKleinRepresentation.lean`: propagate that constructor
  signature to the representation and generator evaluation.
- **New** `Canonical/ReflexiveKleinKernel.lean`:
  - `KleinPresentedGroup.glide_zpow_eq_one_iff`:
    `a ^ n = 1 ↔ n = 0`, for integer n, using the right coordinate of the
    existing semidirect-product representation.
  - `reflexiveKleinRep_nontrivial_kernel`: `a^4 ≠ 1` and `a^4 ∈ ker rho`.
  - `reflexiveKleinRep_not_injective`: every such representation is nonfaithful.
- **New** `Canonical/ReflexiveKleinKernelRegression.lean`:
  extend the existing integer `matD`, `matB` through `Int.castRingHom ℚ`;
  construct the representation at scalar unit 2, verify its actual images
  `W = !![0,1;-1,0]`, `D = !![2,0;0,1/2]`, and their noncommutation.
  Additional kernel-checked counterexamples distinguish grading sign reversal
  from inversion, transpose from reflexive inverse, correct Jordan bracket
  order from the proposed reversed order, and square-zero localization from
  vanishing of all Jordan associators.
- `Canonical/UnifiedGeometryOperatorSignificance.lean`: change
  `jordanAssociator T X S = [[T,S],X]` to the correct `[[S,T],X]` in the helper,
  master theorem and registered claim. The helper now reuses
  `Core.JordanAssociator.symm_operator_commutator`. Correct the module and
  definition documentation; historical identifiers are retained.
- `Canonical/All.lean`, `All.lean`: integrate the new regression chain and
  existing actual Witt representation.

## What the latest proposed synthesis gets wrong

1. **Jordan sign:** with the unnormalized product `J(x,y)=xy+yx`,
   `J(S,J(T,X))-J(T,J(S,X)) = associator(T,X,S) = [[S,T],X]`.
   For `S=X=E01`, `T=E10`, this is `2 E01`; the proposed reversed bracket is
   `-2 E01`. The original universal theorem is therefore false.
2. **Local associators:** even `d=E01`, `B=E10` has
   `associator(d,d,B)=-2d ≠ 0` over ℚ. Orthogonal supports do not imply all
   Jordan associators vanish. Existing `DrazinInterShellJordan` proves the
   normalized real-algebra value `-(1/2) • d`, under explicit inverse hypotheses.
3. **Cyclotomic terminology:** `Γ²=Δ` is active-support `t²-1`, not `Φ₂=t+1`.
   `W^4=1` means order dividing four, not necessarily exactly four. Polynomial
   identities alone do not assert primitive roots in arbitrary characteristic.
4. **Modular terminology:** weighted-support intertwining is algebraic.
   `OperatorAlgebra/TracialCARDensity.lean` constructs the actual weighted
   linear functional and proves cyclic boundary identities, explicitly without
   asserting positive normalized GNS states. The displayed ring equations do
   not construct a Tomita operator, analytic KMS strip, or modular automorphism
   group. No absence claim about other operator-algebra owners is made.
5. **Color superalgebra:** `ZornColorGL31Obstruction.not_faithful_gl31_with_CAR_odd`
   refutes a faithful homogeneous-bracket-preserving gl(3|1) map with its odd
   space sent to the raw CAR odd space. Equal total dimension is insufficient.
6. **Clifford scope:** `Lie/SplitOctonionCliffordAction.lean` constructs a native
   real Clifford algebra homomorphism and proves injectivity of the imaginary
   vector map, not injectivity of the whole Clifford algebra map. In ordinary
   real linear algebra the seven-generator Clifford algebra has dimension
   128 while the endomorphism algebra of an eight-dimensional module has
   dimension 64, so the asserted full embedding cannot hold. This dimension
   observation is explanatory here, not a new Lean dimension theorem.
   The owner's quadratic form is minus the split norm; signs must follow it.
7. **Geometry and exceptional structures:** support projections, opposite
   Peirce corners and diagonal commutators are genuine algebraic objects.
   They do not alone supply a cotangent duality, connection, curvature tensor,
   Kähler manifold, Hodge PDE theorem, or E6/F4 identification. The associator
   defect of left multiplication also does not by itself establish the axioms
   of a Nambu/Filippov 3-Lie bracket.
8. **Inverse existence and shell scope:** square-zero does not ensure a
   Moore–Penrose inverse exists. The inspected Drazin shell owners require a
   Moore–Penrose family for powers of the nilpotent part; the normalized Jordan
   owner uses `Algebra ℝ`. These hypotheses cannot be replaced with a claim
   that everything follows in every star ring from two nilpotency equations.

## Verification

All compiler commands were serialized with process prechecks and the shared
`/tmp/info-geometry-build.lock`. Unrelated active jobs were waited for, never
terminated. Dependency pins and build caches were not changed.

- `/tmp/reflexive-klein-baseline.log`: initially detected stale constructor
  calls after a concurrent signature reduction; not a success receipt.
- `/tmp/reflexive-klein-kernel1.log`: initial exponent-projection simplification
  failure, subsequently repaired.
- `/tmp/reflexive-unified-corrected1.log`: corrected synthesis and kernel owner
  passed; initial ordinary `decide` regression elaboration failed. Final
  regressions use `decide +kernel`, not native evaluation or `native_decide`.
- `/tmp/reflexive-klein-regression2.log`: focused regression build PASS,
  **8,962 jobs**.
- `/tmp/reflexive-unified-integrated2.log`: latest `InfoGeometry.All` PASS,
  **27,038 jobs**.
- `/tmp/reflexive-unified-axioms-final2.log`: latest strict kernel replay and
  transitive axiom checking PASS, **621 declarations in 14 owners**. Allowed axioms only:
  `propext`, `Classical.choice`, `Quot.sound`.
- `STALE_OLEANS []`, `SOURCE_DRIFT_AFTER []`; subsequent hash recheck
  `SOURCE_DRIFT []`; source-aware scan `FORBIDDEN_SOURCE_TOKENS []`.
- Staged whitespace check passed. No task commit was made.

After the first successful 622-declaration audit, a final hash check detected
concurrent changes to the Grassmannian and synthesis owners. The synthesis
change removed unnecessary ambient `StarRing` hypotheses and retained the
corrected bracket order, but replaced the scope corrections and owner-lemma
reuse. The stronger signatures were preserved; scope corrections and reuse
were restored. The second umbrella build and full replay above supersede the
first receipt. The latest synthesis has 155 declarations, not 156.

| Owner | Declarations |
|---|---:|
| Canonical/GrassmannianBundleCyclotomicOrientability | 193 |
| Canonical/ReflexiveNilpotentFlows | 54 |
| Canonical/ReflexiveFlowUnits | 12 |
| Canonical/ReflexiveParabolicUnits | 10 |
| Canonical/ReflexiveKleinRepresentation | 4 |
| Canonical/ReflexiveKleinKernel | 3 |
| Canonical/ReflexiveKleinKernelRegression | 24 |
| Canonical/KleinPresentedGroup | 52 |
| Canonical/KleinNativeSemidirectProductBridge | 36 |
| SuperMetriplectic/WittKleinRepresentation | 5 |
| Canonical/UnifiedGeometryOperatorSignificance | 155 |
| Core/JordanAssociatorRing | 30 |
| OperatorAlgebra/TracialCARDensity | 41 |
| Algebra/ZornColorGL31Obstruction | 2 |
| **Total, including generated declarations** | **621** |

The audit log records SHA-256 hashes for every selected source. Key hashes:

```text
4a3d25d98167748615f28cbfd804cfd9fce093d15580b52e2f69be7f4d631de2  ReflexiveKleinKernel
474909c504e7501e5b55c85c19fa0481a8f92cf87ea3f79d180a08e5377c743d  ReflexiveKleinKernelRegression
7a0c76b7d2ea4f4c2ba503ff994933e63653486432098775861426c84fcb0d2b  UnifiedGeometryOperatorSignificance
```

Unrelated dependency warnings and umbrella axiom reports remain, including
native-decision axioms in other Weyl/wallpaper/E8 owners. This is not a
repository-wide strict certification. No global super-Grassmannian, associated
spinor bundle, geometric holonomy, physical CPT, or analytic modular-theory
completion is asserted.
