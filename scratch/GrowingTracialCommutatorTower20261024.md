# Growing tracial commutator tower: bounded construction contract

Read-only source discovery, 2026-10-24. This is a mathematical contract, not a
Lean proof or kernel closure. No live edits, builds, tests, or new Lean carriers.

## Exact native carrier and existing owners
- `Canonical/CuntzMatrixTowerInstantiation.lean`: `MatrixStage n` is
  Matrix (Fin (2^n)) (Fin (2^n)) ℂ; `matrixTraceState_mul_comm` proves cyclicity.
- `Canonical/CuntzMatrixTraceTower.lean:45,49`: `stageIndexEquiv n` and
  `concreteStep n` implement reindexed A ⊗ I₂. `concreteMap` iterates those maps.
- `Canonical/CantorBernoulliCStarMatrixTraceState.lean`: `CStarMatrixStage`,
  `cstarConcreteStep`, `cstarMatrixInductiveSystem`, `cstarMatrixTraceStateFamily`;
  `cstarMatrixTraceState_faithful` (241) detects A=0 from τ(A* A)=0.
- Use E n = `(cstarMatrixTraceState n).functional.GNS`, equivalently native
  `GNSStage CStarMatrixStage cstarMatrixInductiveSystem cstarMatrixTraceStateFamily n`.
  Use `FilteredGNSHilbertColimit.filteredGNSIsometricDirectSystem` exactly.
  `FilteredGNSRepresentation.filteredGNSMap_toPreGNS` (346) gives the actual
  bonding readback [A] ↦ [cstarConcreteMap A].
- `FilteredCompatibleOperatorColimit.CompatibleOperatorFamily` requires all-index
  intertwining and one bound. `completedOperator_stage` (223) gives readback;
  `FilteredCompatibleOperatorSelfAdjoint.completedOperator_selfAdjoint` (71)
  proves selfadjointness by density once this family is actually constructed.

## Rigorous compatibility obstruction (proposed first small theorem)
For any unital ring hom e:A→+*B and H:A, K:B, elementary distributivity proves:

  (∀ a, K*e a-e a*K = e(H*a-a*H))
    ↔ ∀ a, Commute (K-e H) (e a).

This is a precise algebraic obligation; no output compatibility field is needed.
On faithful trace-GNS stages it is also necessary for bounded commutator
intertwining, because the dense representative embedding is injective.

For LEFT multiplication instead, intertwining evaluated on the unit/vacuum forces
[K] = [e H]; faithful trace implies K=e H. Thus a strictly compatible left-action
Hamiltonian family beginning at scalar stage zero cannot grow new interactions.
This statement requires faithful stage states, not merely faithful GNS representations.
The newly proved matrix representation faithfulness must NOT be confused with a
vacuum vector being separating for an arbitrary nonfaithful state.

For a boundary coupling λ Z_old⊗Z_new, testing old switch X_old⊗I gives
λ[Z_old,X_old]⊗Z_new ≠ 0 for λ≠0. Such increments violate strict compatibility.
The exact criterion is the relative commutant; do not claim that arbitrary
summable nearest-neighbor interactions satisfy it. No formal classification of
that relative commutant is needed for the onsite construction below.

## Genuine growing construction, not a fixed-seed family
Let Z=Physics.KleinBottleSewingExact.tilt2 and X=switch2. Define actual matrices
using the existing reindexing, not a new tensor carrier:

  tailZ n = reindex(stageIndexEquiv n) (I_(2^n) ⊗ Z)
  tailX n = reindex(stageIndexEquiv n) (I_(2^n) ⊗ X)
  H 0 = 0
  H (n+1) = concreteStep n (H n) + w n • tailZ n.

w:ℕ→ℝ, Summable (fun n => |w n|). A concrete non-terminating choice is
w n = (1/2:ℝ)^(n+1), with sum of absolute weights 1.
Each H n is Hermitian. TailZ commutes with every concreteStep n A by
Matrix.mul_kronecker_mul and reindexAlgEquiv.map_mul. Therefore

  [H(n+1), concreteStep n A] = concreteStep n [H n,A].

Define D n on EXISTING trace GNS by [A] ↦ [H n*A-A*H n], transported through
CStarMatrix.ofMatrixStarAlgEquiv. Prove successor compatibility on representatives,
extend by density, then induct to all n≤m. No Hamiltonian compatibility is assumed.

Fresh-stage action is certified by

  [H(n+1),tailX n] = w n • reindex(stageIndexEquiv n) (I ⊗ [Z,X]).

The old part commutes with tailX; this is nonzero when w n≠0. For geometric
weights it occurs at EVERY new stage. This is the appropriate nonconstant claim
for operators on different carriers: genuinely new tail action, not D(n+1)≠D n
(an ill-typed comparison), and not a fixed seed transported unchanged.

## Small analytic helper genuinely still needed in inspected owners
Mathlib Analysis/CStarAlgebra/GelfandNaimarkSegal.lean already gives
`PositiveLinearMap.toPreGNS`, `ofPreGNS`, `preGNS_norm_sq`,
`leftMulMapPreGNS` (159), `gnsStarAlgHom`, and completed action readback.
For a tracial positive map f, construct right multiplication on its SAME PreGNS:

  R_b x = f.toPreGNS (f.ofPreGNS x * b),   ||R_b x|| ≤ ||b|| ||x||.

Trace cyclicity makes x↦star x norm-preserving on this PreGNS. Hence
||[x b]|| = ||[star b * star x]|| ≤ ||b|| ||[x]|| by the native left bound.
Package R as a ContinuousLinearMap and extend to the existing f.GNS completion.
Do not install a NormedAddCommGroup on generic seminormed PreGNS or a new Hilbert carrier.
For Hermitian H, trace cyclicity proves R_H symmetric, as is L_H; hence
D_H=L_H-R_H is selfadjoint. The factor i belongs to the time-flow generator iD_H,
not to this selfadjoint D_H itself.

Uniform bound: ||D n|| ≤ 2||H n|| ≤ 2 Σ_{j<n}|w j| ≤ 2 Σ'j |w j|.
TailZ is a selfadjoint unitary in the native CStarMatrix norm, so norm=1;
cstarConcreteStep is contractive. Geometric weights give bound 2.
Now fill the existing CompatibleOperatorFamily with proved fields and apply
completedOperator_selfAdjoint. New nonzero tail action survives the isometric
stage injection into the existing completed Hilbert colimit.

## Search scope and nearby non-solutions
- FilteredGNSTailRepresentation constructs bounded fixed-observable families;
  these are useful infrastructure but not this growing Hamiltonian recursion.
- FiniteHestenesHilbertSchmidtStandardForm.rightActionLinear is a raw M₂ linear
  map and its commutant theorem, not the general completed trace-GNS right bound.
- FilteredGNSTomitaCore has algebraic star/involution/transport; the graph-closure
  owner explicitly warns generic Tomita need not be bounded. Trace is essential.
- Cl11TraceGNSHilbertColimitBridge proves faithful stage-one vector readback and
  concrete right-action comparisons; it does not construct this all-stage family.
- ConcreteCliffordDiracTower.Dfinite=n•id still fails strict bonding compatibility
  by a bond-vector defect; its cutoff pairing on all ℕ→ℂ is not a Hilbert norm.
- UHFCantorConnesSpectralTriple.stageCommutatorNorm_map assumes e D=E and an
  isometric hom; it does not handle centralizing increments or GNS superoperators.
- DiracHeatSemigroupBridge transports an existing intertwiner through exp; its
  tsum proof is not a construction of summable growing interactions.
Searches covered these actual owners plus CAR/Clifford tensor, trace-GNS,
right-action, interaction, and spin-chain related files. No assembled family or
tracial PreGNS right-bound helper was found in these inspected surfaces.

## Completion and interaction boundary
This is an independently weighted ONSITE sum; it is not a coupled interacting
Dirac tower, nor an unbounded Dirac/spectral-triple theorem. Strict compatibility
rules out boundary-crossing coupling increments unless their commutator vanishes
on the entire old algebra. A genuinely coupled model would need different domain
or asymptotic-compatibility infrastructure, not an unproved CompatibleOperatorFamily.

proofs/DiracColimit.lean hPair requires exact finite-stage coverage of every
completed vector, stronger than native density. Do not fabricate hPair for this
completion: use the accepted density-based bounded-operator owner instead.
The actionable first batch is the algebraic centralizing-increment equivalence
and the native tracial right-action bound. Neither requires inventing a new carrier.
