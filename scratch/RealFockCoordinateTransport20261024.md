# Fixed-coordinate transport through the actual split Clifford tower

New source RealFockCoordinateTransport20261024.lean only. No builds/live edits.
Use native ClNNFockDirectLimitRepresentation, FockTailExteriorBasis and
FiniteRealFockNormBounds. No dependency on unaccepted completion code is needed.

Prove dualTailMap_proj by extensionality on the existing covector LinearMap.
Define only the finite index shift (Nat.leRecOn, Fin.succ at every successor)
and two coordinate elements of existing SplitClNNAlg: iota(neutralToSplit
(basis_i,0)) and iota(neutralToSplit(0,proj_i)). No new action or colimit.

Derive successor transport of these actual algebra elements using native
splitCliffordStep_eq_splitStageCliffordMap, CliffordAlgebra.map_apply_iota,
neutralToSplit_tail, vectorHeadZero_basisFun and dualTailMap_proj. Induction on
the actual splitCliffordMap proves all-index coordinate transport. Apply native
towerSpinorRep_generator to obtain equality with fockExtActionCLM/intActionCLM
on EVERY later-stage vector, not just vectors in the birth-stage image.
The native pointwise finite estimates then give the two all-later-stage bounds.

Consume existing towerSpinorRep_stageMap to expose the corresponding Fock
intertwining formulas; do not reprove its algebraic colimit construction. No
completed operator, global action, or replacement compatible-family fields here.
Keep separate small lemmas for the two coordinate modes and no conclusion bundle.
Source-only candidate awaiting AA/QA; no budget/transparency modifications.
