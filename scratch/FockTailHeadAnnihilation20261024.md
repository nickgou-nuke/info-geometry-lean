# New-head annihilation on the native Fock tail image

Uncompiled sandbox, no builds or live edits. Two separate lemmas; no new carrier,
operator structure, or assumed annihilation conclusion.

Owner/import: InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.
Native carrier: InfoGeometry.Clifford.SpinorSpace (Vector n), definitionally
CliffordAlgebra (0 : QuadraticForm ℝ (Fin n → ℝ)).
Native inclusion: fockTailMap n, the Clifford algebra map induced by vectorHeadZero n.
It inserts a NEW HEAD coordinate; it is not the last-site convention of the
separate matrix Kronecker tower.

1. contractLeft of the native coordinate projection LinearMap.proj 0 kills
   fockTailMap n ψ for every ψ. Proof: CliffordAlgebra.left_induction; scalar
   contraction is zero, addition is linear, and the generator step uses
   fockTailMap_generator, contractLeft_ι_mul and vectorHeadZero_coordinate_zero.
2. New-head number (creation after contraction) also kills that image:
   ι(0)(Pi.single 0 (1:ℝ)) * contractLeft(proj 0)(fockTailMap n ψ) = 0.
   This is an explicit action expression, not a newly defined number carrier.

Reuse sources: ClNNNeutralChevalleyBridge lines 598–645 for the actual maps;
Mathlib LinearAlgebra/CliffordAlgebra/Contraction.lean:125,168 for contraction;
Mathlib LinearAlgebra/Pi.lean:87,100 for the coordinate linear map.
Existing fockTailMap_contractLeft treats transported OLD covectors, rather than
this newly added head covector. The inspected native Fock/Clifford searches did
not find this new-head annihilation statement.

Consumer: ClNNFockDirectLimitRepresentation already owns fockStageMap,
fockDirectedSystem, FockInfinity, and tower action transport. Multiplying this
new-head number action on the left by an old represented observable still
annihilates the embedded old subspace. This supplies the finite algebraic ingredient
for compatible coupled increments, unlike trace-GNS A↦A⊗I compatibility.

Non-Hilbert boundary: fockTailIsometry is an isometry of ZERO QUADRATIC FORMS,
not a Hilbert-space isometry. These lemmas prove no norm bound, adjointness,
positive inner product, complex scalar extension, completed operator, coupled
family recursion, or spectrum statement. Those require additional proved bridges
on the existing carriers. Parent AA and serial QA remain necessary.
