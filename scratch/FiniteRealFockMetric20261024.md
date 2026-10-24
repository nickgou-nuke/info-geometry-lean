# Finite real Fock metric: batch-2 contract (source research only)

No Lean candidate or verified proof is supplied in this batch. No builds/tests,
live edits, global instances, scalar refactor, or completed complex carrier.
Batch-1 basis transport is awaiting parent QA; this contract requires its accepted
native declaration, not an assumption of naturality.

## Existing carrier, basis, and coordinate map
Use exactly InfoGeometry.Clifford.SpinorSpace
(InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.Vector n), definitionally
CliffordAlgebra (0 : QuadraticForm ℝ (Fin n → ℝ)) = ExteriorAlgebra ℝ (Fin n → ℝ).
The already existing FockStage abbreviation in ClNNFockDirectLimitRepresentation
may be reused; do not introduce a new type synonym to evade instance conflicts.

Let b n = (Pi.basisFun ℝ (Fin n)).ExteriorAlgebra, indexed by Finset (Fin n).
Define one named linear equivalence on that actual carrier:

  fockCoordinates n :=
    (b n).equivFun.trans
      (WithLp.linearEquiv 2 ℝ (Finset (Fin n) → ℝ)).symm

Its target is EuclideanSpace ℝ (Finset (Fin n)), used only to transport a metric
back to the original carrier. Ordinary Pi function norm is NOT the intended
norm; the WithLp 2 conversion is essential. No basis choice or eigenbasis is used.

## Small construction and instance boundary
Prefer named reducible non-instance definitions with local activation in a
focused owner, initially sandbox only:

1. fockNormedAddCommGroup n := NormedAddCommGroup.induced _ _
   (fockCoordinates n).toLinearMap (fockCoordinates n).injective.
2. fockInnerProductSpace n := InnerProductSpace.induced
   (fockCoordinates n).toLinearMap, aligned with that induced normed group.
   Mathlib's definition uses the induced SEMInormed parent; check its parent
   projection is definitionally the one from the injective induced normed group.
   Do not install a second competing norm to conceal an elaboration mismatch.
3. Expose norm/inner readback equalities. Inner is literally the target inner:
   inner ℝ x y = sum S, (b n).repr x S * (b n).repr y S.
   Norm squared = sum S, ((b n).repr x S)^2.
   Positive definiteness follows from the injective coordinate equivalence, not
   from the zero quadratic form. Native NormedAddCommGroup.induced proves it.
4. Prove the basis inner formula = if S=T then 1 else 0 using coordinate singles.
   An OrthonormalBasis on the SAME carrier is optional downstream packaging, not
   needed to prove the tail map isometry.

No global instance promotion is proposed before parent review of dependents.
The named structures suffice for explicit/local use and avoid surprising norm
selection on reducible CliffordAlgebra-zero carriers. Do not infer NormedRing
or a CStar structure: exterior multiplication is not shown contractive here.

## Exact tail obligation and proof route
Under these specific local structures, prove for all x,y on the old real carrier:

  inner ℝ (fockTailMap n x) (fockTailMap n y) = inner ℝ x y.

Proof on two basis vectors: use accepted fockTailMap_exteriorBasis and both basis
inner formulas. Finset.map_injective (Fin.succEmb n) identifies equality of mapped
occupancies with equality of old occupancies; no permutation sign appears.
Extend to arbitrary x,y using (b n).sum_repr twice, map_sum/map_smul and real
inner-product additivity/scalar laws. This avoids dependent complement sums or
assuming a coordinate-zero-extension formula. It also handles n=0 and vacuum.

Then define fockTailLinearIsometry n by
  (fockTailMap n).toLinearMap.isometryOfInner <proved identity>.
Require a separate rfl application lemma identifying it with the EXISTING map;
no independent bonding map. Its norm_map gives norm preservation and continuity.
The current fockTailIsometry is only a zero-quadratic isometry and cannot supply
this Hilbert assertion. Iterated fockStageMap isometry is a later small induction
using existing fockStageMap_refl / fockStageMap_succ, not a second tower.

## Grounding and nearby owners actually read
- Clifford/ChevalleySpinorBlueprint.lean:32 native SpinorSpace definition.
- Clifford/ClNNNeutralChevalleyBridge.lean:598–645 actual zero-head map, quadratic
  isometry, Clifford-algebra map, generator transport.
- Clifford/ClNNFockDirectLimitRepresentation.lean:30–74 actual FockStage and
  Nat.leRecOn bonding maps; file explicitly supplies algebraic colimit only.
- Canonical/FockCARTopologicalBridge.lean:23–49 assumes a real Hilbert E and acts
  on DoubledSpace E. It does not construct this exterior metric.
- Canonical/RealCl55FiniteModuleEndBridge.lean:40–47 defines finite function and
  Euclidean Fin32 carriers. RealCl55NativeSpinorGroupActionBridge explicitly
  disclaims a particular matrix-basis identification with the Chevalley carrier.
- Canonical/HodgeCohomologyTopologicalEquiv.lean:30–49 takes inner, positivity,
  adjointness and inverse continuity as parameters; not a constructed Fock metric.
- Canonical/FilteredIsometricInnerProductColimit.lean:25–39 assumes complex
  stage inner-product spaces and complex-linear isometries. It does not yet
  accept this real-stage tower directly.

Search scope: filename inventory of Fock/Spinor/ClNN/Exterior/FilteredIsometric
owners; metric/norm/Euclidean/orthonormal signatures across those paths; wider
SpinorSpace/CliffordAlgebra-zero/ExteriorAlgebra metric cross-search. No all-n
metric on this exact native carrier was located in that search. This is not a
claim that all other spinor metrics or conditional Hodge metrics are absent.

## Exact Mathlib implementation APIs read
- LinearAlgebra/ExteriorAlgebra/Basis.lean:30–41 actual exterior basis.
- LinearAlgebra/Basis/Defs.lean:259 Basis.sum_repr; :316 Basis.ext.
- Analysis/InnerProductSpace/PiL2.lean:606 demonstrates the exact
  Basis.equivFun.trans (WithLp.linearEquiv ...).symm coordinate equivalence;
  EuclideanSpace supplies finite l2 norm/inner, not a new spinor carrier.
- Analysis/Normed/Group/Basic.lean:687–728 induced seminorm/norm constructions;
  additive APIs are generated by to_additive, including NormedAddCommGroup.induced.
- Analysis/InnerProductSpace/Basic.lean:893–906 InnerProductSpace.induced and
  inner_induced_eq; actual norm is read from the induced group.
- Analysis/InnerProductSpace/LinearMap.lean:126–147 isometryOfInner and exact
  underlying-map readbacks for linear maps/equivalences.
- Data/Finset/Image.lean:162 Finset.map_injective.
- Analysis/InnerProductSpace/ExteriorPower.lean:49–117 already constructs a real
  metric on each degree under finite-dimensional inner-product assumptions.
  Reuse for later degree-compatibility if useful; it does not by itself install
  the full exterior-Fock direct-sum metric on our exact carrier. Avoid importing
  it merely to assume the desired full-space structure.

## Minimal scope / follow-up
First implementation batch should stop at induced structures, basis inner formula,
and actual tail linear isometry. Finite-dimensional completeness can follow from
native finite-dimensional normed-space APIs; it is not asserted proved here.
Creation/contraction adjointness and norm bounds require signed basis-action
lemmas and remain separate obligations. No chosen real-generalization versus
complexification route, no complex completion, no coupled-family or Dirac claim.
