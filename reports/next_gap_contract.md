# Next theory gap: concrete Cuntz stage witness

## Missing closure

The repository still lacks a concrete instance of
`CompatibleCuntzRepresentation` for an actual operator algebra.  The missing
data are:

1. a target `Op` carrying a concrete binary Cuntz generator pair;
2. a `CuntzNAlgebra (N := 2) Op` witness;
3. stage maps from `Cl11InfiniteCarrier.Stage n` to `Op`;
4. a kernel-checked proof
   `stageMap (n + 1) (stageBond n x) = stageMap n x`;
5. identification of those maps with the canonical `M_{2^n}(ℂ)` tower maps;
6. transport of matrix units to Cuntz words.

## Already closed infrastructure

* `CuntzMatrixTowerInstantiation.lean` owns the complex matrix stages.
* `CuntzMatrixTraceTower.lean` owns the compatible `concreteMap` tower.
* `CuntzMatrixAlgebraicStarColimit.lean` owns the algebraic star colimit.
* `Cl11CuntzCantorChiralFramework.lean` owns representation descent.
* `Cl11BitWordCuntzCantorBridge.lean` proves UHF stage and colimit readouts
  once a compatible representation witness is supplied.
* `CuntzCantorBoundaryShift.lean` owns finite symbolic boundary shifts, but
  explicitly does not provide a Hilbert-space Cuntz representation.

## First payable theorem

Construct the concrete witness and prove its successor compatibility.  The
matrix-unit/Cuntz-word transport and colimit descent should be subsequent
theorems.  Do not add another abstract compatibility wrapper or use exhaustive
matrix tactics in place of the missing representation data.
