# KK / Analytical Index Bridge Note

This note is a frontier-planning file, not a current owner map.

Its job is to record the present state of the KK/index corridor and keep it
honest relative to the rest of the repository.

## Current live KK surface

The live adjacent file is:

- `lean/InfoGeometry/KK/ClNNFredholmBridge.lean`

This file is real, but thin. It gives a first-step bridge from split
`Cl(1,1)`-style generators into an existing bounded split-Krein Kasparov-cycle
surface. It does not currently define or compute a native analytic Fredholm
index coming from the corrected phase-space owner lane.

## What the corridor does not yet have

The repo does not currently have all of the following as one adjacent packet:

- a corrected-owner to KK-cycle bridge;
- a native Fredholm operator extracted from the corrected phase-space /
  doubled / chirality lane;
- a proved analytic index object for that operator; or
- a theorem welding projector obstruction or chiral anomaly to that index.

Because of that, KK/index remains a frontier extension, not the nearest closure
path.

## Current recommendation

Do not treat KK/index as the next mandatory branch closure.

The current shortest closure work is still:

1. derive the realized-projector to maintained tomita-projector identification;
2. derive projector obstruction from trunk-compatible operator data;
3. close the Weyl branch through that operator theorem; and
4. attach the count/projective trunk at polarization.

Only after those steps should the KK/index anomaly weld move to the front.

## What would be needed for a real index-anomaly bridge

The minimal route now looks like this:

1. corrected owner -> doubled / chirality operator package;
2. doubled / chirality package -> KK cycle or Fredholm package;
3. native analytic index for that Fredholm package;
4. operator-level bridge from projector obstruction / anomaly to the index.

Without those four pieces, any index-anomaly statement is still architectural
planning.

## Status label

Use the following reading:

- current status: thin live frontier
- not current status: closed corridor or active semantic root

If this note needs updating later, it should cite current Lean files first and
only then candidate theorem names.
