# Idempotents in a real scalar–bivector plane

The negative owner `Clifford/BivectorProjectorCorrection.lean` proves that
`1 ± unitBivector` does not satisfy the scaled projector equation, while
the vector-square-one construction does. Its actual carrier is the definite
three-dimensional Clifford algebra, and `unitBivector_sq` supplies `J*J=-1`.

`Clifford/BivectorPlaneIdempotents.lean` proves the complete classification:
in a nontrivial real algebra, `a • 1 + b • J` is idempotent iff
`(a,b)=(0,0)` or `(a,b)=(1,0)`. The theorem uses Mathlib's `Complex.lift`
and injectivity of its algebra homomorphism from a field. Thus the scalar
calculation is transported through an explicit faithful map into the actual
ambient algebra. No centrality of J or commutativity of that algebra is
assumed, and no classification outside this plane is claimed.

The native Clifford specialization includes the normalized half-projector
obstruction. The companion audit includes zero/one witnesses, the negative
half-projector, and five axiom requests including existing negative and
positive owners. Maintained searches for Complex.lift and bivector projector
criteria found the existing central scalar-extension owner but no equivalent
classification in the inspected results. Centrality is required there to
make the whole ambient algebra a complex algebra, not for this embedding.

Independent semantic AA passed and strict screening found zero traps.
Parent locked verification passed on 2026-10-24: session 60716,
`/tmp/bivector-plane-audit.log`, 3,131 jobs, exit code 0. All five axiom
requests report only `propext`, `Classical.choice`, and `Quot.sound`.
The audit also checks three concrete positive/negative specializations.
Independent QA accepted the combined audit in session 10916:
`/tmp/chiral-bivector-graph-final-qa.log`, 8,941 jobs, exit 0. This batch
contributes five standard-axiom reports and three passing examples.
There were zero own-source warnings; six-source strict screening found zero traps.
