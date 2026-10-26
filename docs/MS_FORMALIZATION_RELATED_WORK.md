# Related-work boundary for the mass-spectrometry formalization

Checked 2026-10-26. This note separates retrieved primary-source statements,
repository evidence, and unverified references supplied in discussion. It adds
no external formalization as a dependency and makes no novelty/priority claim.

## Assembly Theory

The January 2026 report *A Machine-Checked Formalization of Assembly Theory in
Lean 4* (Apoth3osis R&D; ResearchGate also lists Richard Goodman) describes an
assembly-space core, a syntax-tree model and a partial molecular interpretation.
Its assembly-index/count equality is scoped to the syntax-tree model. Section 5
explicitly excludes mass-spectrometry inference and empirical threshold validation.
The longer quotation circulated in discussion is a paraphrase, not a verbatim
quotation from that section.

Primary report:
https://www.researchgate.net/publication/399734444_A_Machine-Checked_Formalization_of_Assembly_Theory_in_Lean_4
Report DOI: 10.13140/RG.2.2.22785.52320.
The report names https://github.com/Abraxas1010/assembly-theory-lean ; that repository
returned 404 to the connector during this inspection. The report's declaration
counts and build claims have not been independently reproduced here.

PR #221 supplies conditional experimental-observation and identification contracts;
#223 adds finite ranked fragmentation dynamics. They address some concerns excluded
by the report but do not yet map Assembly Theory objects, joins, or indices to the
molecular graph/fragmentation/readout types here. No chemically validated end-to-end
assembly-index estimator, biosignature threshold or statistical noise model follows.
A formal interoperability theorem would require a specified representation map and
proofs of preservation of its intended semantics.

## STIG reference: not yet verified

The supplied record https://zenodo.org/records/22070682 and DOI
10.5281/zenodo.22070682 could not be retrieved through the available web interfaces.
Exact-title/DOI searches did not verify the supplied title, authors, date, version,
module count or numerical constants. This is an access/verification limitation,
not a proof of nonexistence. No cited STIG theorem, numerical bound or BibTeX metadata
is adopted by this PR pending access to a primary source and its actual code.

A large sufficient worst-case sample bound that does not certify a particular
cohort is not logically the same as an inconsistent carrier. The former can be a
valid but uninformative theorem; the latter has no inhabitants under its stated
hypotheses. `no_normalized_strict_grammar` concerns the latter, with a nonempty finite
strict DAG. The absorbing completion repairs that model without altering the DAG.

## Distinctions for correlation-based formalization

The signature Gram O*O is the operator correlation of a specified linear readout.
It is not automatically an empirical covariance matrix; its MP inverse is not an
identified population precision matrix. Finite kernel/range and Fredholm-style
compatibility results do not establish statistical support recovery, sample
complexity, confidence intervals, Marchenko-Pastur limits or persistent topology.
Those need a probability law, sampling procedure, estimator, hypotheses and a
separate consistency/error theorem.

Rectangular capacity-limited matching is a feasible-plan model with explicit slack.
It is not yet an unbalanced optimal-transport optimizer or a Sinkhorn algorithm:
a cost, penalties, optimizer and convergence/refinement result remain separate.

The m/z/neutral-mass conversion contract in #221 records charge and offsets but
reuses real numbers and Peak; it is not complete dimensionally distinct type safety.

Nilpotence/dynamics belong to #223. The new #225 candidate adds Drazin, observable
Gram kernels, actual finite closed-range MP supports and doubled cyclotomic actions.
Its own successful build and axiom audit, not verification of a parent PR, are the
acceptance requirements. None of these layers establishes the complete physical
inference pipeline on its own.

The repository reports public visibility through GitHub metadata. Absence from a
particular search answer is not evidence that the repository is private, nor enough
to determine why a search engine omitted it. The literature is not asserted to have
exactly two paradigms. Unverified agent-tool references likewise do not establish
proof-carrying data translations or a Lean refinement theorem.
