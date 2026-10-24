# Density consumer v6: explicit native scalar-result and unit-inverse types

NEW sandbox consumer only. Frozen v5 and all native owners unchanged. Import
accepted native InfoGeometry.Canonical.FiniteMappedGibbsDensityExponential.
Exact diagnostic: /tmp/qa-a-density-v5-sq30ebk7/compile.log.

V5 progressed past the primitive structure selections. Its statement failed
synthesizing HSMul real SeedClosure ?m at line67 (200k whnf), and interpreted the
inverse boundary as requiring Inv SeedClosure at line74. No proof acceptance
for the concrete statements is inferred from that progress.

V6 keeps the same fixed-parameter section, exact represented closure, native
CStarAlgebra/superclass projections, density unit, seedStageHom and all-beta
hypotheses. It only supplies missing expected types:
- Annotate the actual seedStageHom H hH beta H value as SeedClosure.
- Annotate each real scalar product's result as SeedClosure BEFORE exp.
- Invert (representedDensityUnit H hH beta : SeedClosure units), THEN explicitly
  coerce the inverse to SeedClosure. No inverse operation on the closure ring
  is requested or constructed.
- Supply A:=SeedClosure to the two accepted generic helper applications.

No separate generator/map/density definition, scalar-action instance, alternate
carrier, norm, topology, assumption, budget or transparency change. Mathematical
claims remain density=exp(-beta Himage) and unit inverse=exp(+beta Himage), for
all real beta and Hermitian H. No normalized-density or analytic KMS claim.
No builds/live edits; source-only proposal awaiting independent AA and QA.
