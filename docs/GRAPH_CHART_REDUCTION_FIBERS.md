# Graph-chart reduction fibers

The existing negative owner is
`SuperGrassmannian/GraphChartOddRegression.reduction_not_injective`:
distinct homogeneous submodules over the genuine exterior algebra reduce
to the same submodule under augmentation.

The replacement uses `GraphChartBaseChange.extend`, the target-module span
of the coefficientwise image. `extend_graph` identifies it with the graph
of the mapped coefficients; `GradedGraphChart.graph_injective` recovers the
linear map from its graph. Evaluation on standard basis vectors recovers
each coefficient, with multiplication on the right for left modules.

`GraphChartReductionFibers.lean` proves five results:

- coefficient arrays inject into their coordinate linear maps;
- equality of extended graphs iff equality of all mapped coefficients;
- equivalently, every coefficient difference maps to zero;
- for nonempty source and target frames, extension on all graph arrays is
  injective iff the coefficient ring homomorphism is injective;
- the kernel criterion holds for actual homogeneous chart submodules through
  the existing `coefficientChartEquiv`.

No surjectivity, commutativity of the coefficient rings, or target grading
is assumed. The ungraded injectivity criterion is not promoted to graded
charts: only permitted homogeneous coefficient spaces are visible there.
Maintained source searches and owner/dependent inspection found transport
and chart uniqueness results but no exact fiber criterion in those results.

The audit uses an identity map on a matrix coefficient ring and the native
exterior augmentation, covering both equality and noninjectivity. It requests
six axiom reports, including the original counterexample.

Independent semantic AA and strict screening passed. Parent owner build
completed with exit 0 (1404 jobs), session 24157,
`/tmp/graph-chart-fibers-build.log`. Parent audit session 8304 completed with
exit 0 (1853 jobs), `/tmp/graph-chart-fibers-audit.log`. All three examples
passed; six axiom reports contain only `propext`, `Classical.choice`, and
`Quot.sound`. There were no source warnings and two existing package notices.
Scoped staged diff checks passed. Independent kernel QA accepted the combined
audit in session 10916, `/tmp/chiral-bivector-graph-final-qa.log`: 8,941 jobs,
exit 0. This batch contributes six standard-axiom reports and three passing
examples. The combined run had zero own-source warnings, five dependency
warnings, and two package notices; six-source strict screening found zero traps.
No topology, continuum, or physical conclusion is asserted.
