# Scope audit of the proposed scalar mass-gap proof

`Millennium/YangMillsMassGapAudit.lean` extracts the valid scalar inequality
from the submitted `YangMillsState` without calling it a Yang-Mills theorem.
The kinetic component is assumed nonnegative and the coupling component is
assumed strictly positive. Their sum is therefore strictly positive.

The same module constructs admissible states with total squared energy smaller
than any prescribed positive number. Consequently the submitted assumptions
admit **no uniform strictly positive lower bound across all states**. This is a
formal counterexample to the proposed inference, not a claim that Yang-Mills
theory has no mass gap. A separate theorem shows how an additional common lower
bound on the coupling would imply a common scalar energy lower bound.

The submitted Lie algebra parameter is unused by `YangMillsState`. No connection,
curvature, quantum Hilbert space, Hamiltonian, spectrum, or vacuum is constructed.
The positive coupling field is a hypothesis, not a consequence of a nonzero Lie
bracket. Likewise, defining `Lambda_QCD` as `g_sq + 1` proves no renormalization
group or dimensional-transmutation statement. Repeating an assumed singlet
constraint proves no confinement theorem. These claims are not installed as
theorems in the repository.

The [official Clay problem page](https://www.claymath.org/millennium/yang-mills-the-maths-gap/)
continues to list Yang-Mills existence and mass gap as unsolved. The finite
resampling model in [FINITE_LATTICE_RESAMPLING.md](FINITE_LATTICE_RESAMPLING.md)
instead has a specific Hamiltonian and a native mathlib spectrum calculation;
its refresh gap must not be substituted for the physical claim.

Verification of the audit source and regression tests is pending the shared
build lane:

```
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Millennium.YangMillsMassGapAuditTests
```
