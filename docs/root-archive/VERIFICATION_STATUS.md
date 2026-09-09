# Multi-Engine Verification Status Report

## Date: 2026-06-23

## Verified Engines

1. Lean4: PASSED
2. SymPy: PASSED
3. SageMath: PASSED
4. Coq/Rocq: PASSED
5. GAP: PASSED
6. Macaulay2: PASSED

## Isabelle/HOL

Status: INSTALLED, but current authored theory does not build.

What I verified:
- Isabelle executable exists at /home/goutev/Isabelle2025-2/bin/isabelle
- I was able to invoke the build system
- Initial failure: imported unavailable theories HOL-Algebra.Matrix and HOL-Algebra.Ring_Hom
- After removing those imports, the current theory still fails parsing as authored

Honest status:
- Isabelle is installed
- Isabelle theory is not yet verified
- Current file needs repair before build can pass

## Not verified yet

- Isabelle/HOL theory build
- galgebra script execution

## Passed artifacts

- /tmp/sympy_bridge_verification.json
- /tmp/sage_aql_instance.json
- /tmp/gap_g2_su3_results.json
- /tmp/macaulay2_tripotent_results.json

## Conclusion

The following engines have been actually run successfully:
- Lean4
- SymPy
- SageMath
- Coq/Rocq
- GAP
- Macaulay2

Isabelle is installed but not yet passing.
