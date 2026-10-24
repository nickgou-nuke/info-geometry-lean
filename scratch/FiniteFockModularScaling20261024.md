# Finite Fock modular scaling — contract before implementation

New sandbox only; no builds, tests, live edits, or changes to the two AA-passed
Fock candidates. This contract authorizes no inverse or analytic-flow claim.

Imports: scratch.FiniteFockCLMReflexivePair20261024;
InfoGeometry.Canonical.RootsOfZeroUnityMoebiusModularG22;
InfoGeometry.Canonical.PeirceWeightedTrace.
Use the same native SpinorSpace(Vector n), locally activated Fock metric and
actual continuous endomorphisms D=fockIntActionCLM n i, C=fockExtActionCLM n i.
All coefficients lam,mu are arbitrary real scalars, including zero.

Source: RootsOfZeroUnityMoebiusModularG22.hyperbolicModularFlow (line243)
is lam•(D*C)+mu•(C*D)+(1-(D*C+C*D)). Frozen fock_coordinate_CLM_CAR
kills its complement. PeirceWeightedTrace.supportWeight (line60) assigns its
FIRST coefficient to C*D, so the exact identity uses supportWeight mu lam D C.
The native hyperbolicModularFlow_conj_d/B (lines286/294) need only respective
square-zero and reflexivity, supplied by the frozen interface owner.

Small separate candidate lemmas:
- operator identity with supportWeight mu lam D C;
- application on every actual spinor x = lam•D(C x)+mu•C(D x);
- flow(lam,mu)*D*flow(mu,lam)=(lam*lam)•D;
- flow(lam,mu)*C*flow(mu,lam)=(mu*mu)•C.

The last two are raw sandwiches, with NO lam*mu=1 hypothesis and no inverse
interpretation. No new carrier, pair structure, weight definition, analytic
wrapper, positivity/state assumption, or master theorem packet. The names of
native theorems containing conj do not upgrade their unconditional conclusions
to inverse conjugation. On promotion only the scratch pair import needs redirecting.
Candidate remains uncompiled until parent-controlled serial QA.
