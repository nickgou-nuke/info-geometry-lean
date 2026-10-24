# Actual multi-mode completed CAR and birth-stage coherence

New helper RealFockModeCoherence20261024.lean; new consumer
RealFockCompletedMultiModeCAR20261024.lean. No builds/live edits. Intended native
imports: RealFockCoordinateTransport and pending RealFockCompletedSameModeCAR
(which supplies only the common-stage representative helper needed here).
No alternate index/mode carrier, finite representation, action, or colimit.

Helper proves injectivity and composition of the EXISTING fockModeShift via
Nat.le_induction and its accepted successor equation. A common-stage equality
of two modes is preserved/reflected by further shifts. Comparing two different
common upper stages reduces to max of those stages via composition/injectivity.

Finite input owners: Clifford/FockSpaceCAR.lean creation_anticommute:84 and
annihilation_anticommute:117, identified with native SpinorSpace actions by
creation_apply/annihilation_apply and fockExteriorEquiv_zero_apply/symm_apply.
ChevalleySpinorBlueprint.ext_int_anticommutator:50 supplies the mixed law;
coordinate evaluation is Pi.basisFun versus LinearMap.proj. Expose only short
readbacks for the existing finite CLMs, not another finite CAR construction.

Consumer proves same-birth completed cross relations for all i,j:Fin m:
C_i*C_j+C_j*C_i=0; D_i*D_j+D_j*D_i=0;
D_i*C_j+C_j*D_i=if i=j then 1 else 0.
Use all-later-stage readbacks, shift injectivity, finite laws, and closed-equality
Completion.induction_on on actual completed operators. Do not reprove same-mode
square-zero or adjoints. The case i=j is permitted but no duplicate same-mode
owner/structure is introduced.

Prove C(m,i)=C(n,shift m n h i), and likewise D, from equality of their actual
Clifford colimit elements (splitCliffordMap_creation/contraction and Algebra.of_f),
the original action application, then completion density. These are operator
coherence equalities, not assumed transport fields.

Different-birth statements for i:Fin m,j:Fin n and ANY common upper k with
hm:m<=k, hn:n<=k:
C(m,i)C(n,j)+C(n,j)C(m,i)=0 and analogously D;
D(m,i)C(n,j)+C(n,j)D(m,i)=
  if shift m k hm i = shift n k hn j then 1 else 0.
Derive by operator coherence and same-birth laws. Helper's comparison theorem
proves the test is independent of the common upper stage. No raw-index equality
across birth stages, or fixed-head substitution. Candidate is source-only and
requires independent AA/QA for all pending imports and newly written proofs.
