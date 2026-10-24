# Finite real Fock metric v2 — focused elaboration repair

Diagnostic read: /tmp/qa-a-real-fock-metric-y7mqox3s/compile.log.
The parent reports dependencies passed stably. The candidate failed at the
conditional equality rewrite and at the last basis-sum simp; one unused simp
argument was reported. No builds/tests/live edits were performed for this revision.

Changes only:
1. Remove unused eq_comm from the basis inner formula.
2. Replace rw of Finset.map_injective.eq_iff under ite by simp only, which uses
   conditional congruence and handles the dependent Decidable arguments.
3. In the finite-basis sum proof, explicitly unfold local b and combine map/inner
   sum normalization with fockTailMap_inner_basis in one simp only call. This
   avoids a subsequent simp_rw requiring progress and exposes the literal basis
   to the native transport lemma. The finite expansion argument is unchanged.

All definitions and theorem statements are unchanged. Actual real SpinorSpace,
exact exterior basis, induced named norm/inner structures with LOCAL instances,
and native fockTailMap linear isometry; no metric assumption, alternate carrier,
scalar generalization, completed carrier, coupled family, budget or linter change.
V1 and its research/implementation contracts are preserved. This v2 is uncompiled
and requires independent QA. Motion v10 is a separate candidate and contract.
