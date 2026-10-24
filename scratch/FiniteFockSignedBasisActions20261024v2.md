# Signed finite Fock basis actions v2 — coercion/API repair

Log read: /tmp/qa-a-fock-signed-basis-qa_4_1wm/compile.log.
No builds/tests/live edits; uncompiled new files. V1 preserved.

Creation insert: change the extAction application to its native generator-product
before using the basis theorem; bind the same powersetCard singleton/set and
prove the disjUnion Finset equals insert explicitly. Rewrite this equality at
the basis multiplication theorem, preserving the same permOfDisjoint sign.
Creation occupied-zero: explicitly expose the generator product on the actual
SpinorSpace before simplification, avoiding unresolved bundled linear-map coercion.
Replace unavailable Finset.not_mem_erase by native Finset.notMem_erase.
Remove the two QA-reported unused simp arguments Pi.single_apply and Ne.symm hne.
Contraction word recursion and sign derivation by native CAR are unchanged.

Same extAction/intAction, exact exterior basis, actual permutation sign, all n;
no new hypotheses, replacement carrier, metric, sign-count assertion, adjointness,
budgets or linter suppression. Independent QA must validate the repaired coercions.
Motion diagnostic probe is separate and unchanged.
