# Enforcement Rules (non-negotiable addenda)

These rules encode concrete failure modes observed in this repository. They do
not modify the immutable goal contract in `../SKILL.md`; they operationalize it.

## 1. Basis-aligned CAS certificates

A CAS certificate (GAP/Sage/SymPy/Singular) certifies Lean content only if it
was computed against the exact matrices/functions defined in the Lean owner
file. GAP `Pcgs`/`SylowSubgroup` generators, atlas-representative groups, or
any re-basing are different presentations and certify nothing.

**Incident:** the Sylow-2 commutator table of `U₆ ⊂ G₂(2)` was first computed
against GAP's arbitrary `Pcgs` basis and appeared to refute a drafted table;
re-computation against Lean's own `pc1Fun..pc6Fun` confirmed the refutation
independently — but had the bases disagreed, the GAP result would have been
void. Always dump the Lean definitions verbatim into the CAS and re-verify.

## 2. No fictional presentations

Compiling cleanly against an alternative presentation (different multiplication
table, different generator orders, involutivity assumptions) does not prove
theorems about the target object.

**Incident:** a `mulGen` collection table assumed all six unipotent generators
were involutions; the carrier proves `e₁² = e₂² = e₅` (orders 4, 4). Every
theorem built on that table certified a fictional group of order 64 while the
kernel reported zero errors.

## 3. Vacuous interfaces are dead code

A structure bundling hypotheses (e.g., an action system requiring involution
laws) with no constructed inhabitant in the repository certifies nothing.
Either construct the instance from verified data or remove the interface.

**Incident:** `G2ActionSystem` carried a false `e_inv : ∀ i, perm_e i² = 1`
axiom-field and had no instance anywhere in the repository — all its "verified"
theorems were conditional on an uninhabited structure.

## 4. Concurrent-agent walking

Other agents edit this repository concurrently. Before editing, check file
mtimes for recency; after any external clobber, re-audit rather than
blind-restore. Never commit a mid-flight foreign state; never build while files
under verification are being written. Watch for quiescence (no writes for
several minutes) before verification runs or commits.

**Incident:** a bridge file was deleted twice by a concurrent agent mid-edit,
and a torn half-written file once produced a phantom parse error.

## 5. Single representative search

When a witness requires a specific representative (e.g., `u * w` inside a
coset `U * w`), brute-force the coset representatives and verify side
conditions (Levi identities, complement closure) explicitly.

**Incident:** the rank-1 identity `s·x_α·s = x_α·s·x_α` held for exactly 2 of
the 32 representatives of `U·w_α` — the raw reflection failed it.

## 6. Char-2 tactic discipline

Over `ZMod 2`, `ring` does not know `2 = 0`. Prefer full coordinate case
analysis with `rcases v 0 with _|_` patterns followed by `decide`/`simp`, or
certified normalizations. Notes:

- `fin_cases` accepts only free local variables, not applications (`fin_cases v 0`
  is a syntax error); case-split the function first via `rcases`.
- Run `fin_cases k` BEFORE value-level `rcases`, otherwise the match on `k`
  never reduces.
- Import `Mathlib.Tactic.Ring` explicitly when using `ring`; missing imports
  surface as confusing "unknown tactic" / parse errors.

## 7. Certificate artifacts

Store every CAS certificate under `scripts/` (deterministic, re-runnable) or
`scratch/` (investigative), with exact input, output, convention, and scope in
the header comment. Reference the artifact path from the Lean module docstring
that consumes it.
