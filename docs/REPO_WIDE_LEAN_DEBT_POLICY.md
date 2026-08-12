# Repository-wide Lean debt policy

The debt boundary is the whole repository, not `Canonical/` and not only the
Lake package. `tools/quality/repo_lean_scope_audit.py --fail-on tracked` scans
every tracked `.lean` file in every subdirectory.

Files that are recovered snapshots, scratch experiments, or deliberately
failing lint fixtures are not proof owners. They must not remain executable
Lean sources containing `sorry`, `admit`, or `axiom`: preserve them as
`.lean.disabled` quarantine artifacts instead. Quarantine is explicit and
reviewable; it is not a proof, and its contents remain a hard release debt.

The active-source gate is therefore strict:

```text
python3 tools/quality/repo_lean_scope_audit.py --fail-on tracked
python3 tools/quality/repo_lean_quarantine_audit.py --fail-on-findings
```

The contents of disabled artifacts remain auditable with:

```text
rg -n --glob '*.lean.disabled' '\b(sorry|admit|axiom)\b' .
```

No claim of kernel verification may be made for a quarantined artifact. A
quarantined file can re-enter active scope only after its debt is removed and
its smallest relevant `lake env lean` check passes; until then the repository
wide release gate remains red.
