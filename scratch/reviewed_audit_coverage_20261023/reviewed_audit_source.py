"""Unexecuted candidate for target validation and complete reviewed-owner coverage.

This generates Lean source; Python validation does not establish Lean behavior.
Supported module paths use ASCII identifier components, including Lean keywords
via quoted identifiers. Unicode/otherwise quoted paths are deliberately rejected.
"""
from __future__ import annotations

import re
import hashlib
from pathlib import Path
from types import MappingProxyType


_MODULE_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")


def validate_targets(targets: object) -> list[str]:
    """Return an ordered copy; reject malformed input before path/source use."""
    if not isinstance(targets, (list, tuple)) or not targets:
        raise ValueError("Reviewed targets must be a nonempty list or tuple")
    result: list[str] = []
    seen: set[str] = set()
    for target in targets:
        if not isinstance(target, str) or _MODULE_NAME.fullmatch(target) is None:
            raise ValueError(f"Invalid reviewed module name: {target!r}")
        if target in seen:
            raise ValueError(f"Duplicate reviewed module: {target}")
        seen.add(target)
        result.append(target)
    return result



# Exact source-reviewed roles, never inferred from an Audit suffix. Values are
# immutable tuples of selected declaration owners printed by these commands.
COMMAND_ONLY_OWNERS = MappingProxyType({'InfoGeometry.Algebra.CuntzClifford22Audit': ('InfoGeometry.Algebra.CuntzClifford22', 'InfoGeometry.Algebra.CuntzClockObstructions'), 'InfoGeometry.Krein.TransitionWeakValueAudit': ('InfoGeometry.Krein.TransitionWeakValue', 'InfoGeometry.Canonical.WeakValuePoleBounds', 'InfoGeometry.Krein.TransitionWeakValueExamples')})
# Freeze the inspected command sources: edits require explicit role re-review.
COMMAND_SOURCE_SHA256 = MappingProxyType({'InfoGeometry.Algebra.CuntzClifford22Audit': '8556be391ef1a69dd5376a1e452be29b5287e3fb1c63778b6c9d3a083d00f289', 'InfoGeometry.Krein.TransitionWeakValueAudit': '8316ce42dfbc8233756b763963c765393ecfca0feeb6000f69f30697b5da1c6c'})


def validate_roles(targets: object, command_only: object = None) -> tuple[str, ...]:
    selected = validate_targets(targets)
    expected = tuple(m for m in selected if m in COMMAND_ONLY_OWNERS)
    if command_only is None:
        roles = expected
    else:
        if not isinstance(command_only, (list, tuple)):
            raise ValueError("Command-only roles must be a list or tuple")
        roles = tuple(validate_targets(command_only)) if command_only else ()
        for module in roles:
            if module not in COMMAND_ONLY_OWNERS:
                raise ValueError(f"Unknown command-only role: {module}")
            if module not in selected:
                raise ValueError(f"Nonselected command-only role: {module}")
        if set(roles) != set(expected):
            raise ValueError("Selected command-only role mapping is incomplete")
    for module in roles:
        for owner in COMMAND_ONLY_OWNERS[module]:
            if owner not in selected or owner in roles:
                raise ValueError(f"Command-only dependency needs selected owner auditing: {owner}")
    return expected


def check_command_sources(source_root: Path, targets: object, command_only=None) -> None:
    """Check both live and copied sources using this function before/after work."""
    for module in validate_roles(targets, command_only):
        path = source_root / (module.replace('.', '/') + '.lean')
        if hashlib.sha256(path.read_bytes()).hexdigest() != COMMAND_SOURCE_SHA256[module]:
            raise ValueError(f"Command-only source changed; role review required: {module}")


def may_reuse_cache(module: str, targets: object, command_only=None) -> bool:
    """Apply in the closure compilation loop, before reading cache metadata."""
    validate_targets([module])
    return module not in validate_roles(targets, command_only)


def _lean_module_name(module: str) -> str:
    # Called only after validation: no delimiter, newline or path escape can
    # reach this function through audit_source. Quoting permits keyword parts.
    return ".".join(f"«{part}»" for part in module.split("."))


def audit_source(targets: object, command_only: object = None) -> str:
    targets = validate_targets(targets)
    roles = validate_roles(targets, command_only)
    role_names = ", ".join("`" + _lean_module_name(m) for m in roles)
    names = [_lean_module_name(module) for module in targets]
    imports = "\n".join("import " + module for module in names)
    module_names = ", ".join("`" + module for module in names)
    return imports + '\nimport Lean.Util.CollectAxioms\nimport Lean.Elab.Command\n\nopen Lean Elab Command\n\n' + f'''run_cmd do
  let env ← getEnv
  let targets : Array Name := #[{module_names}]
  let commandOnly : Array Name := #[{role_names}]
  for target in targets do
    unless env.header.moduleNames.contains target do
      throwError "Selected module not imported: {{target}}"
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count := 0
  let mut ownerCounts : NameMap Nat := {{}}
  let mut allAxioms : Array Name := #[]
  for (name, info) in env.constants do
    let some idx := env.getModuleIdxFor? name | continue
    let owner := env.header.moduleNames[idx.toNat]!
    if !targets.contains owner then continue
    if info.isUnsafe || info.isPartial then
      throwError "Unsafe or partial declaration in reviewed module: {{name}}"
    -- Public API handles imported axiom metadata and private-body lookup.
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Disallowed axiom {{ax}} in {{name}}"
      if !allAxioms.contains ax then
        allAxioms := allAxioms.push ax
    count := count + 1
    ownerCounts := ownerCounts.insert owner ((ownerCounts.find? owner).getD 0 + 1)
    logInfo m!"AUDIT_DECL: {{owner}}: {{name}}"
  for target in targets do
    let moduleCount := (ownerCounts.find? target).getD 0
    logInfo m!"AUDIT_MODULE_COUNT: {{target}}: {{moduleCount}}"
    if commandOnly.contains target then
      if moduleCount != 0 then
        throwError "Command-only module owns declarations: {{target}}"
      logInfo m!"AUDIT_COMMAND_MODULE: {{target}}"
    else
      if moduleCount == 0 then
        throwError "No declarations audited in reviewed module: {{target}}"
      logInfo m!"AUDIT_MODULE: {{target}}"
  if count == 0 then throwError "No declarations audited"
  logInfo m!"AUDIT_AXIOMS: {{allAxioms.qsort Name.lt}}"
  logInfo m!"AUDIT_COUNT: {{count}}"
'''
