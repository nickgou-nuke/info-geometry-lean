import Lean
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Meta.SocketTarget

Macro infrastructure for socket-debt tracking.

A **socket** is a deferred witness-gated interface: a structure carrying
`law : Prop` + `certificate : law` fields where the `Prop` is opaque.
This is architecturally legitimate scaffolding (the finite-only boundary
does not have the analytic content to fill the socket), but it bypasses
normal `sorry` detection because the law itself is a parameter.

This module provides:

- `@[socket_debt_tag]` — tag attribute marking structures as explicit
  socket debt.
- `#audit_socket_debt` — command enumerating all tagged socket surfaces
  and reporting the total debt count.

## Design Principles

1. Sockets are not bugs — they are the typed interface for content that
   requires analytic machinery not yet available (measure-theory towers,
   infinite-product convergence, etc.).
2. The debt must be **machine-visible**, not hidden inside opaque `Prop`
   parameters that look clean to `sorry_analyzer.py`.
3. Tagging a structure `@[socket_debt_tag]` is a declaration of honest
   closure debt — the architectural equivalent of a typed `sorry`.

This directly encodes the "thinness debt" documented in Black Book
Chapter 59 (Decalogue of Functorial Necessity) as compiler-tracked
structure.
-/

open Lean Elab Command

namespace InfoGeometry.Meta

/-- Tag attribute marking structures as socket-level closure debt. -/
initialize socketDebtTagAttr : TagAttribute ←
  registerTagAttribute `socket_debt_tag
    "Mark a structure as witness-gated socket debt for architecture auditing."

/--
Audit all socket-debt declarations in the current environment.

Unlike `#audit_owner_targets` and `#audit_bridge_targets`, this audit does
not check for `sorry` — sockets are *expected* to carry opaque laws.
Instead it reports the total debt surface so the architecture overlay can
track how much deferred content remains.
-/
def checkSocketDebt : CoreM Unit := do
  let env ← getEnv
  let mut total := 0
  let mut names : Array Name := #[]
  for (declName, _) in env.constants do
    if socketDebtTagAttr.hasTag env declName then
      total := total + 1
      names := names.push declName
  if total == 0 then
    logInfo m!"Socket Debt Audit: 0 tagged socket structures found."
  else
    for n in names do
      logInfo m!"SOCKET DEBT: {n}"
    logInfo m!"Socket Debt Audit: {total} tagged socket structure(s) — each represents deferred analytic content."

/-- Command entrypoint for the socket-debt audit. -/
elab "#audit_socket_debt" : command => do
  Command.liftCoreM checkSocketDebt

end InfoGeometry.Meta
