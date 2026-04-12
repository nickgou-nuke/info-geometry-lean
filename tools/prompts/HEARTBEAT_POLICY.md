# Heartbeat Policy Contract

Effective date: **2026-04-12**

Heartbeat is allowed for proof orchestration, not for autonomous public action.

## Allowed Planes

- Heartbeat may run only in `prove` or `orchestrate` planes.
- Heartbeat is forbidden in `publish` plane.

## Required Behavior

- On policy rejection, heartbeat cycles must emit a typed blocker and stop escalation.
- All outbound writes require publish gate approval.

## Blocker Types

- `policy_rejection`
- `proof_failure`
- `permission_denied`
