# Private Reviewer Chat Blueprint

This is a future infrastructure blueprint for exposing a private chat surface
to invited reviewers and collaborators so they can interrogate theory with
agents in a controlled Socratic workflow.

It is a design target, not a statement of already-deployed production service.

## Goals

- Provide invite-only browser chat access for external reviewers.
- Route all model/tool calls through existing repo governance and policy gates.
- Preserve full auditability: transcript, tool trace, artifacts, and replay
  metadata per session.
- Keep the first version simple: text-first chat, optional attachments, no
  mandatory voice stack.

## Non-goals (MVP)

- Public anonymous chat.
- Arbitrary shell/tool execution by reviewers.
- Multi-tenant SaaS billing or open self-service signup.
- Real-time collaborative whiteboard editing.

## Core Architecture

### 1) Client Surface

- Web app with room-based chat UI.
- Room types:
  - `Socratic Review` (Q/A and challenge loop).
  - `Proof Audit` (theorem-focused interrogation with citations).
  - `Design Review` (architecture and workflow review).
- Message rendering supports:
  - markdown
  - code/Lean blocks
  - diagram attachments (image or Mermaid source)

### 2) Identity and Access

- Invite-only account creation (email invite token + password).
- Optional second factor for maintainers and admin roles.
- Role model:
  - `owner`: workspace administration, policy edits.
  - `maintainer`: room setup, participant management.
  - `reviewer`: chat and attachments inside allowed rooms.
  - `observer`: read-only transcript access.
- Per-room ACLs with explicit allowlists.

### 3) Chat/API Service

- Stateless API service for auth, rooms, messages, and session lifecycle.
- Realtime transport via WebSocket (or SSE fallback).
- Idempotent message submit API with server-side sequencing.
- Explicit `review_session_id` for deterministic audit trails.

### 4) Agent Gateway

- A dedicated gateway service sits between chat API and model/tool execution.
- Responsibilities:
  - enforce policy by room type and user role
  - map user intents to approved prompt templates
  - perform tool allow/deny checks
  - redact secrets from prompts and logs
  - attach provenance metadata to every response
- Gateway emits structured execution events:
  - model call
  - tool call
  - artifact read/write
  - policy decision

### 5) Execution Backends

- Model backend(s): local or remote, selected by policy profile.
- Tool backend: existing repo tooling and build/audit lanes executed in
  sandboxed workers.
- Worker profiles:
  - `read_only` (docs/theory interrogation)
  - `proof_check` (Lean build/check execution)
  - `infra_audit` (report generation)
- No direct unrestricted shell from browser users.

### 6) Storage and Audit

- Primary DB (PostgreSQL recommended):
  - users, invites, roles
  - rooms, memberships
  - messages, revisions
  - execution events
  - artifact references
- Object store for attachments and generated report artifacts.
- Immutable append-only audit log stream (DB table or log pipeline).

## Security Model

- Default deny for tools; room profile grants minimal capability set.
- Short-lived signed sessions, rotating refresh tokens.
- Rate limiting by IP/user/room.
- Content and attachment scanning hooks.
- Secret management:
  - environment/vault only
  - never stored in transcript body
  - redaction pass before persistence
- Admin-visible policy diff/audit surface.

## Governance and Policy

- Define policy bundles per room type:
  - allowed models
  - allowed tools/commands
  - max runtime and cost ceilings
  - citation/provenance requirements
- Reviewer-visible “why blocked” responses for denied operations.
- Escalation path: reviewer request -> maintainer approval -> retried action.

## Data Model (Minimal)

- `users(id, email, password_hash, role, mfa_enabled, created_at)`
- `invites(id, email, token_hash, expires_at, accepted_at, invited_by)`
- `rooms(id, name, room_type, created_by, created_at)`
- `room_members(room_id, user_id, role, joined_at)`
- `sessions(id, room_id, started_by, policy_profile, started_at, ended_at)`
- `messages(id, session_id, author_type, author_id, content, created_at)`
- `events(id, session_id, message_id, event_type, payload_json, created_at)`
- `artifacts(id, session_id, path, media_type, checksum, created_at)`

## End-to-End Flow

1. Reviewer accepts invite and logs in.
2. Reviewer joins an allowed room.
3. Reviewer asks a question in a `Socratic Review` session.
4. API records message and forwards to agent gateway.
5. Gateway selects policy profile and executes model/tools in worker.
6. Response streams back to UI with citations/tool trace.
7. Transcript + execution events are persisted for replay/audit.

## Voice and Diagram Extension (Post-MVP)

- Voice:
  - browser audio capture -> speech-to-text
  - text enters the same policy-governed chat pipeline
  - optional text-to-speech playback for agent replies
- Diagram:
  - attachment upload
  - Mermaid render pipeline
  - optional node-level references in replies

Keep both as optional modules so text-only operation remains first-class.

## Deployment Topology

### MVP topology (single environment)

- Reverse proxy + TLS
- Chat/API service
- Agent gateway
- Worker pool (sandboxed)
- PostgreSQL
- Object storage

### Hardened topology

- Separate API and worker networks
- Private worker subnet
- Queue-based job dispatch
- SIEM/log sink integration
- Backup/restore and retention policy

## Integration with Existing Repo Infrastructure

- Treat this as a control plane over existing proving/audit tooling.
- Reuse current build/audit scripts and policy docs as backend capabilities.
- Map room profiles to existing repo lanes:
  - strict Lean verification lane
  - DAG/architecture audit lane
  - documentation synthesis lane

## Phased Implementation Plan

1. Phase 0: Auth + rooms + text chat + transcript persistence.
2. Phase 1: Agent gateway with read-only policy profile.
3. Phase 2: Proof-check tool profile and artifact-linked responses.
4. Phase 3: Full audit trail UI, replay, and policy administration.
5. Phase 4: Optional voice and diagram enhancement.

## Implementation Checklist (Concrete Stack)

Use this as the execution checklist for an MVP that can be deployed quickly and
hardened incrementally.

### Stack picks

- Frontend: Next.js (App Router) + TypeScript.
- API: FastAPI + Pydantic.
- Realtime: WebSocket via FastAPI + Redis pub/sub.
- DB: PostgreSQL.
- Queue/workers: Redis + Arq workers.
- Object storage: S3-compatible (MinIO in dev, cloud bucket in prod).
- Auth: invite token + email/password initially; optional OIDC later.
- Secrets: Vault or cloud secrets manager.
- Reverse proxy/TLS: Caddy or Nginx.
- Observability: OpenTelemetry + Prometheus/Grafana + structured logs.

### Sprint 1: Private text chat baseline

- [ ] Create `users`, `invites`, `rooms`, `room_members`, `messages` schema.
- [ ] Implement invite flow (issue, accept, expire, revoke).
- [ ] Implement login, refresh token rotation, logout everywhere.
- [ ] Build room list and room-scoped chat UI.
- [ ] Persist transcripts and allow transcript export (Markdown/JSON).
- [ ] Add per-room ACL checks in all message endpoints.

Exit gate:
- invited reviewer can log in, join one room, and chat; non-members are denied.

### Sprint 2: Agent gateway and policy enforcement

- [ ] Add gateway service between chat API and model/tool execution.
- [ ] Define policy profiles: `socratic_review`, `proof_audit`, `design_review`.
- [ ] Implement allowlist checks for models and tool families.
- [ ] Add deterministic `review_session_id` and per-response provenance block.
- [ ] Persist execution events (`model_call`, `tool_call`, `policy_decision`).
- [ ] Add user-visible blocked-action messages with reason codes.

Exit gate:
- every agent response includes provenance; disallowed tool call is blocked and logged.

### Sprint 3: Proof/audit workers

- [ ] Provision sandboxed worker profile `read_only`.
- [ ] Provision sandboxed worker profile `proof_check`.
- [ ] Implement bounded job execution (time, CPU, memory, output limits).
- [ ] Attach generated artifacts to responses (report links/checksums).
- [ ] Add queue retry policy and dead-letter queue.
- [ ] Add maintainer approval flow for elevated actions.

Exit gate:
- reviewers can request proof checks; workers run bounded jobs with reproducible artifact links.

### Sprint 4: Security hardening and ops

- [ ] Enable MFA for `owner` and `maintainer`.
- [ ] Add rate limiting by IP/user/room.
- [ ] Add attachment scanning and MIME validation.
- [ ] Add audit dashboard (session replay + event timeline).
- [ ] Add backup/restore for Postgres and object storage.
- [ ] Add retention policies and data purge jobs.

Exit gate:
- security checklist passes and restore drill succeeds.

### Sprint 5: Reviewer experience polish

- [ ] Add room templates for “live exam” sessions.
- [ ] Add moderator controls (mute, close session, pin question).
- [ ] Add citation panel with source/tool trace jump links.
- [ ] Add diagram attachment + Mermaid render support.
- [ ] Add optional voice input/output module behind feature flag.

Exit gate:
- live reviewer session runs end-to-end with transcripts, artifacts, and moderator controls.

### First production SLO targets

- API availability: 99.5% monthly.
- Message p95 latency: < 2.5s (non-tool responses).
- Worker queue p95 wait: < 10s under expected load.
- Failed job rate: < 2% (excluding policy-denied jobs).
- Audit event loss: 0 tolerated.

## Acceptance Criteria

- Invited reviewer can log in and join allowed rooms only.
- Every agent reply in review rooms includes provenance metadata.
- Tool execution is policy-gated and auditable.
- Session transcript is exportable with linked tool events/artifacts.
- Maintainer can revoke access and close sessions immediately.

## Open Questions

- Preferred identity provider: local auth only vs SSO bridge.
- Target hosting: self-hosted VM, Kubernetes, or managed platform.
- Data retention horizon for transcripts and artifacts.
- Which reviewer roles can trigger proof-check workers by default.
