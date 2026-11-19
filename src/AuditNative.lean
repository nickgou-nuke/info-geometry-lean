/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Meta.ArchitectureAudit

/-!
# AuditNative

Lightweight Lean-native architecture and representation-depth audit command
provider (`#audit_architecture`, `#audit_architecture_decl`,
`#audit_architecture_file`, `#audit_architecture_namespace`,
`#audit_rep_depth_coverage`, `#audit_rep_depth_coverage_file`,
`#audit_rep_depth_coverage_namespace`).

Use `AuditNativeRun` to execute the full canonical architecture, coverage, and
strict admission suite over `InfoGeometry.Canonical.All`.
-/
