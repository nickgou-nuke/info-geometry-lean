/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.All
import AuditNative
import AuditStrict

/-!
# AuditNativeRun

Explicit, opt-in execution entrypoint for the repository architecture,
representation-depth, and strict admission audits. `AuditNative` and
`AuditStrict` remain lightweight command providers; this module deliberately
loads the canonical declaration surface before running those commands.
-/

#audit_architecture
#audit_rep_depth_coverage
#audit_admission_namespace InfoGeometry.Canonical
