/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import AuditNative

namespace InfoGeometry.Canonical.AuditNativeScopedTest

@[rep_depth count]
theorem root : True := trivial

@[rep_depth projective]
theorem child : True := root

end InfoGeometry.Canonical.AuditNativeScopedTest

#audit_architecture_namespace InfoGeometry.Canonical.AuditNativeScopedTest
