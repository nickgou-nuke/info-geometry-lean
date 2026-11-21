/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Lake
open Lake DSL

/-!
# Isolated Lake workspace for the `src/` Lean transition tree.

The root `lakefile.lean` compiles `lean/`. This workspace uses the same pinned
manifest and dependencies, but sends its artifacts to `.lake/src-build` so
duplicate Lean module names in `src/` and `lean/` are compiled independently.
The globs select every Lean module rooted in a source-bearing top-level
directory plus every top-level Lean file. They deliberately avoid an
anonymous catch-all, which would capture dependency modules such as `Mathlib`
as if they lived under `src/`.
-/

package infogeometrySrc where
  buildDir := ".lake/src-build"

require InfoGeometryCore from "lib" / "InfoGeometryCore"
require Paperproof from git "https://github.com/Paper-Proof/paperproof.git"
  @ "c85fb0b45ce9ebaaa4715c7d043aadda80306c46" / "lean"
require paranoia from git "https://github.com/oOo0oOo/LeanParanoia.git"
  @ "11c2385ade3cc417d69ce837bfda9d2c5b1d61ab"
require LeanArchitect from git "https://github.com/hanwenzhu/LeanArchitect.git"
  @ "54d3fb249685db8e5a564e0b3f331cff77991607"
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4.git"
  @ "v4.34.1"
require «GIFT» from "external_refs/gift-framework-core"
require Atlas from "external_refs/atlas-lean"
require HomotopyHypothesis from "external_refs/homotopy-hypothesis-lean4"
require LeanCopilot from git "https://github.com/lean-dojo/LeanCopilot.git"
  @ "c360b5df5d8a67ed8f1a8769aa157f6adca7dd53"
require mathlib from git "https://github.com/leanprover-community/mathlib4.git"
  @ "v4.34.1"

-- Keep external OAI modules available to the source tree as they are in the
-- root Lean workspace.  The source lane has a separate build directory, so
-- it must compile these imported owners against the same pinned Mathlib
-- instead of accidentally searching an unrelated path dependency's cache.
lean_lib OAI where
  srcDir := "external_refs/openai-math/lean"
  roots := #[
    `OAI.GroupTheory.BooneHigman.Main,
    `OAI.GroupTheory.BooneHigman.TwistedSimplicity,
    `OAI.GroupTheory.FiniteType.TwistedBrinSeparated,
    `OAI.GroupTheory.SimpleAmenable.PolygonGeometry.ShiftedSlots,
    `OAI.GroupTheory.SimpleAmenable.Main
  ]
  globs := #[
    .submodules `OAI.Analysis.Cuntz,
    .submodules `OAI.Analysis.Quasitrace,
    .submodules `OAI.Algebra.OrderedStates,
    .submodules `OAI.GroupTheory.FiniteType,
    .submodules `OAI.GroupTheory.FiniteLattice,
    .submodules `OAI.GroupTheory.BooneHigman,
    .submodules `OAI.GroupTheory.SimpleOvergroups,
    .submodules `OAI.Computability,
    .submodules `OAI.Combinatorics.PerfectMatching,
    .submodules `OAI.GroupTheory.SimpleAmenable,
    .submodules `OAI.GroupTheory.SimpleAmenable.Arithmetic.PolygonArithmetic,
    .submodules `OAI.GroupTheory.SimpleAmenable.Configurations.TrackPoint,
    .submodules `OAI.GroupTheory.SimpleAmenable.PolygonGeometry.PolygonAction,
    .submodules `OAI.GroupTheory.SimpleAmenable.PolygonGeometry.TupleChartDomain,
    .submodules `OAI.GroupTheory.SimpleAmenable.PolygonGeometry.Supported,
    .submodules `OAI.GroupTheory.SimpleAmenable.PolygonGeometry.ShiftedSlots,
    -- `HomotopyHypothesis` already owns OAI.CategoryTheory.Globular in this
    -- Lake workspace. Including it here gives Lake two distinct providers for
    -- OAI.CategoryTheory.Globular.Model.
  ]

@[default_target]
lean_lib SrcLane where
  srcDir := "src"
  globs := #[
    .andSubmodules `Agent,
    .andSubmodules `DAG,
    .andSubmodules `Docs,
    .andSubmodules `Experimental,
    .andSubmodules `InfoGeometry,
    .andSubmodules `Omega,
    .andSubmodules `SelfReference,
    .andSubmodules `Socratic,
    .andSubmodules `VirasoroProject,
    -- These trees have submodules but no `sandbox.lean` or `scripts.lean`
    -- root module in `src/`; selecting the roots made Lake schedule paths
    -- that do not exist during job computation.
    .submodules `sandbox,
    .submodules `scripts,
    .one `B3PresentedGroup,
    .one `Agent,
    .one `AuditNative,
    .one `AuditStrict,
    .one `CheckBasis,
    .one `CheckTemp,
    .one `DAG,
    .one `Docs,
    .one `Experimental,
    .one `GrandPartitionAll,
    .one `GrandPartitionEuler,
    .one `GrandPartitionOnline,
    .one `GrandPartitionPolynomial,
    .one `GrandPartitionProbability,
    .one `GrandPartitionRational,
    .one `GrandPartitionRobustPoisson,
    .one `GrandPartitionTransform,
    .one `InfoGeometry,
    .one `KaplanskyCliffordBridge,
    .one `NonIsoConf3OrlikSolomon,
    .one `Omega,
    .one `PrimitiveSetsAboveX,
    .one `SelfReference,
    .one `Socratic,
    .one `Test,
    .one `TestFin,
    .one `VirasoroProject,
    .one `SplitOctonionBraidSU3,
    .one `YangBaxterQSwap,
    .one `YangBaxterZornBridge,
    .one `ZornScalingFlow,
    .one `ast_export_test,
    .one `temp_test,
    .one `test_fixes2,
    .one `test_reflection,
    .one `test_rpow,
    .one `test_selfconcordance
  ]

-- `AuditNativeRun` deliberately executes repository-wide architecture and
-- representation-depth audits. Keep it available as an explicit target, but
-- out of ordinary source compilation: the audit is a policy gate whose
-- findings are maintained independently of whether source modules typecheck.
lean_lib AuditRun where
  srcDir := "src"
  roots := #[`AuditNativeRun]
