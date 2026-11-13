/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Lake
open Lake DSL

package clifford_peirce_walsh_validation where
  srcDir := "../../lean"
  packagesDir := "../../.lake/packages"
  enableArtifactCache := false

require mathlib from "../../.lake/packages/mathlib"

lean_lib InfoGeometry
