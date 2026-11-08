/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.CondensedMatter.DIIISuperfluid
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.CondensedMatter.CliffordAtomsZ2n
import InfoGeometry.CondensedMatter.NonOrientableWeylSemimetal
import InfoGeometry.CondensedMatter.KitaevFreeFermionKOSpectrumLocalGapPoset
import InfoGeometry.Canonical.KitaevLocalGapOmegaSpectrumKOPoset
import InfoGeometry.Kitaev.KitaevLocalGapOmegaSpectrumPoset

/-!
# Condensed Matter Interfaces

## i. Overview

Umbrella import module for condensed-matter topological phases, BdG symmetry classes,
and Kitaev local-gap / $KO$-spectrum posets.

## ii. Key results

- Imports `DIIISuperfluid`, `CliffordAtomsZ2n`, `NonOrientableWeylSemimetal`,
  `KitaevFreeFermionKOSpectrumLocalGapPoset`, `KitaevLocalGapOmegaSpectrumKOPoset`,
  and `KitaevLocalGapOmegaSpectrumPoset`.

## iii. Table of contents

- Imports and `InfoGeometry.CondensedMatter` namespace.

### Three-Bucket Audit Map
* **BUCKET 1 — Proved Kernel Content:**
  - Re-exports kernel-checked theorems from the imported `InfoGeometry.CondensedMatter` and `InfoGeometry.Kitaev` owners.
* **BUCKET 2 — Conditional / Interface Boundaries:**
  - Inherits explicit algebraic and finite-dimensional matrix hypotheses from the imported modules.
* **BUCKET 3 — Out-of-Scope / Open Claims:**
  - Adds no new declarations or unproven analytic/topological claims.

## iv. References

- Alexei Kitaev, *Periodic table for topological insulators and superconductors*, AIP Conf. Proc. 1134, 22–30 (2009).
-/

namespace InfoGeometry.CondensedMatter

end InfoGeometry.CondensedMatter
