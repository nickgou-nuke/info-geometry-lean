/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev.
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic

/-!
# Scalar Tri-Facet Eigenspace Algebra

This file proves the scalar spectral projectors attached to a cubic
tri-facet element `O` satisfying `O ^ 3 = O`.  The hyperbolic, elliptic,
and parabolic scalar projectors are

* `P_hyp O = (O ^ 2 + O) / 2`;
* `P_ell O = (O ^ 2 - O) / 2`;
* `P_par O = 1 - O ^ 2`.

The reconstruction theorem requires the explicit characteristic condition
`(2 : A) ≠ 0`.

## Audit Protocol Map

- **BUCKET 1: CLOSED FINITE THEOREMS**:
  - `P_hyp`, `P_ell`, `P_par`.
  - `tri_facet_eigenspace_hyp`, `tri_facet_eigenspace_ell`,
    `tri_facet_eigenspace_par`.
  - `tri_facet_spectral_reconstruction`.
- **BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES**:
  - The eigenspace laws are conditional on `O ^ 3 = O`.
  - Reconstruction is conditional on `(2 : A) ≠ 0`.
- **BUCKET 3: OPEN CLOSURE DEBT**:
  - None for this scalar algebra layer.
-/

namespace InfoGeometry.Algebra.TriFacetScalar

variable {A : Type*} [Field A]

/-- Hyperbolic scalar projector `(O² + O) / 2`. -/
def P_hyp (O : A) : A :=
  (1 / 2 : A) * (O ^ 2 + O)

/-- Elliptic scalar projector `(O² - O) / 2`. -/
def P_ell (O : A) : A :=
  (1 / 2 : A) * (O ^ 2 - O)

/-- Parabolic scalar projector `1 - O²`. -/
def P_par (O : A) : A :=
  1 - O ^ 2

/-- The hyperbolic projector lies in the `+1` scalar eigensector. -/
theorem tri_facet_eigenspace_hyp
    {O : A}
    (hO : O ^ 3 = O) :
    O * P_hyp O = P_hyp O := by
  unfold P_hyp
  have h_calc :
      O * ((1 / 2 : A) * (O ^ 2 + O)) = (1 / 2 : A) * (O ^ 3 + O ^ 2) := by
    ring
  rw [h_calc, hO]
  ring

/-- The elliptic projector lies in the `-1` scalar eigensector. -/
theorem tri_facet_eigenspace_ell
    {O : A}
    (hO : O ^ 3 = O) :
    O * P_ell O = -P_ell O := by
  unfold P_ell
  have h_calc :
      O * ((1 / 2 : A) * (O ^ 2 - O)) = (1 / 2 : A) * (O ^ 3 - O ^ 2) := by
    ring
  rw [h_calc, hO]
  ring

/-- The parabolic projector lies in the zero scalar eigensector. -/
theorem tri_facet_eigenspace_par
    {O : A}
    (hO : O ^ 3 = O) :
    O * P_par O = 0 := by
  unfold P_par
  have h_calc : O * (1 - O ^ 2) = O - O ^ 3 := by
    ring
  rw [h_calc, hO]
  ring

/-- The hyperbolic-minus-elliptic projectors reconstruct `O`. -/
theorem tri_facet_spectral_reconstruction
    (h2 : (2 : A) ≠ 0)
    (O : A) :
    P_hyp O - P_ell O = O := by
  unfold P_hyp P_ell
  field_simp [h2]
  ring

end InfoGeometry.Algebra.TriFacetScalar
