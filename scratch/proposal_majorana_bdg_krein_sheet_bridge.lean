/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
/-!
# Proposal: transport the 8D BdG Majorana vectors to the doubled Krein sheets

Status: exploratory proposal; **not compiled**.  This file is intentionally a
scratch proposal, not an owner module.  It records the carrier map and target
theorems for a later small, kernel-checked bridge.

The two source vectors are the actual kernels of `kitaevSweetSpot8 t` from
`Canonical.MajoranaKitaevSpinor8DClifford`.  The target is
`DoubledSpace (EuclideanSpace ℝ (Fin 4))`, with the first four coordinates on
the first sheet and the last four on the second.  The carrier map must prove
that `particleHole8` becomes `modular_j` and `kreinMetric8` becomes
`spectral_epsilon`.

The proposed conclusions concern the transported BdG operator and its two
kernel vectors.  The plus/minus projector formulas below describe the two
components of each vector; they do **not** assert that either projected
component remains in the BdG kernel.  No topological protection, locality, or
physical zero-mode claim is inferred from these finite-dimensional identities.

The statements and proof sketches below have not been checked by Lean.  In
particular, the `LinearEquiv` construction is the implementation point to
validate first: depending on the local mathlib coercions for `EuclideanSpace`,
the coordinate extensionality steps may need small adjustments.
-/

import Mathlib
import InfoGeometry.Canonical.MajoranaKitaevSpinor8DClifford
import InfoGeometry.Canonical.KreinMajoranaBlockInvariance
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Krein.PolarizedSector

/-!
## Intended core definitions

Use `Fin 4 → ℝ` as the Euclidean fiber, represented by
`EuclideanSpace ℝ (Fin 4)` in the doubled-space construction.  The low and
high coordinate embeddings are explicit, so the split convention is
reviewable and does not depend on an implicit reordering.
-/

namespace InfoGeometry.Krein.MajoranaBdGSheetProposal

open InfoGeometry.Krein
open InfoGeometry.Krein.PolarizedSector
open InfoGeometry.Krein.SplitQuadraticSheets
open InfoGeometry.Canonical.MajoranaKitaevSpinor8DClifford
open InfoGeometry.Canonical.KreinMajoranaBlockInvariance

abbrev E4 := EuclideanSpace ℝ (Fin 4)
abbrev H4 := DoubledSpace E4

private def lowIndex (i : Fin 4) : Fin 8 := ⟨i.val, by omega⟩
private def highIndex (i : Fin 4) : Fin 8 := ⟨i.val + 4, by omega⟩

/-- Candidate coordinate split: entries 0..3 and 4..7 become the two sheets. -/
noncomputable def split8 (v : Vec8R) : H4 :=
  to_doubled
    (WithLp.toLp (2 : ENNReal) (fun i : Fin 4 => v (lowIndex i)))
    (WithLp.toLp (2 : ENNReal) (fun i : Fin 4 => v (highIndex i)))

/-- Candidate inverse coordinate gluing for the split. -/
noncomputable def glue8 (z : H4) : Vec8R := fun j =>
  if hj : j.val < 4 then
    WithLp.fst z ⟨j.val, hj⟩
  else
    WithLp.snd z ⟨j.val - 4, by omega⟩

/-- Desired real-linear equivalence between Nambu coordinates and the double. -/
noncomputable def nambuDoubledEquiv : Vec8R ≃ₗ[ℝ] H4 := by
  refine
    { toFun := split8
      invFun := glue8
      left_inv := ?_
      right_inv := ?_
      map_add' := ?_
      map_smul' := ?_ }
  · intro v
    funext j
    by_cases hj : j.val < 4
    · simp [split8, glue8, hj, lowIndex, highIndex, to_doubled]
    · simp [split8, glue8, hj, lowIndex, highIndex, to_doubled]
  · intro z
    apply DoubledSpace.ext
    · ext i
      simp [split8, glue8, lowIndex, highIndex, to_doubled]
    · ext i
      simp [split8, glue8, lowIndex, highIndex, to_doubled]
  · intro v w
    apply DoubledSpace.ext <;> ext i <;>
      simp [split8, lowIndex, highIndex, to_doubled, PiLp.add_apply]
  · intro c v
    apply DoubledSpace.ext <;> ext i <;>
      simp [split8, lowIndex, highIndex, to_doubled, PiLp.smul_apply]

/-!
### Target intertwining statements

The following equations are the exact compatibility contract.  Their proofs
should reduce to the explicit coordinate formulas after unfolding
`particleHole8`, `kreinMetric8`, and `split8`.  They are deliberately stated on
vectors, so there is no ambiguity about whether the source matrices act on
columns by `mulVec`.
-/

/-
Target theorem contracts (not declarations in this proposal file):

    particleHole8_intertwines_modularSwap (v : Vec8R) :
      split8 (particleHole8.mulVec v) = modular_j (E := E4) (split8 v)

    kreinMetric8_intertwines_spectralEpsilon (v : Vec8R) :
      split8 (kreinMetric8.mulVec v) = spectral_epsilon (E := E4) (split8 v)

Proof plan for both: `apply DoubledSpace.ext <;> ext i <;> fin_cases i`,
then simplify the matrix action using `Matrix.mulVec`, `dotProduct`,
`Fin.sum_univ_eight`, and the explicit low/high index maps.  The first equality
swaps the two blocks; the second leaves the first block fixed and negates the
second.
-/

/-! ### Transported sweet-spot action and its two kernel vectors -/

/-- Conjugate the concrete BdG action across the proposed carrier equivalence. -/
def transportedSweetSpot (t : ℝ) : H4 → H4 := fun z =>
  split8 ((kitaevSweetSpot8 t).mulVec (glue8 z))

/-
Target kernel contracts:

    transportedSweetSpot t (split8 majoranaZeroModeLeft8) = 0
    transportedSweetSpot t (split8 majoranaZeroModeRight8) = 0

Once `glue8_split8` is proved, each follows from the corresponding existing
owner theorem `left_majorana_zero_mode_energy8 t` or
`right_majorana_zero_mode_energy8 t`, respectively, by applying `split8` to
the equality.  The conjugation is defined by the actual inverse `glue8`; no
new Hamiltonian kernel is assumed.
-/

/-!
### Expected component and projection readouts

Coordinate calculation gives the left vector `(e₀, -e₀)` and the right vector
`(e₃, e₃)`.  The projectors retain the first coordinate on the plus sheet and
the second coordinate on the minus sheet.  These are component identities,
not assertions about kernels of the projected vectors.
-/

noncomputable def basis0 : E4 := WithLp.toLp (2 : ENNReal) (fun i => if i = 0 then 1 else 0)
noncomputable def basis3 : E4 := WithLp.toLp (2 : ENNReal) (fun i => if i = 3 then 1 else 0)

/-
Target component and projection contracts:

    split8 majoranaZeroModeLeft8  = to_doubled basis0 (-basis0)
    split8 majoranaZeroModeRight8 = to_doubled basis3 basis3

    spectralPlusProj  (split8 majoranaZeroModeLeft8)  = to_doubled basis0 0
    spectralMinusProj (split8 majoranaZeroModeLeft8)  = to_doubled 0 (-basis0)
    spectralPlusProj  (split8 majoranaZeroModeRight8) = to_doubled basis3 0
    spectralMinusProj (split8 majoranaZeroModeRight8) = to_doubled 0 basis3

The first two coordinate equalities follow by `DoubledSpace.ext`, then
extensionality and `fin_cases` over `Fin 4`.  The four projection formulas
then follow from `spectralPlusProj_apply_to_doubled` and
`spectralMinusProj_apply_to_doubled` in `Krein.PolarizedSector`.
-/

end InfoGeometry.Krein.MajoranaBdGSheetProposal
