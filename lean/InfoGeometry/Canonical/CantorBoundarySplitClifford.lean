import Mathlib
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.CantorBoundarySplitClifford

Infinite Cantor-boundary tilt/switch operators and the local split atom.

This owner stays on the real boundary-function carrier:

* `tilt j` is the sign operator at address slot `j`;
* `switch j` flips the `j`-th boundary bit;
* `splitAtom j = switch j * tilt j` is the local real `Cl(1,1)` atom.

The split direct limit of `Cl(n,n)` is already packaged elsewhere in the repo.
This file gives the Cantor-boundary operator side cleanly, without using
`Complex.I` as a structure operator.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorBoundarySplitClifford

/-- Infinite binary Cantor boundary. -/
abbrev CantorBoundary := ℕ → Bool

/-- Real-valued functions on the infinite Cantor boundary. -/
abbrev CantorBoundaryFunctionSpace := CantorBoundary → ℝ

namespace CantorBoundary

/-- Flip the bit at a chosen boundary slot. -/
def flipAt (j : ℕ) (x : CantorBoundary) : CantorBoundary :=
  fun k => if k = j then ! (x k) else x k

@[simp] theorem flipAt_apply_eq (j : ℕ) (x : CantorBoundary) :
    flipAt j x j = ! (x j) := by
  simp [flipAt]

@[simp] theorem flipAt_apply_ne {j k : ℕ} (h : k ≠ j) (x : CantorBoundary) :
    flipAt j x k = x k := by
  simp [flipAt, h]

theorem flipAt_involutive (j : ℕ) (x : CantorBoundary) :
    flipAt j (flipAt j x) = x := by
  funext k
  by_cases hk : k = j <;> simp [flipAt, hk, Bool.not_not]

theorem flipAt_comm {i j : ℕ} (hij : i ≠ j) (x : CantorBoundary) :
    flipAt i (flipAt j x) = flipAt j (flipAt i x) := by
  funext k
  by_cases hki : k = i
  · by_cases hji : i = j
    · exact False.elim (hij hji)
    · simp [flipAt, hki, hji]
  · by_cases hkj : k = j
    · have hji : j ≠ i := by
        intro h
        apply hki
        rw [hkj, h]
      simp [flipAt, hkj, hji]
    · simp [flipAt, hki, hkj]

end CantorBoundary

namespace CantorBoundaryFunctionSpace

open CantorBoundary

/-- Tilt operator on infinite boundary functions. -/
def tilt (j : ℕ) : CantorBoundaryFunctionSpace →ₗ[ℝ] CantorBoundaryFunctionSpace where
  toFun f := fun x => if x j then -f x else f x
  map_add' := by
    intro f g
    ext x
    by_cases hx : x j <;> simp [hx, add_comm, add_left_comm, add_assoc]
  map_smul' := by
    intro c f
    ext x
    by_cases hx : x j <;> simp [hx]

/-- Switch operator on infinite boundary functions. -/
def switch (j : ℕ) : CantorBoundaryFunctionSpace →ₗ[ℝ] CantorBoundaryFunctionSpace where
  toFun f := fun x => f (CantorBoundary.flipAt j x)
  map_add' := by
    intro f g
    ext x
    rfl
  map_smul' := by
    intro c f
    ext x
    rfl

@[simp] theorem tilt_apply (j : ℕ) (f : CantorBoundaryFunctionSpace) (x : CantorBoundary) :
    tilt j f x = if x j then -f x else f x :=
  rfl

@[simp] theorem switch_apply (j : ℕ) (f : CantorBoundaryFunctionSpace) (x : CantorBoundary) :
    switch j f x = f (CantorBoundary.flipAt j x) :=
  rfl

/-- Tilt squares to the identity. -/
theorem tilt_sq (j : ℕ) :
    (tilt j) * (tilt j) = 1 := by
  apply LinearMap.ext
  intro f
  ext x
  by_cases hx : x j <;> simp [tilt, hx]

/-- Switch squares to the identity. -/
theorem switch_sq (j : ℕ) :
    (switch j) * (switch j) = 1 := by
  apply LinearMap.ext
  intro f
  ext x
  simpa using congrArg f (CantorBoundary.flipAt_involutive j x)

/-- Tilt operators commute at distinct slots. -/
theorem tilt_comm {i j : ℕ} :
    (tilt i) * (tilt j) = (tilt j) * (tilt i) := by
  apply LinearMap.ext
  intro f
  ext x
  by_cases hxi : x i <;> by_cases hxj : x j <;> simp [tilt, hxi, hxj]

/-- Switch operators commute at distinct slots. -/
theorem switch_comm {i j : ℕ} (hij : i ≠ j) :
    (switch i) * (switch j) = (switch j) * (switch i) := by
  apply LinearMap.ext
  intro f
  ext x
  simp [switch, CantorBoundary.flipAt_comm hij]

/-- Tilt and switch commute at different slots. -/
theorem tilt_switch_comm_of_ne {i j : ℕ} (hij : i ≠ j) :
    (tilt i) * (switch j) = (switch j) * (tilt i) := by
  apply LinearMap.ext
  intro f
  ext x
  by_cases hxi : x i <;>
    simp [tilt, switch, CantorBoundary.flipAt_apply_ne hij, hxi]

/-- Tilt and switch anticommute at the same slot. -/
theorem tilt_switch_anticomm (j : ℕ) :
    (tilt j) * (switch j) = - ((switch j) * (tilt j)) := by
  apply LinearMap.ext
  intro f
  ext x
  by_cases hx : x j <;> simp [tilt, switch, CantorBoundary.flipAt, hx]

/-- The local split atom on the Cantor boundary. -/
def splitAtom (j : ℕ) :
    CantorBoundaryFunctionSpace →ₗ[ℝ] CantorBoundaryFunctionSpace :=
  switch j * tilt j

/-- The local split atom squares to `-1`. -/
theorem splitAtom_sq (j : ℕ) :
    splitAtom j * splitAtom j =
      - (1 : CantorBoundaryFunctionSpace →ₗ[ℝ] CantorBoundaryFunctionSpace) := by
  ext f x
  by_cases hx : x j <;>
    simp [splitAtom, tilt, switch, hx, CantorBoundary.flipAt_involutive]

end CantorBoundaryFunctionSpace

end InfoGeometry.Canonical.CantorBoundarySplitClifford
