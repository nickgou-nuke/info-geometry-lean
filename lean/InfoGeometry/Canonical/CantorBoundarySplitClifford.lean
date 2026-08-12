import Mathlib.Tactic
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

namespace CantorBoundary

/-- Flip the bit at a chosen boundary slot. -/
def flipAt (j : ℕ) (x : ℕ → Bool) : ℕ → Bool :=
  fun k => if k = j then ! (x k) else x k

@[simp] theorem flipAt_apply_eq (j : ℕ) (x : ℕ → Bool) :
    flipAt j x j = ! (x j) := by
  simp [flipAt]

@[simp] theorem flipAt_apply_ne {j k : ℕ} (h : k ≠ j) (x : ℕ → Bool) :
    flipAt j x k = x k := by
  simp [flipAt, h]

theorem flipAt_involutive (j : ℕ) (x : ℕ → Bool) :
    flipAt j (flipAt j x) = x := by
  funext k
  by_cases hk : k = j <;> simp [flipAt, hk, Bool.not_not]

theorem flipAt_comm {i j : ℕ} (hij : i ≠ j) (x : ℕ → Bool) :
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
def tilt (j : ℕ) : ((ℕ → Bool) → ℝ) →ₗ[ℝ] ((ℕ → Bool) → ℝ) where
  toFun f := fun x => if x j then -f x else f x
  map_add' := by
    intro f g
    ext x
    by_cases hx : x j <;> simp [hx, add_comm]
  map_smul' := by
    intro c f
    ext x
    by_cases hx : x j <;> simp [hx]

/-- Switch operator on infinite boundary functions. -/
def switch (j : ℕ) : ((ℕ → Bool) → ℝ) →ₗ[ℝ] ((ℕ → Bool) → ℝ) where
  toFun f := fun x => f (CantorBoundary.flipAt j x)
  map_add' := by
    intro f g
    ext x
    rfl
  map_smul' := by
    intro c f
    ext x
    rfl

@[simp] theorem tilt_apply (j : ℕ) (f : (ℕ → Bool) → ℝ) (x : ℕ → Bool) :
    tilt j f x = if x j then -f x else f x :=
  rfl

@[simp] theorem switch_apply (j : ℕ) (f : (ℕ → Bool) → ℝ) (x : ℕ → Bool) :
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

theorem switch_comm_all {i j : ℕ} :
    (switch i) * (switch j) = (switch j) * (switch i) := by
  by_cases hij : i = j
  · subst j
    rfl
  · exact switch_comm hij

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
    ((ℕ → Bool) → ℝ) →ₗ[ℝ] ((ℕ → Bool) → ℝ) :=
  switch j * tilt j

/-- The local split atom squares to `-1`. -/
theorem splitAtom_sq (j : ℕ) :
    splitAtom j * splitAtom j =
      - (1 : ((ℕ → Bool) → ℝ) →ₗ[ℝ] ((ℕ → Bool) → ℝ)) := by
  ext f x
  by_cases hx : x j <;>
    simp [splitAtom, tilt, switch, hx, CantorBoundary.flipAt_involutive]

theorem splitAtom_mul_tilt (j : ℕ) :
    splitAtom j * tilt j = switch j := by
  rw [splitAtom, mul_assoc, tilt_sq, mul_one]

theorem tilt_mul_splitAtom (j : ℕ) :
    tilt j * splitAtom j = - switch j := by
  rw [splitAtom]
  calc
    tilt j * (switch j * tilt j) =
        (tilt j * switch j) * tilt j := by rw [mul_assoc]
    _ = (-(switch j * tilt j)) * tilt j := by
      rw [tilt_switch_anticomm]
    _ = -(switch j * (tilt j * tilt j)) := by
      congr 1
    _ = - switch j := by rw [tilt_sq, mul_one]

theorem switch_mul_splitAtom (j : ℕ) :
    switch j * splitAtom j = tilt j := by
  rw [splitAtom, ← mul_assoc, switch_sq, one_mul]

theorem splitAtom_mul_switch (j : ℕ) :
    splitAtom j * switch j = - tilt j := by
  apply LinearMap.ext
  intro f
  ext x
  by_cases hx : x j <;>
    simp [splitAtom, tilt, switch, CantorBoundary.flipAt, hx,
      CantorBoundary.flipAt_involutive]

theorem splitAtom_comm_of_ne {i j : ℕ} (hij : i ≠ j) :
    splitAtom i * splitAtom j = splitAtom j * splitAtom i := by
  apply LinearMap.ext
  intro f
  ext x
  have hji : j ≠ i := by
    intro h
    exact hij h.symm
  have hflip := CantorBoundary.flipAt_comm hij x
  by_cases hxi : x i <;> by_cases hxj : x j <;>
    simp [splitAtom, tilt, switch, CantorBoundary.flipAt,
      hflip, hij, hji, hxi, hxj]

theorem splitAtom_comm_all {i j : ℕ} :
    splitAtom i * splitAtom j = splitAtom j * splitAtom i := by
  by_cases hij : i = j
  · subst j
    rfl
  · exact splitAtom_comm_of_ne hij

theorem tilt_splitAtom_comm_of_ne {i j : ℕ} (hij : i ≠ j) :
    tilt i * splitAtom j = splitAtom j * tilt i := by
  apply LinearMap.ext
  intro f
  ext x
  have hji : j ≠ i := by
    intro h
    exact hij h.symm
  by_cases hxi : x i <;> by_cases hxj : x j <;>
    simp [splitAtom, tilt, switch, CantorBoundary.flipAt,
      hij, hxi, hxj]

theorem switch_splitAtom_comm_of_ne {i j : ℕ} (hij : i ≠ j) :
    switch i * splitAtom j = splitAtom j * switch i := by
  apply LinearMap.ext
  intro f
  ext x
  have hji : j ≠ i := by
    intro h
    exact hij h.symm
  have hflip := CantorBoundary.flipAt_comm hij x
  by_cases hxi : x i <;> by_cases hxj : x j <;>
    simp [splitAtom, tilt, switch, CantorBoundary.flipAt,
      hflip, hji, hxj]

theorem switch_conjugate_tilt (j : ℕ) :
    switch j * tilt j * switch j = - tilt j := by
  apply LinearMap.ext
  intro f
  ext x
  by_cases hx : x j <;>
    simp [tilt, switch, CantorBoundary.flipAt, hx,
      CantorBoundary.flipAt_involutive]

theorem tilt_conjugate_switch (j : ℕ) :
    tilt j * switch j * tilt j = - switch j := by
  apply LinearMap.ext
  intro f
  ext x
  by_cases hx : x j <;>
    simp [tilt, switch, CantorBoundary.flipAt, hx,
      CantorBoundary.flipAt_involutive]

theorem switch_conjugate_splitAtom (j : ℕ) :
    switch j * splitAtom j * switch j = - splitAtom j := by
  apply LinearMap.ext
  intro f
  ext x
  by_cases hx : x j <;>
    simp [splitAtom, tilt, switch, CantorBoundary.flipAt, hx,
      CantorBoundary.flipAt_involutive]

theorem tilt_conjugate_splitAtom (j : ℕ) :
    tilt j * splitAtom j * tilt j = - splitAtom j := by
  apply LinearMap.ext
  intro f
  ext x
  by_cases hx : x j <;>
    simp [splitAtom, tilt, switch, CantorBoundary.flipAt, hx,
      CantorBoundary.flipAt_involutive]

def cantorSheetPlusProjector (j : ℕ) :
    ((ℕ → Bool) → ℝ) →ₗ[ℝ] ((ℕ → Bool) → ℝ) :=
  (1 / 2 : ℝ) • ((1 : ((ℕ → Bool) → ℝ) →ₗ[ℝ] ((ℕ → Bool) → ℝ)) + tilt j)

def cantorSheetMinusProjector (j : ℕ) :
    ((ℕ → Bool) → ℝ) →ₗ[ℝ] ((ℕ → Bool) → ℝ) :=
  (1 / 2 : ℝ) • ((1 : ((ℕ → Bool) → ℝ) →ₗ[ℝ] ((ℕ → Bool) → ℝ)) - tilt j)

theorem cantorSheetPlusProjector_add_cantorSheetMinusProjector (j : ℕ) :
    cantorSheetPlusProjector j + cantorSheetMinusProjector j = 1 := by
  apply LinearMap.ext
  intro f
  ext x
  by_cases hx : x j <;>
    simp [cantorSheetPlusProjector, cantorSheetMinusProjector, tilt, hx] <;>
      ring

theorem cantorSheetPlusProjector_sq (j : ℕ) :
    cantorSheetPlusProjector j * cantorSheetPlusProjector j =
      cantorSheetPlusProjector j := by
  apply LinearMap.ext
  intro f
  ext x
  by_cases hx : x j <;>
    simp [cantorSheetPlusProjector, tilt, hx] <;> ring

theorem cantorSheetMinusProjector_sq (j : ℕ) :
    cantorSheetMinusProjector j * cantorSheetMinusProjector j =
      cantorSheetMinusProjector j := by
  apply LinearMap.ext
  intro f
  ext x
  by_cases hx : x j <;>
    simp [cantorSheetMinusProjector, tilt, hx] <;> ring

theorem cantorSheetPlusProjector_mul_cantorSheetMinusProjector (j : ℕ) :
    cantorSheetPlusProjector j * cantorSheetMinusProjector j = 0 := by
  apply LinearMap.ext
  intro f
  ext x
  by_cases hx : x j <;>
    simp [cantorSheetPlusProjector, cantorSheetMinusProjector, tilt, hx] <;>
      ring

theorem cantorSheetMinusProjector_mul_cantorSheetPlusProjector (j : ℕ) :
    cantorSheetMinusProjector j * cantorSheetPlusProjector j = 0 := by
  apply LinearMap.ext
  intro f
  ext x
  by_cases hx : x j <;>
    simp [cantorSheetPlusProjector, cantorSheetMinusProjector, tilt, hx] <;>
      ring

theorem cantorSheetPlusProjector_mul_tilt (j : ℕ) :
    cantorSheetPlusProjector j * tilt j = cantorSheetPlusProjector j := by
  apply LinearMap.ext
  intro f
  ext x
  by_cases hx : x j <;>
    simp [cantorSheetPlusProjector, tilt, hx] <;> ring

theorem tilt_mul_cantorSheetPlusProjector (j : ℕ) :
    tilt j * cantorSheetPlusProjector j = cantorSheetPlusProjector j := by
  apply LinearMap.ext
  intro f
  ext x
  by_cases hx : x j <;>
    simp [cantorSheetPlusProjector, tilt, hx] <;> ring

theorem cantorSheetMinusProjector_mul_tilt (j : ℕ) :
    cantorSheetMinusProjector j * tilt j = - cantorSheetMinusProjector j := by
  apply LinearMap.ext
  intro f
  ext x
  by_cases hx : x j <;>
    simp [cantorSheetMinusProjector, tilt, hx] <;> ring

theorem tilt_mul_cantorSheetMinusProjector (j : ℕ) :
    tilt j * cantorSheetMinusProjector j = - cantorSheetMinusProjector j := by
  apply LinearMap.ext
  intro f
  ext x
  by_cases hx : x j <;>
    simp [cantorSheetMinusProjector, tilt, hx] <;> ring

theorem switch_conjugate_cantorSheetPlusProjector (j : ℕ) :
    switch j * cantorSheetPlusProjector j * switch j =
      cantorSheetMinusProjector j := by
  apply LinearMap.ext
  intro f
  ext x
  by_cases hx : x j <;>
    simp [cantorSheetPlusProjector, cantorSheetMinusProjector, tilt, switch,
      CantorBoundary.flipAt, hx, CantorBoundary.flipAt_involutive] <;> ring

theorem switch_conjugate_cantorSheetMinusProjector (j : ℕ) :
    switch j * cantorSheetMinusProjector j * switch j =
      cantorSheetPlusProjector j := by
  apply LinearMap.ext
  intro f
  ext x
  by_cases hx : x j <;>
      simp [cantorSheetPlusProjector, cantorSheetMinusProjector, tilt, switch,
      CantorBoundary.flipAt, hx, CantorBoundary.flipAt_involutive] <;> ring

theorem cantorSheetPlusProjector_mul_splitAtom (j : ℕ) :
    cantorSheetPlusProjector j * splitAtom j =
      splitAtom j * cantorSheetMinusProjector j := by
  apply LinearMap.ext
  intro f
  ext x
  by_cases hx : x j <;>
    simp [cantorSheetPlusProjector, cantorSheetMinusProjector, splitAtom,
      tilt, switch, CantorBoundary.flipAt, hx,
      CantorBoundary.flipAt_involutive] <;> ring

theorem cantorSheetMinusProjector_mul_splitAtom (j : ℕ) :
    cantorSheetMinusProjector j * splitAtom j =
      splitAtom j * cantorSheetPlusProjector j := by
  apply LinearMap.ext
  intro f
  ext x
  by_cases hx : x j <;>
    simp [cantorSheetPlusProjector, cantorSheetMinusProjector, splitAtom,
      tilt, switch, CantorBoundary.flipAt, hx,
      CantorBoundary.flipAt_involutive] <;> ring

theorem splitAtom_mul_cantorSheetPlusProjector (j : ℕ) :
    splitAtom j * cantorSheetPlusProjector j =
      cantorSheetMinusProjector j * splitAtom j := by
  symm
  exact cantorSheetMinusProjector_mul_splitAtom j

theorem splitAtom_mul_cantorSheetMinusProjector (j : ℕ) :
    splitAtom j * cantorSheetMinusProjector j =
      cantorSheetPlusProjector j * splitAtom j := by
  symm
  exact cantorSheetPlusProjector_mul_splitAtom j

theorem tilt_mul_switch_eq_neg_splitAtom (j : ℕ) :
    tilt j * switch j = - splitAtom j := by
  rw [splitAtom]
  exact tilt_switch_anticomm j

theorem tilt_mul_switch_sq (j : ℕ) :
    (tilt j * switch j) * (tilt j * switch j) =
      - (1 : ((ℕ → Bool) → ℝ) →ₗ[ℝ] ((ℕ → Bool) → ℝ)) := by
  apply LinearMap.ext
  intro f
  ext x
  by_cases hx : x j <;>
    simp [tilt, switch, CantorBoundary.flipAt, hx,
      CantorBoundary.flipAt_involutive]

theorem tilt_splitAtom_anticomm (j : ℕ) :
    tilt j * splitAtom j + splitAtom j * tilt j = 0 := by
  rw [tilt_mul_splitAtom, splitAtom_mul_tilt]
  simp

/-- The canonical real annihilation operator of the local split atom. -/
noncomputable def cantorAnnihilation (j : ℕ) :
    ((ℕ → Bool) → ℝ) →ₗ[ℝ] ((ℕ → Bool) → ℝ) :=
  (1 / 2 : ℝ) • (tilt j + splitAtom j)

/-- The canonical real creation operator of the local split atom. -/
noncomputable def cantorCreation (j : ℕ) :
    ((ℕ → Bool) → ℝ) →ₗ[ℝ] ((ℕ → Bool) → ℝ) :=
  (1 / 2 : ℝ) • (tilt j - splitAtom j)

theorem cantorAnnihilation_mul_comm_of_ne {i j : ℕ} (hij : i ≠ j) :
    cantorAnnihilation i * cantorAnnihilation j =
      cantorAnnihilation j * cantorAnnihilation i := by
  have hji : j ≠ i := by
    intro h
    exact hij h.symm
  simp only [cantorAnnihilation, smul_mul_assoc, mul_smul_comm, mul_add,
    add_mul]
  rw [tilt_comm, tilt_splitAtom_comm_of_ne hij,
    (tilt_splitAtom_comm_of_ne hji).symm, splitAtom_comm_of_ne hij]
  module

theorem cantorCreation_mul_comm_of_ne {i j : ℕ} (hij : i ≠ j) :
    cantorCreation i * cantorCreation j =
      cantorCreation j * cantorCreation i := by
  have hji : j ≠ i := by
    intro h
    exact hij h.symm
  simp only [cantorCreation, smul_mul_assoc, mul_smul_comm, mul_sub,
    sub_mul]
  rw [tilt_comm, tilt_splitAtom_comm_of_ne hij,
    (tilt_splitAtom_comm_of_ne hji).symm, splitAtom_comm_of_ne hij]
  module

theorem cantorAnnihilation_mul_creation_comm_of_ne {i j : ℕ} (hij : i ≠ j) :
    cantorAnnihilation i * cantorCreation j =
      cantorCreation j * cantorAnnihilation i := by
  have hji : j ≠ i := by
    intro h
    exact hij h.symm
  simp only [cantorAnnihilation, cantorCreation, smul_mul_assoc,
    mul_smul_comm, mul_add, add_mul, mul_sub, sub_mul]
  rw [tilt_comm, tilt_splitAtom_comm_of_ne hij,
    (tilt_splitAtom_comm_of_ne hji).symm, splitAtom_comm_of_ne hij]
  module

theorem cantorCreation_mul_annihilation_comm_of_ne {i j : ℕ} (hij : i ≠ j) :
    cantorCreation i * cantorAnnihilation j =
      cantorAnnihilation j * cantorCreation i := by
  have hji : j ≠ i := by
    intro h
    exact hij h.symm
  simp only [cantorAnnihilation, cantorCreation, smul_mul_assoc,
    mul_smul_comm, mul_add, add_mul, mul_sub, sub_mul]
  rw [tilt_comm, tilt_splitAtom_comm_of_ne hij,
    (tilt_splitAtom_comm_of_ne hji).symm, splitAtom_comm_of_ne hij]
  module

theorem cantorAnnihilation_sq (j : ℕ) :
    cantorAnnihilation j * cantorAnnihilation j = 0 := by
  simp only [cantorAnnihilation, smul_mul_assoc, mul_smul_comm, mul_add,
    add_mul, tilt_sq, splitAtom_sq, tilt_mul_splitAtom, splitAtom_mul_tilt]
  module

theorem cantorCreation_sq (j : ℕ) :
    cantorCreation j * cantorCreation j = 0 := by
  simp only [cantorCreation, smul_mul_assoc, mul_smul_comm, mul_sub, sub_mul,
    tilt_sq, splitAtom_sq, tilt_mul_splitAtom, splitAtom_mul_tilt]
  module

theorem cantorCAR_anticommutator (j : ℕ) :
    cantorAnnihilation j * cantorCreation j +
        cantorCreation j * cantorAnnihilation j = 1 := by
  simp only [cantorAnnihilation, cantorCreation, smul_mul_assoc,
    mul_smul_comm, mul_add, add_mul, mul_sub, sub_mul, tilt_sq,
    splitAtom_sq, tilt_mul_splitAtom, splitAtom_mul_tilt]
  module

theorem cantorAnnihilation_mul_creation_eq_neg_half_tilt_mul_splitAtom
    (j : ℕ) :
    cantorAnnihilation j * cantorCreation j =
      (1 / 2 : ℝ) • (1 + switch j) := by
  simp only [cantorAnnihilation, cantorCreation, smul_mul_assoc,
    mul_smul_comm, mul_add, add_mul, mul_sub, sub_mul, tilt_sq,
    splitAtom_sq, tilt_mul_splitAtom, splitAtom_mul_tilt]
  module

theorem cantorCreation_mul_annihilation_eq_half_tilt_mul_splitAtom
    (j : ℕ) :
    cantorCreation j * cantorAnnihilation j =
      (1 / 2 : ℝ) • (1 - switch j) := by
  simp only [cantorAnnihilation, cantorCreation, smul_mul_assoc,
    mul_smul_comm, mul_add, add_mul, mul_sub, sub_mul, tilt_sq,
    splitAtom_sq, tilt_mul_splitAtom, splitAtom_mul_tilt]
  module

theorem cantorAnnihilation_commutator_creation (j : ℕ) :
    cantorAnnihilation j * cantorCreation j -
        cantorCreation j * cantorAnnihilation j =
      switch j := by
  rw [cantorAnnihilation_mul_creation_eq_neg_half_tilt_mul_splitAtom,
    cantorCreation_mul_annihilation_eq_half_tilt_mul_splitAtom]
  module

end CantorBoundaryFunctionSpace

end InfoGeometry.Canonical.CantorBoundarySplitClifford
