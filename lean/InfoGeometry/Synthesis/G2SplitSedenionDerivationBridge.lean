/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Lie.CanonicalZornDerivationDimension
import InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge
import InfoGeometry.Canonical.SplitOctonionClifford33Soldering
import InfoGeometry.Synthesis.Cl44LeftIdealSplitSedenionSynthesis
import InfoGeometry.Synthesis.SplitSedenionDerivationAnomaly

/-!
# Concrete 14-Parameter $G_2$ Star-Derivations on $\mathbb{O}_s$ and Diagonal Lift to $\mathbb{S}_s$

This module bridges the 14-parameter Zorn derivation family `parameterAction` from
`InfoGeometry.Lie.CanonicalZornDerivationDimension` with the Zorn split-octonion carrier
`ZornSplitOctonion ℝ` (`InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge`) and its
Cayley–Dickson doubled split-sedenion carrier `SplitSedenion ℝ`
(`InfoGeometry.Synthesis.Cl44LeftIdealSplitSedenionSynthesis`):

1. **Section 1 — Explicit Carrier Equivalence `ZornVectorMatrix ℝ ≃ ZornSplitOctonion ℝ`**:
   - Defines `zornVectorMatrixToSplitOctonion`, `splitOctonionToZornVectorMatrix`, and the
     equivalence `zornVectorMatrixEquiv : ZornVectorMatrix ℝ ≃ ZornSplitOctonion ℝ`.
   - Proves that `zornVectorMatrixEquiv` preserves addition (`zornVectorMatrixEquiv_add`),
     scalar multiplication (`zornVectorMatrixEquiv_smul`), and the non-associative Zorn
     multiplication (`zornVectorMatrixEquiv_mul`).

2. **Section 2 — Concrete 14-Parameter $G_2$ Star-Derivations on `ZornSplitOctonion ℝ`**:
   - Transports `parameterAction p` across `zornVectorMatrixEquiv` to define
     `zornG2Derivation (p : Params) : ZornSplitOctonion ℝ → ZornSplitOctonion ℝ`.
   - Proves additivity (`zornG2Derivation_add`), scalar homogeneity (`zornG2Derivation_smul`),
     the Leibniz derivation law for `zornMul` (`zornG2Derivation_leibniz`), commutation with
     the split-octonion involution `zornConj` (`zornG2Derivation_conj`), trace-vanishing
     (`zornG2Derivation_trace_zero`), and annihilation of `zornZero` and `zornOne`
     (`zornG2Derivation_zornZero`, `zornG2Derivation_zornOne`).

3. **Section 3 — Diagonal Lift of the 14-Parameter $G_2$ Family to `SplitSedenion ℝ`**:
   - Lifts `zornG2Derivation p` diagonally via `cdLift` to define
     `sedenionG2Derivation (p : Params) : SplitSedenion ℝ → SplitSedenion ℝ`.
   - Proves the Leibniz derivation law for `sedenionMul` (`sedenionG2Derivation_leibniz`),
     commutation with `sedenionConj` (`sedenionG2Derivation_conj`), and annihilation of the
     Cayley–Dickson doubling generator `sedenionEll = (0, 1)` (`sedenionG2Derivation_sedenionEll_zero`).
   - Defines the 14-coordinate parameter readout `readSedenionG2Params` on split-sedenion maps
     and proves `readSedenionG2Params_sedenionG2Derivation` and `sedenionG2Derivation_injective`.
-/

noncomputable section

namespace InfoGeometry.Synthesis.G2SplitSedenionDerivationBridge

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornVectorMatrix (E11 E22 U V)
open InfoGeometry.Lie.CanonicalZornDerivationDimension
open InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge
open InfoGeometry.Canonical.SplitOctonionParaKahlerNullCone
open InfoGeometry.Canonical.SplitOctonionClifford33Soldering
open InfoGeometry.Synthesis.Cl44LeftIdealSplitSedenionSynthesis
open InfoGeometry.Synthesis.SplitSedenionDerivationAnomaly

/-!
## Section 1: Algebra Equivalence `ZornVectorMatrix ℝ ≃ ZornSplitOctonion ℝ`
-/

/-- Maps a `ZornVectorMatrix ℝ` to the corresponding `ZornSplitOctonion ℝ` by matching
the Peircian components `(a, v, w, b)` with `(a, u, v, b)`. -/
def zornVectorMatrixToSplitOctonion (X : ZornVectorMatrix ℝ) : ZornSplitOctonion ℝ :=
  ⟨X.a, X.v, X.w, X.b⟩

/-- Inverse map sending a `ZornSplitOctonion ℝ` to `ZornVectorMatrix ℝ`. -/
def splitOctonionToZornVectorMatrix (z : ZornSplitOctonion ℝ) : ZornVectorMatrix ℝ :=
  ⟨z.a, z.u, z.v, z.b⟩

/-- Canonical carrier equivalence `ZornVectorMatrix ℝ ≃ ZornSplitOctonion ℝ`. -/
def zornVectorMatrixEquiv : ZornVectorMatrix ℝ ≃ ZornSplitOctonion ℝ where
  toFun := zornVectorMatrixToSplitOctonion
  invFun := splitOctonionToZornVectorMatrix
  left_inv X := by cases X; rfl
  right_inv z := by cases z; rfl

@[simp] theorem zornVectorMatrixEquiv_apply (X : ZornVectorMatrix ℝ) :
    zornVectorMatrixEquiv X = ⟨X.a, X.v, X.w, X.b⟩ := by
  cases X
  rfl

@[simp] theorem zornVectorMatrixEquiv_symm_apply (z : ZornSplitOctonion ℝ) :
    zornVectorMatrixEquiv.symm z = ⟨z.a, z.u, z.v, z.b⟩ := by
  cases z
  rfl

/-- `zornVectorMatrixEquiv` intertwines `ZornVectorMatrix.add` with `zornAdd`. -/
theorem zornVectorMatrixEquiv_add (X Y : ZornVectorMatrix ℝ) :
    zornVectorMatrixEquiv (ZornVectorMatrix.add X Y) =
      zornAdd (zornVectorMatrixEquiv X) (zornVectorMatrixEquiv Y) := by
  cases X
  cases Y
  rfl

/-- `zornVectorMatrixEquiv.symm` intertwines `zornAdd` with `ZornVectorMatrix.add`. -/
theorem zornVectorMatrixEquiv_symm_add (x y : ZornSplitOctonion ℝ) :
    zornVectorMatrixEquiv.symm (zornAdd x y) =
      ZornVectorMatrix.add (zornVectorMatrixEquiv.symm x) (zornVectorMatrixEquiv.symm y) := by
  cases x
  cases y
  rfl

/-- `zornVectorMatrixEquiv` intertwines `ZornVectorMatrix.smul` with `zornSmul`. -/
theorem zornVectorMatrixEquiv_smul (r : ℝ) (X : ZornVectorMatrix ℝ) :
    zornVectorMatrixEquiv (ZornVectorMatrix.smul r X) =
      zornSmul r (zornVectorMatrixEquiv X) := by
  cases X
  rfl

/-- `zornVectorMatrixEquiv.symm` intertwines `zornSmul` with `ZornVectorMatrix.smul`. -/
theorem zornVectorMatrixEquiv_symm_smul (r : ℝ) (x : ZornSplitOctonion ℝ) :
    zornVectorMatrixEquiv.symm (zornSmul r x) =
      ZornVectorMatrix.smul r (zornVectorMatrixEquiv.symm x) := by
  cases x
  rfl

/-- `zornVectorMatrixEquiv` intertwines the Zorn product `ZornVectorMatrix.mul` with `zornMul`. -/
theorem zornVectorMatrixEquiv_mul (X Y : ZornVectorMatrix ℝ) :
    zornVectorMatrixEquiv (ZornVectorMatrix.mul X Y) =
      zornMul (zornVectorMatrixEquiv X) (zornVectorMatrixEquiv Y) := by
  ext k
  · simp [zornVectorMatrixEquiv, zornVectorMatrixToSplitOctonion, ZornVectorMatrix.mul, zornMul,
      ZornVec3.dot, vec3Dot, Fin.sum_univ_three]
  · fin_cases k <;>
      simp [zornVectorMatrixEquiv, zornVectorMatrixToSplitOctonion, ZornVectorMatrix.mul, zornMul,
        ZornVec3.cross, vec3Cross]
  · fin_cases k <;>
      simp [zornVectorMatrixEquiv, zornVectorMatrixToSplitOctonion, ZornVectorMatrix.mul, zornMul,
        ZornVec3.cross, vec3Cross]
  · simp [zornVectorMatrixEquiv, zornVectorMatrixToSplitOctonion, ZornVectorMatrix.mul, zornMul,
      ZornVec3.dot, vec3Dot, Fin.sum_univ_three]
    ring

/-- `zornVectorMatrixEquiv.symm` intertwines `zornMul` with `ZornVectorMatrix.mul`. -/
theorem zornVectorMatrixEquiv_symm_mul (x y : ZornSplitOctonion ℝ) :
    zornVectorMatrixEquiv.symm (zornMul x y) =
      ZornVectorMatrix.mul (zornVectorMatrixEquiv.symm x) (zornVectorMatrixEquiv.symm y) := by
  apply zornVectorMatrixEquiv.injective
  rw [Equiv.apply_symm_apply, zornVectorMatrixEquiv_mul,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-!
## Section 2: Concrete 14-Parameter $G_2$ Star-Derivations on `ZornSplitOctonion ℝ`
-/

/-- The concrete 14-parameter $G_2$ derivation action transported to `ZornSplitOctonion ℝ`. -/
def zornG2Derivation (p : Params) (z : ZornSplitOctonion ℝ) : ZornSplitOctonion ℝ :=
  zornVectorMatrixEquiv (parameterAction p (zornVectorMatrixEquiv.symm z))

/-- `zornG2Derivation p` is additive with respect to `zornAdd`. -/
theorem zornG2Derivation_add (p : Params) (x y : ZornSplitOctonion ℝ) :
    zornG2Derivation p (zornAdd x y) =
      zornAdd (zornG2Derivation p x) (zornG2Derivation p y) := by
  have h := (parameterDerivation p).map_add'
    (zornVectorMatrixEquiv.symm x) (zornVectorMatrixEquiv.symm y)
  change parameterAction p
      (ZornVectorMatrix.add (zornVectorMatrixEquiv.symm x) (zornVectorMatrixEquiv.symm y)) =
    ZornVectorMatrix.add
      (parameterAction p (zornVectorMatrixEquiv.symm x))
      (parameterAction p (zornVectorMatrixEquiv.symm y)) at h
  unfold zornG2Derivation
  rw [zornVectorMatrixEquiv_symm_add, h, zornVectorMatrixEquiv_add]

/-- `zornG2Derivation p` is $\mathbb{R}$-homogeneous with respect to `zornSmul`. -/
theorem zornG2Derivation_smul (p : Params) (r : ℝ) (x : ZornSplitOctonion ℝ) :
    zornG2Derivation p (zornSmul r x) = zornSmul r (zornG2Derivation p x) := by
  have h := (parameterDerivation p).map_smul' r (zornVectorMatrixEquiv.symm x)
  change parameterAction p
      (ZornVectorMatrix.smul r (zornVectorMatrixEquiv.symm x)) =
    ZornVectorMatrix.smul r
      (parameterAction p (zornVectorMatrixEquiv.symm x)) at h
  unfold zornG2Derivation
  rw [zornVectorMatrixEquiv_symm_smul, h, zornVectorMatrixEquiv_smul]

/-- `zornG2Derivation p` satisfies the Leibniz derivation rule for `zornMul`. -/
theorem zornG2Derivation_leibniz (p : Params) (x y : ZornSplitOctonion ℝ) :
    zornG2Derivation p (zornMul x y) =
      zornAdd (zornMul (zornG2Derivation p x) y) (zornMul x (zornG2Derivation p y)) := by
  have h := (parameterDerivation p).map_mul'
    (zornVectorMatrixEquiv.symm x) (zornVectorMatrixEquiv.symm y)
  change parameterAction p
      (ZornVectorMatrix.mul (zornVectorMatrixEquiv.symm x) (zornVectorMatrixEquiv.symm y)) =
    ZornVectorMatrix.add
      (ZornVectorMatrix.mul (parameterAction p (zornVectorMatrixEquiv.symm x))
        (zornVectorMatrixEquiv.symm y))
      (ZornVectorMatrix.mul (zornVectorMatrixEquiv.symm x)
        (parameterAction p (zornVectorMatrixEquiv.symm y))) at h
  unfold zornG2Derivation
  rw [zornVectorMatrixEquiv_symm_mul, h, zornVectorMatrixEquiv_add,
    zornVectorMatrixEquiv_mul, zornVectorMatrixEquiv_mul,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- `zornG2Derivation p` commutes with the split-octonion involution `zornConj`. -/
theorem zornG2Derivation_conj (p : Params) (x : ZornSplitOctonion ℝ) :
    zornG2Derivation p (zornConj x) = zornConj (zornG2Derivation p x) := by
  ext k
  · simp [zornG2Derivation, zornVectorMatrixEquiv, zornVectorMatrixToSplitOctonion,
      splitOctonionToZornVectorMatrix, parameterAction, zornConj]
    ring
  · fin_cases k <;>
      (simp [zornG2Derivation, zornVectorMatrixEquiv, zornVectorMatrixToSplitOctonion,
        splitOctonionToZornVectorMatrix, parameterAction, zornConj]; ring)
  · fin_cases k <;>
      (simp [zornG2Derivation, zornVectorMatrixEquiv, zornVectorMatrixToSplitOctonion,
        splitOctonionToZornVectorMatrix, parameterAction, zornConj]; ring)
  · simp [zornG2Derivation, zornVectorMatrixEquiv, zornVectorMatrixToSplitOctonion,
      splitOctonionToZornVectorMatrix, parameterAction, zornConj]
    ring

/-- Every `zornG2Derivation p` lands in the trace-zero subspace `a + b = 0`. -/
theorem zornG2Derivation_trace_zero (p : Params) (x : ZornSplitOctonion ℝ) :
    (zornG2Derivation p x).a + (zornG2Derivation p x).b = 0 := by
  simp [zornG2Derivation, zornVectorMatrixEquiv, zornVectorMatrixToSplitOctonion,
    splitOctonionToZornVectorMatrix, parameterAction]

/-- `zornG2Derivation p` annihilates `zornZero`. -/
theorem zornG2Derivation_zornZero (p : Params) :
    zornG2Derivation p zornZero = zornZero := by
  ext k
  · simp [zornG2Derivation, zornVectorMatrixEquiv, zornVectorMatrixToSplitOctonion,
      splitOctonionToZornVectorMatrix, parameterAction, zornZero]
  · fin_cases k <;>
      simp [zornG2Derivation, zornVectorMatrixEquiv, zornVectorMatrixToSplitOctonion,
        splitOctonionToZornVectorMatrix, parameterAction, zornZero]
  · fin_cases k <;>
      simp [zornG2Derivation, zornVectorMatrixEquiv, zornVectorMatrixToSplitOctonion,
        splitOctonionToZornVectorMatrix, parameterAction, zornZero]
  · simp [zornG2Derivation, zornVectorMatrixEquiv, zornVectorMatrixToSplitOctonion,
      splitOctonionToZornVectorMatrix, parameterAction, zornZero]

/-- `zornG2Derivation p` annihilates the multiplicative identity `zornOne`. -/
theorem zornG2Derivation_zornOne (p : Params) :
    zornG2Derivation p zornOne = zornZero := by
  ext k
  · simp [zornG2Derivation, zornVectorMatrixEquiv, zornVectorMatrixToSplitOctonion,
      splitOctonionToZornVectorMatrix, parameterAction, zornOne, zornZero]
  · fin_cases k <;>
      simp [zornG2Derivation, zornVectorMatrixEquiv, zornVectorMatrixToSplitOctonion,
        splitOctonionToZornVectorMatrix, parameterAction, zornOne, zornZero]
  · fin_cases k <;>
      simp [zornG2Derivation, zornVectorMatrixEquiv, zornVectorMatrixToSplitOctonion,
        splitOctonionToZornVectorMatrix, parameterAction, zornOne, zornZero]
  · simp [zornG2Derivation, zornVectorMatrixEquiv, zornVectorMatrixToSplitOctonion,
      splitOctonionToZornVectorMatrix, parameterAction, zornOne, zornZero]

/-!
## Section 3: Diagonal Lift of the 14-Parameter $G_2$ Family to `SplitSedenion ℝ`
-/

/-- Diagonal Cayley–Dickson lift $D_p(a, b) = (D_p(a), D_p(b))$ of the 14-parameter
$G_2$ derivation family from `ZornSplitOctonion ℝ` to `SplitSedenion ℝ`. -/
def sedenionG2Derivation (p : Params) (X : SplitSedenion ℝ) : SplitSedenion ℝ :=
  cdLift (zornG2Derivation p) X

/-- Four-term `zornAdd` rearrangement for the first component of the Cayley–Dickson Leibniz expansion. -/
theorem zornAdd_rearrange_fst (a b c d : ZornSplitOctonion ℝ) :
    zornAdd (zornAdd a b) (zornAdd c d) = zornAdd (zornAdd a d) (zornAdd b c) := by
  ext k
  · dsimp [zornAdd]; ring
  · fin_cases k <;> (dsimp [zornAdd]; ring)
  · fin_cases k <;> (dsimp [zornAdd]; ring)
  · dsimp [zornAdd]; ring

/-- Four-term `zornAdd` rearrangement for the second component of the Cayley–Dickson Leibniz expansion. -/
theorem zornAdd_rearrange_snd (a b c d : ZornSplitOctonion ℝ) :
    zornAdd (zornAdd a b) (zornAdd c d) = zornAdd (zornAdd b c) (zornAdd a d) := by
  ext k
  · dsimp [zornAdd]; ring
  · fin_cases k <;> (dsimp [zornAdd]; ring)
  · fin_cases k <;> (dsimp [zornAdd]; ring)
  · dsimp [zornAdd]; ring

/-- `sedenionG2Derivation p` is additive on `SplitSedenion ℝ`. -/
theorem sedenionG2Derivation_add (p : Params) (X Y : SplitSedenion ℝ) :
    sedenionG2Derivation p (sedenionAdd X Y) =
      sedenionAdd (sedenionG2Derivation p X) (sedenionG2Derivation p Y) := by
  apply Prod.ext
  · dsimp [sedenionG2Derivation, cdLift, sedenionAdd]
    exact zornG2Derivation_add p X.1 Y.1
  · dsimp [sedenionG2Derivation, cdLift, sedenionAdd]
    exact zornG2Derivation_add p X.2 Y.2

/-- Every diagonally lifted 14-parameter $G_2$ map `sedenionG2Derivation p` is an exact
derivation of the non-associative split-sedenion multiplication `sedenionMul`. -/
theorem sedenionG2Derivation_leibniz (p : Params) (X Y : SplitSedenion ℝ) :
    sedenionG2Derivation p (sedenionMul X Y) =
      sedenionAdd (sedenionMul (sedenionG2Derivation p X) Y)
        (sedenionMul X (sedenionG2Derivation p Y)) := by
  apply Prod.ext
  · dsimp [sedenionG2Derivation, cdLift, sedenionMul, sedenionAdd]
    rw [zornG2Derivation_add, zornG2Derivation_leibniz, zornG2Derivation_leibniz,
      zornG2Derivation_conj]
    exact zornAdd_rearrange_fst _ _ _ _
  · dsimp [sedenionG2Derivation, cdLift, sedenionMul, sedenionAdd]
    rw [zornG2Derivation_add, zornG2Derivation_leibniz, zornG2Derivation_leibniz,
      zornG2Derivation_conj]
    exact zornAdd_rearrange_snd _ _ _ _

/-- `sedenionG2Derivation p` commutes with the Cayley–Dickson involution `sedenionConj`. -/
theorem sedenionG2Derivation_conj (p : Params) (X : SplitSedenion ℝ) :
    sedenionG2Derivation p (sedenionConj X) = sedenionConj (sedenionG2Derivation p X) := by
  apply Prod.ext
  · dsimp [sedenionG2Derivation, cdLift, sedenionConj]
    exact zornG2Derivation_conj p X.1
  · dsimp [sedenionG2Derivation, cdLift, sedenionConj]
    exact zornG2Derivation_smul p (-1 : ℝ) X.2

/-- `sedenionG2Derivation p` annihilates the Cayley–Dickson doubling unit `sedenionEll = (0, 1)`. -/
theorem sedenionG2Derivation_sedenionEll_zero (p : Params) :
    sedenionG2Derivation p sedenionEll = sedenionZero := by
  apply Prod.ext
  · dsimp [sedenionG2Derivation, cdLift, sedenionEll, sedenionZero]
    exact zornG2Derivation_zornZero p
  · dsimp [sedenionG2Derivation, cdLift, sedenionEll, sedenionZero]
    exact zornG2Derivation_zornOne p

/-- `sedenionG2Derivation p` annihilates the multiplicative identity `sedenionOne = (1, 0)`. -/
theorem sedenionG2Derivation_sedenionOne_zero (p : Params) :
    sedenionG2Derivation p sedenionOne = sedenionZero := by
  apply Prod.ext
  · dsimp [sedenionG2Derivation, cdLift, sedenionOne, sedenionZero]
    exact zornG2Derivation_zornOne p
  · dsimp [sedenionG2Derivation, cdLift, sedenionOne, sedenionZero]
    exact zornG2Derivation_zornZero p

/-- Canonical 14-coordinate parameter readout from a split-sedenion operator
`F : SplitSedenion ℝ → SplitSedenion ℝ`, evaluating the first-slot action on the
basis elements `E22, U 0, U 1, V 0, V 1, V 2`. -/
def readSedenionG2Params (F : SplitSedenion ℝ → SplitSedenion ℝ) : Params := fun i =>
  if i = 0 then ((F (zornVectorMatrixEquiv E22, zornZero)).1).v 0
  else if i = 1 then ((F (zornVectorMatrixEquiv (V 1), zornZero)).1).v 0
  else if i = 2 then ((F (zornVectorMatrixEquiv (V 2), zornZero)).1).v 0
  else if i = 3 then ((F (zornVectorMatrixEquiv E22, zornZero)).1).v 1
  else if i = 4 then ((F (zornVectorMatrixEquiv (U 0), zornZero)).1).v 1
  else if i = 5 then ((F (zornVectorMatrixEquiv (V 0), zornZero)).1).v 1
  else if i = 6 then ((F (zornVectorMatrixEquiv (V 1), zornZero)).1).v 1
  else if i = 7 then ((F (zornVectorMatrixEquiv (V 2), zornZero)).1).v 1
  else if i = 8 then ((F (zornVectorMatrixEquiv E22, zornZero)).1).v 2
  else if i = 9 then ((F (zornVectorMatrixEquiv (U 0), zornZero)).1).v 2
  else if i = 10 then ((F (zornVectorMatrixEquiv (U 1), zornZero)).1).v 2
  else if i = 11 then ((F (zornVectorMatrixEquiv (V 0), zornZero)).1).v 2
  else if i = 12 then ((F (zornVectorMatrixEquiv (V 1), zornZero)).1).v 2
  else ((F (zornVectorMatrixEquiv (V 2), zornZero)).1).v 2

/-- Reading the 14 canonical coordinates from `sedenionG2Derivation p` recovers `p` identically. -/
theorem readSedenionG2Params_sedenionG2Derivation (p : Params) :
    readSedenionG2Params (sedenionG2Derivation p) = p := by
  funext i
  fin_cases i <;>
    simp [readSedenionG2Params, sedenionG2Derivation, cdLift, zornG2Derivation,
      zornVectorMatrixEquiv, zornVectorMatrixToSplitOctonion,
      splitOctonionToZornVectorMatrix, parameterAction, E22, U, V, ZornVec3.basis]

/-- The 14-parameter diagonal $G_2$ derivation lift `sedenionG2Derivation` is injective. -/
theorem sedenionG2Derivation_injective :
    Function.Injective sedenionG2Derivation := by
  intro p q hpq
  have h := congrArg readSedenionG2Params hpq
  rw [readSedenionG2Params_sedenionG2Derivation p,
      readSedenionG2Params_sedenionG2Derivation q] at h
  exact h

end InfoGeometry.Synthesis.G2SplitSedenionDerivationBridge
