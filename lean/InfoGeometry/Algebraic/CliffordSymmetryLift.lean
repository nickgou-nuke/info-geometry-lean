/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
/-
InfoGeometry/Algebraic/CliffordSymmetryLift.lean

Orthogonal-to-Clifford symmetry lift for the split quadratic carrier.

This file does not introduce modular generators or Pin/Spin elements.
It packages quadratic-form isometries, lifts them to Clifford algebra
automorphisms using Mathlib's `CliffordAlgebra.equivOfIsometry`, and
specializes the coordinate-less invariance results of
`InfoGeometry.Clifford.CoordinateLessCliffordInvariance` to `Cl_nn n`.
-/

import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebraic.SplitCliffordCarrier
import InfoGeometry.Clifford.CoordinateLessCliffordInvariance

noncomputable section

namespace InfoGeometry.Algebraic.SplitSignature

open InfoGeometry.Clifford
open InfoGeometry.Clifford.GradedGraceContraction
open InfoGeometry.Clifford.CoordinateLessCliffordInvariance
open InfoGeometry.OperatorAlgebra
open InfoGeometry.Riemannian

/--
A split quadratic symmetry is a quadratic-form isometry of the real split
carrier.

This is the correct input for a Clifford lift.
-/
structure SplitQuadraticSymmetry (n : ℕ) where
  iso : (splitQuadraticForm n).IsometryEquiv (splitQuadraticForm n)

namespace SplitQuadraticSymmetry

/-- Underlying linear equivalence of a split quadratic symmetry. -/
def toLinearEquiv {n : ℕ} (S : SplitQuadraticSymmetry n) :
    SplitModule n ≃ₗ[ℝ] SplitModule n :=
  S.iso

@[simp]
theorem toLinearEquiv_apply
    {n : ℕ} (S : SplitQuadraticSymmetry n) (v : SplitModule n) :
    S.toLinearEquiv v = S.iso v :=
  rfl

end SplitQuadraticSymmetry

/--
Clifford algebra automorphism induced by a split quadratic symmetry.

This is the canonical lift used by the split Clifford carrier.
-/
def splitCliffordLift (n : ℕ) (S : SplitQuadraticSymmetry n) :
    Cl_nn n ≃ₐ[ℝ] Cl_nn n :=
  CliffordAlgebra.equivOfIsometry S.iso

@[simp]
theorem splitCliffordLift_apply
    (n : ℕ) (S : SplitQuadraticSymmetry n) (x : Cl_nn n) :
    splitCliffordLift n S x = CliffordAlgebra.equivOfIsometry S.iso x :=
  rfl

/--
Any split quadratic symmetry yields a Clifford algebra automorphism.

This is the base gate for later rotor, Narain, and modular specializations.
-/
structure SplitCliffordSymmetry (n : ℕ) where
  lift : Cl_nn n ≃ₐ[ℝ] Cl_nn n

/-- Canonical packaging of the Clifford lift as a symmetry object. -/
def canonicalCliffordSymmetry (n : ℕ) (S : SplitQuadraticSymmetry n) :
    SplitCliffordSymmetry n where
  lift := splitCliffordLift n S

/-! ## Group Structure, SymmetryAction, and Coordinate-Less Invariance on `Cl_nn n` -/

namespace SplitQuadraticSymmetry

@[ext]
theorem ext {n : ℕ} {S T : SplitQuadraticSymmetry n} (h : S.iso = T.iso) : S = T := by
  cases S
  cases T
  cases h
  rfl

/-- Group structure on `SplitQuadraticSymmetry n`, transported directly from
`InfoGeometry.Clifford.quadraticIsometryEquivGroup (splitQuadraticForm n)`
without introducing any duplicate `Group (Q.IsometryEquiv Q)` instance. -/
noncomputable instance instGroup (n : ℕ) : Group (SplitQuadraticSymmetry n) where
  one := ⟨1⟩
  mul S T := ⟨S.iso * T.iso⟩
  inv S := ⟨S.iso⁻¹⟩
  mul_assoc S T U := by apply ext; exact mul_assoc S.iso T.iso U.iso
  one_mul S := by apply ext; exact one_mul S.iso
  mul_one S := by apply ext; exact mul_one S.iso
  inv_mul_cancel S := by apply ext; exact inv_mul_cancel S.iso

@[simp]
theorem one_iso (n : ℕ) : (1 : SplitQuadraticSymmetry n).iso = 1 :=
  rfl

@[simp]
theorem mul_iso {n : ℕ} (S T : SplitQuadraticSymmetry n) :
    (S * T).iso = S.iso * T.iso :=
  rfl

@[simp]
theorem inv_iso {n : ℕ} (S : SplitQuadraticSymmetry n) :
    S⁻¹.iso = S.iso⁻¹ :=
  rfl

end SplitQuadraticSymmetry

/-- Group isomorphism between `SplitQuadraticSymmetry n` and the native isometry
group `(splitQuadraticForm n).IsometryEquiv (splitQuadraticForm n)`. -/
def splitQuadraticSymmetryMulEquiv (n : ℕ) :
    SplitQuadraticSymmetry n ≃*
      ((splitQuadraticForm n).IsometryEquiv (splitQuadraticForm n)) where
  toFun := SplitQuadraticSymmetry.iso
  invFun := SplitQuadraticSymmetry.mk
  left_inv S := by cases S; rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Group homomorphism lifting `SplitQuadraticSymmetry n` into `Aut(Cl_nn n)`. -/
def splitCliffordLiftHom (n : ℕ) :
    SplitQuadraticSymmetry n →* (Cl_nn n ≃ₐ[ℝ] Cl_nn n) where
  toFun S := splitCliffordLift n S
  map_one' := by
    apply AlgEquiv.ext
    intro x
    change CliffordAlgebra.equivOfIsometry (QuadraticMap.IsometryEquiv.refl _) x = x
    rw [CliffordAlgebra.equivOfIsometry_refl]
    rfl
  map_mul' S T := by
    apply AlgEquiv.ext
    intro x
    change CliffordAlgebra.equivOfIsometry (T.iso.trans S.iso) x =
      CliffordAlgebra.equivOfIsometry S.iso (CliffordAlgebra.equivOfIsometry T.iso x)
    rw [← CliffordAlgebra.equivOfIsometry_trans]
    rfl

/-- Canonical `SymmetryAction` of `SplitQuadraticSymmetry n` on `Cl_nn n`. -/
def splitCliffordSymmetryAction (n : ℕ) :
    SymmetryAction (SplitQuadraticSymmetry n) (Cl_nn n) where
  act S := (splitCliffordLift n S).toRingEquiv
  act_one x := by
    change (splitCliffordLiftHom n 1) x = x
    rw [map_one]
    rfl
  act_mul S T x := by
    change (splitCliffordLiftHom n (S * T)) x =
      (splitCliffordLiftHom n S) ((splitCliffordLiftHom n T) x)
    rw [map_mul]
    rfl

@[simp]
theorem splitCliffordSymmetryAction_act_apply (n : ℕ) (S : SplitQuadraticSymmetry n)
    (x : Cl_nn n) :
    (splitCliffordSymmetryAction n).act S x = splitCliffordLift n S x :=
  rfl

/-- Canonical `OperatorSymmetryAction` of `SplitQuadraticSymmetry n` on `Cl_nn n`. -/
def splitCliffordOperatorSymmetryAction (n : ℕ) :
    OperatorSymmetryAction (SplitQuadraticSymmetry n) (Cl_nn n) where
  toFun S := splitCliffordLift n S⁻¹
  map_one' := by
    change splitCliffordLiftHom n (1⁻¹) = AlgEquiv.refl
    rw [inv_one, map_one]
    rfl
  map_mul' S T := by
    apply AlgEquiv.ext
    intro x
    change CliffordAlgebra.equivOfIsometry ((S * T)⁻¹.iso) x =
      CliffordAlgebra.equivOfIsometry (T⁻¹.iso)
        (CliffordAlgebra.equivOfIsometry (S⁻¹.iso) x)
    rw [mul_inv_rev, SplitQuadraticSymmetry.mul_iso]
    change CliffordAlgebra.equivOfIsometry (S⁻¹.iso.trans T⁻¹.iso) x = _
    rw [← CliffordAlgebra.equivOfIsometry_trans]
    rfl

@[simp]
theorem splitCliffordOperatorSymmetryAction_act_apply (n : ℕ)
    (S : SplitQuadraticSymmetry n) (x : Cl_nn n) :
    (splitCliffordOperatorSymmetryAction n).act S x = splitCliffordLift n S x := by
  change splitCliffordLift n (S⁻¹)⁻¹ x = splitCliffordLift n S x
  rw [inv_inv]

theorem toSymmetryAction_splitCliffordOperatorSymmetryAction (n : ℕ) :
    toSymmetryAction (splitCliffordOperatorSymmetryAction n) =
      splitCliffordSymmetryAction n := by
  dsimp [toSymmetryAction, splitCliffordSymmetryAction]
  congr 1

theorem splitCliffordLift_ι_sq (n : ℕ) (S : SplitQuadraticSymmetry n) (v : SplitModule n) :
    (CliffordAlgebra.ι (splitQuadraticForm n) (S.iso v)) ^ 2 =
      (CliffordAlgebra.ι (splitQuadraticForm n) v) ^ 2 :=
  ι_sq_equivOfIsometry S.iso v

theorem splitCliffordLift_involute (n : ℕ) (S : SplitQuadraticSymmetry n) (x : Cl_nn n) :
    CliffordAlgebra.involute (splitCliffordLift n S x) =
      splitCliffordLift n S (CliffordAlgebra.involute x) :=
  involute_equivOfIsometry S.iso x

theorem splitCliffordLift_reverse (n : ℕ) (S : SplitQuadraticSymmetry n) (x : Cl_nn n) :
    CliffordAlgebra.reverse (splitCliffordLift n S x) =
      splitCliffordLift n S (CliffordAlgebra.reverse x) :=
  reverse_equivOfIsometry S.iso x

theorem splitCliffordLift_evenOdd_map (n : ℕ) (S : SplitQuadraticSymmetry n) (i : ZMod 2) :
    (CliffordAlgebra.evenOdd (splitQuadraticForm n) i).map
        (splitCliffordLift n S).toLinearMap =
      CliffordAlgebra.evenOdd (splitQuadraticForm n) i :=
  evenOdd_map_equivOfIsometry S.iso i

theorem splitCliffordLift_mem_evenOdd_iff (n : ℕ) (S : SplitQuadraticSymmetry n)
    (i : ZMod 2) (x : Cl_nn n) :
    splitCliffordLift n S x ∈ CliffordAlgebra.evenOdd (splitQuadraticForm n) i ↔
      x ∈ CliffordAlgebra.evenOdd (splitQuadraticForm n) i :=
  equivOfIsometry_mem_evenOdd_iff S.iso i x

theorem splitCliffordLift_cliffordGradeProj (n : ℕ) (S : SplitQuadraticSymmetry n)
    (k : ℕ) (x : Cl_nn n) :
    splitCliffordLift n S (cliffordGradeProj (splitQuadraticForm n) k x) =
      cliffordGradeProj (splitQuadraticForm n) k (splitCliffordLift n S x) :=
  cliffordGradeProj_equivOfIsometry S.iso k x

theorem splitCliffordLift_hTrace_cl (n : ℕ) (S : SplitQuadraticSymmetry n) (x : Cl_nn n) :
    hTrace_cl (splitQuadraticForm n) (splitCliffordLift n S x) =
      hTrace_cl (splitQuadraticForm n) x :=
  hTrace_cl_equivOfIsometry S.iso x

/-- The symmetry-invariant subalgebra of `Cl_nn n` under `SplitQuadraticSymmetry n`
is precisely the scalar subalgebra `range (algebraMap ℝ (Cl_nn n))`. -/
theorem splitClifford_invariant_iff_scalar (n : ℕ) (x : Cl_nn n) :
    IsInvariant (splitCliffordSymmetryAction n) x ↔
      ∃ c : ℝ, x = algebraMap ℝ (Cl_nn n) c := by
  have hiff :
      IsInvariant (splitCliffordSymmetryAction n) x ↔
        IsInvariant (cliffordSymmetryAction (splitQuadraticForm n)) x := by
    constructor
    · intro hx g
      exact hx ⟨g⟩
    · intro hx S
      exact hx S.iso
  rw [hiff]
  exact isInvariant_cliffordSymmetryAction_iff_mem_range (splitQuadraticForm n) x


abbrev iso {n : ℕ} (S : SplitQuadraticSymmetry n) :=
  S


abbrev lift {n : ℕ} (S : SplitCliffordSymmetry n) :=
  S

end InfoGeometry.Algebraic.SplitSignature
