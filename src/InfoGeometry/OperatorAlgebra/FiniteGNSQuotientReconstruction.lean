/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.External.Auto.GNSQuotientFinite

noncomputable section
namespace InfoGeometry.OperatorAlgebra.FiniteGNSQuotientReconstruction
open GNSQuotientFinite

/-- Read the first column from a class in the existing GNS quotient. -/
def firstColumn (u : GNSSpace) : V2C :=
  Quotient.lift (fun A : M2C => fun i => A i 0)
    (by intro A B h; funext i; fin_cases i; exact h.1; exact h.2) u

@[simp] theorem firstColumn_class (A : M2C) (i : Fin 2) :
    firstColumn (gnsClass A) i = A i 0 := rfl

/-- The actual quotient is the existing two-dimensional column model. -/
def firstColumnEquiv : GNSSpace ≃ V2C where
  toFun := firstColumn
  invFun v := gnsClass (FiniteGNSConstruction.firstColumnMatrix v)
  left_inv u := by
    refine Quotient.inductionOn u ?_
    intro A
    apply Quotient.sound
    constructor <;> rfl
  right_inv v := by
    funext i
    simp [firstColumn, gnsClass, FiniteGNSConstruction.firstColumnMatrix]

@[simp] theorem firstColumnEquiv_class (A : M2C) (i : Fin 2) :
    firstColumnEquiv (gnsClass A) i = A i 0 := rfl

theorem firstColumnEquiv_representation (A : M2C) (u : GNSSpace) :
    firstColumnEquiv (representation A u) =
      FiniteGNSConstruction.pi A (firstColumnEquiv u) := by
  refine Quotient.inductionOn u ?_
  intro X
  funext i
  change (A * X) i 0 = FiniteGNSConstruction.pi A (fun j => X j 0) i
  rfl

theorem firstColumnEquiv_inner (u v : GNSSpace) :
    GNSQuotientFinite.inner u v =
      FiniteGNSConstruction.inner (firstColumnEquiv u) (firstColumnEquiv v) := by
  refine Quotient.inductionOn₂ u v ?_
  intro A B
  change innerRaw A B = FiniteGNSConstruction.inner (fun i => A i 0) (fun i => B i 0)
  rw [innerRaw_eq_first_column]
  simp [FiniteGNSConstruction.inner, Fin.sum_univ_two]

/-- Recover every matrix coefficient from its action on the two column classes. -/
theorem representation_entry_readback (A : M2C) (i j : Fin 2) :
    firstColumnEquiv (representation A
      (gnsClass (FiniteGNSConstruction.firstColumnMatrix (Pi.single j 1)))) i = A i j := by
  rw [firstColumnEquiv_representation]
  fin_cases j <;>
    simp [FiniteGNSConstruction.pi, FiniteGNSConstruction.matVec,
      FiniteGNSConstruction.firstColumnMatrix, Fin.sum_univ_two]

/-- The representation is faithful even though the class map is not injective. -/
theorem representation_eq_iff (A B : M2C) :
    representation A = representation B ↔ A = B := by
  constructor
  · intro h
    ext i j
    have he := congrArg (fun f : GNSSpace → GNSSpace =>
      firstColumnEquiv (f (gnsClass
        (FiniteGNSConstruction.firstColumnMatrix (Pi.single j 1)))) i) h
    simpa only [representation_entry_readback] using he
  · rintro rfl
    rfl

theorem representation_injective : Function.Injective representation :=
  fun A B h => (representation_eq_iff A B).mp h

end InfoGeometry.OperatorAlgebra.FiniteGNSQuotientReconstruction
