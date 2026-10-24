/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.ColeFuryEmbedding

namespace InfoGeometry.OperatorAlgebra.ColeFury
open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication

@[simp] theorem quadrantReadout_a (X : SplitOct) : quadrantReadout X 0 0 = X.a := by
  simp only [quadrantReadout, Matrix.add_apply, Matrix.smul_apply]
  norm_num [upperLeft, lowerRight, horizonUp, horizonDown]

@[simp] theorem quadrantReadout_b (X : SplitOct) : quadrantReadout X 16 16 = X.b := by
  simp only [quadrantReadout, Matrix.add_apply, Matrix.smul_apply]
  norm_num [upperLeft, lowerRight, horizonUp, horizonDown]

@[simp] theorem quadrantReadout_x (X : SplitOct) :
    quadrantReadout X 0 16 = X.x0 + X.x1 + X.x2 := by
  simp only [quadrantReadout, Matrix.add_apply, Matrix.smul_apply]
  norm_num [upperLeft, lowerRight, horizonUp, horizonDown]

@[simp] theorem quadrantReadout_y (X : SplitOct) :
    quadrantReadout X 16 0 = X.y0 + X.y1 + X.y2 := by
  simp only [quadrantReadout, Matrix.add_apply, Matrix.smul_apply]
  norm_num [upperLeft, lowerRight, horizonUp, horizonDown]

theorem quadrantReadout_eq_iff (X Y : SplitOct) :
    quadrantReadout X = quadrantReadout Y ↔
      X.a = Y.a ∧ X.b = Y.b ∧ X.x0 + X.x1 + X.x2 = Y.x0 + Y.x1 + Y.x2 ∧
      X.y0 + X.y1 + X.y2 = Y.y0 + Y.y1 + Y.y2 := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg (fun M : Spin32Matrix => M 0 0) h,
      by simpa using congrArg (fun M : Spin32Matrix => M 16 16) h,
      by simpa using congrArg (fun M : Spin32Matrix => M 0 16) h,
      by simpa using congrArg (fun M : Spin32Matrix => M 16 0) h⟩
  · rintro ⟨ha, hb, hx, hy⟩
    simp only [quadrantReadout, ha, hb, hx, hy]

/-- Canonical representative with the two color sums in coordinate zero. -/
def aggregateRepresentative (X : SplitOct) : SplitOct :=
  ⟨X.a, X.b, X.x0 + X.x1 + X.x2, 0, 0, X.y0 + X.y1 + X.y2, 0, 0⟩

/-- Four independent contrasts invisible to the aggregate readout. -/
def invisibleContrasts (r s t u : ℤ) : SplitOct :=
  ⟨0, 0, -r-s, r, s, -t-u, t, u⟩

theorem quadrantReadout_representative (X : SplitOct) :
    quadrantReadout (aggregateRepresentative X) = quadrantReadout X := by
  apply (quadrantReadout_eq_iff _ _).mpr
  simp [aggregateRepresentative]

theorem quadrantReadout_contrasts (r s t u : ℤ) :
    quadrantReadout (invisibleContrasts r s t u) = 0 := by
  rw [← embed_zero]
  change quadrantReadout (invisibleContrasts r s t u) = quadrantReadout (0 : SplitOct)
  apply (quadrantReadout_eq_iff _ _).mpr
  change (0 : ℤ) = 0 ∧ 0 = 0 ∧ -r-s+r+s = 0 ∧ -t-u+t+u = 0
  omega

theorem aggregate_reconstruction (X : SplitOct) :
    aggregateRepresentative X + invisibleContrasts X.x1 X.x2 X.y1 X.y2 = X := by
  ext <;> simp [aggregateRepresentative, invisibleContrasts]

theorem quadrantReadout_kernel_iff (X : SplitOct) :
    quadrantReadout X = 0 ↔ X = invisibleContrasts X.x1 X.x2 X.y1 X.y2 := by
  constructor
  · intro h
    have hc := (quadrantReadout_eq_iff X 0).mp (h.trans embed_zero.symm)
    change X.a = 0 ∧ X.b = 0 ∧ X.x0 + X.x1 + X.x2 = 0 ∧
      X.y0 + X.y1 + X.y2 = 0 at hc
    rcases hc with ⟨ha, hb, hx, hy⟩
    ext <;> simp_all [invisibleContrasts] <;> omega
  · intro h
    rw [h]
    exact quadrantReadout_contrasts _ _ _ _

end InfoGeometry.OperatorAlgebra.ColeFury
