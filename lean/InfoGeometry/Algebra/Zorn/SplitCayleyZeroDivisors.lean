import InfoGeometry.Algebra.Zorn.SplitCayleyStabilizer

/-!
# Split-Cayley idempotent and nilpotent packets over ℝ

Finite algebraic identities from the real split-octonion basis used in
arXiv:1511.05818v2.  This file makes no physical particle identification and
no `G₂` classification claim.
-/

namespace InfoGeometry.Algebra.Zorn.SplitCayleyZeroDivisors

noncomputable section

open InfoGeometry.Algebra.Zorn.ConcreteComposition
open InfoGeometry.Algebra.Zorn.SplitCayleyStabilizer

private theorem cell_ext {X Y : ZornCell ℝ}
    (hr : X.r = Y.r) (hs : X.s = Y.s)
    (hx1 : X.x1 = Y.x1) (hx2 : X.x2 = Y.x2) (hx3 : X.x3 = Y.x3)
    (hy1 : X.y1 = Y.y1) (hy2 : X.y2 = Y.y2) (hy3 : X.y3 = Y.y3) : X = Y := by
  cases X
  cases Y
  simp_all

@[simp] private theorem zero_r : (0 : ZornCell ℝ).r = 0 := rfl
@[simp] private theorem zero_s : (0 : ZornCell ℝ).s = 0 := rfl
@[simp] private theorem zero_x1 : (0 : ZornCell ℝ).x1 = 0 := rfl
@[simp] private theorem zero_x2 : (0 : ZornCell ℝ).x2 = 0 := rfl
@[simp] private theorem zero_x3 : (0 : ZornCell ℝ).x3 = 0 := rfl
@[simp] private theorem zero_y1 : (0 : ZornCell ℝ).y1 = 0 := rfl
@[simp] private theorem zero_y2 : (0 : ZornCell ℝ).y2 = 0 := rfl
@[simp] private theorem zero_y3 : (0 : ZornCell ℝ).y3 = 0 := rfl

def e11 : ZornCell ℝ := ⟨1, 0, 0, 0, 0, 0, 0, 0⟩
def e22 : ZornCell ℝ := ⟨0, 1, 0, 0, 0, 0, 0, 0⟩
def u1 : ZornCell ℝ := ⟨0, 0, 1, 0, 0, 0, 0, 0⟩
def v1 : ZornCell ℝ := ⟨0, 0, 0, 0, 0, 1, 0, 0⟩

def Dplus : ZornCell ℝ := ⟨1 / 2, 1 / 2, 1 / 2, 0, 0, 1 / 2, 0, 0⟩
def Dminus : ZornCell ℝ := ⟨1 / 2, 1 / 2, -(1 / 2), 0, 0, -(1 / 2), 0, 0⟩
def dplus : ZornCell ℝ := ⟨0, 1, 0, 0, 0, 0, 0, 0⟩
def dminus : ZornCell ℝ := ⟨1, 0, 0, 0, 0, 0, 0, 0⟩

abbrev Gplus : ZornCell ℝ := u1
abbrev Gminus : ZornCell ℝ := v1

@[simp] theorem Dplus_idempotent : Dplus * Dplus = Dplus := by
  change ZornCell.mulZ Dplus Dplus = Dplus
  apply cell_ext <;> norm_num [Dplus, ZornCell.mulZ]

@[simp] theorem Dminus_idempotent : Dminus * Dminus = Dminus := by
  change ZornCell.mulZ Dminus Dminus = Dminus
  apply cell_ext <;> norm_num [Dminus, ZornCell.mulZ]

@[simp] theorem dplus_idempotent : dplus * dplus = dplus := by
  change ZornCell.mulZ dplus dplus = dplus
  apply cell_ext <;> norm_num [dplus, ZornCell.mulZ]

@[simp] theorem dminus_idempotent : dminus * dminus = dminus := by
  change ZornCell.mulZ dminus dminus = dminus
  apply cell_ext <;> norm_num [dminus, ZornCell.mulZ]

@[simp] theorem Dplus_Dminus : Dplus * Dminus = 0 := by
  change ZornCell.mulZ Dplus Dminus = 0
  apply cell_ext <;> norm_num [Dplus, Dminus, ZornCell.mulZ]

@[simp] theorem dplus_dminus : dplus * dminus = 0 := by
  change ZornCell.mulZ dplus dminus = 0
  apply cell_ext <;> norm_num [dplus, dminus, ZornCell.mulZ]

theorem D_resolution : Dplus + Dminus = zornOne := by
  change ZornCell.addZ Dplus Dminus = zornOne
  apply cell_ext <;> norm_num [Dplus, Dminus, zornOne, ZornCell.addZ]

theorem d_resolution : dplus + dminus = zornOne := by
  change ZornCell.addZ dplus dminus = zornOne
  apply cell_ext <;> norm_num [dplus, dminus, zornOne, ZornCell.addZ]

@[simp] theorem Gplus_nilpotent : Gplus * Gplus = 0 := by
  change ZornCell.mulZ Gplus Gplus = 0
  apply cell_ext <;> norm_num [Gplus, u1, ZornCell.mulZ]

@[simp] theorem Gminus_nilpotent : Gminus * Gminus = 0 := by
  change ZornCell.mulZ Gminus Gminus = 0
  apply cell_ext <;> norm_num [Gminus, v1, ZornCell.mulZ]

theorem Gplus_Gminus : Gplus * Gminus = e11 := by
  change ZornCell.mulZ Gplus Gminus = e11
  apply cell_ext <;> norm_num [Gplus, Gminus, u1, v1, e11, ZornCell.mulZ]

theorem Gminus_Gplus : Gminus * Gplus = e22 := by
  change ZornCell.mulZ Gminus Gplus = e22
  apply cell_ext <;> norm_num [Gplus, Gminus, u1, v1, e22, ZornCell.mulZ]

theorem G_anticommutator : Gplus * Gminus + Gminus * Gplus = zornOne := by
  rw [Gplus_Gminus, Gminus_Gplus]
  change ZornCell.addZ e11 e22 = zornOne
  apply cell_ext <;> norm_num [e11, e22, zornOne, ZornCell.addZ]

@[simp] theorem detZ_Dplus : ZornCell.detZ Dplus = 0 := by
  unfold Dplus ZornCell.detZ
  norm_num

@[simp] theorem detZ_Dminus : ZornCell.detZ Dminus = 0 := by
  unfold Dminus ZornCell.detZ
  norm_num

@[simp] theorem detZ_dplus : ZornCell.detZ dplus = 0 := by
  unfold dplus ZornCell.detZ
  norm_num

@[simp] theorem detZ_dminus : ZornCell.detZ dminus = 0 := by
  unfold dminus ZornCell.detZ
  norm_num

@[simp] theorem detZ_Gplus : ZornCell.detZ Gplus = 0 := by
  unfold Gplus u1 ZornCell.detZ
  norm_num

@[simp] theorem detZ_Gminus : ZornCell.detZ Gminus = 0 := by
  unfold Gminus v1 ZornCell.detZ
  norm_num

end
end InfoGeometry.Algebra.Zorn.SplitCayleyZeroDivisors
