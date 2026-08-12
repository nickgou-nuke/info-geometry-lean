import Mathlib.Tactic
import InfoGeometry.Canonical.SplitOctonionQuaternionPolar
import InfoGeometry.Canonical.SplitOctonionExpLog

noncomputable section

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SplitOctonion

@[simp] lemma H_star_smul (r : ℝ) (x : H) : star (r • x) = r • star x := by
  ext <;> simp

@[simp] lemma H_neg_smul_mul_neg_smul (r s : ℝ) (x y : H) :
    -(r • x) * -(s • y) = (r * s) • (x * y) := by
  ext <;> simp <;> ring

@[simp] lemma H_neg_smul_mul_smul (r s : ℝ) (x y : H) :
    -(r • x) * (s • y) = -(r * s) • (x * y) := by
  ext <;> simp <;> ring

@[simp] lemma H_smul_mul_neg_smul (r s : ℝ) (x y : H) :
    (r • x) * -(s • y) = -(r * s) • (x * y) := by
  ext <;> simp <;> ring

@[simp] lemma H_mul_smul (s : ℝ) (x y : H) :
    x * (s • y) = s • (x * y) := by
  ext <;> simp <;> ring

@[simp] lemma H_smul_mul (r : ℝ) (x y : H) :
    (r • x) * y = r • (x * y) := by
  ext <;> simp <;> ring

@[simp] lemma H_neg_smul_mul (r : ℝ) (x y : H) :
    -(r • x) * y = -(r) • (x * y) := by
  ext <;> simp <;> ring

@[simp] lemma H_mul_neg_smul (s : ℝ) (x y : H) :
    x * -(s • y) = -(s) • (x * y) := by
  ext <;> simp <;> ring

def hyperbolicProjPlus (g : H) : SplitOctonion :=
  (1 / 2 : ℝ) • (1 + J_g g)

def hyperbolicProjMinus (g : H) : SplitOctonion :=
  (1 / 2 : ℝ) • (1 - J_g g)

attribute [local simp] SplitOctonion.mul_a SplitOctonion.mul_b SplitOctonion.add_a SplitOctonion.add_b SplitOctonion.smul_a SplitOctonion.smul_b SplitOctonion.one_a SplitOctonion.one_b SplitOctonion.zero_a SplitOctonion.zero_b SplitOctonion.neg_a SplitOctonion.neg_b SplitOctonion.sub_a SplitOctonion.sub_b J_g H_star_smul H_smul_mul_smul H_star_mul_self star_neg neg_mul mul_neg neg_neg smul_neg mul_smul_comm

lemma smul_mul_smul_SO (r s : ℝ) (X Y : SplitOctonion) :
    (r • X) * (s • Y) = (r * s) • (X * Y) := by
  apply SplitOctonion.ext
  · ext <;> simp <;> ring_nf
  · ext <;> simp <;> ring_nf

lemma smul_mul_SO (r : ℝ) (X Y : SplitOctonion) :
    (r • X) * Y = r • (X * Y) := by
  apply SplitOctonion.ext
  · ext <;> simp
  · ext <;> simp

lemma mul_smul_SO (r : ℝ) (X Y : SplitOctonion) :
    X * (r • Y) = r • (X * Y) := by
  apply SplitOctonion.ext
  · ext <;> simp
  · ext <;> simp

theorem hyperbolicProjPlus_sq (g : H) (hg : Quaternion.normSq g = 1) :
    hyperbolicProjPlus g * hyperbolicProjPlus g = hyperbolicProjPlus g := by
  unfold hyperbolicProjPlus
  apply SplitOctonion.ext
  · ext <;> simp [hg] <;> ring_nf
  · ext <;> simp [hg] <;> ring_nf

theorem hyperbolicProjMinus_sq (g : H) (hg : Quaternion.normSq g = 1) :
    hyperbolicProjMinus g * hyperbolicProjMinus g = hyperbolicProjMinus g := by
  unfold hyperbolicProjMinus
  apply SplitOctonion.ext
  · ext <;> simp [hg] <;> ring_nf
  · ext <;> simp [hg] <;> ring_nf

theorem hyperbolicProjPlus_mul_minus (g : H) (hg : Quaternion.normSq g = 1) :
    hyperbolicProjPlus g * hyperbolicProjMinus g = 0 := by
  unfold hyperbolicProjPlus hyperbolicProjMinus
  apply SplitOctonion.ext
  · ext <;> simp [hg]
  · ext <;> simp [hg]

theorem hyperbolicProjMinus_mul_plus (g : H) (hg : Quaternion.normSq g = 1) :
    hyperbolicProjMinus g * hyperbolicProjPlus g = 0 := by
  unfold hyperbolicProjPlus hyperbolicProjMinus
  apply SplitOctonion.ext
  · ext <;> simp [hg]
  · ext <;> simp [hg]

theorem hyperbolicProjPlus_add_minus (g : H) :
    hyperbolicProjPlus g + hyperbolicProjMinus g = 1 := by
  unfold hyperbolicProjPlus hyperbolicProjMinus
  apply SplitOctonion.ext
  · ext <;> simp <;> ring_nf
  · ext <;> simp

theorem J_g_mul_projPlus (g : H) (hg : Quaternion.normSq g = 1) :
    J_g g * hyperbolicProjPlus g = hyperbolicProjPlus g := by
  unfold hyperbolicProjPlus
  apply SplitOctonion.ext
  · ext <;> simp [hg]
  · ext <;> simp [hg]

theorem J_g_mul_projMinus (g : H) (hg : Quaternion.normSq g = 1) :
    J_g g * hyperbolicProjMinus g = -hyperbolicProjMinus g := by
  unfold hyperbolicProjMinus
  apply SplitOctonion.ext
  · ext <;> simp [hg]
  · ext <;> simp [hg]

theorem expHyperbolic_projector_decomposition (g : H) (_hg : Quaternion.normSq g = 1) (η : ℝ) :
    expHyperbolic 1 η (J_g g) =
      Real.exp η • hyperbolicProjPlus g +
      Real.exp (-η) • hyperbolicProjMinus g := by
  unfold hyperbolicProjPlus hyperbolicProjMinus expHyperbolic
  apply SplitOctonion.ext
  · have h1 : Real.cosh η = (Real.exp η + Real.exp (-η)) / 2 := Real.cosh_eq η
    rw [h1]
    ext <;> simp [_hg] <;> ring_nf
  · have h1 : Real.sinh η = (Real.exp η - Real.exp (-η)) / 2 := Real.sinh_eq η
    rw [h1]
    ext <;> simp [_hg] <;> ring_nf

end SplitOctonion
