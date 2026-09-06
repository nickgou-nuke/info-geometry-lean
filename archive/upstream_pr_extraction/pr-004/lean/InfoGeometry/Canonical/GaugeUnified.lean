import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.Ring
import Architect
import InfoGeometry.Canonical.FormalScaffold

namespace InfoGeometry.Canonical.Gauge

abbrev Plane := ℝ × ℝ

@[blueprint "def:gauge-signature"]
inductive Signature
  | euclid
  | split

def quad : Signature → Plane → ℝ
  | .euclid, (x, y) => x^2 + y^2
  | .split,  (x, y) => x^2 - y^2

def bilinear : Signature → Plane → Plane → ℝ
  | .euclid, (x1, y1), (x2, y2) => x1 * x2 + y1 * y2
  | .split,  (x1, y1), (x2, y2) => x1 * x2 - y1 * y2

noncomputable def rot (θ : ℝ) : Plane → Plane :=
  fun (x, y) => (Real.cos θ * x - Real.sin θ * y, Real.sin θ * x + Real.cos θ * y)

noncomputable def boost (φ : ℝ) : Plane → Plane :=
  fun (x, y) => (Real.cosh φ * x + Real.sinh φ * y, Real.sinh φ * x + Real.cosh φ * y)

noncomputable def act (σ : Signature) (t : ℝ) : Plane → Plane :=
  match σ with
  | .euclid => rot t
  | .split  => boost t

lemma rot_preserves_bilinear (θ : ℝ) (u v : Plane) :
    bilinear .euclid (rot θ u) (rot θ v) = bilinear .euclid u v := by
  rcases u with ⟨x1, y1⟩; rcases v with ⟨x2, y2⟩
  unfold bilinear rot
  simp only
  calc
    (Real.cos θ * x1 - Real.sin θ * y1) * (Real.cos θ * x2 - Real.sin θ * y2) +
    (Real.sin θ * x1 + Real.cos θ * y1) * (Real.sin θ * x2 + Real.cos θ * y2)
      = x1 * x2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) + y1 * y2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by ring
    _ = x1 * x2 * 1 + y1 * y2 * 1 := by rw [Real.cos_sq_add_sin_sq]
    _ = x1 * x2 + y1 * y2 := by ring

lemma boost_preserves_bilinear (φ : ℝ) (u v : Plane) :
    bilinear .split (boost φ u) (boost φ v) = bilinear .split u v := by
  rcases u with ⟨x1, y1⟩; rcases v with ⟨x2, y2⟩
  unfold bilinear boost
  simp only
  calc
    (Real.cosh φ * x1 + Real.sinh φ * y1) * (Real.cosh φ * x2 + Real.sinh φ * y2) -
    (Real.sinh φ * x1 + Real.cosh φ * y1) * (Real.sinh φ * x2 + Real.cosh φ * y2)
      = x1 * x2 * (Real.cosh φ ^ 2 - Real.sinh φ ^ 2) - y1 * y2 * (Real.cosh φ ^ 2 - Real.sinh φ ^ 2) := by ring
    _ = x1 * x2 * 1 - y1 * y2 * 1 := by rw [Real.cosh_sq_sub_sinh_sq]
    _ = x1 * x2 - y1 * y2 := by ring

@[blueprint "thm:gauge-action-preserves-bilinear"]
theorem act_preserves_bilinear (σ : Signature) (t : ℝ) (u v : Plane) :
    bilinear σ (act σ t u) (act σ t v) = bilinear σ u v := by
  cases σ
  · exact rot_preserves_bilinear t u v
  · exact boost_preserves_bilinear t u v

end InfoGeometry.Canonical.Gauge
