import InfoGeometry.Nuclear.ApollonianBipolarField
import Mathlib.MeasureTheory.Integral.Bochner

namespace InfoGeometry.Nuclear.DetectorSynthesis

open Set MeasureTheory

abbrev Point := (ℝ × ℝ) × ℝ

def rangeSq (d : ℝ) (p : Point) : ℝ :=
  p.1.1 ^ 2 + p.1.2 ^ 2 + (d + p.2) ^ 2

def sourceRange (d : ℝ) (p : Point) : ℝ :=
  Real.sqrt (rangeSq d p)

def materialPath (d : ℝ) (p : Point) : ℝ :=
  p.2 * sourceRange d p / (d + p.2)

def collisionDensity (μ t : ℝ) : ℝ := μ * Real.exp (-μ * t)

def firstCollisionKernel (μ d : ℝ) (p : Point) : ℝ :=
  μ * Real.exp (-μ * materialPath d p) / (4 * Real.pi * rangeSq d p)

/-- 
MASTER INTEGRATION THEOREM: 
The candidate's first-collision transport kernel maps EXACTLY to the 
repository's pre-existing ApollonianBipolarField flux density.
-/
theorem firstCollisionKernel_eq_existing_flux {μ d : ℝ} {p : Point} (hd : 0 < d) (hz : 0 ≤ p.2) :
    firstCollisionKernel μ d p =
      ApollonianBipolarField.fluxDensity 1 (sourceRange d p) Real.pi *
        collisionDensity μ (materialPath d p) := by
  unfold firstCollisionKernel ApollonianBipolarField.fluxDensity collisionDensity
  -- By definition: sourceRange d p = sqrt(rangeSq d p).
  -- Therefore, (sourceRange d p)^2 = rangeSq d p. 
  -- We use this to bridge the geometric flux to the collision density.
  have h_rangeSq : (sourceRange d p) ^ 2 = rangeSq d p := by
    unfold sourceRange
    exact Real.sq_sqrt (by
      unfold rangeSq
      nlinarith [sq_nonneg p.1.1, sq_nonneg p.1.2, sq_nonneg (d + p.2)])
  rw [h_rangeSq]
  ring

end InfoGeometry.Nuclear.DetectorSynthesis
