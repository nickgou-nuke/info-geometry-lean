import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.Canonical.KMSShearTubuleKleinPrimon

open Complex
open Real
open Matrix

variable {R : Type*} [CommRing R]

/-! ## 1. The KMS Strip & Midline Gliding Reflection (Klein Seam) -/

/-- Gliding reflection on the cylinder coordinates (σ, t):
    σ ↦ 1 - σ (reflection across midline 1/2) and t ↦ t + L/2. -/
def glideReflection (L : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (1 - p.1, p.2 + L / 2)

/-- The spatial reflection component σ ↦ 1 - σ is an involution. -/
theorem glide_sigma_involution (σ : ℝ) : 1 - (1 - σ) = σ := by
  ring

/-- 🏆 THEOREM: The fixed locus of the spatial reflection is precisely the critical midline σ = 1/2. -/
theorem glide_fixed_iff_midline (σ : ℝ) : 1 - σ = σ ↔ σ = 1 / 2 := by
  constructor
  · intro h; linarith
  · intro h; rw [h]; ring

/-- 🏆 THEOREM: Applying the glide reflection twice gives a pure translation by L along the tube axis. -/
theorem glide_squared (L : ℝ) (p : ℝ × ℝ) :
    glideReflection L (glideReflection L p) = (p.1, p.2 + L) := by
  dsimp [glideReflection]
  ext
  · ring
  · ring

/-! ## 2. Affine Sheared Helical Tubule Coordinates -/

/-- Sheared angle coordinate on the helical tubule: θ(σ, t) = ω t + α σ. -/
def shearedAngle (omega alpha : ℝ) (σ t : ℝ) : ℝ :=
  omega * t + alpha * σ

/-- Radius of the helical tubule: x² + y² = R². -/
theorem helical_radius_sq (R omega alpha σ t : ℝ) :
    let x := R * Real.cos (shearedAngle omega alpha σ t)
    let y := R * Real.sin (shearedAngle omega alpha σ t)
    x * x + y * y = R * R := by
  intro x y
  dsimp [x, y]
  calc (R * Real.cos (shearedAngle omega alpha σ t)) * (R * Real.cos (shearedAngle omega alpha σ t)) +
       (R * Real.sin (shearedAngle omega alpha σ t)) * (R * Real.sin (shearedAngle omega alpha σ t))
    _ = R * R * (Real.cos (shearedAngle omega alpha σ t) ^ 2 + Real.sin (shearedAngle omega alpha σ t) ^ 2) := by ring
    _ = R * R * 1 := by rw [Real.cos_sq_add_sin_sq]
    _ = R * R := by ring

/-- Helical angle period: shifting t by 2π / ω advances the angle by 2π. -/
theorem helical_angle_period (omega alpha σ t : ℝ) (h_om : omega ≠ 0) :
    shearedAngle omega alpha σ (t + 2 * Real.pi / omega) =
      shearedAngle omega alpha σ t + 2 * Real.pi := by
  dsimp [shearedAngle]
  calc omega * (t + 2 * Real.pi / omega) + alpha * σ
    _ = omega * t + omega * (2 * Real.pi / omega) + alpha * σ := by ring
    _ = omega * t + 2 * Real.pi + alpha * σ := by rw [mul_div_cancel₀ (2 * Real.pi) h_om]
    _ = (omega * t + alpha * σ) + 2 * Real.pi := by ring

/-! ## 3. Bost-Connes Primon Gas & Logarithmic Caliper (Surprisal Metric) -/

/-- Single-particle primon surprisal / energy: E(n) = log n. -/
def primonEnergy (n : ℝ) : ℝ :=
  Real.log n

/-- 🏆 THEOREM: Additivity of primon surprisal on products:
    log(m * n) = log m + log n. -/
theorem primon_energy_add (m n : ℝ) (hm : 0 < m) (hn : 0 < n) :
    primonEnergy (m * n) = primonEnergy m + primonEnergy n := by
  dsimp [primonEnergy]
  exact Real.log_mul (ne_of_gt hm) (ne_of_gt hn)

/-- Surprisal energy gap created by prime p scaling: E(p * n) - E(n) = log p. -/
theorem primon_energy_shift (p n : ℝ) (hp : 0 < p) (hn : 0 < n) :
    primonEnergy (p * n) - primonEnergy n = primonEnergy p := by
  rw [primon_energy_add p n hp hn]
  ring

/-- Monodromy phase winding: the phase factor is 1 at integer multiples of the period 2π. -/
theorem primon_caliper_period (k : ℤ) :
    Real.cos ((k : ℝ) * (2 * Real.pi)) = 1 := by
  have : (k : ℝ) * (2 * Real.pi) = (k : ℝ) * (2 * Real.pi) + 0 := by ring
  exact Real.cos_int_mul_two_pi k

/-! ## 4. Cayley Projection of the Critical Line to the Unit Circle -/

/-- The Cayley coordinate of a point on the critical line s = 1/2 + i t:
    W(t) = (-1 + i t) / (1 + i t). -/
def cayleyCritical (t : ℝ) : ℂ :=
  (-1 + (t : ℂ) * Complex.I) / (1 + (t : ℂ) * Complex.I)

/-- 🏆 THEOREM: The squared norm of the Cayley projection on the critical line is 1:
    |W(t)|² = 1. -/
theorem cayley_critical_normSq (t : ℝ) :
    Complex.normSq (cayleyCritical t) = 1 := by
  dsimp [cayleyCritical]
  rw [Complex.normSq_div]
  have hnum : Complex.normSq (-1 + (t : ℂ) * Complex.I) = 1 + t^2 := by
    simp [Complex.normSq]
    ring
  have hden : Complex.normSq (1 + (t : ℂ) * Complex.I) = 1 + t^2 := by
    simp [Complex.normSq]
    ring
  rw [hnum, hden]
  have hpos : (1 + t^2 : ℝ) ≠ 0 := by positivity
  exact div_self hpos

/-! ## 5. The CPT Clifford Atom & C₂ᵥ Symmetry -/

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ

/-- Scale signum / parity involution generator: ε = !![0, 1; 1, 0]. -/
def atomEps : M2R := !![0, 1; 1, 0]

/-- Modular conjugation / glide generator: J = !![0, -1; 1, 0]. -/
def atomJ : M2R := !![0, -1; 1, 0]

/-- CPT product: CPT = ε * J. -/
def atomCPT : M2R := atomEps * atomJ

/-- 🏆 THEOREM: ε² = 1. -/
theorem atomEps_sq : atomEps * atomEps = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [atomEps]

/-- 🏆 THEOREM: J² = -1. -/
theorem atomJ_sq : atomJ * atomJ = (-1 : ℝ) • (1 : M2R) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [atomJ]

/-- 🏆 THEOREM: Anticommutation: ε J + J ε = 0. -/
theorem atomEps_J_anticomm : atomEps * atomJ + atomJ * atomEps = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [atomEps, atomJ]

/-- 🏆 THEOREM: CPT² = 1. -/
theorem atomCPT_sq : atomCPT * atomCPT = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [atomCPT, atomEps, atomJ]

/-! ## 6. Grand Synthesis Packet -/

structure KMSShearTubuleKleinPrimonPacket where
  glide_sigma_invol : ∀ σ : ℝ, 1 - (1 - σ) = σ
  glide_midline_fix : ∀ σ : ℝ, 1 - σ = σ ↔ σ = 1 / 2
  glide_double : ∀ L : ℝ, ∀ p : ℝ × ℝ, glideReflection L (glideReflection L p) = (p.1, p.2 + L)
  helical_rad : ∀ R omega alpha σ t : ℝ,
    let x := R * Real.cos (shearedAngle omega alpha σ t)
    let y := R * Real.sin (shearedAngle omega alpha σ t)
    x * x + y * y = R * R
  primon_additive : ∀ m n : ℝ, 0 < m → 0 < n → primonEnergy (m * n) = primonEnergy m + primonEnergy n
  primon_caliper : ∀ k : ℤ, Real.cos ((k : ℝ) * (2 * Real.pi)) = 1
  cayley_circle : ∀ t : ℝ, Complex.normSq (cayleyCritical t) = 1
  cpt_eps_sq : atomEps * atomEps = 1
  cpt_j_sq : atomJ * atomJ = (-1 : ℝ) • (1 : M2R)
  cpt_anticomm : atomEps * atomJ + atomJ * atomEps = 0
  cpt_sq : atomCPT * atomCPT = 1

def makeKMSShearTubuleKleinPrimonPacket : KMSShearTubuleKleinPrimonPacket where
  glide_sigma_invol := glide_sigma_involution
  glide_midline_fix := glide_fixed_iff_midline
  glide_double := glide_squared
  helical_rad := helical_radius_sq
  primon_additive := primon_energy_add
  primon_caliper := primon_caliper_period
  cayley_circle := cayley_critical_normSq
  cpt_eps_sq := atomEps_sq
  cpt_j_sq := atomJ_sq
  cpt_anticomm := atomEps_J_anticomm
  cpt_sq := atomCPT_sq

theorem kms_shear_tubule_klein_primon_certified :
    atomCPT * atomCPT = 1 :=
  makeKMSShearTubuleKleinPrimonPacket.cpt_sq

end InfoGeometry.Canonical.KMSShearTubuleKleinPrimon
