import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Nuclear Coincidence Cross-Section Duality and Target-Detector Scattering

Formalizes the dual-area structure of gamma-ray coincidence spectrometry:
- The detector acts as a macroscopic scattering/absorption target.
- `Speak`: Partial photopeak capture cross-section for transition gamma_i.
- `Sv`: Total absorption cross-section envelope for companion gamma_j.
- `peak_to_total_cross_ratio`: The cross-quotient recovers the intrinsic Peak-to-Total ratio (P/T)_i.
- Activity cancellation: absolute activity A drops out through coincidence matching.

All theorems verified constructively in Lean 4 with 0 `sorry`s and 0 custom axioms.
-/

noncomputable section

namespace InfoGeometry.Nuclear.CrossSectionDuality

/-! ### 1. Cascade Spectrometric Parameters -/

/-- Parameters defining a two-photon coincidence cascade in a semiconductor detector:
    - `a`   : Coincidence linearizer slope (> 0)
    - `W0`  : Angular correlation factor at zero degrees (> 0)
    - `Pi`  : Transition emission probability for gamma_i (> 0)
    - `Pj`  : Transition emission probability for gamma_j (> 0)
    - `Pij` : Cascade coincidence branching ratio (> 0)
    - `Ci`  : Linear singles transmission coefficient for gamma_i (> 0)
    - `Cj`  : Linear singles transmission coefficient for gamma_j (> 0)
    - `Bj`  : Coincidence summing-out loss coefficient for gamma_j (> 0) -/
structure CascadeModel where
  a   : ℝ
  W0  : ℝ
  Pi  : ℝ
  Pj  : ℝ
  Pij : ℝ
  Ci  : ℝ
  Cj  : ℝ
  Bj  : ℝ
  ha  : 0 < a
  hW0 : 0 < W0
  hPi : 0 < Pi
  hPj : 0 < Pj
  hPij: 0 < Pij
  hCi : 0 < Ci
  hCj : 0 < Cj
  hBj : 0 < Bj

/-- Source activity A dynamically derived from coincidence parameter matching:
    A = C_i * C_j * (P_ij / (P_i * P_j)) * W(0). -/
def derivedActivity (m : CascadeModel) : ℝ :=
  m.Ci * m.Cj * (m.Pij / (m.Pi * m.Pj)) * m.W0

/-- Partial Photopeak Cross-Section (Restored Linear Channel):
    S^(peak)_i = 4π * C_i / (A * P_i * a²). -/
def Speak (m : CascadeModel) (pi : ℝ) : ℝ :=
  (4 * pi * m.Ci) / (derivedActivity m * m.Pi * m.a^2)

/-- Total Absorption Cross-Section Envelope (Virtual Summing Area of Partner j):
    S_v,j = 4π * B_j / (C_j * a²). -/
def Sv (m : CascadeModel) (pi : ℝ) : ℝ :=
  (4 * pi * m.Bj) / (m.Cj * m.a^2)

/-! ### 2. Core Equivalence and Cancellation Theorems -/

/-- **Master Theorem 1 (Activity Cancellation in Photopeak Cross-Section)**:
    The partial photopeak cross-section S^(peak)_i is completely independent
    of source activity and isolates the partner's transmission:
    S^(peak)_i = 4π * P_j / (C_j * P_ij * W(0) * a²). -/
theorem Speak_independent_of_activity (m : CascadeModel) (pi : ℝ) (hpi : pi ≠ 0) :
    Speak m pi = (4 * pi * m.Pj) / (m.Cj * m.Pij * m.W0 * m.a^2) := by
  dsimp [Speak, derivedActivity]
  have ha  : m.a ≠ 0 := ne_of_gt m.ha
  have _ha2 : m.a^2 ≠ 0 := pow_ne_zero 2 ha
  have _hW0 : m.W0 ≠ 0 := ne_of_gt m.hW0
  have _hPi : m.Pi ≠ 0 := ne_of_gt m.hPi
  have _hPj : m.Pj ≠ 0 := ne_of_gt m.hPj
  have _hPij: m.Pij ≠ 0 := ne_of_gt m.hPij
  have _hCi : m.Ci ≠ 0 := ne_of_gt m.hCi
  have _hCj : m.Cj ≠ 0 := ne_of_gt m.hCj
  field_simp

/-- **Master Theorem 2 (Intrinsic Peak-to-Total Ratio as Branching Ratio)**:
    The cross-ratio of the partial photopeak cross-section to the conjugate
    total absorption cross-section recovers the intrinsic Peak-to-Total ratio (P/T)_i
    independent of geometry, detector area, and activity:
    (P/T)_i = S^(peak)_i / S_v,j = P_j / (B_j * P_ij * W(0)). -/
theorem peak_to_total_cross_ratio (m : CascadeModel) (pi : ℝ) (hpi : pi ≠ 0) :
    Speak m pi / Sv m pi = m.Pj / (m.Bj * m.Pij * m.W0) := by
  rw [Speak_independent_of_activity m pi hpi]
  dsimp [Sv]
  have ha  : m.a ≠ 0 := ne_of_gt m.ha
  have _ha2 : m.a^2 ≠ 0 := pow_ne_zero 2 ha
  have _hW0 : m.W0 ≠ 0 := ne_of_gt m.hW0
  have _hPi : m.Pi ≠ 0 := ne_of_gt m.hPi
  have _hPj : m.Pj ≠ 0 := ne_of_gt m.hPj
  have _hPij: m.Pij ≠ 0 := ne_of_gt m.hPij
  have _hCi : m.Ci ≠ 0 := ne_of_gt m.hCi
  have _hCj : m.Cj ≠ 0 := ne_of_gt m.hCj
  have _hBj : m.Bj ≠ 0 := ne_of_gt m.hBj
  field_simp

/-- **Master Theorem 3 (Constructive Positivity of Cross-Sections)**:
    Both the partial and total cross-sections are strictly positive
    for any physical decay cascade. -/
theorem cross_sections_positive (m : CascadeModel) (pi : ℝ) (hpi : 0 < pi) :
    0 < Speak m pi ∧ 0 < Sv m pi := by
  have ha : 0 < m.a := m.ha
  have ha2 : 0 < m.a^2 := sq_pos_of_pos ha
  have hW0 : 0 < m.W0 := m.hW0
  have _hPi : 0 < m.Pi := m.hPi
  have hPj : 0 < m.Pj := m.hPj
  have hPij: 0 < m.Pij := m.hPij
  have _hCi : 0 < m.Ci := m.hCi
  have hCj : 0 < m.Cj := m.hCj
  have hBj : 0 < m.Bj := m.hBj
  constructor
  · rw [Speak_independent_of_activity m pi (ne_of_gt hpi)]
    have h_num : 0 < 4 * pi * m.Pj := by positivity
    have h_den : 0 < m.Cj * m.Pij * m.W0 * m.a^2 := by positivity
    exact div_pos h_num h_den
  · dsimp [Sv]
    have h_num : 0 < 4 * pi * m.Bj := by positivity
    have h_den : 0 < m.Cj * m.a^2 := by positivity
    exact div_pos h_num h_den

end InfoGeometry.Nuclear.CrossSectionDuality
