import Mathlib

/-!
# RP³ Brillouin octupole finite operators

Repaired external file: nonsymmorphic momentum reflections on triples of real
coordinates and their explicit composition law.
-/

noncomputable section

namespace RP3Topology

def WaveVector := ℝ × ℝ × ℝ

/-- k-NS reflection operator `M_x`. -/
def Mx (k : WaveVector) : WaveVector := (-k.1, k.2.1 + Real.pi, k.2.2 + Real.pi)

/-- k-NS reflection operator `M_y`. -/
def My (k : WaveVector) : WaveVector := (k.1 + Real.pi, -k.2.1, k.2.2 + Real.pi)

/-- k-NS reflection operator `M_z`. -/
def Mz (k : WaveVector) : WaveVector := (k.1 + Real.pi, k.2.1 + Real.pi, -k.2.2)

/-- Composition target `P_xy = M_x ∘ M_y`. -/
def Pxy (k : WaveVector) : WaveVector := (-(k.1 + Real.pi), -k.2.1 + Real.pi, k.2.2 + 2 * Real.pi)

/-- Direct coordinate computation of `M_x ∘ M_y`. -/
theorem M_x_comp_M_y_eq_P_xy (k : WaveVector) : Mx (My k) = Pxy k := by
  rcases k with ⟨x, yz⟩
  rcases yz with ⟨y, z⟩
  simp [Mx, My, Pxy]
  ring

#check M_x_comp_M_y_eq_P_xy

end RP3Topology
