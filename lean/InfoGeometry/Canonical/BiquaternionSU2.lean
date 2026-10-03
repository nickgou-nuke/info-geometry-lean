import Mathlib.Data.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.QuaternionBasis

noncomputable section

namespace InfoGeometry.Canonical.Biquaternions

open Complex

/-!
# Biquaternion Commutators and the `su(2)` Lie Algebra

This module proves the commutator relations of the three pure quaternion
generators after complexification. These are the `su(2)` Lie-algebra bracket
relations (with the displayed normalization); they do not by themselves define
the Lie group `SU(2)`, a representation of that group, or a physical weak-force
action. Those require separate group and representation constructions.
-/

/-- The biquaternions are the quaternions over the complex numbers. -/
abbrev Biquaternion := Quaternion ℂ

/-- The pure biquaternion generators corresponding to Pauli matrices (scaled). -/
def Qi : Biquaternion := ⟨0, 1, 0, 0⟩
def Qj : Biquaternion := ⟨0, 0, 1, 0⟩
def Qk : Biquaternion := ⟨0, 0, 0, 1⟩

/-- A standard Lie bracket (commutator) for the biquaternion algebra. -/
def commutator (A B : Biquaternion) : Biquaternion := A * B - B * A

/-- The first pure-imaginary commutator, `[Qi,Qj] = 2 Qk`. -/
theorem biquaternion_su2_ij : commutator Qi Qj = (2 : ℂ) • Qk := by
  dsimp [commutator, Qi, Qj, Qk]
  ext <;> norm_num

/-- The second pure-imaginary commutator, `[Qj,Qk] = 2 Qi`. -/
theorem biquaternion_su2_jk : commutator Qj Qk = (2 : ℂ) • Qi := by
  dsimp [commutator, Qi, Qj, Qk]
  ext <;> norm_num

/-- The third pure-imaginary commutator, `[Qk,Qi] = 2 Qj`. -/
theorem biquaternion_su2_ki : commutator Qk Qi = (2 : ℂ) • Qj := by
  dsimp [commutator, Qi, Qj, Qk]
  ext <;> norm_num

end InfoGeometry.Canonical.Biquaternions
