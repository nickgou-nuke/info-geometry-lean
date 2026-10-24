/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.SignedBogoliubovCAR

/-! Six consumer elaboration tests for the existing signed particle-hole API.
No new owner definitions or forwarding declarations are introduced. -/
open InfoGeometry.OperatorAlgebra

section
variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
variable (a c b d : A) (u v : R)
variable (haa : a * a = 0) (hcc : c * c = 0)
variable (hbb : b * b = 0) (hdd : d * d = 0)
variable (hac : thermalAnticommutator a c = 1)
variable (hbd : thermalAnticommutator b d = 1)
variable (hab : thermalAnticommutator a b = 0)
variable (hcd : thermalAnticommutator c d = 0)
variable (had : thermalAnticommutator a d = 0)
variable (hbc : thermalAnticommutator b c = 0)

example : thermalAnticommutator (u • a + v • d) (u • b - v • c) = 0 := by
  exact particleHole_annihilator_cross a c b d u v hac hbd hab hcd

example : thermalAnticommutator (u • c + v • b) (u • d - v • a) = 0 := by
  apply particleHole_annihilator_cross c a d b u v
  · rw [thermalAnticommutator_symm]; exact hac
  · rw [thermalAnticommutator_symm]; exact hbd
  · exact hcd
  · exact hab

example : thermalAnticommutator (u • a + v • d) (u • d - v • a) = 0 := by
  exact particleHole_mixed_cross a d u v v haa hdd had

example : thermalAnticommutator (u • b - v • c) (u • c + v • b) = 0 := by
  simpa only [neg_smul, sub_eq_add_neg, neg_neg] using
    particleHole_mixed_cross b c u (-v) (-v) hbb hcc hbc

example : thermalAnticommutator (u • a + v • d) (u • c + v • b) =
    (u * u + v * v) • (1 : A) := by
  exact particleHole_diagonal a c b d u v v hac hbd hab hcd

example : thermalAnticommutator (u • b - v • c) (u • d - v • a) =
    (u * u + v * v) • (1 : A) := by
  have hba : thermalAnticommutator b a = 0 := by
    rw [thermalAnticommutator_symm]; exact hab
  have hdc : thermalAnticommutator d c = 0 := by
    rw [thermalAnticommutator_symm]; exact hcd
  simpa only [neg_smul, sub_eq_add_neg, neg_mul_neg] using
    particleHole_diagonal b d a c u (-v) (-v) hbd hac hba hdc

end
