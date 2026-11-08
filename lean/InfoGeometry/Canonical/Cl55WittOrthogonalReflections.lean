import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Explicit orthogonal reflections on the split Witt carrier

This owner is deliberately independent of the Clifford/Lie closure files.  It
formalizes only the elementary split quadratic carrier
`(Fin 5 → ℚ × ℚ)` with form `∑ uᵢ vᵢ`, together with particle--hole swaps.
No Pin group, spin lift, or Weyl-group identification is asserted here.
-/

namespace InfoGeometry.Canonical.Cl55WittOrthogonalReflections

abbrev WittCarrier := Fin 5 → ℚ × ℚ

def splitQuadratic (x : WittCarrier) : ℚ :=
  ∑ i : Fin 5, (x i).1 * (x i).2

def particleHole (x : WittCarrier) : WittCarrier :=
  fun i => ((x i).2, (x i).1)

def modeParticleHole (k : Fin 5) (x : WittCarrier) : WittCarrier :=
  fun i => if i = k then ((x i).2, (x i).1) else x i

@[simp] theorem particleHole_particleHole (x : WittCarrier) :
    particleHole (particleHole x) = x := by
  funext i
  simp [particleHole]

@[simp] theorem modeParticleHole_modeParticleHole (k : Fin 5) (x : WittCarrier) :
    modeParticleHole k (modeParticleHole k x) = x := by
  funext i
  by_cases h : i = k <;> simp [modeParticleHole, h]

theorem splitQuadratic_particleHole (x : WittCarrier) :
    splitQuadratic (particleHole x) = splitQuadratic x := by
  simp only [splitQuadratic, particleHole]
  apply Finset.sum_congr rfl
  intro i hi
  exact mul_comm _ _

theorem splitQuadratic_modeParticleHole (k : Fin 5) (x : WittCarrier) :
    splitQuadratic (modeParticleHole k x) = splitQuadratic x := by
  classical
  unfold splitQuadratic modeParticleHole
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : i = k
  · subst i
    simp [mul_comm]
  · simp [h]

end InfoGeometry.Canonical.Cl55WittOrthogonalReflections
