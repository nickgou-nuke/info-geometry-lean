import Mathlib

/-!
# Explicit finite quasiparticle CAR bridge

This owner gives a concrete one-mode fermionic realization on `2 × 2` real
matrices. It is intentionally finite and exact: creation and annihilation are
nilpotent and satisfy the canonical anticommutation relation. No phonon or RPA
claim is made here.
-/

noncomputable section

namespace InfoGeometry.Nuclear.NuclearQuasiparticleCARBridge

abbrev Mode2 := Fin 2
abbrev Mat2 := Matrix Mode2 Mode2 ℝ

/-- One-mode annihilation operator. -/
def annihilation : Mat2 := !![0, 1; 0, 0]

/-- One-mode creation operator. -/
def creation : Mat2 := !![0, 0; 1, 0]

/-- Fermionic number projector `a† a`. -/
def numberProjector : Mat2 := creation * annihilation

@[simp] theorem annihilation_sq : annihilation * annihilation = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [annihilation, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem creation_sq : creation * creation = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [creation, Matrix.mul_apply, Fin.sum_univ_two]

/-- Exact one-mode CAR: `{a,a†}=1`. -/
theorem annihilation_creation_anticommutator :
    annihilation * creation + creation * annihilation = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [annihilation, creation]

@[simp] theorem numberProjector_idempotent :
    numberProjector * numberProjector = numberProjector := by
  unfold numberProjector
  have hcar := annihilation_creation_anticommutator
  have hrewrite : annihilation * creation = 1 - creation * annihilation := by
    calc
      annihilation * creation =
          (annihilation * creation + creation * annihilation) -
            creation * annihilation := by noncomm_ring
      _ = 1 - creation * annihilation := by rw [hcar]
  calc
    (creation * annihilation) * (creation * annihilation) =
        creation * (annihilation * creation) * annihilation := by
          simp only [Matrix.mul_assoc]
    _ = creation * (1 - creation * annihilation) * annihilation := by rw [hrewrite]
    _ = creation * annihilation := by
      rw [mul_sub, sub_mul]
      simp only [mul_one]
      rw [Matrix.mul_assoc, Matrix.mul_assoc creation annihilation annihilation,
        annihilation_sq, mul_zero]
      simp

/-- The occupied projector is complementary to `a a†`. -/
theorem complementary_projectors :
    annihilation * creation + numberProjector = 1 := by
  simpa [numberProjector] using annihilation_creation_anticommutator

end InfoGeometry.Nuclear.NuclearQuasiparticleCARBridge

end noncomputable section
