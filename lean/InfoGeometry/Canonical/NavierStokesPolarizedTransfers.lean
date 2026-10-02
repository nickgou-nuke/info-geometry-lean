import InfoGeometry.Canonical.NavierStokesBridge

/-!
# Nondegenerate transfers between the existing doubled sheets

The legacy `backwardWave` vanishes because its input is lifted to the positive
sheet before the negative projector is applied.  The operators below use the
existing embedding, projection, and sheet exchange to retain both mixed Peirce
corners. They describe linear operators, not solutions of a fluid PDE.
-/

noncomputable section

namespace InfoGeometry.Canonical.NavierStokesPolarizedTransfers

open InfoGeometry.Krein

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- The existing positive-sheet lift, named for the corner identities below. -/
def baseLift (u : VelocityField E) : AlgebraEnd E :=
  embedBase.comp (u.comp projBase)

/-- Transfer from the negative sheet to the positive sheet. -/
def upward (u : VelocityField E) : AlgebraEnd E :=
  (baseLift u).comp modular_j

/-- Transfer from the positive sheet to the negative sheet. -/
def downward (v : VelocityField E) : AlgebraEnd E :=
  modular_j.comp (baseLift v)

@[simp] theorem baseLift_apply (u : VelocityField E) (z : DoubledSpace E) :
    baseLift u z = to_doubled (u (WithLp.fst z)) 0 := rfl

@[simp] theorem upward_apply (u : VelocityField E) (z : DoubledSpace E) :
    upward u z = to_doubled (u (WithLp.snd z)) 0 := rfl

@[simp] theorem downward_apply (v : VelocityField E) (z : DoubledSpace E) :
    downward v z = to_doubled 0 (v (WithLp.fst z)) := rfl

/-- Each directed transfer is nilpotent; the other sheet is its missing input. -/
theorem upward_comp_upward (u v : VelocityField E) :
    (upward u).comp (upward v) = 0 := by
  apply ContinuousLinearMap.ext
  intro z
  apply DoubledSpace.ext <;> simp

theorem downward_comp_downward (u v : VelocityField E) :
    (downward u).comp (downward v) = 0 := by
  apply ContinuousLinearMap.ext
  intro z
  apply DoubledSpace.ext <;> simp

/-- Oppositely directed transfers retain the positive-sheet product. -/
theorem upward_comp_downward (u v : VelocityField E) :
    (upward u).comp (downward v) = baseLift (u.comp v) := by
  apply ContinuousLinearMap.ext
  intro z
  apply DoubledSpace.ext <;> simp

/-- The reversed product lives on the negative sheet. -/
theorem downward_comp_upward (u v : VelocityField E) :
    (downward u).comp (upward v) =
      modular_j.comp ((baseLift (u.comp v)).comp modular_j) := by
  apply ContinuousLinearMap.ext
  intro z
  apply DoubledSpace.ext <;> simp [modular_j]

/-- The two mixed corners determine the original base operators faithfully. -/
theorem upward_injective : Function.Injective (upward (E := E)) := by
  intro u v h
  ext x
  have hx := congrArg (fun T : AlgebraEnd E => WithLp.fst (T (to_doubled 0 x))) h
  simpa using hx

theorem downward_injective : Function.Injective (downward (E := E)) := by
  intro u v h
  ext x
  have hx := congrArg (fun T : AlgebraEnd E => WithLp.snd (T (to_doubled x 0))) h
  simpa using hx

/-- The two-way transfer whose square has negative diagonal products. -/
def pairedGenerator (u v : VelocityField E) : AlgebraEnd E :=
  upward u - downward v

theorem pairedGenerator_sq (u v : VelocityField E) :
    (pairedGenerator u v).comp (pairedGenerator u v) =
      -(baseLift (u.comp v)) -
        modular_j.comp ((baseLift (v.comp u)).comp modular_j) := by
  apply ContinuousLinearMap.ext
  intro z
  apply DoubledSpace.ext <;>
    simp [pairedGenerator, modular_j, WithLp.sub_fst, WithLp.sub_snd]

/-- Diagnostic of the old readout; this is not a statement about fluid helicity. -/
theorem legacy_backwardWave_eq_zero (u : VelocityField E) :
    backwardWave u = 0 := by
  apply ContinuousLinearMap.ext
  intro z
  apply DoubledSpace.ext <;>
    simp [backwardWave, embedBase, projBase, spectral_epsilon, to_doubled]

theorem legacy_twinWaveHelicity_eq_zero (u : VelocityField E)
    (weight : AlgebraEnd E →L[ℝ] ℝ) : twinWaveHelicity u weight = 0 := by
  simp [twinWaveHelicity, legacy_backwardWave_eq_zero]

end InfoGeometry.Canonical.NavierStokesPolarizedTransfers
