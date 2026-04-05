import InfoGeometry.Projective.ProjectiveMap

/-!
# InfoGeometry.Projective.Dynamics

Projective dynamical maps induced by the doubled-space `Cl(1,1)` operators.
-/


namespace InfoGeometry

namespace Projective.Dynamics
end Projective.Dynamics

section KreinClifford

open InfoGeometry.Krein
open InfoGeometry.Projective

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace ProjectiveDynamics

/-- Projective dynamics induced by the modular involution `J`. -/
noncomputable def J : ProjectiveState (E := E) → ProjectiveState (E := E) :=
  projectiveMap (E := E) (modular_j (E := E))

/-- Projective dynamics induced by the spectral sign operator `ε`. -/
noncomputable def epsilon : ProjectiveState (E := E) → ProjectiveState (E := E) :=
  projectiveMap (E := E) (spectral_epsilon (E := E))

/-- Projective dynamics induced by the Clifford complex structure `I`. -/
noncomputable def I : ProjectiveState (E := E) → ProjectiveState (E := E) :=
  projectiveMap (E := E) (complex_i (E := E))

@[simp] lemma J_projectivize (v : DoubledSpace E) :
    J (E := E) (projectivize (E := E) v)
      = projectivize (E := E) (modular_j (E := E) v) := rfl

@[simp] lemma epsilon_projectivize (v : DoubledSpace E) :
    epsilon (E := E) (projectivize (E := E) v)
      = projectivize (E := E) (spectral_epsilon (E := E) v) := rfl

@[simp] lemma I_projectivize (v : DoubledSpace E) :
    I (E := E) (projectivize (E := E) v)
      = projectivize (E := E) (complex_i (E := E) v) := rfl

/-- Upstairs sign ambiguity disappears on projective rays. -/
lemma projectiveMap_neg_id :
    projectiveMap (E := E) (-(ContinuousLinearMap.id ℝ (DoubledSpace E))) = id := by
  rw [projectiveMap_neg (E := E) (A := ContinuousLinearMap.id ℝ (DoubledSpace E))]
  exact projectiveMap_id (E := E)

/-- The exact projective product `J ∘ ε = I`. -/
lemma J_comp_epsilon :
    (J (E := E)) ∘ (epsilon (E := E)) = I (E := E) := by
  calc
    (J (E := E)) ∘ (epsilon (E := E))
        = projectiveMap (E := E) ((modular_j (E := E)).comp (spectral_epsilon (E := E))) := by
            symm
            simpa [ProjectiveDynamics.J, ProjectiveDynamics.epsilon] using
              (projectiveMap_comp (E := E) (modular_j (E := E)) (spectral_epsilon (E := E)))
    _ = projectiveMap (E := E) (complex_i (E := E)) := by
          rfl
    _ = I (E := E) := rfl

/-- The exact projective product `ε ∘ J = I`; upstairs sign changes vanish on rays. -/
lemma epsilon_comp_J :
    (epsilon (E := E)) ∘ (J (E := E)) = I (E := E) := by
  have hswap :
      (spectral_epsilon (E := E)).comp (modular_j (E := E))
        = -(complex_i (E := E)) := by
    apply ContinuousLinearMap.ext
    intro u
    apply DoubledSpace.ext <;> simp [complex_i]
  calc
    (epsilon (E := E)) ∘ (J (E := E))
        = projectiveMap (E := E) ((spectral_epsilon (E := E)).comp (modular_j (E := E))) := by
            symm
            simpa [ProjectiveDynamics.J, ProjectiveDynamics.epsilon] using
              (projectiveMap_comp (E := E) (spectral_epsilon (E := E)) (modular_j (E := E)))
    _ = projectiveMap (E := E) (-(complex_i (E := E))) := by
          rw [hswap]
    _ = projectiveMap (E := E) (complex_i (E := E)) := by
          rw [projectiveMap_neg (E := E) (A := complex_i (E := E))]
    _ = I (E := E) := rfl

/-- The exact projective product `J ∘ I = ε`. -/
lemma J_comp_I :
    (J (E := E)) ∘ (I (E := E)) = epsilon (E := E) := by
  calc
    (J (E := E)) ∘ (I (E := E))
        = projectiveMap (E := E) ((modular_j (E := E)).comp (complex_i (E := E))) := by
            symm
            simpa [ProjectiveDynamics.J, ProjectiveDynamics.I] using
              (projectiveMap_comp (E := E) (modular_j (E := E)) (complex_i (E := E)))
    _ = projectiveMap (E := E) (spectral_epsilon (E := E)) := by
          unfold InfoGeometry.Krein.complex_i
          rw [← ContinuousLinearMap.comp_assoc, modular_j_involution, ContinuousLinearMap.id_comp]
    _ = epsilon (E := E) := rfl

/-- The exact projective product `I ∘ J = ε`; upstairs sign changes vanish on rays. -/
lemma I_comp_J :
    (I (E := E)) ∘ (J (E := E)) = epsilon (E := E) := by
  have hswap :
      (complex_i (E := E)).comp (modular_j (E := E))
        = -(spectral_epsilon (E := E)) := by
    apply ContinuousLinearMap.ext
    intro u
    apply DoubledSpace.ext <;> simp [complex_i]
  calc
    (I (E := E)) ∘ (J (E := E))
        = projectiveMap (E := E) ((complex_i (E := E)).comp (modular_j (E := E))) := by
            symm
            simpa [ProjectiveDynamics.J, ProjectiveDynamics.I] using
              (projectiveMap_comp (E := E) (complex_i (E := E)) (modular_j (E := E)))
    _ = projectiveMap (E := E) (-(spectral_epsilon (E := E))) := by
          rw [hswap]
    _ = projectiveMap (E := E) (spectral_epsilon (E := E)) := by
          rw [projectiveMap_neg (E := E) (A := spectral_epsilon (E := E))]
    _ = epsilon (E := E) := rfl

/-- The exact projective product `I ∘ ε = J`. -/
lemma I_comp_epsilon :
    (I (E := E)) ∘ (epsilon (E := E)) = J (E := E) := by
  calc
    (I (E := E)) ∘ (epsilon (E := E))
        = projectiveMap (E := E) ((complex_i (E := E)).comp (spectral_epsilon (E := E))) := by
            symm
            simpa [ProjectiveDynamics.I, ProjectiveDynamics.epsilon] using
              (projectiveMap_comp (E := E) (complex_i (E := E)) (spectral_epsilon (E := E)))
    _ = projectiveMap (E := E) (modular_j (E := E)) := by
          unfold InfoGeometry.Krein.complex_i
          rw [ContinuousLinearMap.comp_assoc, spectral_epsilon_involution, ContinuousLinearMap.comp_id]
    _ = J (E := E) := rfl

/-- The exact projective product `ε ∘ I = J`; upstairs sign changes vanish on rays. -/
lemma epsilon_comp_I :
    (epsilon (E := E)) ∘ (I (E := E)) = J (E := E) := by
  have hswap :
      (spectral_epsilon (E := E)).comp (complex_i (E := E))
        = -(modular_j (E := E)) := by
    apply ContinuousLinearMap.ext
    intro u
    apply DoubledSpace.ext <;> simp [complex_i]
  calc
    (epsilon (E := E)) ∘ (I (E := E))
        = projectiveMap (E := E) ((spectral_epsilon (E := E)).comp (complex_i (E := E))) := by
            symm
            simpa [ProjectiveDynamics.I, ProjectiveDynamics.epsilon] using
              (projectiveMap_comp (E := E) (spectral_epsilon (E := E)) (complex_i (E := E)))
    _ = projectiveMap (E := E) (-(modular_j (E := E))) := by
          rw [hswap]
    _ = projectiveMap (E := E) (modular_j (E := E)) := by
          rw [projectiveMap_neg (E := E) (A := modular_j (E := E))]
    _ = J (E := E) := rfl

/-- On projective real Krein rays, the descended `Cl(1,1)` generators commute. -/
lemma J_epsilon_commute :
    (J (E := E)) ∘ (epsilon (E := E)) = (epsilon (E := E)) ∘ (J (E := E)) := by
  rw [J_comp_epsilon, epsilon_comp_J]

/-- On projective real Krein rays, `J` and `I` commute. -/
lemma J_I_commute :
    (J (E := E)) ∘ (I (E := E)) = (I (E := E)) ∘ (J (E := E)) := by
  rw [J_comp_I, I_comp_J]

/-- On projective real Krein rays, `ε` and `I` commute. -/
lemma epsilon_I_commute :
    (epsilon (E := E)) ∘ (I (E := E)) = (I (E := E)) ∘ (epsilon (E := E)) := by
  rw [epsilon_comp_I, I_comp_epsilon]

/-- `J² = Id` on projective states. -/
lemma J_sq :
    (J (E := E)) ∘ (J (E := E)) = id := by
  calc
    (J (E := E)) ∘ (J (E := E))
        = projectiveMap (E := E) ((modular_j (E := E)).comp (modular_j (E := E))) := by
            symm
            simpa [ProjectiveDynamics.J] using
              (projectiveMap_comp (E := E) (modular_j (E := E)) (modular_j (E := E)))
    _ = projectiveMap (E := E) (ContinuousLinearMap.id ℝ (DoubledSpace E)) := by
          simp [modular_j_involution (E := E)]
    _ = id := projectiveMap_id (E := E)

/-- `ε² = Id` on projective states. -/
lemma epsilon_sq :
    (epsilon (E := E)) ∘ (epsilon (E := E)) = id := by
  calc
    (epsilon (E := E)) ∘ (epsilon (E := E))
        = projectiveMap (E := E)
            ((spectral_epsilon (E := E)).comp (spectral_epsilon (E := E))) := by
              symm
              simpa [ProjectiveDynamics.epsilon] using
                (projectiveMap_comp (E := E)
                  (spectral_epsilon (E := E)) (spectral_epsilon (E := E)))
    _ = projectiveMap (E := E) (ContinuousLinearMap.id ℝ (DoubledSpace E)) := by
          simp [spectral_epsilon_involution (E := E)]
    _ = id := projectiveMap_id (E := E)

/-- `I² = -Id` upstairs becomes `I² = Id` on projective rays. -/
lemma I_sq :
    (I (E := E)) ∘ (I (E := E)) = id := by
  calc
    (I (E := E)) ∘ (I (E := E))
        = projectiveMap (E := E) ((complex_i (E := E)).comp (complex_i (E := E))) := by
            symm
            simpa [ProjectiveDynamics.I] using
              (projectiveMap_comp (E := E) (complex_i (E := E)) (complex_i (E := E)))
    _ = projectiveMap (E := E) (-(ContinuousLinearMap.id ℝ (DoubledSpace E))) := by
          rw [complex_i_sq (E := E)]
    _ = id := projectiveMap_neg_id (E := E)

@[simp] lemma J_vacuum : J (E := E) (vacuum (E := E)) = vacuum (E := E) := by
  exact projectiveMap_vacuum (E := E) (modular_j (E := E))

@[simp] lemma epsilon_vacuum : epsilon (E := E) (vacuum (E := E)) = vacuum (E := E) := by
  exact projectiveMap_vacuum (E := E) (spectral_epsilon (E := E))

@[simp] lemma I_vacuum : I (E := E) (vacuum (E := E)) = vacuum (E := E) := by
  exact projectiveMap_vacuum (E := E) (complex_i (E := E))

end ProjectiveDynamics

end KreinClifford

end InfoGeometry
