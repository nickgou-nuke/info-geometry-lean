import InfoGeometry.Projective.ProjectiveMap

/-!
# InfoGeometry.Projective.Dynamics

Projective dynamical maps induced by the doubled-space `Cl(1,1)` operators.
-/

namespace InfoGeometry.Projective.Dynamics
end InfoGeometry.Projective.Dynamics

section KreinClifford

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace ProjectiveDynamics

/-- Projective dynamics induced by the modular involution `J`. -/
def J : ProjectiveState (E := E) → ProjectiveState (E := E) :=
  projectiveMap (E := E) (modularJ (E := E))

/-- Projective dynamics induced by the spectral sign operator `ε`. -/
def epsilon : ProjectiveState (E := E) → ProjectiveState (E := E) :=
  projectiveMap (E := E) (spectralEpsilon (E := E))

/-- Projective dynamics induced by the Clifford complex structure `I`. -/
def I : ProjectiveState (E := E) → ProjectiveState (E := E) :=
  projectiveMap (E := E) (complexI (E := E))

@[simp] lemma J_projectivize (v : DoubledSpace E) :
    J (E := E) (projectivize (E := E) v)
      = projectivize (E := E) (modularJ (E := E) v) := rfl

@[simp] lemma epsilon_projectivize (v : DoubledSpace E) :
    epsilon (E := E) (projectivize (E := E) v)
      = projectivize (E := E) (spectralEpsilon (E := E) v) := rfl

@[simp] lemma I_projectivize (v : DoubledSpace E) :
    I (E := E) (projectivize (E := E) v)
      = projectivize (E := E) (complexI (E := E) v) := rfl

/-- The projective map induced by `-Id` is the identity (ray quotient kills sign). -/
lemma projectiveMap_neg_id :
    projectiveMap (E := E) (-(ContinuousLinearMap.id ℝ (DoubledSpace E))) = id := by
  funext q
  refine Quotient.inductionOn q ?_
  intro v
  show projectivize (E := E) ((-(ContinuousLinearMap.id ℝ (DoubledSpace E))) v)
      = projectivize (E := E) v
  have hsmul : projectivize (E := E) ((-1 : Gauge) • v) = projectivize (E := E) v := by
    simpa using (projectivize_smul (E := E) (-1 : Gauge) v)
  simpa using hsmul

/-- `J² = Id` on projective states. -/
lemma J_sq :
    (J (E := E)) ∘ (J (E := E)) = id := by
  calc
    (J (E := E)) ∘ (J (E := E))
        = projectiveMap (E := E) ((modularJ (E := E)).comp (modularJ (E := E))) := by
            symm
            simpa [J] using
              (projectiveMap_comp (E := E) (modularJ (E := E)) (modularJ (E := E)))
    _ = projectiveMap (E := E) (ContinuousLinearMap.id ℝ (DoubledSpace E)) := by
          simp [modularJ_involution (E := E)]
    _ = id := projectiveMap_id (E := E)

/-- `ε² = Id` on projective states. -/
lemma epsilon_sq :
    (epsilon (E := E)) ∘ (epsilon (E := E)) = id := by
  calc
    (epsilon (E := E)) ∘ (epsilon (E := E))
        = projectiveMap (E := E)
            ((spectralEpsilon (E := E)).comp (spectralEpsilon (E := E))) := by
              symm
              simpa [epsilon] using
                (projectiveMap_comp (E := E)
                  (spectralEpsilon (E := E)) (spectralEpsilon (E := E)))
    _ = projectiveMap (E := E) (ContinuousLinearMap.id ℝ (DoubledSpace E)) := by
          simp [spectralEpsilon_involution (E := E)]
    _ = id := projectiveMap_id (E := E)

/-- `I² = -Id` upstairs becomes `I² = Id` on projective rays. -/
lemma I_sq :
    (I (E := E)) ∘ (I (E := E)) = id := by
  calc
    (I (E := E)) ∘ (I (E := E))
        = projectiveMap (E := E) ((complexI (E := E)).comp (complexI (E := E))) := by
            symm
            simpa [I] using
              (projectiveMap_comp (E := E) (complexI (E := E)) (complexI (E := E)))
    _ = projectiveMap (E := E) (-(ContinuousLinearMap.id ℝ (DoubledSpace E))) := by
          rw [complexI_sq (E := E)]
    _ = id := projectiveMap_neg_id (E := E)

@[simp] lemma J_vacuum : J (E := E) (vacuum (E := E)) = vacuum (E := E) := by
  exact projectiveMap_vacuum (E := E) (modularJ (E := E))

@[simp] lemma epsilon_vacuum : epsilon (E := E) (vacuum (E := E)) = vacuum (E := E) := by
  exact projectiveMap_vacuum (E := E) (spectralEpsilon (E := E))

@[simp] lemma I_vacuum : I (E := E) (vacuum (E := E)) = vacuum (E := E) := by
  exact projectiveMap_vacuum (E := E) (complexI (E := E))

end ProjectiveDynamics

end KreinClifford
